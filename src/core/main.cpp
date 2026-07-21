#include "common.h"
#ifdef _WIN32
#include <windows.h>
#ifdef RW_D3D9
#include <d3d9.h>
#endif
#endif
#include <time.h>
#include "rpmatfx.h"
#include "rphanim.h"
#include "rpskin.h"
#include "rtbmp.h"
#include "rtpng.h"
#ifdef ANISOTROPIC_FILTERING
#include "rpanisot.h"
#endif

#include "main.h"
#include "CdStream.h"
#include "General.h"
#include "RwHelper.h"
#include "Clouds.h"
#include "Draw.h"
#include "Sprite.h"
#include "Sprite2d.h"
#include "FileLoader.h"
#include "Renderer.h"
#include "Coronas.h"
#include "WaterLevel.h"
#include "Weather.h"
#include "Glass.h"
#include "WaterCannon.h"
#include "SpecialFX.h"
#include "Shadows.h"
#include "Skidmarks.h"
#include "Antennas.h"
#include "Rubbish.h"
#include "Particle.h"
#include "Pickups.h"
#include "WeaponEffects.h"
#include "Weapon.h"
#include "ColPoint.h"
#include "EventList.h"
#include "PointLights.h"
#include "Fluff.h"
#include "Replay.h"
#include "Camera.h"
#include "World.h"
#include "Ped.h"
#include "PlayerPed.h"
#include "Wanted.h"
#include "Streaming.h"
#include "Font.h"
#include "Pad.h"
#include "Hud.h"
#include "User.h"
#include "Messages.h"
#include "Darkel.h"
#include "Garages.h"
#include "MusicManager.h"
#include "VisibilityPlugins.h"
#include "NodeName.h"
#include "DMAudio.h"
#include "CutsceneMgr.h"
#include "Lights.h"
#include "Credits.h"
#include "ZoneCull.h"
#include "Timecycle.h"
#include "TxdStore.h"
#include "FileMgr.h"
#include "Text.h"
#include "RpAnimBlend.h"
#include "Frontend.h"
#include "AnimViewer.h"
#include "Script.h"
#include "PathFind.h"
#include "Debug.h"
#include "Console.h"
#include "timebars.h"
#include "GenericGameStorage.h"
#include "MemoryCard.h"
#include "MemoryHeap.h"
#include "SceneEdit.h"
#include "debugmenu.h"
#include "Clock.h"
#include "Occlusion.h"
#include "Ropes.h"
#include "postfx.h"
#include "custompipes.h"
#include "screendroplets.h"
#include "VarConsole.h"
#ifdef USE_OUR_VERSIONING
#include "GitSHA1.h"
#endif

extern int gRevcBackBufferWidth;
extern int gRevcBackBufferHeight;

static FILE *gRevcCoreLog = nil;
// Keep a short hosted-frame trace enabled for the portal build. RevcLogCore
// stops after the first few gameplay frames, so this is useful for diagnosing
// camera/render-target startup without producing an ever-growing log.
static bool gRevcLogEnabled = true;
static uint32 gRevcFrameLogCount = 0;

#if defined(REVC_DLL) && defined(RW_D3D9)
namespace rw { namespace d3d {
extern int32 nativeRasterOffset;
extern IDirect3DDevice9 *d3ddevice;
} }
struct RevcD3dRasterExt
{
	void *texture;
	void *palette;
	void *lockedSurf;
	uint32 format;
	uint32 bpp;
	bool hasAlpha;
	bool customFormat;
	bool autogenMipmap;
};
#endif

#ifdef REVC_DLL
extern void ReVC_SetPortalInputEnabled(bool enabled);
extern bool ReVC_IsPortalInputEnabled(void);
static void RevcLogPortal(const char *msg);

struct RevcPortalBridgeState
{
	bool enabled;
	bool viewValid;
	bool preparePending;
	bool enterPending;
	bool prepared;
	bool playerVisibilitySaved;
	bool savedPlayerVisibility;
	bool playerProtectionSaved;
	bool savedBulletProof;
	bool savedFireProof;
	bool savedCollisionProof;
	bool savedMeleeProof;
	bool savedExplosionProof;
	bool savedCanBeDamaged;
	bool entered;
	bool returnRequested;
	bool havePreviousReturnDistance;
	bool returnPlaceKeyDown;
	CVector position;
	CVector right;
	CVector up;
	CVector forward;
	float fov;
	float viewWindowX;
	float viewWindowY;
	CVector preparePosition;
	float prepareHeading;
	CVector enterPosition;
	float enterHeading;
	CVector returnPosition;
	float returnYaw;
	float previousReturnDistance;
	CVector previousReturnSample;
	uint32 returnCooldownUntil;
	uint32 playerProtectionUntil;
	uint32 returnDebugCounter;
	RwRaster *returnRaster;
	IDirect3DTexture9 *returnTexture;
	int32 returnTextureWidth;
	int32 returnTextureHeight;
	bool returnTextureCopyLogged;
	uint32 returnTextureCopyFailures;
	uint32 traceFrames;
};

static RevcPortalBridgeState gRevcPortalBridge;
static void RevcPortalUpdateReturnPortal(void);
static void RevcPortalRenderReturnPortal(void);
static float RevcPortalProjectionBaseFov(void);
static void RevcPortalUpdatePlayerProtection(void);

static bool
RevcPortalPlayerProtectionActive(void)
{
	const uint32 now = CTimer::GetTimeInMilliseconds();
	const bool graceActive = gRevcPortalBridge.playerProtectionUntil != 0 &&
		(int32)(gRevcPortalBridge.playerProtectionUntil - now) > 0;
	return (gRevcPortalBridge.enabled && !gRevcPortalBridge.entered) || graceActive;
}

// Cop AI must remain live during the preview so wanted levels, pursuits and
// gunfire stay native. Only the final arrest transition is suppressed while
// Tommy is the invisible hitscan owner, plus a short grace period after entry.
bool
RevcPortalBlocksPlayerArrest(void)
{
	return RevcPortalPlayerProtectionActive();
}

static void
RevcPortalUpdatePlayerProtection(void)
{
	CPlayerPed *player = FindPlayerPed();
	if(player == nil)
		return;

	if(RevcPortalPlayerProtectionActive()){
		if(!gRevcPortalBridge.playerProtectionSaved){
			gRevcPortalBridge.playerProtectionSaved = true;
			gRevcPortalBridge.savedBulletProof = player->bBulletProof;
			gRevcPortalBridge.savedFireProof = player->bFireProof;
			gRevcPortalBridge.savedCollisionProof = player->bCollisionProof;
			gRevcPortalBridge.savedMeleeProof = player->bMeleeProof;
			gRevcPortalBridge.savedExplosionProof = player->bExplosionProof;
			gRevcPortalBridge.savedCanBeDamaged = player->m_bCanBeDamaged;
			char buf[160];
			snprintf(buf, sizeof(buf),
				"preview player protection armed health=%.1f armour=%.1f wanted=%d",
				player->m_fHealth, player->m_fArmour,
				player->m_pWanted ? player->m_pWanted->GetWantedLevel() : -1);
			RevcLogPortal(buf);
		}
		player->bBulletProof = true;
		player->bFireProof = true;
		player->bCollisionProof = true;
		player->bMeleeProof = true;
		player->bExplosionProof = true;
		player->m_bCanBeDamaged = false;
		return;
	}

	if(gRevcPortalBridge.playerProtectionSaved){
		player->bBulletProof = gRevcPortalBridge.savedBulletProof;
		player->bFireProof = gRevcPortalBridge.savedFireProof;
		player->bCollisionProof = gRevcPortalBridge.savedCollisionProof;
		player->bMeleeProof = gRevcPortalBridge.savedMeleeProof;
		player->bExplosionProof = gRevcPortalBridge.savedExplosionProof;
		player->m_bCanBeDamaged = gRevcPortalBridge.savedCanBeDamaged;
		gRevcPortalBridge.playerProtectionSaved = false;
		gRevcPortalBridge.playerProtectionUntil = 0;
		RevcLogPortal("post-entry player protection released after 2000 ms");
	}
}

extern "C" __declspec(dllexport) void
ReVC_PortalSetView(float px, float py, float pz,
	float rx, float ry, float rz,
	float ux, float uy, float uz,
	float fx, float fy, float fz,
	float fov, float viewWindowX, float viewWindowY)
{
	gRevcPortalBridge.position = CVector(px, py, pz);
	gRevcPortalBridge.right = CVector(rx, ry, rz);
	gRevcPortalBridge.up = CVector(ux, uy, uz);
	gRevcPortalBridge.forward = CVector(fx, fy, fz);
	gRevcPortalBridge.fov = Clamp(fov, 10.0f, 150.0f);
	gRevcPortalBridge.viewWindowX = Max(viewWindowX, 0.01f);
	gRevcPortalBridge.viewWindowY = Max(viewWindowY, 0.01f);
	gRevcPortalBridge.viewValid = true;
}

extern "C" __declspec(dllexport) void
ReVC_PortalPrepare(float x, float y, float z, float heading)
{
	CVector position(x, y, z);
	if(!gRevcPortalBridge.prepared ||
	   (position - gRevcPortalBridge.preparePosition).MagnitudeSqr() > 0.01f ||
	   Abs(heading - gRevcPortalBridge.prepareHeading) > 0.001f){
		gRevcPortalBridge.preparePosition = position;
		gRevcPortalBridge.prepareHeading = heading;
		gRevcPortalBridge.preparePending = true;
		gRevcPortalBridge.prepared = false;
		gRevcPortalBridge.returnPosition = position;
		gRevcPortalBridge.returnYaw = heading;
		gRevcPortalBridge.havePreviousReturnDistance = false;
	}
	ReVC_SetPortalInputEnabled(false);
}

extern "C" __declspec(dllexport) void
ReVC_PortalSetEnabled(int enabled)
{
	gRevcPortalBridge.enabled = enabled != 0;
	if(gRevcPortalBridge.enabled){
		gRevcPortalBridge.entered = false;
		gRevcPortalBridge.havePreviousReturnDistance = false;
		ReVC_SetPortalInputEnabled(false);
	}else
		gRevcPortalBridge.viewValid = false;
}

extern "C" __declspec(dllexport) void
ReVC_PortalEnter(float x, float y, float z, float heading)
{
	gRevcPortalBridge.enterPosition = CVector(x, y, z);
	gRevcPortalBridge.enterHeading = heading;
	gRevcPortalBridge.enterPending = true;
	gRevcPortalBridge.preparePending = false;
	gRevcPortalBridge.enabled = false;
	gRevcPortalBridge.viewValid = false;
	gRevcPortalBridge.traceFrames = 0;
	// Cover the host/guest handoff frame as well; the deadline is restarted
	// when the enter command is actually applied below.
	gRevcPortalBridge.playerProtectionUntil = CTimer::GetTimeInMilliseconds() + 2000;
}

static void
RevcPortalPlacePlayer(CPlayerPed *player, const CVector &position, float heading)
{
	player->Teleport(position);
	player->SetHeading(heading);
	player->m_fRotationCur = heading;
	player->m_fRotationDest = heading;
	player->SetMoveSpeed(0.0f, 0.0f, 0.0f);
}

static void
RevcPortalGrantPlayerLoadout(CPlayerPed *player)
{
	// Load only the three useful portal-test weapons. This mirrors the native
	// weapon cheats' streaming discipline and avoids a missing weapon clump on
	// the first frame after entering Vice City.
	CStreaming::RequestModel(MI_COLT45, STREAMFLAGS_DONT_REMOVE);
	CStreaming::RequestModel(MI_UZI, STREAMFLAGS_DONT_REMOVE);
	CStreaming::RequestModel(MI_M4, STREAMFLAGS_DONT_REMOVE);
	CStreaming::LoadAllRequestedModels(false);
	player->GiveWeapon(WEAPONTYPE_COLT45, 500);
	player->GiveWeapon(WEAPONTYPE_UZI, 750);
	player->GiveWeapon(WEAPONTYPE_M4, 750);
	player->SetCurrentWeapon(WEAPONTYPE_COLT45);
	CStreaming::SetModelIsDeletable(MI_COLT45);
	CStreaming::SetModelIsDeletable(MI_UZI);
	CStreaming::SetModelIsDeletable(MI_M4);
}

static void
RevcPortalProcessCommands(void)
{
	CPlayerPed *player = FindPlayerPed();
	if(player == nil)
		return;

	if(gRevcPortalBridge.enterPending){
		gRevcPortalBridge.enterPending = false;
		RevcPortalPlacePlayer(player, gRevcPortalBridge.enterPosition, gRevcPortalBridge.enterHeading);
		RevcPortalGrantPlayerLoadout(player);
		if(gRevcPortalBridge.playerVisibilitySaved){
			player->bIsVisible = gRevcPortalBridge.savedPlayerVisibility;
			gRevcPortalBridge.playerVisibilitySaved = false;
		}else
			player->bIsVisible = true;
		TheCamera.RestoreWithJumpCut();
		// Keep the azimuth seen through the portal. Forcing the camera directly
		// behind Tommy made the destination appear unrelated to the preview even
		// though it was the same persistent world.
		CCam &cam = TheCamera.Cams[TheCamera.ActiveCam];
		CVector portalForward = gRevcPortalBridge.forward;
		portalForward.Normalise();
		TheCamera.m_bCamDirectlyBehind = false;
		TheCamera.m_bCamDirectlyInFront = false;
		TheCamera.m_bUseTransitionBeta = true;
		cam.m_fTransitionBeta = CGeneral::GetATanOfXY(portalForward.x, portalForward.y) + PI;
		while(cam.m_fTransitionBeta >= PI) cam.m_fTransitionBeta -= 2.0f * PI;
		while(cam.m_fTransitionBeta < -PI) cam.m_fTransitionBeta += 2.0f * PI;
		cam.ResetStatics = true;
		cam.FOV = RevcPortalProjectionBaseFov();
		TheCamera.Process();
		// The hosted game starts through the frontend state machine. Its world can
		// be fully initialised and rendering while CTimer still carries the
		// frontend user/code pause, which produces a perfectly rendered but static
		// Vice City after traversal. Entering the portal is the explicit handoff to
		// gameplay, so release both pause sources here.
		CTimer::EndUserPause();
		CTimer::SetCodePause(false);
		ReVC_SetPortalInputEnabled(true);
		gRevcPortalBridge.entered = true;
		gRevcPortalBridge.playerProtectionUntil = CTimer::GetTimeInMilliseconds() + 2000;
		gRevcPortalBridge.returnRequested = false;
		gRevcPortalBridge.havePreviousReturnDistance = false;
		gRevcPortalBridge.returnCooldownUntil = CTimer::GetTimeInMilliseconds() + 1000;
		RevcLogPortal("enter command applied; gameplay restored with 2000 ms player protection");
		return;
	}

	if(gRevcPortalBridge.preparePending){
		gRevcPortalBridge.preparePending = false;
		CStreaming::LoadSceneCollision(gRevcPortalBridge.preparePosition);
		CStreaming::LoadScene(gRevcPortalBridge.preparePosition);
		RevcPortalPlacePlayer(player, gRevcPortalBridge.preparePosition, gRevcPortalBridge.prepareHeading);
		// Preview is a live persistent Vice City, not a frozen loading snapshot.
		// Keep input gated, but let timecycle, streaming, traffic and population
		// advance before the player crosses the portal.
		CTimer::EndUserPause();
		CTimer::SetCodePause(false);
		gRevcPortalBridge.prepared = true;
		RevcLogPortal("destination prepared; preview simulation timer released");
	}
}

extern "C" __declspec(dllexport) int
ReVC_PortalGetGameplayView(float *values)
{
	if(values == nil || !gRevcPortalBridge.entered || Scene.camera == nil)
		return 0;
	RwMatrix *matrix = Scene.camera->getFrame()->getLTM();
	if(matrix == nil)
		return 0;
	values[0] = matrix->pos.x; values[1] = matrix->pos.y; values[2] = matrix->pos.z;
	values[3] = matrix->right.x; values[4] = matrix->right.y; values[5] = matrix->right.z;
	values[6] = matrix->up.x; values[7] = matrix->up.y; values[8] = matrix->up.z;
	values[9] = matrix->at.x; values[10] = matrix->at.y; values[11] = matrix->at.z;
	values[12] = TheCamera.Cams[TheCamera.ActiveCam].FOV;
	const RwV2d *viewWindow = RwCameraGetViewWindow(Scene.camera);
	values[13] = viewWindow ? viewWindow->x : SCREEN_VIEWWINDOW;
	values[14] = viewWindow ? viewWindow->y : SCREEN_VIEWWINDOW / SCREEN_ASPECT_RATIO;
	return 1;
}

extern "C" __declspec(dllexport) int
ReVC_PortalGetDestination(float *x, float *y, float *z, float *yaw)
{
	if(x == nil || y == nil || z == nil || yaw == nil)
		return 0;
	*x = gRevcPortalBridge.returnPosition.x;
	*y = gRevcPortalBridge.returnPosition.y;
	*z = gRevcPortalBridge.returnPosition.z;
	*yaw = gRevcPortalBridge.returnYaw;
	return gRevcPortalBridge.prepared || gRevcPortalBridge.entered ? 1 : 0;
}

extern "C" __declspec(dllexport) int
ReVC_PortalConsumeReturnRequest(void)
{
	if(!gRevcPortalBridge.returnRequested)
		return 0;
	gRevcPortalBridge.returnRequested = false;
	gRevcPortalBridge.entered = false;
	gRevcPortalBridge.havePreviousReturnDistance = false;
	return 1;
}

extern "C" __declspec(dllexport) void
ReVC_PortalSetReturnTexture(IDirect3DTexture9 *texture, int32 width, int32 height)
{
#if defined(RW_D3D9)
	if(texture == nil || width <= 0 || height <= 0){
		if(gRevcPortalBridge.returnRaster)
			RwRasterDestroy(gRevcPortalBridge.returnRaster);
		gRevcPortalBridge.returnRaster = nil;
		gRevcPortalBridge.returnTexture = nil;
		gRevcPortalBridge.returnTextureWidth = 0;
		gRevcPortalBridge.returnTextureHeight = 0;
		gRevcPortalBridge.returnTextureCopyLogged = false;
		return;
	}

	const bool recreate = gRevcPortalBridge.returnRaster == nil ||
		gRevcPortalBridge.returnTextureWidth != width ||
		gRevcPortalBridge.returnTextureHeight != height;
	if(recreate && gRevcPortalBridge.returnRaster){
		RwRasterDestroy(gRevcPortalBridge.returnRaster);
		gRevcPortalBridge.returnRaster = nil;
		gRevcPortalBridge.returnTexture = nil;
	}
	if(gRevcPortalBridge.returnRaster == nil){
		// Own the sampled raster in reVC/librw. A foreign SA RenderWare raster
		// cannot safely be wrapped because both engines maintain independent
		// native-raster and D3D state caches on the shared device.
		RwRaster *raster = RwRasterCreate(width, height, 32,
			rwRASTERTYPECAMERATEXTURE | rwRASTERFORMAT888);
		if(raster == nil){
			RevcLogPortal("San Andreas return raster creation failed");
			return;
		}
		RevcD3dRasterExt *ext = reinterpret_cast<RevcD3dRasterExt*>(
			reinterpret_cast<uint8*>(raster) + rw::d3d::nativeRasterOffset);
		if(ext == nil || ext->texture == nil){
			RwRasterDestroy(raster);
			RevcLogPortal("San Andreas return raster has no native D3D texture");
			return;
		}
		gRevcPortalBridge.returnRaster = raster;
		gRevcPortalBridge.returnTexture = reinterpret_cast<IDirect3DTexture9*>(ext->texture);
		gRevcPortalBridge.returnTextureWidth = width;
		gRevcPortalBridge.returnTextureHeight = height;
		gRevcPortalBridge.returnTextureCopyLogged = false;
		gRevcPortalBridge.returnTextureCopyFailures = 0;
	}

	IDirect3DSurface9 *source = nil;
	IDirect3DSurface9 *destination = nil;
	HRESULT hr = texture->GetSurfaceLevel(0, &source);
	if(SUCCEEDED(hr))
		hr = gRevcPortalBridge.returnTexture->GetSurfaceLevel(0, &destination);
	if(SUCCEEDED(hr))
		hr = rw::d3d::d3ddevice->StretchRect(source, nil, destination, nil, D3DTEXF_NONE);
	if(source) source->Release();
	if(destination) destination->Release();
	if(SUCCEEDED(hr)){
		if(!gRevcPortalBridge.returnTextureCopyLogged){
			D3DSURFACE_DESC sourceDesc, destinationDesc;
			texture->GetLevelDesc(0, &sourceDesc);
			gRevcPortalBridge.returnTexture->GetLevelDesc(0, &destinationDesc);
			char buf[256];
			sprintf(buf, "San Andreas return texture copied source=%p %ux%u fmt=%u destination=%p %ux%u fmt=%u",
				texture, sourceDesc.Width, sourceDesc.Height, (uint32)sourceDesc.Format,
				gRevcPortalBridge.returnTexture, destinationDesc.Width, destinationDesc.Height,
				(uint32)destinationDesc.Format);
			RevcLogPortal(buf);
			gRevcPortalBridge.returnTextureCopyLogged = true;
		}
	}else if(gRevcPortalBridge.returnTextureCopyFailures++ < 5){
		char buf[128];
		sprintf(buf, "San Andreas return texture copy failed hr=0x%08X", (uint32)hr);
		RevcLogPortal(buf);
	}
#else
	(void)texture; (void)width; (void)height;
#endif
}

static eWeaponType
RevcPortalWeaponFromBridgeCode(int32 code)
{
	switch(code){
	case 0: return WEAPONTYPE_COLT45;
	case 1: return WEAPONTYPE_PYTHON;
	case 2: return WEAPONTYPE_TEC9;
	case 3: return WEAPONTYPE_UZI;
	case 4: return WEAPONTYPE_MP5;
	case 5: return WEAPONTYPE_M4;
	case 6: return WEAPONTYPE_RUGER;
	default: return WEAPONTYPE_UNARMED;
	}
}

extern "C" __declspec(dllexport) int
ReVC_PortalFireHitscan(float sx, float sy, float sz,
	float ex, float ey, float ez, int32 weaponCode)
{
	if(!gRevcPortalBridge.enabled || !gRevcPortalBridge.prepared ||
	   gRevcPortalBridge.entered)
		return -1;

	CPlayerPed *shooter = FindPlayerPed();
	const eWeaponType weaponType = RevcPortalWeaponFromBridgeCode(weaponCode);
	if(shooter == nil || weaponType == WEAPONTYPE_UNARMED)
		return -1;

	CVector source(sx, sy, sz);
	CVector target(ex, ey, ez);
	const CVector shot = target - source;
	if(shot.MagnitudeSqr() < 0.0001f)
		return -1;

	CColPoint point{};
	CEntity *victim = nil;
	CEntity *oldIgnoreEntity = CWorld::pIgnoreEntity;
	const bool oldIncludeDeadPeds = CWorld::bIncludeDeadPeds;
	const bool oldIncludeCarTyres = CWorld::bIncludeCarTyres;
	const bool oldIncludeBikers = CWorld::bIncludeBikers;
	CWorld::pIgnoreEntity = shooter;
	CWorld::bIncludeDeadPeds = true;
	CWorld::bIncludeCarTyres = true;
	CWorld::bIncludeBikers = true;
	const bool hit = CWeapon::ProcessLineOfSight(source, target, point, victim,
		weaponType, shooter, true, true, true, true, true, false, false);
	CWorld::pIgnoreEntity = oldIgnoreEntity;
	CWorld::bIncludeDeadPeds = oldIncludeDeadPeds;
	CWorld::bIncludeCarTyres = oldIncludeCarTyres;
	CWorld::bIncludeBikers = oldIncludeBikers;

	if(victim)
		CWeapon::CheckForShootingVehicleOccupant(&victim, &point, weaponType, source, target);

	CVector2D ahead(shot.x, shot.y);
	const float aheadLength = Sqrt(ahead.x * ahead.x + ahead.y * ahead.y);
	if(aheadLength > 0.0001f){
		ahead.x /= aheadLength;
		ahead.y /= aheadLength;
	}else{
		ahead.x = 0.0f;
		ahead.y = 1.0f;
	}

	CEventList::RegisterEvent(EVENT_GUNSHOT, EVENT_ENTITY_PED, shooter, shooter, 1000);
	CWeapon::MakePedsJumpAtShot(shooter, &source, &target);
	CWeapon weapon(weaponType, 1);
	weapon.DoBulletImpact(shooter, victim, &source, &target, &point, ahead);

	char buf[256];
	snprintf(buf, sizeof(buf),
		"SA hitscan code=%d weapon=%d hit=%d entityType=%d model=%d impact=(%.2f %.2f %.2f)",
		weaponCode, (int)weaponType, hit ? 1 : 0,
		victim ? (int)victim->GetType() : -1,
		victim ? (int)victim->GetModelIndex() : -1,
		hit ? point.point.x : target.x,
		hit ? point.point.y : target.y,
		hit ? point.point.z : target.z);
	RevcLogPortal(buf);
	return hit ? 1 : 0;
}

static void
RevcPortalApplyViewWindow(void)
{
	if(!gRevcPortalBridge.enabled || !gRevcPortalBridge.viewValid || Scene.camera == nil)
		return;
	RwV2d viewWindow;
	viewWindow.x = gRevcPortalBridge.viewWindowX;
	viewWindow.y = gRevcPortalBridge.viewWindowY;
	RwCameraSetViewWindow(Scene.camera, &viewWindow);
}

static float
RevcPortalProjectionBaseFov(void)
{
	float halfTan = Max(gRevcPortalBridge.viewWindowX, 0.01f);
#ifdef ASPECT_RATIO_SCALE
	float aspect = CDraw::CalculateAspectRatio();
	if(aspect > 0.01f)
		halfTan *= DEFAULT_ASPECT_RATIO / aspect;
#endif
	return Clamp(RADTODEG(2.0f * Atan(halfTan)), 10.0f, 150.0f);
}

static void
RevcPortalApplyCamera(void)
{
	CPlayerPed *player = FindPlayerPed();
	if(!gRevcPortalBridge.enabled || !gRevcPortalBridge.viewValid || Scene.camera == nil){
		if(player && gRevcPortalBridge.playerVisibilitySaved){
			player->bIsVisible = gRevcPortalBridge.savedPlayerVisibility;
			gRevcPortalBridge.playerVisibilitySaved = false;
		}
		return;
	}

	if(player && !gRevcPortalBridge.playerVisibilitySaved){
		gRevcPortalBridge.savedPlayerVisibility = player->bIsVisible;
		gRevcPortalBridge.playerVisibilitySaved = true;
	}
	if(player)
		player->bIsVisible = false;

	// The lightweight freeroam SCM starts with the loading splash fully faded
	// out but, unlike the stock story script, never schedules a fade-in. Force
	// preview rendering visible; once PortalEnter disables the override, normal
	// VC scripts own the fade system again.
	if(TheCamera.GetScreenFadeStatus() != FADE_0){
		StillToFadeOut = false;
		JustLoadedDontFadeInYet = false;
		TheCamera.Fade(0.0f, FADE_IN);
		TheCamera.ProcessFade();
		TheCamera.ProcessMusicFade();
	}

	CVector up = gRevcPortalBridge.up;
	CVector forward = gRevcPortalBridge.forward;
	up.Normalise();
	forward.Normalise();
	// GTA's camera matrix stores the camera-left vector in GetRight().
	// Rebuild that handed basis instead of copying the host's world-right vector.
	CVector right = CrossProduct(up, forward);
	right.Normalise();
	up = CrossProduct(forward, right);
	up.Normalise();

	TheCamera.GetMatrix().GetRight() = right;
	TheCamera.GetMatrix().GetUp() = up;
	TheCamera.GetMatrix().GetForward() = forward;
	TheCamera.GetMatrix().GetPosition() = gRevcPortalBridge.position;
	TheCamera.GetGameCamPosition() = gRevcPortalBridge.position;
	CDraw::SetFOV(RevcPortalProjectionBaseFov());
	TheCamera.CalculateDerivedValues();
	RevcPortalApplyViewWindow();

	RwFrame *frame = RwCameraGetFrame(Scene.camera);
	if(frame){
		RwMatrix *matrix = RwFrameGetMatrix(frame);
		*RwMatrixGetPos(matrix) = gRevcPortalBridge.position;
		*RwMatrixGetRight(matrix) = right;
		*RwMatrixGetUp(matrix) = up;
		*RwMatrixGetAt(matrix) = forward;
		RwMatrixUpdate(matrix);
		RwFrameUpdateObjects(frame);
		RwFrameOrthoNormalize(frame);
	}
	RwCameraSetNearClipPlane(Scene.camera, 0.05f);
}
#endif
// SA overlay (tvcorn) disabled for now
#if 0
static RwTexDictionary *gSaOverlayTxd = nil;
static RwTexture *gSaTvCornTex = nil;
static bool gSaOverlayLoaded = false;
static int gSaOverlayTexDumped = 0;
#endif
static void RevcLogCore(const char *msg)
{
	if(!gRevcLogEnabled || gRevcFrameLogCount > 8)
		return;
	if(gRevcCoreLog == nil){
		char exePath[MAX_PATH];
		GetModuleFileNameA(nil, exePath, MAX_PATH);
		char *slash = strrchr(exePath, '\\');
		if(slash) *(slash + 1) = '\0';
		char logPath[MAX_PATH];
		strcpy(logPath, exePath);
		strcat(logPath, "revc_in_sa.log");
		gRevcCoreLog = fopen(logPath, "a");
	}
	if(gRevcCoreLog == nil)
		return;
	fprintf(gRevcCoreLog, "Core: %s\n", msg);
	fflush(gRevcCoreLog);
}

#ifdef REVC_DLL
static void
RevcLogPortal(const char *msg)
{
	if(gRevcCoreLog == nil){
		char exePath[MAX_PATH];
		GetModuleFileNameA(nil, exePath, MAX_PATH);
		char *slash = strrchr(exePath, '\\');
		if(slash) *(slash + 1) = '\0';
		char logPath[MAX_PATH];
		strcpy(logPath, exePath);
		strcat(logPath, "revc_in_sa.log");
		gRevcCoreLog = fopen(logPath, "a");
	}
	if(gRevcCoreLog == nil)
		return;
	fprintf(gRevcCoreLog, "Portal: %s\n", msg);
	fflush(gRevcCoreLog);
}

static void
RevcPortalTraceState(void)
{
	if(gRevcPortalBridge.traceFrames == 0)
		return;

	const uint32 frame = gRevcPortalBridge.traceFrames--;
	if((frame % 15) != 0 && frame != 149)
		return;

	char buf[512];
	CPlayerPed *player = FindPlayerPed();
	CVector pos = player ? player->GetPosition() : CVector(0.0f, 0.0f, 0.0f);
	CVector cam = TheCamera.GetPosition();
	const RwV2d *viewWindow = Scene.camera ? RwCameraGetViewWindow(Scene.camera) : nil;
	sprintf(buf,
		"trace remaining=%u time=%u stepMs=%u timerPaused=%d input=%d controlsMask=0x%X "
		"pending=%d player=%.2f %.2f %.2f camera=%.2f %.2f %.2f "
		"fovRaw=%.3f fovScaled=%.3f viewWindow=(%.5f %.5f) screen=%dx%d keyW(temp/new)=%d/%d",
		frame, CTimer::GetTimeInMilliseconds(), CTimer::GetTimeStepInMilliseconds(),
		CTimer::GetIsPaused() ? 1 : 0, ReVC_IsPortalInputEnabled() ? 1 : 0,
		(unsigned)CPad::GetPad(0)->DisablePlayerControls,
		gRevcPortalBridge.enterPending ? 1 : 0,
		pos.x, pos.y, pos.z, cam.x, cam.y, cam.z,
		CDraw::GetFOV(), CDraw::GetScaledFOV(),
		viewWindow ? viewWindow->x : 0.0f, viewWindow ? viewWindow->y : 0.0f,
		(int)SCREEN_WIDTH, (int)SCREEN_HEIGHT,
		(int)CPad::TempKeyState.VK_KEYS['W'], (int)CPad::NewKeyState.VK_KEYS['W']);
	RevcLogPortal(buf);
}

static CVector
RevcPortalNormal(void)
{
	return CVector(Cos(gRevcPortalBridge.returnYaw), Sin(gRevcPortalBridge.returnYaw), 0.0f);
}

static CVector
RevcPortalRight(void)
{
	return CVector(-Sin(gRevcPortalBridge.returnYaw), Cos(gRevcPortalBridge.returnYaw), 0.0f);
}

static void
RevcPortalUpdateReturnPortal(void)
{
	if(!gRevcPortalBridge.entered)
		return;
	CPlayerPed *player = FindPlayerPed();
	if(player == nil)
		return;

	// The host owns the real Win32 window and forwards normal gameplay input to
	// reVC. Read F4 directly as well: this avoids losing a short key transition
	// between the host's BeginScene and CPad::UpdatePads.
	const bool placeKeyDown = (GetAsyncKeyState(VK_F4) & 0x8000) != 0;
	const bool placeRequested = placeKeyDown && !gRevcPortalBridge.returnPlaceKeyDown;
	gRevcPortalBridge.returnPlaceKeyDown = placeKeyDown;
	if(placeRequested){
		CCam &cam = TheCamera.Cams[TheCamera.ActiveCam];
		CVector viewDirection = cam.Front;
		viewDirection.Normalise();
		CVector horizontalView(viewDirection.x, viewDirection.y, 0.0f);
		if(horizontalView.MagnitudeSqr() < 0.0001f)
			horizontalView = player->GetForward();
		horizontalView.z = 0.0f;
		horizontalView.Normalise();

		CVector position;
		CVector portalNormal = horizontalView * -1.0f;
		CColPoint hitPoint;
		CEntity *hitEntity = nil;
		CEntity *oldIgnoreEntity = CWorld::pIgnoreEntity;
		CWorld::pIgnoreEntity = player;
		const bool aimedAtSurface = CWorld::ProcessLineOfSight(
			cam.Source, cam.Source + viewDirection * 40.0f,
			hitPoint, hitEntity, true, false, false, true, true, true, false);
		CWorld::pIgnoreEntity = oldIgnoreEntity;
		if(aimedAtSurface){
			position = hitPoint.point;
			CVector surfaceNormal(hitPoint.normal.x, hitPoint.normal.y, 0.0f);
			if(surfaceNormal.MagnitudeSqr() > 0.16f){
				surfaceNormal.Normalise();
				portalNormal = surfaceNormal;
			}
			// Keep the vertical portal just outside the aimed geometry.
			position += portalNormal * 0.10f;
		}else{
			position = player->GetPosition() + horizontalView * 4.0f;
		}
		bool groundFound = false;
		float ground = CWorld::FindGroundZFor3DCoord(position.x, position.y, position.z + 10.0f, &groundFound);
		if(groundFound)
			position.z = ground;
		gRevcPortalBridge.returnPosition = position;
		gRevcPortalBridge.returnYaw = CGeneral::GetATanOfXY(portalNormal.x, portalNormal.y);
		gRevcPortalBridge.preparePosition = position;
		gRevcPortalBridge.prepareHeading = gRevcPortalBridge.returnYaw;
		gRevcPortalBridge.prepared = true;
		gRevcPortalBridge.havePreviousReturnDistance = false;
		gRevcPortalBridge.returnCooldownUntil = CTimer::GetTimeInMilliseconds() + 750;
		char buf[192];
		sprintf(buf, "return portal placed at %.2f %.2f %.2f yaw=%.3f",
			position.x, position.y, position.z, gRevcPortalBridge.returnYaw);
		RevcLogPortal(buf);
		static wchar placedMessage[64];
		AsciiToUnicode("Portal to San Andreas placed", placedMessage);
		CHud::SetHelpMessage(placedMessage, true);
	}

	CVector sample = player->GetPosition();
	sample.z += 1.0f;
	CVector center = gRevcPortalBridge.returnPosition + CVector(0.0f, 0.0f, 2.56f);
	CVector relative = sample - center;
	const float signedDistance = DotProduct(relative, RevcPortalNormal());
	const float horizontal = DotProduct(relative, RevcPortalRight());
	if(gRevcPortalBridge.havePreviousReturnDistance &&
	   CTimer::GetTimeInMilliseconds() >= gRevcPortalBridge.returnCooldownUntil){
		const float previousDistance = gRevcPortalBridge.previousReturnDistance;
		const bool crossed = (previousDistance > 0.01f && signedDistance <= 0.0f) ||
			(previousDistance < -0.01f && signedDistance >= 0.0f);
		const float denominator = previousDistance - signedDistance;
		if(crossed && Abs(denominator) > 0.0001f){
			const float t = Clamp(previousDistance / denominator, 0.0f, 1.0f);
			const CVector hit = gRevcPortalBridge.previousReturnSample +
				(sample - gRevcPortalBridge.previousReturnSample) * t;
			const CVector hitRelative = hit - center;
			const float hitHorizontal = DotProduct(hitRelative, RevcPortalRight());
			if(Abs(hitHorizontal) <= 2.15f && Abs(hitRelative.z) <= 2.60f){
				gRevcPortalBridge.returnRequested = true;
				gRevcPortalBridge.returnCooldownUntil = CTimer::GetTimeInMilliseconds() + 1500;
				char buf[224];
				sprintf(buf, "return portal crossed; requesting San Andreas handoff d=%.3f->%.3f hit=(%.2f %.2f %.2f) local=(%.2f %.2f)",
					previousDistance, signedDistance, hit.x, hit.y, hit.z, hitHorizontal, hitRelative.z);
				RevcLogPortal(buf);
			}
		}
	}
	if((++gRevcPortalBridge.returnDebugCounter % 180) == 0 &&
	   (sample - center).MagnitudeSqr() < 100.0f){
		char buf[224];
		sprintf(buf, "return probe d=%.3f horizontal=%.3f vertical=%.3f portal=(%.2f %.2f %.2f yaw=%.3f) f4=%d",
			signedDistance, horizontal, relative.z,
			gRevcPortalBridge.returnPosition.x, gRevcPortalBridge.returnPosition.y,
			gRevcPortalBridge.returnPosition.z, gRevcPortalBridge.returnYaw,
			placeKeyDown ? 1 : 0);
		RevcLogPortal(buf);
	}
	gRevcPortalBridge.previousReturnDistance = signedDistance;
	gRevcPortalBridge.previousReturnSample = sample;
	gRevcPortalBridge.havePreviousReturnDistance = true;
}

static void
RevcPortalDrawQuad(const CVector *positions, RwRaster *raster,
	uint8 red, uint8 green, uint8 blue, const float *projectedU = nil,
	const float *projectedV = nil)
{
	RwIm3DVertex vertices[4];
	for(int i = 0; i < 4; i++){
		RwIm3DVertexSetPos(&vertices[i], positions[i].x, positions[i].y, positions[i].z);
		RwIm3DVertexSetRGBA(&vertices[i], red, green, blue, 255);
	}
	static const float defaultU[4] = {0.0f, 0.0f, 1.0f, 1.0f};
	static const float defaultV[4] = {1.0f, 0.0f, 0.0f, 1.0f};
	const float *u = projectedU ? projectedU : defaultU;
	const float *v = projectedV ? projectedV : defaultV;
	for(int i = 0; i < 4; i++){
		RwIm3DVertexSetU(&vertices[i], u[i]);
		RwIm3DVertexSetV(&vertices[i], v[i]);
	}
	RwRenderStateSet(rwRENDERSTATETEXTURERASTER, raster);
	RwImVertexIndex indices[6] = {0, 1, 2, 0, 2, 3};
	if(RwIm3DTransform(vertices, 4, nil, rwIM3D_VERTEXXYZ | rwIM3D_VERTEXRGBA | rwIM3D_VERTEXUV)){
		// VC is hosted inside SA and the host restores raw D3D state between
		// engines. librw's cache cannot observe that restore, so force the real
		// native texture immediately before the draw.
#if defined(RW_D3D9)
		if(raster == gRevcPortalBridge.returnRaster &&
		   gRevcPortalBridge.returnTexture && rw::d3d::d3ddevice)
			rw::d3d::d3ddevice->SetTexture(0, gRevcPortalBridge.returnTexture);
#endif
		RwIm3DRenderIndexedPrimitive(rwPRIMTYPETRILIST, indices, 6);
		RwIm3DEnd();
	}
}

static bool
RevcPortalDrawScreenSpaceQuad(const CVector *positions, RwRaster *raster)
{
	if(raster == nil || Scene.camera == nil || SCREEN_WIDTH <= 0.0f || SCREEN_HEIGHT <= 0.0f)
		return false;

	RwIm2DVertex vertices[4];
	const float nearClip = CDraw::GetNearClipZ();
	const float farClip = CDraw::GetFarClipZ();
	const float nearScreenZ = RwIm2DGetNearScreenZ();
	const float farScreenZ = RwIm2DGetFarScreenZ();
	// The SA texture is a completed camera projection. It must therefore be
	// sampled in screen space. A normal Im3D portal quad applies perspective
	// correction once more and visibly bends/slides straight world geometry
	// when the VC viewer looks at the portal obliquely.
	const float screenSpaceRecipZ = 1.0f;
	for(int i = 0; i < 4; i++){
		CVector screen;
		float spriteWidth, spriteHeight;
		if(!CSprite::CalcScreenCoors(positions[i], &screen, &spriteWidth, &spriteHeight, false) ||
		   screen.z <= nearClip || farClip <= nearClip)
			return false;

		const float depth = nearScreenZ +
			(screen.z - nearClip) * (farScreenZ - nearScreenZ) * farClip /
			((farClip - nearClip) * screen.z);
		RwIm2DVertexSetScreenX(&vertices[i], screen.x);
		RwIm2DVertexSetScreenY(&vertices[i], screen.y);
		RwIm2DVertexSetScreenZ(&vertices[i], depth);
		RwIm2DVertexSetRecipCameraZ(&vertices[i], screenSpaceRecipZ);
		RwIm2DVertexSetIntRGBA(&vertices[i], 255, 255, 255, 255);
		// Do not clamp per-vertex UVs. When a portal corner is outside the
		// viewport, clipping happens after interpolation. Clamping only the UV
		// while leaving the vertex off-screen destroys the screen-space identity
		// mapping and makes the visible image look like a second shifted camera.
		// The sampler itself remains CLAMP, so pixels outside the source raster are
		// still handled safely.
		RwIm2DVertexSetU(&vertices[i], screen.x / SCREEN_WIDTH, screenSpaceRecipZ);
		RwIm2DVertexSetV(&vertices[i], screen.y / SCREEN_HEIGHT, screenSpaceRecipZ);
	}

	RwRenderStateSet(rwRENDERSTATETEXTURERASTER, raster);
#if defined(RW_D3D9)
	// SA owns the source texture and updates it outside librw. Force the native
	// binding because librw's state cache cannot observe the host-side copy.
	if(raster == gRevcPortalBridge.returnRaster &&
	   gRevcPortalBridge.returnTexture && rw::d3d::d3ddevice)
		rw::d3d::d3ddevice->SetTexture(0, gRevcPortalBridge.returnTexture);
#endif
	RwImVertexIndex indices[6] = {0, 1, 2, 0, 2, 3};
	RwIm2DRenderIndexedPrimitive(rwPRIMTYPETRILIST, vertices, 4, indices, 6);
	return true;
}

static void
RevcPortalRenderReturnPortal(void)
{
	if(!gRevcPortalBridge.entered)
		return;
	const CVector normal = RevcPortalNormal();
	const CVector right = RevcPortalRight();
	const CVector up(0.0f, 0.0f, 1.0f);
	const CVector center = gRevcPortalBridge.returnPosition + up * 2.56f + normal * 0.035f;
	const float outerW = 2.18f, outerH = 2.68f;
	const float innerW = 2.0f, innerH = 2.5f;
	CVector outer[4] = {
		center - right*outerW - up*outerH, center - right*outerW + up*outerH,
		center + right*outerW + up*outerH, center + right*outerW - up*outerH
	};
	CVector inner[4] = {
		center - right*innerW - up*innerH + normal*0.006f,
		center - right*innerW + up*innerH + normal*0.006f,
		center + right*innerW + up*innerH + normal*0.006f,
		center + right*innerW - up*innerH + normal*0.006f
	};
	RwRenderStateSet(rwRENDERSTATEZTESTENABLE, (void*)TRUE);
	RwRenderStateSet(rwRENDERSTATEZWRITEENABLE, (void*)TRUE);
	RwRenderStateSet(rwRENDERSTATEVERTEXALPHAENABLE, (void*)FALSE);
	RwRenderStateSet(rwRENDERSTATEFOGENABLE, (void*)FALSE);
	RwRenderStateSet(rwRENDERSTATECULLMODE, (void*)rwCULLMODECULLNONE);
	RwRenderStateSet(rwRENDERSTATETEXTUREADDRESS, (void*)rwTEXTUREADDRESSCLAMP);
	RwRenderStateSet(rwRENDERSTATETEXTUREFILTER, (void*)rwFILTERLINEAR);
	// The orange quad is a backing frame. Do not let it write depth and mask
	// the textured aperture when the player views the portal from its rear.
	RwRenderStateSet(rwRENDERSTATEZWRITEENABLE, (void*)FALSE);
	RevcPortalDrawQuad(outer, nil, 255, 154, 24);
	RwRenderStateSet(rwRENDERSTATEZWRITEENABLE, (void*)TRUE);
	RevcPortalDrawScreenSpaceQuad(inner, gRevcPortalBridge.returnRaster);
	RwRenderStateSet(rwRENDERSTATETEXTURERASTER, nil);
}
#endif

static void
LoadSaOverlayTexture(void)
{
#if 0
	if(gSaOverlayLoaded)
		return;
	gSaOverlayLoaded = true;

	char exePath[MAX_PATH];
	GetModuleFileNameA(nil, exePath, MAX_PATH);
	char *slash = strrchr(exePath, '\\');
	if(slash) *(slash + 1) = '\0';
	char txdPath[MAX_PATH];
	strcpy(txdPath, exePath);
	strcat(txdPath, "models\\txd\\LD_SPAC_VC.txd");
	{
		char buf[256];
		WIN32_FILE_ATTRIBUTE_DATA fad;
		BOOL ok = GetFileAttributesExA(txdPath, GetFileExInfoStandard, &fad);
		unsigned long long sz = 0;
		if(ok)
			sz = ((unsigned long long)fad.nFileSizeHigh << 32) | fad.nFileSizeLow;
		sprintf(buf, "Overlay: loading txd path=%s", txdPath);
		RevcLogCore(buf);
		sprintf(buf, "Overlay: txd exists=%d size=%llu", ok != FALSE, sz);
		RevcLogCore(buf);
	}

	gSaOverlayTxd = CFileLoader::LoadTexDictionary(txdPath);
	if(gSaOverlayTxd){
		RevcLogCore("Overlay: txd loaded");
		RwTexDictionary *prevTxd = RwTexDictionaryGetCurrent();
		RwTexDictionarySetCurrent(gSaOverlayTxd);
		gSaTvCornTex = RwTexDictionaryFindNamedTexture(gSaOverlayTxd, "tvcorn");
		if(gSaTvCornTex == nil)
			gSaTvCornTex = RwTexDictionaryFindNamedTexture(gSaOverlayTxd, "TVCORN");
		RwTexDictionarySetCurrent(prevTxd);
		if(gSaTvCornTex){
			RwTextureSetAddressing(gSaTvCornTex, rwTEXTUREADDRESSCLAMP);
			RwTextureSetFilterMode(gSaTvCornTex, rwFILTERLINEAR);
			RevcLogCore("Overlay: tvcorn loaded");
		}else{
			RevcLogCore("Overlay: tvcorn not found in LD_SPAC.txd");
			if(!gSaOverlayTexDumped){
				gSaOverlayTexDumped = 1;
				struct DumpCtx { int count; };
				DumpCtx ctx = {0};
				auto cb = [](RwTexture *tex, void *data) -> RwTexture* {
					DumpCtx *c = (DumpCtx*)data;
					char b[128];
					sprintf(b, "Overlay: txd tex[%d]=%s", c->count, tex->name);
					RevcLogCore(b);
					c->count++;
					return tex;
				};
				RwTexDictionaryForAllTextures(gSaOverlayTxd, cb, &ctx);
				char b[128];
				sprintf(b, "Overlay: txd texture count=%d", ctx.count);
				RevcLogCore(b);
			}
		}
	}else{
		RevcLogCore("Overlay: failed to load LD_SPAC.txd");
	}

	if(!gSaTvCornTex)
		RevcLogCore("Overlay: tvcorn not available (TXD only)");
#endif
}

static void
DrawSaOverlayCorners(void)
{
#if 0
	char buf[128];
	sprintf(buf, "Overlay: draw begin tex=%p", gSaTvCornTex);
	RevcLogCore(buf);
	if(!gSaTvCornTex)
		return;
	RwRaster *ras = RwTextureGetRaster(gSaTvCornTex);
	sprintf(buf, "Overlay: raster=%p", ras);
	RevcLogCore(buf);
	if(!ras)
		return;

	float w = (float)RwRasterGetWidth(ras);
	float h = (float)RwRasterGetHeight(ras);
	sprintf(buf, "Overlay: size %.0f x %.0f", w, h);
	RevcLogCore(buf);
	if(w <= 0.0f || h <= 0.0f)
		return;

	float screenW = (float)RsGlobal.maximumWidth;
	float screenH = (float)RsGlobal.maximumHeight;

	CSprite2d spr;
	spr.m_pTexture = gSaTvCornTex;
	const CRGBA col(255, 255, 255, 255);

	// top-left
	spr.Draw(CRect(0.0f, 0.0f, w, h), col, 0.0f, 0.0f, 1.0f, 0.0f, 0.0f, 1.0f, 1.0f, 1.0f);
	// top-right (flip U)
	spr.Draw(CRect(screenW - w, 0.0f, screenW, h), col, 1.0f, 0.0f, 0.0f, 0.0f, 1.0f, 1.0f, 0.0f, 1.0f);
	// bottom-left (flip V)
	spr.Draw(CRect(0.0f, screenH - h, w, screenH), col, 0.0f, 1.0f, 1.0f, 1.0f, 0.0f, 0.0f, 1.0f, 0.0f);
	// bottom-right (flip U+V)
	spr.Draw(CRect(screenW - w, screenH - h, screenW, screenH), col, 1.0f, 1.0f, 0.0f, 1.0f, 1.0f, 0.0f, 0.0f, 0.0f);
#endif
}

GlobalScene Scene;

uint8 work_buff[55000];
char gString[256];
char gString2[512];
wchar gUString[256];
wchar gUString2[256];

float FramesPerSecond = 30.0f;

bool gbPrintShite = false;
bool gbModelViewer;
#ifdef TIMEBARS
bool gbShowTimebars;
#endif
#ifdef DRAW_GAME_VERSION_TEXT
bool gbDrawVersionText; // Our addition, we think it was always enabled on !MASTER builds
#endif
#ifdef NO_MOVIES
bool gbNoMovies;
#endif

volatile int32 frameCount;

RwRGBA gColourTop;

bool gameAlreadyInitialised;

float NumberOfChunksLoaded;
#define TOTALNUMCHUNKS 95.0f

bool g_SlowMode = false;
char version_name[64];


void GameInit(void);
void SystemInit(void);
void TheGame(void);

#ifdef DEBUGMENU
void DebugMenuPopulate(void);
#endif

#ifndef FINAL
bool gbPrintMemoryUsage;
#endif

#ifdef GTA_PS2
#define WANT_TO_LOAD TheMemoryCard.m_bWantToLoad
#define FOUND_GAME_TO_LOAD TheMemoryCard.b_FoundRecentSavedGameWantToLoad
#else
#define WANT_TO_LOAD FrontEndMenuManager.m_bWantToLoad
#define FOUND_GAME_TO_LOAD b_FoundRecentSavedGameWantToLoad
#endif

#ifdef NEW_RENDERER
bool gbNewRenderer;
#endif
#ifdef REVC_DLL
// SA's depth buffer may not have a stencil component; requesting
// D3DCLEAR_STENCIL causes the entire Clear to fail (including Z).
#define CLEARMODE (rwCAMERACLEARZ)
#elif defined(FIX_BUGS)
// need to clear stencil for mblur fx. no idea why it works in the original game
// also for clearing out water rects in new renderer
#define CLEARMODE (rwCAMERACLEARZ | rwCAMERACLEARSTENCIL)
#else
#define CLEARMODE (rwCAMERACLEARZ)
#endif

bool bDisplayNumOfAtomicsRendered = false;
bool bDisplayPosn = false;

#ifdef __MWERKS__
void
debug(char *fmt, ...)
{
#ifndef MASTER
	// TODO put something here
#endif
}

void
Error(char *fmt, ...)
{
#ifndef MASTER
	// TODO put something here
#endif
}
#endif

void
ValidateVersion()
{
	int32 file = CFileMgr::OpenFile("models\\coll\\peds.col", "rb");
	char buff[128];

	if ( file != -1 )
	{
		CFileMgr::Seek(file, 100, SEEK_SET);
		
		for ( int i = 0; i < 128; i++ )
		{
			CFileMgr::Read(file, &buff[i], sizeof(char));
			buff[i] -= 23;
			if ( buff[i] == '\0' )
				break;
			CFileMgr::Seek(file, 99, SEEK_CUR);
		}
		
		if ( !strncmp(buff, "grandtheftauto3", 15) )
		{
			strncpy(version_name, &buff[15], 64);
			CFileMgr::CloseFile(file);
			return;
		}
	}

	LoadingScreen("Invalid version", NULL, NULL);
	
	while(true)
	{
		;
	}
}

bool
DoRWStuffStartOfFrame(int16 TopRed, int16 TopGreen, int16 TopBlue, int16 BottomRed, int16 BottomGreen, int16 BottomBlue, int16 Alpha)
{
	CRGBA TopColor(TopRed, TopGreen, TopBlue, Alpha);
	CRGBA BottomColor(BottomRed, BottomGreen, BottomBlue, Alpha);

	CDraw::CalculateAspectRatio();
#ifdef REVC_DLL
	RwRect rect;
	RwRect *prect = nil;
	if(gRevcBackBufferWidth > 0 && gRevcBackBufferHeight > 0){
		rect.x = 0;
		rect.y = 0;
		rect.w = gRevcBackBufferWidth;
		rect.h = gRevcBackBufferHeight;
		prect = &rect;
	}
	CameraSize(Scene.camera, prect, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#else
	CameraSize(Scene.camera, nil, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#endif
#ifdef REVC_DLL
	RevcPortalApplyViewWindow();
#endif
	CVisibilityPlugins::SetRenderWareCamera(Scene.camera);
	RwCameraClear(Scene.camera, &TopColor.rwRGBA, CLEARMODE);

	if(!RsCameraBeginUpdate(Scene.camera))
		return false;

	CSprite2d::InitPerFrame();

	if(Alpha != 0)
		CSprite2d::DrawRect(CRect(0.0f, 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT), BottomColor, BottomColor, TopColor, TopColor);

	return true;
}

bool
DoRWStuffStartOfFrame_Horizon(int16 TopRed, int16 TopGreen, int16 TopBlue, int16 BottomRed, int16 BottomGreen, int16 BottomBlue, int16 Alpha)
{
	CDraw::CalculateAspectRatio();
#ifdef REVC_DLL
	RwRect rect;
	RwRect *prect = nil;
	if(gRevcBackBufferWidth > 0 && gRevcBackBufferHeight > 0){
		rect.x = 0;
		rect.y = 0;
		rect.w = gRevcBackBufferWidth;
		rect.h = gRevcBackBufferHeight;
		prect = &rect;
	}
	CameraSize(Scene.camera, prect, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#else
	CameraSize(Scene.camera, nil, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#endif
#ifdef REVC_DLL
	RevcPortalApplyViewWindow();
#endif
	CVisibilityPlugins::SetRenderWareCamera(Scene.camera);
	RwCameraClear(Scene.camera, &gColourTop, CLEARMODE);

	if(!RsCameraBeginUpdate(Scene.camera))
		return false;

	TheCamera.m_viewMatrix.Update();
	CClouds::RenderBackground(TopRed, TopGreen, TopBlue, BottomRed, BottomGreen, BottomBlue, Alpha);

	return true;
}

// This is certainly a very useful function
void
DoRWRenderHorizon(void)
{
	CClouds::RenderHorizon();
}

void
DoFade(void)
{
	if(CTimer::GetIsPaused())
		return;

#ifdef PS2_MENU
	if(TheMemoryCard.JustLoadedDontFadeInYet){
		TheMemoryCard.JustLoadedDontFadeInYet = false;
		TheMemoryCard.TimeStartedCountingForFade = CTimer::GetTimeInMilliseconds();
	}
#else
	if(JustLoadedDontFadeInYet){
		JustLoadedDontFadeInYet = false;
		TimeStartedCountingForFade = CTimer::GetTimeInMilliseconds();
	}
#endif

#ifdef PS2_MENU
	if(TheMemoryCard.StillToFadeOut){
		if(CTimer::GetTimeInMilliseconds() - TheMemoryCard.TimeStartedCountingForFade > TheMemoryCard.TimeToStayFadedBeforeFadeOut){
			TheMemoryCard.StillToFadeOut = false;
#else
	if(StillToFadeOut){
		if(CTimer::GetTimeInMilliseconds() - TimeStartedCountingForFade > TimeToStayFadedBeforeFadeOut){
			StillToFadeOut = false;
#endif
			TheCamera.Fade(3.0f, FADE_IN);
			TheCamera.ProcessFade();
			TheCamera.ProcessMusicFade();
		}else{
			TheCamera.SetFadeColour(0, 0, 0);
			TheCamera.Fade(0.0f, FADE_OUT);
			TheCamera.ProcessFade();
		}
	}

	if(CDraw::FadeValue != 0 || FrontEndMenuManager.m_PrefsBrightness < 256){
		CSprite2d *splash = LoadSplash(nil);

		CRGBA fadeColor;
		CRect rect;
		int fadeValue = CDraw::FadeValue;
		float brightness = Min(FrontEndMenuManager.m_PrefsBrightness, 256);
		if(brightness <= 50)
			brightness = 50;
		if(FrontEndMenuManager.m_bMenuActive)
			brightness = 256;

		if(TheCamera.m_FadeTargetIsSplashScreen)
			fadeValue = 0;

		float fade = fadeValue + 256 - brightness;
		if(fade == 0){
			fadeColor.r = 0;
			fadeColor.g = 0;
			fadeColor.b = 0;
			fadeColor.a = 0;
		}else{
			fadeColor.r = fadeValue * CDraw::FadeRed / fade;
			fadeColor.g = fadeValue * CDraw::FadeGreen / fade;
			fadeColor.b = fadeValue * CDraw::FadeBlue / fade;
			int alpha = 255 - brightness*(256 - fadeValue)/256;
			if(alpha < 0)
				alpha = 0;
			fadeColor.a = alpha;
		}

		TheCamera.GetScreenRect(rect);
		CSprite2d::DrawRect(rect, fadeColor);

		if(CDraw::FadeValue != 0 && TheCamera.m_FadeTargetIsSplashScreen){
			RwRenderStateSet(rwRENDERSTATETEXTUREFILTER, (void*)rwFILTERLINEAR);
			fadeColor.r = 255;
			fadeColor.g = 255;
			fadeColor.b = 255;
			fadeColor.a = CDraw::FadeValue;
			splash->Draw(CRect(0.0f, 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT), fadeColor, fadeColor, fadeColor, fadeColor);
		}
	}
}

bool
RwGrabScreen(RwCamera *camera, RwChar *filename)
{
	char temp[255];
	RwImage *pImage = RsGrabScreen(camera);
	bool result = true;

	if (pImage == nil)
		return false;

	strcpy(temp, CFileMgr::GetRootDirName());
	strcat(temp, filename);

#ifndef LIBRW
	if (RtBMPImageWrite(pImage, &temp[0]) == nil)
#else
	if (RtPNGImageWrite(pImage, &temp[0]) == nil)
#endif
		result = false;
	RwImageDestroy(pImage);
	return result;
}

#define TILE_WIDTH 576
#define TILE_HEIGHT 432

void
DoRWStuffEndOfFrame(void)
{
	CDebug::DisplayScreenStrings();	// custom
	CDebug::DebugDisplayTextBuffer();
	FlushObrsPrintfs();
	RevcLogCore("DoRWStuffEndOfFrame: begin");
	__try {
		RwCameraEndUpdate(Scene.camera);
		RevcLogCore("DoRWStuffEndOfFrame: after RwCameraEndUpdate");
	} __except(EXCEPTION_EXECUTE_HANDLER) {
		RevcLogCore("DoRWStuffEndOfFrame: RwCameraEndUpdate SEH");
	}
	__try {
		RsCameraShowRaster(Scene.camera);
		RevcLogCore("DoRWStuffEndOfFrame: after RsCameraShowRaster");
	} __except(EXCEPTION_EXECUTE_HANDLER) {
		RevcLogCore("DoRWStuffEndOfFrame: RsCameraShowRaster SEH");
	}
#ifndef MASTER
	char s[48];
#ifdef THIS_IS_STUPID
	if (CPad::GetPad(1)->GetLeftShockJustDown()) {
		// try using both controllers for this thing... crazy bastards
		if (CPad::GetPad(0)->GetRightStickY() > 0) {
			sprintf(s, "screen%d%d.ras", CClock::ms_nGameClockHours, CClock::ms_nGameClockMinutes);
			// TODO
			//RtTileRender(Scene.camera, TILE_WIDTH * 2, TILE_HEIGHT * 2, TILE_WIDTH, TILE_HEIGHT, &NewTileRendererCB, nil, s);
		} else {
			sprintf(s, "screen%d%d.bmp", CClock::ms_nGameClockHours, CClock::ms_nGameClockMinutes);
			RwGrabScreen(Scene.camera, s);
		}
	}
#else
#ifdef GTA_PC_CONTROLS
	if (CPad::GetPad(1)->GetLeftShockJustDown() || CPad::GetPad(0)->GetFJustDown(11))
#else
	if (CPad::GetPad(1)->GetLeftShockJustDown())
#endif
	{
		sprintf(s, "screen_%011lld.png", time(nil));
		RwGrabScreen(Scene.camera, s);
	}
#endif
#endif // !MASTER
}

static RwBool 
PluginAttach(void)
{
	if( !RpWorldPluginAttach() )
	{
		printf("Couldn't attach world plugin\n");
		
		return FALSE;
	}
	
	if( !RpSkinPluginAttach() )
	{
		printf("Couldn't attach RpSkin plugin\n");
		
		return FALSE;
	}
#ifndef LIBRW
	if (!RtAnimInitialize())
	{
		return FALSE;
	}
#endif
	if( !RpHAnimPluginAttach() )
	{
		printf("Couldn't attach RpHAnim plugin\n");
		
		return FALSE;
	}
	
	if( !NodeNamePluginAttach() )
	{
		printf("Couldn't attach node name plugin\n");
		
		return FALSE;
	}
	
	if( !CVisibilityPlugins::PluginAttach() )
	{
		printf("Couldn't attach visibility plugins\n");
		
		return FALSE;
	}
	
	if( !RpAnimBlendPluginAttach() )
	{
		printf("Couldn't attach RpAnimBlend plugin\n");
		
		return FALSE;
	}
	
	if( !RpMatFXPluginAttach() )
	{
		printf("Couldn't attach RpMatFX plugin\n");
		
		return FALSE;
	}
#ifdef ANISOTROPIC_FILTERING
	RpAnisotPluginAttach();
#endif
#ifdef EXTENDED_PIPELINES
	CustomPipes::CustomPipeRegister();
#endif

	return TRUE;
}

#ifdef GTA_PS2
#define NUM_PREALLOC_ATOMICS 1800
#define NUM_PREALLOC_CLUMPS 80
#define NUM_PREALLOC_FRAMES 2600
#define NUM_PREALLOC_GEOMETRIES 850
#define NUM_PREALLOC_TEXDICTS 121
#define NUM_PREALLOC_TEXTURES 1700
#define NUM_PREALLOC_MATERIALS 2600
bool preAlloc;

void
PreAllocateRwObjects(void)
{
	int i;

	PUSH_MEMID(MEMID_PRE_ALLOC);
	void **tmp = new void*[0x8000];
	preAlloc = true;

	for(i = 0; i < NUM_PREALLOC_ATOMICS; i++)
		tmp[i] = RpAtomicCreate();
	for(i = 0; i < NUM_PREALLOC_ATOMICS; i++)
		RpAtomicDestroy((RpAtomic*)tmp[i]);

	for(i = 0; i < NUM_PREALLOC_CLUMPS; i++)
		tmp[i] = RpClumpCreate();
	for(i = 0; i < NUM_PREALLOC_CLUMPS; i++)
		RpClumpDestroy((RpClump*)tmp[i]);

	for(i = 0; i < NUM_PREALLOC_FRAMES; i++)
		tmp[i] = RwFrameCreate();
	for(i = 0; i < NUM_PREALLOC_FRAMES; i++)
		RwFrameDestroy((RwFrame*)tmp[i]);

	for(i = 0; i < NUM_PREALLOC_GEOMETRIES; i++)
		tmp[i] = RpGeometryCreate(0, 0, 0);
	for(i = 0; i < NUM_PREALLOC_GEOMETRIES; i++)
		RpGeometryDestroy((RpGeometry*)tmp[i]);

	for(i = 0; i < NUM_PREALLOC_TEXDICTS; i++)
		tmp[i] = RwTexDictionaryCreate();
	for(i = 0; i < NUM_PREALLOC_TEXDICTS; i++)
		RwTexDictionaryDestroy((RwTexDictionary*)tmp[i]);

	for(i = 0; i < NUM_PREALLOC_TEXTURES; i++)
		tmp[i] = RwTextureCreate(RwRasterCreate(0, 0, 0, 0));
	for(i = 0; i < NUM_PREALLOC_TEXDICTS; i++)
		RwTextureDestroy((RwTexture*)tmp[i]);

	for(i = 0; i < NUM_PREALLOC_MATERIALS; i++)
		tmp[i] = RpMaterialCreate();
	for(i = 0; i < NUM_PREALLOC_MATERIALS; i++)
		RpMaterialDestroy((RpMaterial*)tmp[i]);

	delete[] tmp;
	preAlloc = false;
	POP_MEMID();
}
#endif

static RwBool 
Initialise3D(void *param)
{
	RevcLogCore("Initialise3D begin");
	PUSH_MEMID(MEMID_RENDER);

#ifndef MASTER
	VarConsole.Add("Display number of atomics rendered", &bDisplayNumOfAtomicsRendered, true);
	VarConsole.Add("Display posn and framerate", &bDisplayPosn, true);
#endif

	if (RsRwInitialize(param))
	{
		RevcLogCore("Initialise3D RsRwInitialize ok");
		POP_MEMID();

#ifdef DEBUGMENU
		DebugMenuInit();
		DebugMenuPopulate();
#endif // !DEBUGMENU
		if (CGame::InitialiseRenderWare()) {
			RevcLogCore("Initialise3D InitialiseRenderWare ok");
			return true;
		}
		RevcLogCore("Initialise3D InitialiseRenderWare failed");
		return false;
	}
	RevcLogCore("Initialise3D RsRwInitialize failed");
	POP_MEMID();

	return (FALSE);
}

static void 
Terminate3D(void)
{
	CGame::ShutdownRenderWare();
#ifdef DEBUGMENU
	DebugMenuShutdown();
#endif // !DEBUGMENU
	
	RsRwTerminate();

	return;
}

CSprite2d splash;
int splashTxdId = -1;

CSprite2d*
LoadSplash(const char *name)
{
	RwTexDictionary *txd;
	char filename[140];
	RwTexture *tex = nil;

	if(name == nil)
		return &splash;
	if(splashTxdId == -1)
		splashTxdId = CTxdStore::AddTxdSlot("splash");

	txd = CTxdStore::GetSlot(splashTxdId)->texDict;
	if(txd)
		tex = RwTexDictionaryFindNamedTexture(txd, name);
	// if texture is found, splash was already set up below

	if(tex == nil){
		CFileMgr::SetDir("TXD\\");
		sprintf(filename, "%s.txd", name);
		if(splash.m_pTexture)
			splash.Delete();
		if(txd)
			CTxdStore::RemoveTxd(splashTxdId);
		CTxdStore::LoadTxd(splashTxdId, filename);
		CTxdStore::AddRef(splashTxdId);
		CTxdStore::PushCurrentTxd();
		CTxdStore::SetCurrentTxd(splashTxdId);
		splash.SetTexture(name);
		CTxdStore::PopCurrentTxd();
		CFileMgr::SetDir("");
	}

	return &splash;
}

void
DestroySplashScreen(void)
{
	splash.Delete();
	if(splashTxdId != -1)
		CTxdStore::RemoveTxdSlot(splashTxdId);
	splashTxdId = -1;
}

Const char*
GetRandomSplashScreen(void)
{
	int index;
	static int index2 = 0;
	static char splashName[128];
	static int splashIndex[12] = {
		1, 2,
		3, 4,
		5, 11,
		6, 8,
		9, 10,
		7, 12
	};

	index = splashIndex[2*index2 + CGeneral::GetRandomNumberInRange(0, 2)];
	index2++;
	if(index2 == 6)
		index2 = 0;
	sprintf(splashName, "loadsc%d", index);
	return splashName;
}

Const char*
GetLevelSplashScreen(int level)
{
	static Const char *splashScreens[4] = {
		nil,
		"splash1",
		"splash2",
		"splash3",
	};

	return splashScreens[level];
}

void
ResetLoadingScreenBar()
{
	NumberOfChunksLoaded = 0.0f;
}

void
LoadingScreen(const char *str1, const char *str2, const char *splashscreen)
{
	CSprite2d *splash;

#ifdef DISABLE_LOADING_SCREEN
	if (str1 && str2)
		return;
#endif

#ifndef RANDOMSPLASH
	splashscreen = "LOADSC0";
#endif

	splash = LoadSplash(splashscreen);

#ifndef GTA_PS2
	if(RsGlobal.quit)
		return;
#endif

	if(DoRWStuffStartOfFrame(0, 0, 0, 0, 0, 0, 255)){
		CSprite2d::SetRecipNearClip();
		CSprite2d::InitPerFrame();
		CFont::InitPerFrame();
		DefinedState();
		RwRenderStateSet(rwRENDERSTATETEXTUREADDRESS, (void*)rwTEXTUREADDRESSCLAMP);
		splash->Draw(CRect(0.0f, 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT), CRGBA(255, 255, 255, 255));

		if(str1){
			NumberOfChunksLoaded += 1;

#ifndef RANDOMSPLASH
			float hpos = SCREEN_SCALE_X(40);
			float length = SCREEN_WIDTH - SCREEN_SCALE_X(80);
			float top = SCREEN_HEIGHT - SCREEN_SCALE_Y(14);
			float bottom = top + SCREEN_SCALE_Y(5);
#else
			float hpos = SCREEN_STRETCH_X(40);
			float length = SCREEN_STRETCH_X(440);
			// this is rather weird
			float top = SCREEN_STRETCH_Y(407.4f - 7.0f/3.0f);
			float bottom = SCREEN_STRETCH_Y(407.4f + 7.0f/3.0f);
#endif

			CSprite2d::DrawRect(CRect(hpos-1.0f, top-1.0f, hpos+length+1.0f, bottom+1.0f), CRGBA(40, 53, 68, 255));

			CSprite2d::DrawRect(CRect(hpos, top, hpos+length, bottom), CRGBA(155, 50, 125, 255));

			length *= NumberOfChunksLoaded/TOTALNUMCHUNKS;
			CSprite2d::DrawRect(CRect(hpos, top, hpos+length, bottom), CRGBA(255, 150, 225, 255));

			// this is done by the game but is unused
			CFont::SetBackgroundOff();
			CFont::SetScale(SCREEN_SCALE_X(2), SCREEN_SCALE_Y(2));
			CFont::SetPropOn();
			CFont::SetRightJustifyOn();
			CFont::SetDropShadowPosition(1);
			CFont::SetDropColor(CRGBA(0, 0, 0, 255));
			CFont::SetFontStyle(FONT_HEADING);

#ifdef CHATTYSPLASH
			// my attempt
			static wchar tmpstr[80];
			float yscale = SCREEN_SCALE_Y(0.9f);
			top -= 45*yscale;
			CFont::SetScale(SCREEN_SCALE_X(0.75f), yscale);
			CFont::SetPropOn();
			CFont::SetRightJustifyOff();
			CFont::SetFontStyle(FONT_STANDARD);
			CFont::SetColor(CRGBA(255, 255, 255, 255));
			AsciiToUnicode(str1, tmpstr);
			CFont::PrintString(hpos, top, tmpstr);
			top += 22*yscale;
			if (str2) {
				AsciiToUnicode(str2, tmpstr);
				CFont::PrintString(hpos, top, tmpstr);
			}
#endif
		}

		CFont::DrawFonts();
 		DoRWStuffEndOfFrame();
	}
}

void
LoadingIslandScreen(const char *levelName)
{
	CSprite2d *splash;

	splash = LoadSplash(nil);
	if(!DoRWStuffStartOfFrame(0, 0, 0, 0, 0, 0, 255))
		return;

	CSprite2d::SetRecipNearClip();
	CSprite2d::InitPerFrame();
	CFont::InitPerFrame();
	DefinedState();
	CRGBA col = CRGBA(255, 255, 255, 255);
	CRGBA col2 = CRGBA(0, 0, 0, 255);
	CSprite2d::DrawRect(CRect(0.0f, 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT), col2);
	splash->Draw(CRect(0.0f, 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT), col, col, col, col);
	CFont::DrawFonts();
	DoRWStuffEndOfFrame();
}

void
ProcessSlowMode(void)
{  
	int16 lX = CPad::GetPad(0)->NewState.LeftStickX;
	int16 lY = CPad::GetPad(0)->NewState.LeftStickY;
	int16 rX = CPad::GetPad(0)->NewState.RightStickX;
	int16 rY = CPad::GetPad(0)->NewState.RightStickY;
	int16 L1 = CPad::GetPad(0)->NewState.LeftShoulder1;
	int16 L2 = CPad::GetPad(0)->NewState.LeftShoulder2;
	int16 R1 = CPad::GetPad(0)->NewState.RightShoulder1;
	int16 R2 = CPad::GetPad(0)->NewState.RightShoulder2;
	int16 up = CPad::GetPad(0)->NewState.DPadUp;
	int16 down = CPad::GetPad(0)->NewState.DPadDown;
	int16 left = CPad::GetPad(0)->NewState.DPadLeft;
	int16 right = CPad::GetPad(0)->NewState.DPadRight;
	int16 start = CPad::GetPad(0)->NewState.Start;
	int16 select = CPad::GetPad(0)->NewState.Select;
	int16 square = CPad::GetPad(0)->NewState.Square;
	int16 triangle = CPad::GetPad(0)->NewState.Triangle;
	int16 cross = CPad::GetPad(0)->NewState.Cross;
	int16 circle = CPad::GetPad(0)->NewState.Circle;
	int16 L3 = CPad::GetPad(0)->NewState.LeftShock;
	int16 R3 = CPad::GetPad(0)->NewState.RightShock;
	int16 networktalk = CPad::GetPad(0)->NewState.NetworkTalk;
	int16 stop = true;
	
	do
	{
		if ( CPad::GetPad(1)->GetSelectJustDown() || CPad::GetPad(1)->GetStart() )
			break;
		
		if ( stop )
		{
			CTimer::Stop();
			stop = false;
		}
		
		CPad::UpdatePads();
		
		RwCameraBeginUpdate(Scene.camera);
		RwCameraEndUpdate(Scene.camera);
		
	} while (!CPad::GetPad(1)->GetSelectJustDown() && !CPad::GetPad(1)->GetStart());
	
	
	CPad::GetPad(0)->OldState.LeftStickX = lX;
	CPad::GetPad(0)->OldState.LeftStickY = lY;
	CPad::GetPad(0)->OldState.RightStickX = rX;
	CPad::GetPad(0)->OldState.RightStickY = rY;
	CPad::GetPad(0)->OldState.LeftShoulder1 = L1;
	CPad::GetPad(0)->OldState.LeftShoulder2 = L2;
	CPad::GetPad(0)->OldState.RightShoulder1 = R1;
	CPad::GetPad(0)->OldState.RightShoulder2 = R2;
	CPad::GetPad(0)->OldState.DPadUp = up;
	CPad::GetPad(0)->OldState.DPadDown = down;
	CPad::GetPad(0)->OldState.DPadLeft = left;
	CPad::GetPad(0)->OldState.DPadRight = right;
	CPad::GetPad(0)->OldState.Start = start;
	CPad::GetPad(0)->OldState.Select = select;
	CPad::GetPad(0)->OldState.Square = square;
	CPad::GetPad(0)->OldState.Triangle = triangle;
	CPad::GetPad(0)->OldState.Cross = cross;
	CPad::GetPad(0)->OldState.Circle = circle;
	CPad::GetPad(0)->OldState.LeftShock = L3;
	CPad::GetPad(0)->OldState.RightShock = R3;
	CPad::GetPad(0)->OldState.NetworkTalk = networktalk;
	CPad::GetPad(0)->NewState.LeftStickX = lX;
	CPad::GetPad(0)->NewState.LeftStickY = lY;
	CPad::GetPad(0)->NewState.RightStickX = rX;
	CPad::GetPad(0)->NewState.RightStickY = rY;
	CPad::GetPad(0)->NewState.LeftShoulder1 = L1;
	CPad::GetPad(0)->NewState.LeftShoulder2 = L2;
	CPad::GetPad(0)->NewState.RightShoulder1 = R1;
	CPad::GetPad(0)->NewState.RightShoulder2 = R2;
	CPad::GetPad(0)->NewState.DPadUp = up;
	CPad::GetPad(0)->NewState.DPadDown = down;
	CPad::GetPad(0)->NewState.DPadLeft = left;
	CPad::GetPad(0)->NewState.DPadRight = right;
	CPad::GetPad(0)->NewState.Start = start;
	CPad::GetPad(0)->NewState.Select = select;
	CPad::GetPad(0)->NewState.Square = square;
	CPad::GetPad(0)->NewState.Triangle = triangle;
	CPad::GetPad(0)->NewState.Cross = cross;
	CPad::GetPad(0)->NewState.Circle = circle;
	CPad::GetPad(0)->NewState.LeftShock = L3;
	CPad::GetPad(0)->NewState.RightShock = R3;
	CPad::GetPad(0)->NewState.NetworkTalk = networktalk;
}


float FramesPerSecondCounter;
int32 FrameSamples;

#ifndef MASTER
struct tZonePrint
{
	char name[11];
	char area[5];
	CRect rect;
};

tZonePrint ZonePrint[] =
{
	{ "DOWNTOWN", "GM", CRect(-1500.0f, 1500.0f, -300.0f, 980.0f)},
	{ "DOWNTOWS", "KB", CRect(-1200.0f, 980.0f, -300.0f, 435.0f)},
	{ "GOLF", "NT", CRect(-300.0f, 660.0f, 320.0f, -255.0f)},
	{ "LITTLEHA", "AG", CRect(-1250.0f, -310.0f, -746.0f, -926.0f)},
	{ "HAITI", "CJ", CRect(-1355.0f, 30.0f, -637.0f, -304.0f)},
	{ "HAITIN", "SM", CRect(-1355.0f, 435.0f, -637.0f, 30.0f)},
	{ "DOCKS", "AW", CRect(-1122.0f, -926.0f, -609.0f, -1575.0f)},
	{ "AIRPORT", "NT", CRect(-2000.0f, 200.0f, -871.0f, -2000.0f)},
	{ "STARISL", "CJ", CRect(-724.0f, -320.0f, -40.0f, -380.0f)},
	{ "CENT.ISLA", "NT", CRect(-163.0f, 1260.0f,  120.0f, 830.0f)},
	{ "MALL", "AW", CRect( 300.0f, 1266.0f,  483.0f, 995.0f)},
	{ "MANSION", "KB", CRect(-724.0f, -500.0f, -40.0f, -670.0f)},
	{ "NBEACH", "AS", CRect( 120.0f,  1340.0f,  900.0f,  600.0f)},
	{ "NBEACHBT", "AS", CRect( 200.0f, 680.0f,  660.0f, -50.0f)},
	{ "NBEACHW", "AS", CRect(-93.0f, 80.0f,  410.0f, -680.0f)},
	{ "OCEANDRV", "AC", CRect( 200.0f, -964.0f,  955.0f, -1797.0f)},
	{ "OCEANDN", "WS", CRect( 400.0f, 50.0f,  955.0f,  -964.0f)},
	{ "WASHINGTN", "AC", CRect(-320.0f, -487.0f,  500.0f, -1200.0f)},
	{ "WASHINBTM", "AC", CRect(-255.0f, -1200.0f,  500.0f, -1690.0f)}
};

void
PrintMemoryUsage(void)
{
// little hack
if(CPools::GetPtrNodePool() == nil)
return;

	// Style taken from LCS, modified for III
//	CFont::SetFontStyle(FONT_PAGER);
	CFont::SetFontStyle(FONT_BANK);
	CFont::SetBackgroundOff();
	CFont::SetWrapx(640.0f);
//	CFont::SetScale(0.5f, 0.75f);
	CFont::SetScale(0.4f, 0.75f);
	CFont::SetCentreOff();
	CFont::SetCentreSize(640.0f);
	CFont::SetJustifyOff();
	CFont::SetPropOn();
	CFont::SetColor(CRGBA(200, 200, 200, 200));
	CFont::SetBackGroundOnlyTextOff();
	CFont::SetDropShadowPosition(0);

	float y;

#ifdef USE_CUSTOM_ALLOCATOR
	y = 24.0f;
	sprintf(gString, "Total: %d blocks, %d bytes", gMainHeap.m_totalBlocksUsed, gMainHeap.m_totalMemUsed);
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Game: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_GAME), gMainHeap.GetMemoryUsed(MEMID_GAME));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "World: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_WORLD), gMainHeap.GetMemoryUsed(MEMID_WORLD));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Render: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_RENDER), gMainHeap.GetMemoryUsed(MEMID_RENDER));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "PreAlloc: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_PRE_ALLOC), gMainHeap.GetMemoryUsed(MEMID_PRE_ALLOC));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Default Models: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_DEF_MODELS), gMainHeap.GetMemoryUsed(MEMID_DEF_MODELS));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Textures: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_TEXTURES), gMainHeap.GetMemoryUsed(MEMID_TEXTURES));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Streaming: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_STREAM), gMainHeap.GetMemoryUsed(MEMID_STREAM));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Streamed Models: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_STREAM_MODELS), gMainHeap.GetMemoryUsed(MEMID_STREAM_MODELS));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Streamed LODs: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_STREAM_LODS), gMainHeap.GetMemoryUsed(MEMID_STREAM_LODS));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Streamed Textures: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_STREAM_TEXUTRES), gMainHeap.GetMemoryUsed(MEMID_STREAM_TEXUTRES));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Streamed Collision: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_STREAM_COLLISION), gMainHeap.GetMemoryUsed(MEMID_STREAM_COLLISION));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Streamed Animation: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_STREAM_ANIMATION), gMainHeap.GetMemoryUsed(MEMID_STREAM_ANIMATION));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Ped Attr: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_PED_ATTR), gMainHeap.GetMemoryUsed(MEMID_PED_ATTR));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Animation: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_ANIMATION), gMainHeap.GetMemoryUsed(MEMID_ANIMATION));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Pools: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_POOLS), gMainHeap.GetMemoryUsed(MEMID_POOLS));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Collision: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_COLLISION), gMainHeap.GetMemoryUsed(MEMID_COLLISION));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Game Process: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_GAME_PROCESS), gMainHeap.GetMemoryUsed(MEMID_GAME_PROCESS));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Script: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_SCRIPT), gMainHeap.GetMemoryUsed(MEMID_SCRIPT));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Cars: %d blocks, %d bytes", gMainHeap.GetBlocksUsed(MEMID_CARS), gMainHeap.GetMemoryUsed(MEMID_CARS));
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(24.0f, y, gUString);
	y += 12.0f;
#endif

	y = 132.0f;
	AsciiToUnicode("Pools usage:", gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "PtrNode: %d/%d", CPools::GetPtrNodePool()->GetNoOfUsedSpaces(), CPools::GetPtrNodePool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "EntryInfoNode: %d/%d", CPools::GetEntryInfoNodePool()->GetNoOfUsedSpaces(), CPools::GetEntryInfoNodePool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Ped: %d/%d", CPools::GetPedPool()->GetNoOfUsedSpaces(), CPools::GetPedPool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Vehicle: %d/%d", CPools::GetVehiclePool()->GetNoOfUsedSpaces(), CPools::GetVehiclePool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Building: %d/%d", CPools::GetBuildingPool()->GetNoOfUsedSpaces(), CPools::GetBuildingPool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Treadable: %d/%d", CPools::GetTreadablePool()->GetNoOfUsedSpaces(), CPools::GetTreadablePool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Object: %d/%d", CPools::GetObjectPool()->GetNoOfUsedSpaces(), CPools::GetObjectPool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "Dummy: %d/%d", CPools::GetDummyPool()->GetNoOfUsedSpaces(), CPools::GetDummyPool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;

	sprintf(gString, "AudioScriptObjects: %d/%d", CPools::GetAudioScriptObjectPool()->GetNoOfUsedSpaces(), CPools::GetAudioScriptObjectPool()->GetSize());
	AsciiToUnicode(gString, gUString);
	CFont::PrintString(400.0f, y, gUString);
	y += 12.0f;
}

void
DisplayGameDebugText()
{
	static bool bDisplayCheatStr = false; // custom

#ifndef FINAL
	{
		SETTWEAKPATH("Debug");
		TWEAKBOOL(bDisplayPosn);
		TWEAKBOOL(bDisplayCheatStr);
	}

	if(gbPrintMemoryUsage)
		PrintMemoryUsage();
#endif

	char str[200];
	wchar ustr[200];

#ifdef DRAW_GAME_VERSION_TEXT
	wchar ver[200];

	if(gbDrawVersionText) // This realtime switch is our thing
	{

#ifdef USE_OUR_VERSIONING
	char verA[200];
	sprintf(verA,
#if defined _WIN32
			"Win "
#elif defined __linux__
		    "Linux "
#elif defined __APPLE__
		    "Mac OS X "
#elif defined __FreeBSD__
		    "FreeBSD "
#else
		    "Posix-compliant "
#endif
#if defined __LP64__ || defined _WIN64
			"64-bit "
#else
			"32-bit "
#endif
#if defined RW_D3D9
		    "D3D9 "
#elif defined RWLIBS
		    "D3D8 "
#elif defined RW_GL3
		    "OpenGL "
#endif
#if defined AUDIO_OAL
		    "OAL "
#elif defined AUDIO_MSS
		    "MSS "
#endif
#if defined _DEBUG || defined DEBUG
		    "DEBUG "
#endif
		    "%.8s",
		    g_GIT_SHA1);
	AsciiToUnicode(verA, ver);
	CFont::SetScale(SCREEN_SCALE_X(0.5f), SCREEN_SCALE_Y(0.7f));
#else
	AsciiToUnicode(version_name, ver);
	CFont::SetScale(SCREEN_SCALE_X(0.5f), SCREEN_SCALE_Y(0.5f));
#endif

	CFont::SetPropOn();
	CFont::SetBackgroundOff();
	CFont::SetFontStyle(FONT_STANDARD);
	CFont::SetCentreOff();
	CFont::SetRightJustifyOff();
	CFont::SetWrapx(SCREEN_WIDTH);
	CFont::SetJustifyOff();
	CFont::SetBackGroundOnlyTextOff();
	CFont::SetColor(CRGBA(255, 108, 0, 255));
	CFont::PrintString(SCREEN_SCALE_X(10.0f), SCREEN_SCALE_Y(10.0f), ver);
	}
#endif // #ifdef DRAW_GAME_VERSION_TEXT

	FrameSamples++;
#ifdef FIX_BUGS
	// this is inaccurate with over 1000 fps
	static uint32 PreviousTimeInMillisecondsPauseMode = 0;
	FramesPerSecondCounter += (CTimer::GetTimeInMillisecondsPauseMode() - PreviousTimeInMillisecondsPauseMode) / 1000.0f; // convert to seconds
	PreviousTimeInMillisecondsPauseMode = CTimer::GetTimeInMillisecondsPauseMode();
	FramesPerSecond = FrameSamples / FramesPerSecondCounter;
#else
	FramesPerSecondCounter += 1000.0f / CTimer::GetTimeStepNonClippedInMilliseconds();
	FramesPerSecond = FramesPerSecondCounter / FrameSamples;
#endif
	
	if ( FrameSamples > 30 )
	{
		FramesPerSecondCounter = 0.0f;
		FrameSamples = 0;
	}

	if ( bDisplayPosn )
	{
		CVector pos = FindPlayerCoors();
		int32 ZoneId = ARRAY_SIZE(ZonePrint)-1; // no zone
		
		for ( int32 i = 0; i < ARRAY_SIZE(ZonePrint)-1; i++ )
		{
			if ( pos.x > ZonePrint[i].rect.left
				&& pos.x < ZonePrint[i].rect.right
				&& pos.y > ZonePrint[i].rect.bottom
				&& pos.y < ZonePrint[i].rect.top )
			{
				ZoneId = i;
			}
		}

		//NOTE: fps should be 30, but its 29 due to different fp2int conversion 
		sprintf(str, "X:%4.0f Y:%4.0f Z:%4.0f F-%d %s-%s", pos.x, pos.y, pos.z, (int32)FramesPerSecond,
			ZonePrint[ZoneId].name, ZonePrint[ZoneId].area);

		AsciiToUnicode(str, ustr);
		
		CFont::SetPropOn();
		CFont::SetBackgroundOff();
		CFont::SetScale(SCREEN_SCALE_X(0.6f), SCREEN_SCALE_Y(0.8f));
		CFont::SetCentreOff();
		CFont::SetRightJustifyOff();
		CFont::SetJustifyOff();
		CFont::SetBackGroundOnlyTextOff();
		CFont::SetWrapx(SCREEN_STRETCH_X(DEFAULT_SCREEN_WIDTH));
		CFont::SetFontStyle(FONT_STANDARD);
		CFont::SetDropColor(CRGBA(0, 0, 0, 255));
		CFont::SetDropShadowPosition(2);
		CFont::SetColor(CRGBA(0, 0, 0, 255));
		CFont::PrintString(41.0f, 41.0f, ustr);
		
		CFont::SetColor(CRGBA(205, 205, 0, 255));
		CFont::PrintString(40.0f, 40.0f, ustr);
	}

	// custom
	if (bDisplayCheatStr)
	{
		sprintf(str, "%s", CPad::KeyBoardCheatString);
		AsciiToUnicode(str, ustr);

		CFont::SetPropOn();
		CFont::SetBackgroundOff();
		CFont::SetScale(SCREEN_SCALE_X(0.6f), SCREEN_SCALE_Y(0.8f));
		CFont::SetCentreOn();
		CFont::SetBackGroundOnlyTextOff();
		CFont::SetWrapx(SCREEN_STRETCH_X(DEFAULT_SCREEN_WIDTH));
		CFont::SetFontStyle(FONT_STANDARD);

		CFont::SetColor(CRGBA(0, 0, 0, 255));
		CFont::PrintString(SCREEN_SCALE_X(DEFAULT_SCREEN_WIDTH * 0.5f)+2.f, SCREEN_SCALE_FROM_BOTTOM(20.0f)+2.f, ustr);

		CFont::SetColor(CRGBA(255, 150, 225, 255));
		CFont::PrintString(SCREEN_SCALE_X(DEFAULT_SCREEN_WIDTH * 0.5f), SCREEN_SCALE_FROM_BOTTOM(20.0f), ustr);
	}
}
#endif

#ifdef NEW_RENDERER
bool gbRenderRoads = true;
bool gbRenderEverythingBarRoads = true;
bool gbRenderFadingInUnderwaterEntities = true;
bool gbRenderFadingInEntities = true;
bool gbRenderWater = true;
bool gbRenderBoats = true;
bool gbRenderVehicles = true;
bool gbRenderWorld0 = true;
bool gbRenderWorld1 = true;
bool gbRenderWorld2 = true;

void
MattRenderScene(void)
{
	// this calls CMattRenderer::Render
	/// CWorld::AdvanceCurrentScanCode();
	// CMattRenderer::ResetRenderStates
	/// CRenderer::ClearForFrame();		// before ConstructRenderList
	// CClock::CalcEnvMapTimeMultiplicator
	RwRenderStateSet(rwRENDERSTATECULLMODE, (void*)rwCULLMODECULLNONE);
	CWaterLevel::RenderWater();	// actually CMattRenderer::RenderWater
	// CClock::ms_EnvMapTimeMultiplicator = 1.0f;
	// cWorldStream::ClearDynamics
	/// CRenderer::ConstructRenderList();	// before PreRender
if(gbRenderWorld0)
	CRenderer::RenderWorld(0);	// roads
	// CMattRenderer::ResetRenderStates
	/// CRenderer::PreRender();	// has to be called before BeginUpdate because of cutscene shadows
	CCoronas::RenderReflections();
if(gbRenderWorld1)
	CRenderer::RenderWorld(1);	// opaque
if(gbRenderRoads)
	CRenderer::RenderRoads();

	CRenderer::RenderPeds();

	// not sure where to put these since LCS has no underwater entities
if(gbRenderBoats)
	CRenderer::RenderBoats();
if(gbRenderFadingInUnderwaterEntities)
	CRenderer::RenderFadingInUnderwaterEntities();
	RwRenderStateSet(rwRENDERSTATECULLMODE, (void*)rwCULLMODECULLNONE);
if(gbRenderWater)
	CRenderer::RenderTransparentWater();

if(gbRenderEverythingBarRoads)
	CRenderer::RenderEverythingBarRoads();
	// seam fixer
	// moved this:
	// CRenderer::RenderFadingInEntities();
}

void
RenderScene_new(void)
{
	PUSH_RENDERGROUP("RenderScene_new");
	CClouds::Render();
	DoRWRenderHorizon();

	MattRenderScene();
	DefinedState();
	// CMattRenderer::ResetRenderStates
	// moved CRenderer::RenderBoats to before transparent water
	POP_RENDERGROUP();
}

// TODO
bool FredIsInFirstPersonCam(void) { return false; }
void
RenderEffects_new(void)
{
	PUSH_RENDERGROUP("RenderEffects_new");
/*	// stupid to do this before the whole world is drawn!
	CShadows::RenderStaticShadows();
	// CRenderer::GenerateEnvironmentMap
	CShadows::RenderStoredShadows();
	CSkidmarks::Render();
	CRubbish::Render();
*/

	// these aren't really effects
	DefinedState();
	if(FredIsInFirstPersonCam()){
		DefinedState();
		C3dMarkers::Render();	// normally rendered in CSpecialFX::Render()
if(gbRenderWorld2)
		CRenderer::RenderWorld(2);	// transparent
if(gbRenderVehicles)
		CRenderer::RenderVehicles();
	}else{
		// flipped these two, seems to give the best result
if(gbRenderWorld2)
		CRenderer::RenderWorld(2);	// transparent
if(gbRenderVehicles)
		CRenderer::RenderVehicles();
	}
	// better render these after transparent world
if(gbRenderFadingInEntities)
	CRenderer::RenderFadingInEntities();

	// actual effects here

	// from above
	CShadows::RenderStaticShadows();
	CShadows::RenderStoredShadows();
	CSkidmarks::Render();
	CRubbish::Render();

	CGlass::Render();
	// CMattRenderer::ResetRenderStates
	DefinedState();
	CCoronas::RenderSunReflection();
	CWeather::RenderRainStreaks();
	// CWeather::AddSnow
	CWaterCannons::Render();
	CAntennas::Render();
	CSpecialFX::Render();
	CRopes::Render();
	CCoronas::Render();
	CParticle::Render();
	CPacManPickups::Render();
	CWeaponEffects::Render();
	CPointLights::RenderFogEffect();
	CMovingThings::Render();
	CRenderer::RenderFirstPersonVehicle();
	POP_RENDERGROUP();
}
#endif

void
RenderScene(void)
{
#ifdef NEW_RENDERER
	if(gbNewRenderer){
		RenderScene_new();
		return;
	}
#endif
	PUSH_RENDERGROUP("RenderScene");
	CClouds::Render();
	DoRWRenderHorizon();
	CRenderer::RenderRoads();
	CCoronas::RenderReflections();
	CRenderer::RenderEverythingBarRoads();
	RwRenderStateSet(rwRENDERSTATECULLMODE, (void*)rwCULLMODECULLNONE);
	CWaterLevel::RenderWater();
	CRenderer::RenderBoats();
	CRenderer::RenderFadingInUnderwaterEntities();
	RwRenderStateSet(rwRENDERSTATECULLMODE, (void*)rwCULLMODECULLNONE);
	CWaterLevel::RenderTransparentWater();
	CRenderer::RenderFadingInEntities();
	RwRenderStateSet(rwRENDERSTATECULLMODE, (void*)rwCULLMODECULLNONE);
	CWeather::RenderRainStreaks();
	CCoronas::RenderSunReflection();
	POP_RENDERGROUP();
}

void
RenderDebugShit(void)
{
	PUSH_RENDERGROUP("RenderDebugShit");
	CTheScripts::RenderTheScriptDebugLines();
#ifndef FINAL
	if(gbShowCollisionLines)
		CRenderer::RenderCollisionLines();
	ThePaths.DisplayPathData();
	CDebug::DrawLines();
	DefinedState();
#endif
	POP_RENDERGROUP();
}

void
RenderEffects(void)
{
#ifdef NEW_RENDERER
	if(gbNewRenderer){
		RenderEffects_new();
		return;
	}
#endif
	PUSH_RENDERGROUP("RenderEffects");
	CGlass::Render();
	CWaterCannons::Render();
	CSpecialFX::Render();
	CRopes::Render();
	CShadows::RenderStaticShadows();
	CShadows::RenderStoredShadows();
	CSkidmarks::Render();
	CAntennas::Render();
	CRubbish::Render();
	CCoronas::Render();
	CParticle::Render();
	CPacManPickups::Render();
	CWeaponEffects::Render();
	CPointLights::RenderFogEffect();
	CMovingThings::Render();
	CRenderer::RenderFirstPersonVehicle();
	POP_RENDERGROUP();
}

void
Render2dStuff(void)
{
	PUSH_RENDERGROUP("Render2dStuff");
	RwRenderStateSet(rwRENDERSTATEZTESTENABLE, (void*)FALSE);
	RwRenderStateSet(rwRENDERSTATEZWRITEENABLE, (void*)FALSE);
	RwRenderStateSet(rwRENDERSTATEVERTEXALPHAENABLE, (void*)TRUE);
	RwRenderStateSet(rwRENDERSTATESRCBLEND, (void*)rwBLENDSRCALPHA);
	RwRenderStateSet(rwRENDERSTATEDESTBLEND, (void*)rwBLENDINVSRCALPHA);
	RwRenderStateSet(rwRENDERSTATECULLMODE, (void*)rwCULLMODECULLNONE);

	CReplay::Display();
	CPickups::RenderPickUpText();

	if(TheCamera.m_WideScreenOn
#ifdef CUTSCENE_BORDERS_SWITCH
		&& CMenuManager::m_PrefsCutsceneBorders
#endif
		)
		TheCamera.DrawBordersForWideScreen();

	CPed *player = FindPlayerPed();
	int weaponType = 0;
	if(player)
		weaponType = player->GetWeapon()->m_eWeaponType;

	bool firstPersonWeapon = false;
	int cammode = TheCamera.Cams[TheCamera.ActiveCam].Mode;
	if(cammode == CCam::MODE_SNIPER ||
	   cammode == CCam::MODE_SNIPER_RUNABOUT ||
	   cammode == CCam::MODE_ROCKETLAUNCHER ||
	   cammode == CCam::MODE_ROCKETLAUNCHER_RUNABOUT ||
	   cammode == CCam::MODE_CAMERA)
		firstPersonWeapon = true;

	// Draw black border for sniper and rocket launcher
	if((weaponType == WEAPONTYPE_SNIPERRIFLE || weaponType == WEAPONTYPE_ROCKETLAUNCHER || weaponType == WEAPONTYPE_LASERSCOPE) && firstPersonWeapon){
		CRGBA black(0, 0, 0, 255);

		// top and bottom strips
		if (weaponType == WEAPONTYPE_ROCKETLAUNCHER) {
			CSprite2d::DrawRect(CRect(0.0f, 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT / 2 - SCREEN_SCALE_Y(180)), black);
			CSprite2d::DrawRect(CRect(0.0f, SCREEN_HEIGHT / 2 + SCREEN_SCALE_Y(170), SCREEN_WIDTH, SCREEN_HEIGHT), black);
		}
		else {
			CSprite2d::DrawRect(CRect(0.0f, 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT / 2 - SCREEN_SCALE_Y(210)), black);
			CSprite2d::DrawRect(CRect(0.0f, SCREEN_HEIGHT / 2 + SCREEN_SCALE_Y(210), SCREEN_WIDTH, SCREEN_HEIGHT), black);
		}
		CSprite2d::DrawRect(CRect(0.0f, 0.0f, SCREEN_WIDTH / 2 - SCREEN_SCALE_X(210), SCREEN_HEIGHT), black);
		CSprite2d::DrawRect(CRect(SCREEN_WIDTH / 2 + SCREEN_SCALE_X(210), 0.0f, SCREEN_WIDTH, SCREEN_HEIGHT), black);
	}

	MusicManager.DisplayRadioStationName();
	TheConsole.Display();
#ifdef GTA_SCENE_EDIT
	if(CSceneEdit::m_bEditOn)
		CSceneEdit::Draw();
	else
#endif
		CHud::Draw();

	CSpecialFX::Render2DFXs();
	CUserDisplay::OnscnTimer.ProcessForDisplay();
	CMessages::Display();
	CDarkel::DrawMessages();
	CGarages::PrintMessages();
	CPad::PrintErrorMessage();
	CFont::DrawFonts();
#ifndef MASTER
	COcclusion::Render();
#endif

#ifdef DEBUGMENU
	DebugMenuRender();
#endif
	POP_RENDERGROUP();
}

void
RenderMenus(void)
{
	if (FrontEndMenuManager.m_bMenuActive)
	{
		PUSH_RENDERGROUP("RenderMenus");
		FrontEndMenuManager.DrawFrontEnd();
		POP_RENDERGROUP();
	}
#ifndef MASTER
	else
		VarConsole.Check();
#endif
}

void
Render2dStuffAfterFade(void)
{
	PUSH_RENDERGROUP("Render2dStuffAfterFade");
#ifndef MASTER
	DisplayGameDebugText();
#endif

#ifdef MOBILE_IMPROVEMENTS
	if (CDraw::FadeValue != 0)
#endif
	CHud::DrawAfterFade();
	CFont::DrawFonts();
	CCredits::Render();
	POP_RENDERGROUP();
}

void
Idle(void *arg)
{
	RevcLogCore("Idle: begin");
	if(gRevcFrameLogCount < 120){
		char buf[256];
		CPlayerPed *ped = FindPlayerPed();
		if(ped){
			CVector pos = ped->GetPosition();
			sprintf(buf, "Idle: playerPed=%p pos=%.2f %.2f %.2f", ped, pos.x, pos.y, pos.z);
		}else{
			sprintf(buf, "Idle: playerPed=nil");
		}
		RevcLogCore(buf);
		if(Scene.camera){
			CVector cpos = Scene.camera->getFrame()->getLTM()->pos;
			CVector at = Scene.camera->getFrame()->getLTM()->at;
			RwRaster *r = RwCameraGetRaster(Scene.camera);
			if(r){
				sprintf(buf, "Idle: camera pos=%.2f %.2f %.2f at=%.2f %.2f %.2f raster=%dx%d", cpos.x, cpos.y, cpos.z, at.x, at.y, at.z, r->width, r->height);
			}else{
				sprintf(buf, "Idle: camera pos=%.2f %.2f %.2f at=%.2f %.2f %.2f raster=nil", cpos.x, cpos.y, cpos.z, at.x, at.y, at.z);
			}
			RevcLogCore(buf);
		}else{
			RevcLogCore("Idle: Scene.camera=nil");
		}
		gRevcFrameLogCount++;
	}
	CTimer::Update();
	RevcLogCore("Idle: after CTimer::Update");

	tbInit();
	RevcLogCore("Idle: after tbInit");

	CSprite2d::InitPerFrame();
	RevcLogCore("Idle: after CSprite2d::InitPerFrame");
	CFont::InitPerFrame();
	RevcLogCore("Idle: after CFont::InitPerFrame");

	PUSH_MEMID(MEMID_GAME_PROCESS);
	CPointLights::InitPerFrame();
	RevcLogCore("Idle: after CPointLights::InitPerFrame");

	tbStartTimer(0, "CGame::Process");
#ifdef REVC_DLL
	RevcPortalUpdatePlayerProtection();
#endif
	CGame::Process();
	tbEndTimer("CGame::Process");
	RevcLogCore("Idle: after CGame::Process");
#ifdef REVC_DLL
	RevcPortalProcessCommands();
	RevcPortalUpdatePlayerProtection();
	RevcPortalApplyCamera();
	RevcPortalTraceState();
	RevcPortalUpdateReturnPortal();
#endif
	POP_MEMID();

	tbStartTimer(0, "DMAudio.Service");
	DMAudio.Service();
	tbEndTimer("DMAudio.Service");
	RevcLogCore("Idle: after DMAudio.Service");

	if(CGame::bDemoMode && CTimer::GetTimeInMilliseconds() > (3*60 + 30)*1000 && !CCutsceneMgr::IsCutsceneProcessing()){
		WANT_TO_LOAD = false;
		FrontEndMenuManager.m_bWantToRestart = true;
		return;
	}

	if(FrontEndMenuManager.m_bWantToRestart || FOUND_GAME_TO_LOAD)
	{
		RevcLogCore("Idle: early return (restart/load)");
		return;
	}
	
	SetLightsWithTimeOfDayColour(Scene.world);
	RevcLogCore("Idle: after SetLightsWithTimeOfDayColour");

	if(arg == nil)
	{
		RevcLogCore("Idle: arg nil, return");
		return;
	}

	PUSH_MEMID(MEMID_RENDER);
	RevcLogCore("Idle: MEMID_RENDER begin");

	int menuActive = 0;
	int renderGameInMenu = 0;
	int fadeStatus = -999;
	__try {
		menuActive = FrontEndMenuManager.m_bMenuActive ? 1 : 0;
#ifdef PS2_MENU
		renderGameInMenu = FrontEndMenuManager.m_bRenderGameInMenu ? 1 : 0;
#else
#ifdef REVC_DLL
		// In external-device DLL mode, rendering world behind menu causes
		// one-frame flashes during menu page transitions.
		renderGameInMenu = 0;
#else
		renderGameInMenu = FrontEndMenuManager.m_bGameNotLoaded ? 0 : 1;
#endif
#endif
		fadeStatus = TheCamera.GetScreenFadeStatus();
	} __except(EXCEPTION_EXECUTE_HANDLER) {
		RevcLogCore("Idle: exception reading menu/fade status");
		goto popret;
	}
	{
		char buf[96];
		sprintf(buf, "Idle: menuActive=%d renderGameInMenu=%d fadeStatus=%d",
			menuActive, renderGameInMenu, fadeStatus);
		RevcLogCore(buf);
	}

	if((!menuActive || renderGameInMenu) && fadeStatus != FADE_2)
	{
		RevcLogCore("Idle: render branch start");
		// This is from SA, but it's nice for windowed mode
#if defined(GTA_PC) && !defined(RW_GL3)
		RwV2d pos;
		pos.x = SCREEN_WIDTH / 2.0f;
		pos.y = SCREEN_HEIGHT / 2.0f;
		RsMouseSetPos(&pos);
		RevcLogCore("Idle: after RsMouseSetPos");
#endif

		tbStartTimer(0, "CnstrRenderList");
#ifdef PC_WATER
		CWaterLevel::PreCalcWaterGeometry();
		RevcLogCore("Idle: after CWaterLevel::PreCalcWaterGeometry");
#endif
#ifdef NEW_RENDERER
		if(gbNewRenderer){
			CWorld::AdvanceCurrentScanCode();	// don't think this is even necessary
			CRenderer::ClearForFrame();
			RevcLogCore("Idle: after CRenderer::ClearForFrame");
		}
#endif
		CRenderer::ConstructRenderList();
		tbEndTimer("CnstrRenderList");
		RevcLogCore("Idle: after CRenderer::ConstructRenderList");

		tbStartTimer(0, "PreRender");
		CRenderer::PreRender();
		tbEndTimer("PreRender");
		RevcLogCore("Idle: after CRenderer::PreRender");

#ifdef FIX_BUGS
		RwRenderStateSet(rwRENDERSTATEZWRITEENABLE, (void *)FALSE); // TODO: temp? this fixes OpenGL render but there should be a better place for this
		// This has to be done BEFORE RwCameraBeginUpdate
		RwCameraSetFarClipPlane(Scene.camera, CTimeCycle::GetFarClip());
		RwCameraSetFogDistance(Scene.camera, CTimeCycle::GetFogStart());
#endif

		if(CWeather::LightningFlash && !CCullZones::CamNoRain()){
			RevcLogCore("Idle: lightning branch");
			if(!DoRWStuffStartOfFrame_Horizon(255, 255, 255, 255, 255, 255, 255))
				goto popret;
		}else{
			RevcLogCore("Idle: normal sky branch");
			if(!DoRWStuffStartOfFrame_Horizon(CTimeCycle::GetSkyTopRed(), CTimeCycle::GetSkyTopGreen(), CTimeCycle::GetSkyTopBlue(),
						CTimeCycle::GetSkyBottomRed(), CTimeCycle::GetSkyBottomGreen(), CTimeCycle::GetSkyBottomBlue(),
						255))
				goto popret;
		}
		RevcLogCore("Idle: after DoRWStuffStartOfFrame_Horizon");

		DefinedState();
		RevcLogCore("Idle: after DefinedState");

#ifndef FIX_BUGS
		RwCameraSetFarClipPlane(Scene.camera, CTimeCycle::GetFarClip());
		RwCameraSetFogDistance(Scene.camera, CTimeCycle::GetFogStart());
#endif

		tbStartTimer(0, "RenderScene");
		RenderScene();
		tbEndTimer("RenderScene");
		RevcLogCore("Idle: after RenderScene");

#ifdef EXTENDED_PIPELINES
		CustomPipes::EnvMapRender();
#endif

		RenderDebugShit();
		RevcLogCore("Idle: after RenderDebugShit");
		RenderEffects();
		RevcLogCore("Idle: after RenderEffects");
#ifdef REVC_DLL
		// Effects are part of the local VC camera. Drawing the SA aperture before
		// them let coronas, particles, glass and other late VC passes bleed over
		// the remote image, literally producing two camera views superimposed.
		// Draw after all 3D effects; the portal's depth test still preserves Tommy
		// and opaque foreground geometry that is physically in front of it.
		RevcPortalRenderReturnPortal();
#endif

		if((TheCamera.m_BlurType == MOTION_BLUR_NONE || TheCamera.m_BlurType == MOTION_BLUR_LIGHT_SCENE) &&
		   TheCamera.m_ScreenReductionPercentage > 0.0f)
		        TheCamera.SetMotionBlurAlpha(150);

#if defined(SCREEN_DROPLETS) && !defined(REVC_DLL)
		RevcLogCore("Idle: before ScreenDroplets");
		CPostFX::GetBackBuffer(Scene.camera);
		RevcLogCore("Idle: after CPostFX::GetBackBuffer");
		ScreenDroplets::Process();
		RevcLogCore("Idle: after ScreenDroplets::Process");
		ScreenDroplets::Render();
		RevcLogCore("Idle: after ScreenDroplets::Render");
#endif

		tbStartTimer(0, "RenderMotionBlur");
		RevcLogCore("Idle: before RenderMotionBlur");
#ifdef REVC_DLL
		RevcLogCore("Idle: RenderMotionBlur skipped (REVC_DLL)");
#else
		TheCamera.RenderMotionBlur();
		RevcLogCore("Idle: after RenderMotionBlur");
#endif
		tbEndTimer("RenderMotionBlur");

	#ifdef REVC_DLL
		if(!gRevcPortalBridge.enabled)
	#endif
		{
			tbStartTimer(0, "Render2dStuff");
			RevcLogCore("Idle: before Render2dStuff");
			Render2dStuff();
			RevcLogCore("Idle: after Render2dStuff");
			tbEndTimer("Render2dStuff");
		}
	}else{
		RevcLogCore("Idle: menu branch start");
		__try {
			CDraw::CalculateAspectRatio();
			RevcLogCore("Idle: after CDraw::CalculateAspectRatio");
#ifdef REVC_DLL
			RwRect rect;
			RwRect *prect = nil;
			if(gRevcBackBufferWidth > 0 && gRevcBackBufferHeight > 0){
				rect.x = 0;
				rect.y = 0;
				rect.w = gRevcBackBufferWidth;
				rect.h = gRevcBackBufferHeight;
				prect = &rect;
			}
#endif
#ifdef ASPECT_RATIO_SCALE
#ifdef REVC_DLL
			CameraSize(Scene.camera, prect, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#else
			CameraSize(Scene.camera, nil, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#endif
#else
#ifdef REVC_DLL
			CameraSize(Scene.camera, prect, SCREEN_VIEWWINDOW, DEFAULT_ASPECT_RATIO);
#else
			CameraSize(Scene.camera, nil, SCREEN_VIEWWINDOW, DEFAULT_ASPECT_RATIO);
#endif
#endif
			RevcLogCore("Idle: after CameraSize");
			CVisibilityPlugins::SetRenderWareCamera(Scene.camera);
			RevcLogCore("Idle: after CVisibilityPlugins::SetRenderWareCamera");
			RwCameraClear(Scene.camera, &gColourTop, CLEARMODE);
			RevcLogCore("Idle: after RwCameraClear");
			{
				char buf[128];
				sprintf(buf, "Idle: Scene.camera=%p raster=%p", Scene.camera, RwCameraGetRaster(Scene.camera));
				RevcLogCore(buf);
			}
			__try {
				if(!RsCameraBeginUpdate(Scene.camera))
					goto popret;
			} __except(EXCEPTION_EXECUTE_HANDLER) {
				RevcLogCore("Idle: RsCameraBeginUpdate SEH");
				goto popret;
			}
			RevcLogCore("Idle: after RsCameraBeginUpdate (menu)");
		} __except(EXCEPTION_EXECUTE_HANDLER) {
			RevcLogCore("Idle: menu branch SEH");
			goto popret;
		}
	}

	#ifdef REVC_DLL
	if(!gRevcPortalBridge.enabled)
	#endif
	{
		tbStartTimer(0, "RenderMenus");
		RenderMenus();
		tbEndTimer("RenderMenus");
		RevcLogCore("Idle: after RenderMenus");
	}

#ifdef PS2_MENU
	if ( TheMemoryCard.m_bWantToLoad )
		goto popret;
#endif

	// DoFade also advances StillToFadeOut and starts the gameplay fade-in.
	// Skipping it for portal preview leaves the camera permanently at
	// FADE_2, so only the last loading splash ever reaches the portal target.
	tbStartTimer(0, "DoFade");
	DoFade();
	tbEndTimer("DoFade");
	RevcLogCore("Idle: after DoFade");

	#ifdef REVC_DLL
	if(!gRevcPortalBridge.enabled)
	#endif
	{
		tbStartTimer(0, "Render2dStuff-Fade");
		Render2dStuffAfterFade();
		tbEndTimer("Render2dStuff-Fade");
		RevcLogCore("Idle: after Render2dStuffAfterFade");
	}
#ifdef REVC_DLL
	// SA overlay disabled for now
	RwRenderStateSet(rwRENDERSTATEZTESTENABLE, (void*)FALSE);
	RwRenderStateSet(rwRENDERSTATEZWRITEENABLE, (void*)FALSE);
	RwRenderStateSet(rwRENDERSTATEVERTEXALPHAENABLE, (void*)FALSE);
	RwRenderStateSet(rwRENDERSTATETEXTURERASTER, nil);
	RevcLogCore("Idle: debug quad disabled");
#endif
	// CCredits::Render(); // They added it to function above and also forgot it here
#ifdef XBOX_MESSAGE_SCREEN
	FrontEndMenuManager.DrawOverlays();
#endif

	if (gbShowTimebars)
		tbDisplay();

	DoRWStuffEndOfFrame();
	RevcLogCore("Idle: after DoRWStuffEndOfFrame");

	POP_MEMID();	// MEMID_RENDER
	RevcLogCore("Idle: end");

	if(g_SlowMode) 
		ProcessSlowMode();
	return;

popret:	POP_MEMID();	// MEMID_RENDER
}

void
FrontendIdle(void)
{
	CDraw::CalculateAspectRatio();
	CTimer::Update();
	CSprite2d::SetRecipNearClip(); // this should be on InitialiseRenderWare according to PS2 asm. seems like a bug fix
	CSprite2d::InitPerFrame();
	CFont::InitPerFrame();
	CPad::UpdatePads();
	FrontEndMenuManager.Process();

	if(RsGlobal.quit)
		return;

#ifdef REVC_DLL
	RwRect rect;
	RwRect *prect = nil;
	if(gRevcBackBufferWidth > 0 && gRevcBackBufferHeight > 0){
		rect.x = 0;
		rect.y = 0;
		rect.w = gRevcBackBufferWidth;
		rect.h = gRevcBackBufferHeight;
		prect = &rect;
	}
	CameraSize(Scene.camera, prect, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#else
	CameraSize(Scene.camera, nil, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
#endif
	CVisibilityPlugins::SetRenderWareCamera(Scene.camera);
	RwCameraClear(Scene.camera, &gColourTop, CLEARMODE);
	if(!RsCameraBeginUpdate(Scene.camera))
		return;

	DefinedState(); // seems redundant, but breaks resolution change.
	RenderMenus();
#ifdef XBOX_MESSAGE_SCREEN
	FrontEndMenuManager.DrawOverlays();
#endif
	DoFade();
	Render2dStuffAfterFade();
	CFont::DrawFonts();
	DoRWStuffEndOfFrame();
}

void
InitialiseGame(void)
{
	LoadingScreen(nil, nil, "loadsc0");
	CGame::Initialise("DATA\\GTA_VC.DAT");
}

RsEventStatus
AppEventHandler(RsEvent event, void *param)
{
	switch( event )
	{
		case rsINITIALIZE:
		{
			CGame::InitialiseOnceBeforeRW();
			return RsInitialize() ? rsEVENTPROCESSED : rsEVENTERROR;
		}

		case rsCAMERASIZE:
		{
											
			CameraSize(Scene.camera, (RwRect *)param,
				SCREEN_VIEWWINDOW, DEFAULT_ASPECT_RATIO);
			
			return rsEVENTPROCESSED;
		}

	case rsRWINITIALIZE:
	{
		RevcLogCore("AppEventHandler rsRWINITIALIZE");
		return Initialise3D(param) ? rsEVENTPROCESSED : rsEVENTERROR;
	}

	case rsRWTERMINATE:
	{
		RevcLogCore("AppEventHandler rsRWTERMINATE");
		Terminate3D();

			return rsEVENTPROCESSED;
		}

		case rsTERMINATE:
		{
			CGame::FinalShutdown();

			return rsEVENTPROCESSED;
		}

		case rsPLUGINATTACH:
		{
			return PluginAttach() ? rsEVENTPROCESSED : rsEVENTERROR;
		}

		case rsINPUTDEVICEATTACH:
		{
			AttachInputDevices();

			return rsEVENTPROCESSED;
		}

		case rsIDLE:
		{
			Idle(param);

			return rsEVENTPROCESSED;
		}

		case rsFRONTENDIDLE:
		{
			FrontendIdle();

			return rsEVENTPROCESSED;
		}

		case rsACTIVATE:
		{
			param ? DMAudio.ReacquireDigitalHandle() : DMAudio.ReleaseDigitalHandle();

			return rsEVENTPROCESSED;
		}

		default:
		{
			return rsEVENTNOTPROCESSED;
		}
	}
}

#ifndef MASTER
void
TheModelViewer(void)
{
#if (defined(GTA_PS2) || defined(GTA_XBOX))
	//TODO
#else

	// This is not original. Because;
	// 1- We want 2D things to be initalized, whereas original AnimViewer doesn't use them. my additions marked with X
	// 2- VC Mobile code run it like main function(as opposed to III and LCS), so it has it's own loop inside it, but our func. already called in a loop.

	CDraw::CalculateAspectRatio(); // X
	CAnimViewer::Update();
	SetLightsWithTimeOfDayColour(Scene.world);
	CRenderer::ConstructRenderList();
	DoRWStuffStartOfFrame(CTimeCycle::GetSkyTopRed()*0.5f, CTimeCycle::GetSkyTopGreen()*0.5f, CTimeCycle::GetSkyTopBlue()*0.5f,
		CTimeCycle::GetSkyBottomRed(), CTimeCycle::GetSkyBottomGreen(), CTimeCycle::GetSkyBottomBlue(),
		255);

	CSprite2d::SetRecipNearClip(); // X
	CSprite2d::InitPerFrame(); // X
	CFont::InitPerFrame(); // X
	DefinedState();
	CVisibilityPlugins::InitAlphaEntityList();
	CAnimViewer::Render();
	Render2dStuff(); // X
	DoRWStuffEndOfFrame();
	CTimer::Update();
#endif
}
#endif


#ifdef GTA_PS2
void TheGame(void)
{
	printf("Into TheGame!!!\n");

	PUSH_MEMID(MEMID_GAME);	// NB: not popped

	CTimer::Initialise();

	CGame::Initialise("DATA\\GTA3.DAT");

	Const char *splash = GetRandomSplashScreen(); // inlined here

	LoadingScreen("Starting Game", NULL, splash);

#ifdef GTA_PS2
	// TODO(MIAMI): not checked yet
	if (   TheMemoryCard.CheckCardInserted(CARD_ONE) == CMemoryCard::NO_ERR_SUCCESS
		&& TheMemoryCard.ChangeDirectory(CARD_ONE, TheMemoryCard.Cards[CARD_ONE].dir)
		&& TheMemoryCard.FindMostRecentFileName(CARD_ONE, TheMemoryCard.MostRecentFile) == true
		&& TheMemoryCard.CheckDataNotCorrupt(TheMemoryCard.MostRecentFile))
	{
		strcpy(TheMemoryCard.LoadFileName, TheMemoryCard.MostRecentFile);
		TheMemoryCard.b_FoundRecentSavedGameWantToLoad = true;

		if (FrontEndMenuManager.m_PrefsLanguage != TheMemoryCard.GetLanguageToLoad())
		{
			FrontEndMenuManager.m_PrefsLanguage = TheMemoryCard.GetLanguageToLoad();
			TheText.Unload();
			TheText.Load();
		}

		CGame::currLevel = (eLevelName)TheMemoryCard.GetLevelToLoad();
	}
#else
	//TODO
#endif

	while (true)
	{
		if (FOUND_GAME_TO_LOAD)
		{
			Const char *splash1 = GetLevelSplashScreen(CGame::currLevel);
			LoadSplash(splash1);
		}

		WANT_TO_LOAD = false;

		CTimer::Update();

		while (!(FrontEndMenuManager.m_bWantToRestart || FOUND_GAME_TO_LOAD))
		{
			CSprite2d::InitPerFrame();
			CFont::InitPerFrame();

			PUSH_MEMID(MEMID_GAME_PROCESS);
			CPointLights::InitPerFrame();
			CGame::Process();
			POP_MEMID();

			DMAudio.Service();

			if (CGame::bDemoMode && CTimer::GetTimeInMilliseconds() > (3*60 + 30)*1000 && !CCutsceneMgr::IsCutsceneProcessing())
			{
				WANT_TO_LOAD = false;
				FrontEndMenuManager.m_bWantToRestart = true;
				break;
			}

			if (FrontEndMenuManager.m_bWantToRestart || FOUND_GAME_TO_LOAD)
				break;

			SetLightsWithTimeOfDayColour(Scene.world);

			PUSH_MEMID(MEMID_RENDER);

			CRenderer::ConstructRenderList();

#ifdef PS2_MENU
				if ((!FrontEndMenuManager.m_bMenuActive || FrontEndMenuManager.m_bRenderGameInMenu == true) && TheCamera.GetScreenFadeStatus() != FADE_2 )
#else
#ifdef REVC_DLL
				if (!FrontEndMenuManager.m_bMenuActive && TheCamera.GetScreenFadeStatus() != FADE_2 )
#else
				if ((!FrontEndMenuManager.m_bMenuActive || !FrontEndMenuManager.m_bGameNotLoaded) && TheCamera.GetScreenFadeStatus() != FADE_2 )
#endif
#endif
				{
				CRenderer::PreRender();
				// TODO(MIAMI): something ps2all specific

#ifdef FIX_BUGS
				// This has to be done BEFORE RwCameraBeginUpdate
				RwCameraSetFarClipPlane(Scene.camera, CTimeCycle::GetFarClip());
				RwCameraSetFogDistance(Scene.camera, CTimeCycle::GetFogStart());
#endif

				if (CWeather::LightningFlash && !CCullZones::CamNoRain())
					DoRWStuffStartOfFrame_Horizon(255, 255, 255, 255, 255, 255, 255);
				else
					DoRWStuffStartOfFrame_Horizon(CTimeCycle::GetSkyTopRed(), CTimeCycle::GetSkyTopGreen(), CTimeCycle::GetSkyTopBlue(), CTimeCycle::GetSkyBottomRed(), CTimeCycle::GetSkyBottomGreen(), CTimeCycle::GetSkyBottomBlue(), 255);

				DefinedState();
#ifndef FIX_BUGS
				RwCameraSetFarClipPlane(Scene.camera, CTimeCycle::GetFarClip());
				RwCameraSetFogDistance(Scene.camera, CTimeCycle::GetFogStart());
#endif

				RenderScene();
				RenderDebugShit();
				RenderEffects();

				if ((TheCamera.m_BlurType == MOTION_BLUR_NONE || TheCamera.m_BlurType == MOTION_BLUR_LIGHT_SCENE) && TheCamera.m_ScreenReductionPercentage > 0.0f)
					TheCamera.SetMotionBlurAlpha(150);
				TheCamera.RenderMotionBlur();

				Render2dStuff();
			}
			else
			{
				CameraSize(Scene.camera, NULL, SCREEN_VIEWWINDOW, SCREEN_ASPECT_RATIO);
				CVisibilityPlugins::SetRenderWareCamera(Scene.camera);
				RwCameraClear(Scene.camera, &gColourTop, CLEARMODE);
				RsCameraBeginUpdate(Scene.camera);
			}

			RenderMenus();

			if (WANT_TO_LOAD)
			{
				POP_MEMID();	// MEMID_RENDER
				break;
			}

			DoFade();
			Render2dStuffAfterFade();
			CCredits::Render();

			DoRWStuffEndOfFrame();

			while (frameCount < 2)
				;

			frameCount = 0;

			CTimer::Update();

			POP_MEMID();	// MEMID_RENDER

			if (g_SlowMode)
				ProcessSlowMode();
		}

		CPad::ResetCheats();
		CPad::StopPadsShaking();
		DMAudio.ChangeMusicMode(MUSICMODE_DISABLE);
		CGame::ShutDownForRestart();
		CTimer::Stop();

		if (FrontEndMenuManager.m_bWantToRestart || FOUND_GAME_TO_LOAD)
		{
			if (FOUND_GAME_TO_LOAD)
			{
				FrontEndMenuManager.m_bWantToRestart = true;
				WANT_TO_LOAD = true;
			}

			CGame::InitialiseWhenRestarting();
			DMAudio.ChangeMusicMode(MUSICMODE_GAME);
			FrontEndMenuManager.m_bWantToRestart = false;

			continue;
		}

		break;
	}

	DMAudio.Terminate();
}


void SystemInit()
{
#ifdef USE_CUSTOM_ALLOCATOR
	InitMemoryMgr();
#endif
	
#ifdef GTA_PS2
	CFileMgr::InitCdSystem();
	
	char path[256];
	
	sprintf(path, "cdrom0:\\%s%s;1", "SYSTEM\\", "IOPRP241.IMG");
	
	sceSifInitRpc(0);
	
	while ( !sceSifRebootIop(path) )
		;
	while( !sceSifSyncIop() )
		;
	
	sceSifInitRpc(0);
	
	CFileMgr::InitCdSystem();
	
	sceFsReset();

	CFileMgr::InitCd();
	
	char modulepath[256];
	
	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "SIO2MAN.IRX");
	LoadModule(modulepath);
	
	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "PADMAN.IRX");
	LoadModule(modulepath);
	
	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "LIBSD.IRX");
	LoadModule(modulepath);
	
	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "SDRDRV.IRX");
	LoadModule(modulepath);
	
	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "MCMAN.IRX");
	LoadModule(modulepath);
	
	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "MCSERV.IRX");
	LoadModule(modulepath);

	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "CDSTREAM.IRX");
	LoadModule(modulepath);

	strcpy(modulepath, "cdrom0:\\");
	strcat(modulepath, "SYSTEM\\");
	strcat(modulepath, "SAMPMAN2.IRX");
	LoadModule(modulepath);
#endif
	

#ifdef GTA_PS2
	ThreadParam param;
	
	param.entry = &IdleThread;
	param.stack = idleThreadStack;
	param.stackSize = 2048;
	param.initPriority = 127;
	param.gpReg = &_gp;
	
	int thread = CreateThread(&param);
	StartThread(thread, NULL);
#else
	//
#endif
	
#ifdef GTA_PS2_STUFF
	CPad::Initialise();
#endif
	CPad::GetPad(0)->Mode = 0;
	
	CGame::frenchGame = false;
	CGame::germanGame = false;
	CGame::nastyGame = true;
	FrontEndMenuManager.m_PrefsAllowNastyGame = true;
	
#ifdef GTA_PS2
	// TODO(MIAMI): this code probably went elsewhere?
	int32 lang = sceScfGetLanguage();
	if ( lang  == SCE_ITALIAN_LANGUAGE )
		FrontEndMenuManager.m_PrefsLanguage = LANGUAGE_ITALIAN;
	else if ( lang  == SCE_SPANISH_LANGUAGE )
		FrontEndMenuManager.m_PrefsLanguage = LANGUAGE_SPANISH;
	else if ( lang  == SCE_GERMAN_LANGUAGE )
	{
		CGame::germanGame = true;
		CGame::nastyGame = false;
		FrontEndMenuManager.m_PrefsAllowNastyGame = false;
		FrontEndMenuManager.m_PrefsLanguage = LANGUAGE_GERMAN;
	}
	else if ( lang  == SCE_FRENCH_LANGUAGE )
	{
		CGame::frenchGame = true;
		CGame::nastyGame = false;
		FrontEndMenuManager.m_PrefsAllowNastyGame = false;
		FrontEndMenuManager.m_PrefsLanguage = LANGUAGE_FRENCH;
	}
	else
		FrontEndMenuManager.m_PrefsLanguage = LANGUAGE_AMERICAN;
	
	FrontEndMenuManager.InitialiseMenuContentsAfterLoadingGame();
#else
	//
#endif
	
#ifdef GTA_PS2
	TheMemoryCard.Init();
#endif
}

int VBlankCounter(int ca)
{
	frameCount++;
	ExitHandler();
	return 0;
}

// linked against by RW!
extern "C" void WaitVBlank(void)
{
	int32 startFrame = frameCount;
	while(startFrame == frameCount);
}

void GameInit(bool onlyRW)
{
	if(onlyRW)
	{
#ifdef GTA_PS2
		Initialise3D(nil);
#else
		Initialise3D(nil);	//TODO: window parameter
#endif
		gameAlreadyInitialised = true;
	}
	else
	{
		if ( !gameAlreadyInitialised )
#ifdef GTA_PS2
			Initialise3D(nil);
#else
			Initialise3D(nil);	//TODO: window parameter
#endif
		}

#ifdef GTA_PS2
		char *files[] =
		{
			"\\ANIM\\CUTS.IMG;1",
			"\\ANIM\\CUTS.DIR;1",
			"\\ANIM\\PED.IFP;1",
			"\\MODELS\\FRONTEN1.TXD;1",
			"\\MODELS\\FRONTEN2.TXD;1",
			"\\MODELS\\FONTS.TXD;1",
			"\\MODELS\\HUD.TXD;1",
			"\\MODELS\\PARTICLE.TXD;1",
			"\\MODELS\\MISC.TXD;1",
			"\\MODELS\\GENERIC.TXD;1",
			"\\MODELS\\GTA3.DIR;1",
			// TODO: japanese?
#ifdef GTA_PAL
			"\\TEXT\\ENGLISH.GXT;1",
			"\\TEXT\\FRENCH.GXT;1",
			"\\TEXT\\GERMAN.GXT;1",
			"\\TEXT\\ITALIAN.GXT;1",
			"\\TEXT\\SPANISH.GXT;1",
#else
			"\\TEXT\\AMERICAN.GXT;1",
#endif
			"\\MODELS\\COLL\\GENERIC.COL;1",
			"\\MODELS\\COLL\\VEHICLES.COL;1",
			"\\MODELS\\COLL\\PEDS.COL;1",
			"\\MODELS\\COLL\\WEAPONS.COL;1",
			"\\MODELS\\GENERIC\\AIR_VLO.DFF;1",
			"\\MODELS\\GENERIC\\WHEELS.DFF;1",
			"\\MODELS\\GENERIC\\ARROW.DFF;1",
			"\\MODELS\\GENERIC\\ZONECYLB.DFF;1",
			"\\DATA\\HANDLING.CFG;1",
			"\\DATA\\SURFACE.DAT;1",
			"\\DATA\\PEDSTATS.DAT;1",
			"\\DATA\\TIMECYC.DAT;1",
			"\\DATA\\PARTICLE.CFG;1",
			"\\DATA\\DEFAULT.DAT;1",
			"\\DATA\\DEFAULT.IDE;1",
			"\\DATA\\GTA_VC.DAT;1",
			"\\DATA\\OBJECT.DAT;1",
			"\\DATA\\MAP.ZON;1",
			"\\DATA\\NAVIG.ZON;1",
			"\\DATA\\INFO.ZON;1",
			"\\DATA\\WATERPRO.DAT;1",
			"\\DATA\\MAIN.SCM;1",
			"\\DATA\\CARCOLS.DAT;1",
			"\\DATA\\PED.DAT;1",
			"\\DATA\\FISTFITE.DAT;1",
			"\\DATA\\WEAPON.DAT;1",
			"\\DATA\\PEDGRP.DAT;1",
			"\\DATA\\PATHS\\FLIGHT.DAT;1",
			"\\DATA\\PATHS\\FLIGHT2.DAT;1",
			"\\DATA\\PATHS\\FLIGHT3.DAT;1",
			"\\DATA\\PATHS\\SPATH0.DAT;1",
			"\\DATA\\MAPS\\LITTLEHA\\LITTLEHA.IDE;1",
			"\\DATA\\MAPS\\DOWNTOWN\\DOWNTOWN.IDE;1",
			"\\DATA\\MAPS\\DOWNTOWS\\DOWNTOWS.IDE;1",
			"\\DATA\\MAPS\\DOCKS\\DOCKS.IDE;1",
			"\\DATA\\MAPS\\WASHINTN\\WASHINTN.IDE;1",
			"\\DATA\\MAPS\\WASHINTS\\WASHINTS.IDE;1",
			"\\DATA\\MAPS\\OCEANDRV\\OCEANDRV.IDE;1",
			"\\DATA\\MAPS\\OCEANDN\\OCEANDN.IDE;1",
			"\\DATA\\MAPS\\GOLF\\GOLF.IDE;1",
			"\\DATA\\MAPS\\BRIDGE\\BRIDGE.IDE;1",
			"\\DATA\\MAPS\\STARISL\\STARISL.IDE;1",
			"\\DATA\\MAPS\\NBEACHBT\\NBEACHBT.IDE;1",
			"\\DATA\\MAPS\\NBEACHW\\NBEACHW.IDE;1",
			"\\DATA\\MAPS\\NBEACH\\NBEACH.IDE;1",
			"\\DATA\\MAPS\\BANK\\BANK.IDE;1",
			"\\DATA\\MAPS\\MALL\\MALL.IDE;1",
			"\\DATA\\MAPS\\YACHT\\YACHT.IDE;1",
			"\\DATA\\MAPS\\CISLAND\\CISLAND.IDE;1",
			"\\DATA\\MAPS\\CLUB\\CLUB.IDE;1",
			"\\DATA\\MAPS\\HOTEL\\HOTEL.IDE;1",
			"\\DATA\\MAPS\\LAWYERS\\LAWYERS.IDE;1",
			"\\DATA\\MAPS\\STRIPCLB\\STRIPCLB.IDE;1",
			"\\DATA\\MAPS\\AIRPORT\\AIRPORT.IDE;1",
			"\\DATA\\MAPS\\HAITI\\HAITI.IDE;1",
			"\\DATA\\MAPS\\HAITIN\\HAITIN.IDE;1",
			"\\DATA\\MAPS\\CONCERTH\\CONCERTH.IDE;1",
			"\\DATA\\MAPS\\MANSION\\MANSION.IDE;1",
			"\\DATA\\MAPS\\ISLANDSF\\ISLANDSF.IDE;1",
			"\\DATA\\MAPS\\LITTLEHA\\LITTLEHA.IPL;1",
			"\\DATA\\MAPS\\DOWNTOWN\\DOWNTOWN.IPL;1",
			"\\DATA\\MAPS\\DOWNTOWS\\DOWNTOWS.IPL;1",
			"\\DATA\\MAPS\\DOCKS\\DOCKS.IPL;1",
			"\\DATA\\MAPS\\WASHINTN\\WASHINTN.IPL;1",
			"\\DATA\\MAPS\\WASHINTS\\WASHINTS.IPL;1",
			"\\DATA\\MAPS\\OCEANDRV\\OCEANDRV.IPL;1",
			"\\DATA\\MAPS\\OCEANDN\\OCEANDN.IPL;1",
			"\\DATA\\MAPS\\GOLF\\GOLF.IPL;1",
			"\\DATA\\MAPS\\BRIDGE\\BRIDGE.IPL;1",
			"\\DATA\\MAPS\\STARISL\\STARISL.IPL;1",
			"\\DATA\\MAPS\\NBEACHBT\\NBEACHBT.IPL;1",
			"\\DATA\\MAPS\\NBEACH\\NBEACH.IPL;1",
			"\\DATA\\MAPS\\NBEACHW\\NBEACHW.IPL;1",
			"\\DATA\\MAPS\\CISLAND\\CISLAND.IPL;1",
			"\\DATA\\MAPS\\AIRPORT\\AIRPORT.IPL;1",
			"\\DATA\\MAPS\\HAITI\\HAITI.IPL;1",
			"\\DATA\\MAPS\\HAITIN\\HAITIN.IPL;1",
			"\\DATA\\MAPS\\ISLANDSF\\ISLANDSF.IPL;1",
			"\\DATA\\MAPS\\BANK\\BANK.IPL;1",
			"\\DATA\\MAPS\\MALL\\MALL.IPL;1",
			"\\DATA\\MAPS\\YACHT\\YACHT.IPL;1",
			"\\DATA\\MAPS\\CLUB\\CLUB.IPL;1",
			"\\DATA\\MAPS\\HOTEL\\HOTEL.IPL;1",
			"\\DATA\\MAPS\\LAWYERS\\LAWYERS.IPL;1",
			"\\DATA\\MAPS\\STRIPCLB\\STRIPCLB.IPL;1",
			"\\DATA\\MAPS\\CONCERTH\\CONCERTH.IPL;1",
			"\\DATA\\MAPS\\MANSION\\MANSION.IPL;1",
			"\\DATA\\MAPS\\GENERIC.IDE;1",
			"\\DATA\\OCCLU.IPL;1",
			"\\DATA\\MAPS\\PATHS.IPL;1",
			"\\TXD\\LOADSC0.TXD;1",
			"\\TXD\\LOADSC1.TXD;1",
			"\\TXD\\LOADSC2.TXD;1",
			"\\TXD\\LOADSC3.TXD;1",
			"\\TXD\\LOADSC4.TXD;1",
			"\\TXD\\LOADSC5.TXD;1",
			"\\TXD\\LOADSC6.TXD;1",
			"\\TXD\\LOADSC7.TXD;1",
			"\\TXD\\LOADSC8.TXD;1",
			"\\TXD\\LOADSC9.TXD;1",
			"\\TXD\\LOADSC10.TXD;1",
			"\\TXD\\LOADSC11.TXD;1",
			"\\TXD\\LOADSC12.TXD;1",
			"\\TXD\\LOADSC13.TXD;1",
			"\\TXD\\SPLASH1.TXD;1"
		};
		
		for ( int32 i = 0; i < ARRAY_SIZE(files); i++ )
			SkyRegisterFileOnCd([i]);
#endif
		
#ifdef GTA_PS2
		AddIntcHandler(INTC_VBLANK_S, VBlankCounter, 0);
#endif
		
#ifdef GTA_PS2
		sceCdCLOCK rtc;
		sceCdReadClock(&rtc);
		uint32 seed = rtc.minute + rtc.day;
		uint32 seed2 = (seed << 4)-seed;
		uint32 seed3 = (seed2 << 4)-seed2;
		srand ((seed3<<4)+rtc.second);
#else
		//TODO: mysrand();
#endif
		
		// gameAlreadyInitialised = true;	// why is this gone?
	}
}

int32 SkipAllMPEGs;
int32 gMemoryStickLoadOK;

void PlayIntroMPEGs()
{
#ifdef GTA_PS2
	if (gameAlreadyInitialised)
		RpSkySuspend();

	InitMPEGPlayer();

	float skipTime;		// wrong type, should be int
#ifdef GTA_PAL
	if(gMemoryStickLoadOK)
		skipTime = 2500000;
	else
		skipTime = 5300000;

	if(!SkipAllMPEGs)
		PlayMPEG("cdrom0:\\MOVIES\\VCPAL.PSS;1", false, unk);

	if(!SkipAllMPEGs){
		SkipAllMPEGs = true;
		PlayMPEG("cdrom0:\\MOVIES\\VICEPAL.PSS;1", true, 0);
	}
#else
	if(gMemoryStickLoadOK)
		skipTime = 2750000;
	else
		skipTime = 5500000;

	if(!SkipAllMPEGs)
		PlayMPEG("cdrom0:\\MOVIES\\VCNTSC.PSS;1", false, unk);

	if(!SkipAllMPEGs){
		SkipAllMPEGs = true;
		PlayMPEG("cdrom0:\\MOVIES\\VICE.PSS;1", true, 0);
	}
#endif

	ShutdownMPEGPlayer();

	if ( gameAlreadyInitialised )
		RpSkyResume();
#else
	//TODO
#endif
}

int
main(int argc, char *argv[])
{
#ifdef __MWERKS__
	mwInit(); // metrowerks initialisation
#endif

	SystemInit();

	if(RsEventHandler(rsINITIALIZE, nil) == rsEVENTERROR)
		return 0;

#ifdef GTA_PS2
	int32 r = TheMemoryCard.CheckCardStateAtGameStartUp(CARD_ONE);
		
	if ( r == CMemoryCard::ERR_DIRNOENTRY  || r == CMemoryCard::ERR_NOFORMAT )
	{
		GameInit(true);
		
		TheText.Unload();
		TheText.Load();
		
		CFont::Initialise();
		
		FrontEndMenuManager.DrawMemoryCardStartUpMenus();
	}else if(r == CMemoryCard::ERR_OPENNOENTRY)
		gMemoryStickLoadOK = false;
	else if(r == CMemoryCard::ERR_NONE)
		gMemoryStickLoadOK = true;
#endif

	PlayIntroMPEGs();

	GameInit(false);

	frameCount = 0;
	while(frameCount < 100);

	CGame::InitialiseOnceAfterRW();

	TheGame();

#if 0	// maybe ifndef FINAL or MASTER?
	CGame::ShutDown();
	
	RwEngineStop();
	RwEngineClose();
	RwEngineTerm();
	
#ifdef __MWERKS__
	mwExit(); // metrowerks shutdown
#endif
#endif
	return 0;
}
#endif
