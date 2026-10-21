#define NOMINMAX
#include <windows.h>
#include <shlobj.h>
#include <windowsx.h>
#include <gdiplus.h>
#include <wininet.h>
#include <thread>
#include <atomic>
#include <map>
#include <mutex>
#include "config_merge.hpp"
#include "update.hpp"
#include "version.h"
#include <cmath>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>
#include <algorithm>
#include <memory>
#include <array>
#include <regex>
#pragma comment(lib,"gdiplus.lib")
#pragma comment(lib,"shlwapi.lib")
#pragma comment(lib,"wininet.lib")
using namespace Gdiplus;
namespace fs = std::filesystem;

struct Instance { std::wstring id, name, version, icon; };
struct Click { Rect r; int kind, index; };

static const std::wstring APP_VERSION=PRISM_VERSION_W;
static const std::wstring APP_TITLE=L"PrismSync v"+APP_VERSION;
static const std::wstring GITHUB_REPO_URL=L"https://github.com/SILENCE-SIMSOOL/PrismSync";
static const std::wstring GITHUB_RELEASES_URL=L"https://github.com/SILENCE-SIMSOOL/PrismSync/releases";

static HWND windowHandle;
static fs::path settingsDir, prismDir;
static std::vector<Instance> instances;
static std::vector<Click> clicks;
static std::array<bool,7> enabled{true,true,false,true,true,true,false};
static std::wstring mainId, language=L"en", selectedId, status;
static bool optionsPage=false, choosingMain=false, langDropdownOpen=false;
static int scrollX=0, contentWidth=0;
static ULONG_PTR gdiplusToken;

static float dpiScale=1.f;
static HWND searchWindow;
static HFONT searchFont;
static WNDPROC originalSearchProc;
static HBRUSH searchBrush;
static std::wstring searchText;
static int keyboardFocus=-1;
static std::unique_ptr<Bitmap> paintBuffer;
static std::thread worker;
static std::atomic<bool> cancelWork{false};
static bool busy=false, closing=false;
static std::mutex workMutex;
static constexpr UINT WORK_PROGRESS=WM_APP+1, WORK_DONE=WM_APP+2;
enum class ReportTone { Info, Success, Warning, Error };
enum class WorkKind { Preview, Apply, CheckUpdate, Download, UpdateMods };
struct WorkEvent {
	WorkKind kind;
	syncer::Plan plan;
	syncer::Result result;
	updater::Release release;
	fs::path path;
	std::string error;
	std::wstring modTitle, modSummary, modDetails;
	ReportTone modTone = ReportTone::Info;
};
static std::unique_ptr<WorkEvent> completedWork;
static std::wstring workProgress;
static ULONGLONG workStarted=0, lastProgress=0;

static std::unique_ptr<PrivateFontCollection> privateFonts, medColl, semiColl, boldColl, iconFonts;
static std::unique_ptr<FontFamily> regularFamily, mediumFamily, semiboldFamily, boldFamily, iconFamily;
static fs::path assetDir;
static std::map<std::wstring,std::unique_ptr<Bitmap>> iconCache;
static std::map<std::wstring,fs::path> iconPaths;

static std::array<float,7> togglePosition{};
static float scrollPosition=0, tabPosition=0, choosingMainAnim=0, langDropdownAnim=0;
static float navHoverLeft=0, navHoverRight=0, btnApplyHover=0, btnChangeHover=0, btnUpdateHover=0;
static std::array<float,32> cardHover{};
static int hoveredKind=-1, hoveredIndex=-1;
static bool draggingScroll=false, animations=true;
static int dragOffset=0;
static ULONGLONG lastFrame=0;
static int optionsScroll=0, optionHitOffset=0, optionHitBottom=0;
static bool draggingOptions=false;
static int optionDragOffset=0;
static Rect optionTrack, optionThumb;
static std::wstring contextId,lastClickedInstance;
static Rect contextRect;


enum class FontWeight { Regular, Medium, SemiBold, Bold };

static constexpr int listTop=286, listHeight=134, trackY=422;
static constexpr int cardWidth=108, cardHeight=130, cardGap=12;

static void redraw(HWND hwnd) {
	SetTimer(hwnd,1,10,nullptr);
	InvalidateRect(hwnd,nullptr,FALSE);
}

static std::wstring getEnv(const wchar_t* key) {
	DWORD n=GetEnvironmentVariableW(key,nullptr,0);
	if (!n) return L"";
	std::wstring s(n,L'\0');
	GetEnvironmentVariableW(key,s.data(),n);
	s.resize(n-1);
	return s;
}

static std::wstring trim(std::wstring s) {
	auto a=s.find_first_not_of(L" \t\r\n\"");
	if (a==std::wstring::npos) return L"";
	auto b=s.find_last_not_of(L" \t\r\n\"");
	return s.substr(a,b-a+1);
}

static std::wstring iniRead(const fs::path& p,const wchar_t* sec,const wchar_t* key,const wchar_t* def=L"") {
	wchar_t buf[32768];
	GetPrivateProfileStringW(sec,key,def,buf,32768,p.c_str());
	return buf;
}

static std::wstring utf8ToWide(const std::string& bytes) {
	if(bytes.empty()) return {};
	int n=MultiByteToWideChar(CP_UTF8,0,bytes.data(),(int)bytes.size(),nullptr,0);
	if(n<=0) return {};
	std::wstring result(n,L'\0');
	MultiByteToWideChar(CP_UTF8,0,bytes.data(),(int)bytes.size(),result.data(),n);
	return result;
}

static std::string wideToUtf8(const std::wstring& wide) {
	if(wide.empty()) return {};
	int n=WideCharToMultiByte(CP_UTF8,0,wide.data(),(int)wide.size(),nullptr,0,nullptr,nullptr);
	if(n<=0) return {};
	std::string result(n,'\0');
	WideCharToMultiByte(CP_UTF8,0,wide.data(),(int)wide.size(),result.data(),n,nullptr,nullptr);
	return result;
}

static std::wstring cfgRead(const fs::path& path,const std::wstring& key,const std::wstring& fallback=L"") {
	std::ifstream stream(path,std::ios::binary);
	std::string line;
	while(std::getline(stream,line)) {
		auto pos=line.find('=');
		if(pos==std::string::npos) continue;
		if(line.empty() || line.front()=='#' || line.front()==';' || line.front()=='[') continue;
		auto name=trim(utf8ToWide(line.substr(0,pos)));
		if(name==key) {
			auto value=utf8ToWide(line.substr(pos+1));
			auto first=value.find_first_not_of(L" \t\r\n"), last=value.find_last_not_of(L" \t\r\n");
			if(first==std::wstring::npos) return L"";
			value=value.substr(first,last-first+1);
			if(value.size()>=2 && value.front()==L'"' && value.back()==L'"') value=value.substr(1,value.size()-2);
			return value;
		}
	}
	return fallback;
}

static void iniWrite(const wchar_t* key,const std::wstring& val) {
	WritePrivateProfileStringW(L"PrismSync",key,val.c_str(),(settingsDir/L"settings.ini").c_str());
}

static std::wstring tr(const wchar_t* en,const wchar_t* kr,const wchar_t* zh=L"",const wchar_t* ja=L"") {
	if(language==L"ko") return kr;
	if(language==L"zh" && *zh) return zh;
	if(language==L"ja" && *ja) return ja;
	return en;
}

static void persist() {
	iniWrite(L"prism_path",prismDir.wstring());
	iniWrite(L"main_id",mainId);
	iniWrite(L"language",language);
	for(int i=0;i<7;i++) iniWrite((L"copy_"+std::to_wstring(i)).c_str(),enabled[i]?L"1":L"0");
}

static void load() {
	settingsDir=fs::path(getEnv(L"APPDATA"))/L"PrismSync";
	std::error_code ec;
	fs::create_directories(settingsDir,ec);
	auto p=settingsDir/L"settings.ini";
	prismDir=iniRead(p,L"PrismSync",L"prism_path",(fs::path(getEnv(L"APPDATA"))/L"PrismLauncher").c_str());
	mainId=iniRead(p,L"PrismSync",L"main_id");
	WORD lang=PRIMARYLANGID(GetUserDefaultUILanguage());
	std::wstring systemLang=lang==LANG_KOREAN?L"ko":lang==LANG_CHINESE?L"zh":lang==LANG_JAPANESE?L"ja":L"en";
	language=iniRead(p,L"PrismSync",L"language",systemLang.c_str());
	if (language!=L"ko" && language!=L"en" && language!=L"zh" && language!=L"ja") language=L"en";
	for(int i=0;i<7;i++) enabled[i]=iniRead(p,L"PrismSync",(L"copy_"+std::to_wstring(i)).c_str(),enabled[i]?L"1":L"0")==L"1";
}

static bool safeId(const std::wstring& id) {
	return !id.empty() && id!=L"." && id!=L".." && id.find_first_of(L"/\\:")==std::wstring::npos;
}

static fs::path instanceBase() {
	fs::path configured=cfgRead(prismDir/L"prismlauncher.cfg",L"InstanceDir");
	if(configured.empty()) configured=cfgRead(prismDir/L"prismlauncher.cfg",L"InstancesDir",L"instances");
	return configured.is_absolute()?configured:prismDir/configured;
}

static bool visibleInstance(const Instance& instance) {
	if(instance.id==mainId) return false;
	if(searchText.empty()) return true;
	return FindNLSStringEx(LOCALE_NAME_USER_DEFAULT,FIND_FROMSTART|NORM_IGNORECASE,
		instance.name.c_str(),(int)instance.name.size(),searchText.c_str(),(int)searchText.size(),nullptr,nullptr,nullptr,0)>=0;
}

static void refresh() {
	instances.clear();
	iconCache.clear();
	iconPaths.clear();
	std::error_code ec;
	auto base=instanceBase();
	if(fs::exists(base,ec)) {
		for(auto& entry:fs::directory_iterator(base,fs::directory_options::skip_permission_denied,ec)) {
			if(!entry.is_directory(ec)) continue;
			Instance in;
			in.id=entry.path().filename().wstring();
			if(!safeId(in.id)) continue;
			auto cfg=entry.path()/L"instance.cfg";
			if(!fs::exists(cfg,ec)) continue;
			in.name=cfgRead(cfg,L"name",in.id);
			in.icon=cfgRead(cfg,L"iconKey");
			if(in.icon.empty()) in.icon=cfgRead(cfg,L"IconKey");
			in.version=cfgRead(cfg,L"IntendedVersion");
			if(in.version.empty()) {
				try {
					auto pack=syncer::Json::parse(syncer::read(entry.path()/L"mmc-pack.json"));
					for(const auto& component:pack.at("components")) {
						if(component.value("uid",std::string())=="net.minecraft") {
							in.version=utf8ToWide(component.value("version",std::string()));
							break;
						}
					}
				} catch(const std::exception&) { in.version=L"Minecraft (metadata unavailable)"; }
			}
			if(in.version.empty()) in.version=L"Minecraft";
			instances.push_back(std::move(in));
		}
	}
	std::sort(instances.begin(),instances.end(),[](const Instance& a,const Instance& b){return a.name<b.name;});
	if(!instances.empty() && std::none_of(instances.begin(),instances.end(),[](const Instance& i){return i.id==mainId;})) mainId=instances.front().id;
	if(instances.empty()) mainId.clear();
	selectedId.clear();
	scrollX=0;
	choosingMain=false;
	persist();
}

static const Instance* lookup(const std::wstring& id) {
	for(const auto& i:instances) if(i.id==id) return &i;
	return nullptr;
}

static fs::path imageFor(const Instance& in,bool exactPng=false) {
	std::wstring key=safeId(in.icon)?in.icon:L"grass";
	if(key==L"default" || key.empty()) key=L"grass";
	std::error_code ec;

	auto instDir=instanceBase()/in.id;
	for(auto ext:{L".png",L".jpg",L".jpeg",L".ico",L".bmp"}) {
		if(exactPng && std::wstring_view(ext)!=L".png") continue;
		auto path=instDir/(key+ext);
		if(fs::is_regular_file(path,ec)) return path;
	}
	if(!exactPng && !key.ends_with(L"_legacy") && fs::is_regular_file(instDir/L"icon.png",ec)) return instDir/L"icon.png";

	std::wstring iconsDirSetting=cfgRead(prismDir/L"prismlauncher.cfg",L"IconsDir",L"icons");
	fs::path custom=iconsDirSetting;
	if(custom.is_relative()) custom=prismDir/custom;
	for(auto ext:{L".png",L".jpg",L".jpeg",L".ico",L".bmp"}) {
		if(exactPng && std::wstring_view(ext)!=L".png") continue;
		auto path=custom/(key+ext);
		if(fs::is_regular_file(path,ec)) return path;
	}
	if(fs::is_directory(custom,ec)) {
		for(auto& folder:fs::directory_iterator(custom,fs::directory_options::skip_permission_denied,ec)) {
			if(!folder.is_directory(ec)) continue;
			for(auto ext:{L".png",L".jpg",L".jpeg",L".ico",L".bmp"}) {
				if(exactPng && std::wstring_view(ext)!=L".png") continue;
				auto path=folder.path()/(key+ext);
				if(fs::is_regular_file(path,ec)) return path;
			}
		}
	}

	std::wstring iconTheme=cfgRead(prismDir/L"prismlauncher.cfg",L"IconTheme",L"");
	if(!iconTheme.empty()) {
		fs::path themeDir=prismDir/L"iconthemes"/iconTheme;
		for(auto ext:{L".png",L".jpg",L".jpeg",L".ico",L".bmp"}) {
			if(exactPng && std::wstring_view(ext)!=L".png") continue;
			auto path=themeDir/(key+ext);
			if(fs::is_regular_file(path,ec)) return path;
		}
	}

	auto builtin=assetDir/L"prism-icons"/(key+L".png");
	if(fs::is_regular_file(builtin,ec)) return builtin;
	if(exactPng) return {};
	if(key.ends_with(L"_legacy")) {
		Instance current=in;
		current.icon=key.substr(0,key.size()-7);
		auto currentPng=imageFor(current,true);
		return currentPng.empty()?assetDir/L"prism-icons"/L"grass.png":currentPng;
	}
	auto legacy=assetDir/L"prism-icons"/(key+L"_legacy.png");
	if(key!=L"grass" && fs::is_regular_file(legacy,ec)) return legacy;

	return assetDir/L"prism-icons"/L"grass.png";
}

static bool validFontFile(const fs::path& path) {
	std::error_code ec;
	if(!fs::is_regular_file(path,ec) || fs::file_size(path,ec)==0 || ec) return false;
	PrivateFontCollection fonts;
	return fonts.AddFontFile(path.c_str())==Ok && fonts.GetFamilyCount()>0;
}

static bool ensureFontFile(const fs::path& target,const std::wstring& url) {
	if(validFontFile(target)) return true;
	try {
		syncer::validatePath(target);
		fs::create_directories(target.parent_path());
		syncer::TempFile partial{syncer::temporary(target)};
		std::ofstream output(partial.path,std::ios::binary);
		std::atomic<bool> cancel{false};
		updater::fetch(url,output,16*1024*1024,cancel);
		output.close();
		if(!output || !validFontFile(partial.path)) return false;
		syncer::flush(partial.path);
		syncer::replace(partial.path,target,fs::exists(target));
		return true;
	} catch(const std::exception&) { return false; }
}

static std::unique_ptr<FontFamily> loadFamilyFrom(std::unique_ptr<PrivateFontCollection>& coll, const fs::path& path) {
	std::error_code ec;
	if(!fs::exists(path, ec) || fs::file_size(path, ec) == 0) return nullptr;
	coll = std::make_unique<PrivateFontCollection>();
	if(coll->AddFontFile(path.c_str()) != Ok) return nullptr;
	int count = coll->GetFamilyCount();
	if(count <= 0) return nullptr;
	std::vector<FontFamily> fams(count);
	coll->GetFamilies(count, fams.data(), &count);
	if(count > 0) return std::unique_ptr<FontFamily>(fams[0].Clone());
	return nullptr;
}

static void fontSetup() {
	wchar_t exe[32768];
	GetModuleFileNameW(nullptr,exe,32768);
	assetDir=fs::path(exe).parent_path()/L"assets";
	if(!fs::exists(assetDir)) assetDir=fs::path(exe).parent_path().parent_path()/L"assets";

	fs::path fontBase=fs::path(getEnv(L"APPDATA"))/L"Lucent"/L"resources"/L"fonts";
	const std::wstring fontUrl=L"https://raw.githubusercontent.com/SILENCE-SIMSOOL/FontManager/main/pretendard/";
	for(auto name:{L"pretendard.ttf",L"pretendard_medium.ttf",L"pretendard_semibold.ttf",L"pretendard_bold.ttf"})
		ensureFontFile(fontBase/name,fontUrl+name);
	auto faFont=fontBase/L"fa-solid-900.ttf";
	ensureFontFile(faFont,L"https://raw.githubusercontent.com/FortAwesome/Font-Awesome/6.7.2/webfonts/fa-solid-900.ttf");

	regularFamily=loadFamilyFrom(privateFonts,fontBase/L"pretendard.ttf");

	mediumFamily=loadFamilyFrom(medColl,fontBase/L"pretendard_medium.ttf");
	semiboldFamily=loadFamilyFrom(semiColl,fontBase/L"pretendard_semibold.ttf");
	boldFamily=loadFamilyFrom(boldColl,fontBase/L"pretendard_bold.ttf");

	if(!privateFonts) privateFonts=std::make_unique<PrivateFontCollection>();

	iconFonts=std::make_unique<PrivateFontCollection>();
	if(validFontFile(faFont)) iconFonts->AddFontFile(faFont.c_str());

	int iconCount=iconFonts->GetFamilyCount();
	if(iconCount>0) {
		std::vector<FontFamily> families(iconCount);
		iconFonts->GetFamilies(iconCount,families.data(),&iconCount);
		if(iconCount>0) {
			iconFamily.reset(families[0].Clone());
		}
	}
}

static Color rgb(int r,int g,int b,int a=255) { return Color(a,r,g,b); }

static void roundedPath(GraphicsPath& path,float x,float y,float w,float h,float radius) {
	if(radius<=0.f) {
		path.AddRectangle(RectF(x,y,w,h));
		return;
	}
	float d=radius*2.f;
	if(d>w) d=w;
	if(d>h) d=h;
	path.AddArc(x,y,d,d,180.f,90.f);
	path.AddArc(x+w-d,y,d,d,270.f,90.f);
	path.AddArc(x+w-d,y+h-d,d,d,0.f,90.f);
	path.AddArc(x,y+h-d,d,d,90.f,90.f);
	path.CloseFigure();
}

static void rect(Graphics& g,float x,float y,float w,float h,Color color,int radius=0) {
	SolidBrush brush(color);
	if(radius<=0) {
		g.FillRectangle(&brush,x,y,w,h);
		return;
	}
	GraphicsPath path;
	roundedPath(path,x,y,w,h,(float)radius);
	g.FillPath(&brush,&path);
}

static void line(Graphics& g,float x,float y,float w,Color color) {
	Pen pen(color,1.f);
	g.DrawLine(&pen,x,y,x+w,y);
}

static void vline(Graphics& g,float x,float y,float h,Color color) {
	Pen pen(color,1.f);
	g.DrawLine(&pen,x,y,x,y+h);
}

static void drawChevron(Graphics& g,float cx,float cy,bool right,Color color) {
	Pen pen(color,2.0f);
	pen.SetStartCap(LineCapRound);
	pen.SetEndCap(LineCapRound);
	pen.SetLineJoin(LineJoinRound);
	float dir=right?1.f:-1.f;
	PointF pts[3]={
		{cx-2.5f*dir,cy-4.5f},
		{cx+2.0f*dir,cy},
		{cx-2.5f*dir,cy+4.5f}
	};
	g.DrawLines(&pen,pts,3);
}

static void label(Graphics& g,const std::wstring& s,float x,float y,float w,float h,int size=14,Color c=Color(255,31,41,55),FontWeight weight=FontWeight::Regular,int align=0) {
	FontFamily* family=nullptr;
	INT style=FontStyleRegular;
	if(language!=L"zh" && language!=L"ja") {
		switch(weight) {
		case FontWeight::Bold:
			if(boldFamily) family=boldFamily.get();
			else if(semiboldFamily) family=semiboldFamily.get();
			else { family=regularFamily.get(); style=FontStyleBold; }
			break;
		case FontWeight::SemiBold:
			if(semiboldFamily) family=semiboldFamily.get();
			else if(boldFamily) family=boldFamily.get();
			else { family=regularFamily.get(); style=FontStyleBold; }
			break;
		case FontWeight::Medium:
			if(mediumFamily) family=mediumFamily.get();
			else family=regularFamily.get();
			break;
		case FontWeight::Regular:
		default:
			family=regularFamily.get();
			break;
		}
	}
	const wchar_t* fallbackName=language==L"zh"?L"Microsoft YaHei UI":language==L"ja"?L"Yu Gothic UI":language==L"ko"?L"Malgun Gothic":L"Segoe UI";
	FontFamily fallback(fallbackName);
	if(!family) {
		family=&fallback;
		if(weight==FontWeight::Bold || weight==FontWeight::SemiBold) style=FontStyleBold;
	}
	Font font(family,(REAL)size,style,UnitPixel);
	SolidBrush brush(c);
	StringFormat format(StringFormat::GenericTypographic());
	format.SetFormatFlags(StringFormatFlagsNoWrap|StringFormatFlagsMeasureTrailingSpaces);
	format.SetTrimming(StringTrimmingEllipsisCharacter);
	if(align==1) format.SetAlignment(StringAlignmentCenter);
	else if(align==2) format.SetAlignment(StringAlignmentFar);
	format.SetLineAlignment(StringAlignmentCenter);
	g.DrawString(s.c_str(),-1,&font,RectF(x,y,w,h),&format,&brush);
}

static void label(Graphics& g,const std::wstring& s,float x,float y,float w,float h,int size,Color c,bool bold,int align=0) {
	label(g,s,x,y,w,h,size,c,bold?FontWeight::Bold:FontWeight::Regular,align);
}

static float labelWidth(Graphics& g,const std::wstring& text,int size,FontWeight weight) {
	FontFamily* family=nullptr;
	if(language!=L"zh" && language!=L"ja") {
		family=weight==FontWeight::SemiBold?(semiboldFamily?semiboldFamily.get():boldFamily.get()):mediumFamily.get();
		if(!family) family=regularFamily.get();
	}
	FontFamily fallback(language==L"zh"?L"Microsoft YaHei UI":language==L"ja"?L"Yu Gothic UI":language==L"ko"?L"Malgun Gothic":L"Segoe UI");
	Font font(family?family:&fallback,(REAL)size,!family && weight==FontWeight::SemiBold?FontStyleBold:FontStyleRegular,UnitPixel);
	StringFormat format(StringFormat::GenericTypographic());
	format.SetFormatFlags(StringFormatFlagsNoWrap|StringFormatFlagsMeasureTrailingSpaces);
	RectF bounds;
	g.MeasureString(text.c_str(),-1,&font,PointF(0,0),&format,&bounds);
	return std::ceil(bounds.Width)+2.f;
}

static float glyphWidth(Graphics& g,wchar_t code,int size) {
	if(!iconFamily) return (float)size;
	Font font(iconFamily.get(),(REAL)size,FontStyleRegular,UnitPixel);
	StringFormat format(StringFormat::GenericTypographic());
	RectF bounds;
	g.MeasureString(&code,1,&font,PointF(0,0),&format,&bounds);
	return std::ceil(bounds.Width);
}

static void glyph(Graphics& g,wchar_t code,int x,int y,int size,Color color) {
	if(!iconFamily) return;
	Font font(iconFamily.get(),(REAL)size,FontStyleRegular,UnitPixel);
	SolidBrush brush(color);
	StringFormat format(StringFormat::GenericTypographic());
	format.SetFormatFlags(StringFormatFlagsNoWrap|StringFormatFlagsMeasureTrailingSpaces);
	format.SetAlignment(StringAlignmentCenter);
	format.SetLineAlignment(StringAlignmentCenter);
	wchar_t text[]={code,0};
	g.DrawString(text,1,&font,RectF((REAL)x,(REAL)y,(REAL)size,(REAL)size),&format,&brush);
}

static void panel(Graphics& g,float x,float y,float w,float h,Color fill,Color edge,float radius=8.f,float strokeWidth=1.f) {
	GraphicsPath path;
	roundedPath(path,x,y,w,h,radius);
	SolidBrush brush(fill);
	g.FillPath(&brush,&path);
	if(edge.GetA()>0 && strokeWidth>0.f) {
		Pen pen(edge,strokeWidth);
		pen.SetAlignment(PenAlignmentInset);
		g.DrawPath(&pen,&path);
	}
}

static void hit(int x,int y,int w,int h,int kind,int index=0) {
		y+=optionHitOffset;
	if(optionHitBottom) {
		int bottom=std::min(y+h,optionHitBottom);
		y=std::max(y,60); h=bottom-y;
	}
	if(w>0 && h>0) clicks.push_back({Rect(x,y,w,h),kind,index});
}

static void button(Graphics& g,int x,int y,int w,int h,const std::wstring& text,int kind,int index,bool active=false,wchar_t icon=0,bool available=true,int radius=8) {
	bool hover=available && hoveredKind==kind && hoveredIndex==index;
	Color bg=active?(hover?rgb(0,98,233):rgb(20,117,255)):(hover?rgb(241,245,249):rgb(255,255,255));
	Color border=active?bg:rgb(203,213,225);
	if(!available) {
		bg=rgb(226,232,240);
		border=bg;
	}
	panel(g,(float)x,(float)y,(float)w,(float)h,bg,border,(float)radius);
	Color fg=active&&available?rgb(255,255,255):available?rgb(30,41,59):rgb(148,163,184);
	if(icon) {
		glyph(g,icon,x+14,y+(h-18)/2,18,fg);
		label(g,text,(float)x+38,(float)y,(float)w-46,(float)h,14,fg,active);
	} else {
		label(g,text,(float)x,(float)y,(float)w,(float)h,14,fg,active,1);
	}
	if(available) hit(x,y,w,h,kind,index);
}

static Bitmap* cachedBitmap(const fs::path& path) {
	auto key=path.wstring();
	auto found=iconCache.find(key);
	if(found==iconCache.end()) found=iconCache.emplace(key,std::make_unique<Bitmap>(path.c_str())).first;
	auto bitmap=found->second.get();
	return bitmap->GetLastStatus()==Ok && bitmap->GetWidth() && bitmap->GetHeight()?bitmap:nullptr;
}

static Bitmap* instanceBitmap(const Instance& in) {
	auto found=iconPaths.find(in.id);
	if(found==iconPaths.end()) found=iconPaths.emplace(in.id,imageFor(in)).first;
	auto bitmap=cachedBitmap(found->second);
	if(!bitmap && found->second.stem().wstring().ends_with(L"_legacy")) {
		Instance current=in;
		auto stem=found->second.stem().wstring();
		current.icon=stem.substr(0,stem.size()-7);
		auto currentPng=imageFor(current,true);
		if(!currentPng.empty()) {
			bitmap=cachedBitmap(currentPng);
			if(bitmap) found->second=currentPng;
		}
	}
	if(!bitmap) {
		found->second=assetDir/L"prism-icons"/L"grass.png";
		bitmap=cachedBitmap(found->second);
	}
	return bitmap;
}

static void instanceIcon(Graphics& g,const Instance& in,int x,int y,int size,int cornerRadius=8) {
	auto bitmap=instanceBitmap(in);
	GraphicsPath clip;
	roundedPath(clip,(float)x,(float)y,(float)size,(float)size,(float)cornerRadius);

	if(bitmap) {
		auto& bmp=*bitmap;
		float scale=std::max((float)size/bmp.GetWidth(),(float)size/bmp.GetHeight());
		float w=bmp.GetWidth()*scale, h=bmp.GetHeight()*scale;
		float ox=x+(size-w)/2.f, oy=y+(size-h)/2.f;
		GraphicsState state=g.Save();
		g.SetClip(&clip,CombineModeIntersect);
		g.SetInterpolationMode(InterpolationModeHighQualityBicubic);
		g.DrawImage(&bmp,ox,oy,w,h);
		g.Restore(state);
	} else {
		SolidBrush bgBrush(rgb(226,232,240));
		g.FillPath(&bgBrush,&clip);
		glyph(g,0xF11B,x+size/4,y+size/4,size/2,rgb(82,124,178));
	}
	Pen borderPen(rgb(226,232,240),1.f);
	borderPen.SetAlignment(PenAlignmentInset);
	g.DrawPath(&borderPen,&clip);
}

static int maxScrollFor(int width) {
	return std::max(0,contentWidth-(width-48));
}

static void scrollGeometry(int width,int& thumbWidth,int& thumbX) {
	int area=width-48, maxScroll=maxScrollFor(width);
	thumbWidth=std::max(38,area*area/std::max(area,contentWidth));
	thumbX=24+(maxScroll?(int)std::lround(scrollPosition*(area-thumbWidth)/maxScroll):0);
}

static Rect scrollbar(Graphics& g,const Rect& track,int offset,int maximum,bool active=false) {
	panel(g,(float)track.X,(float)track.Y,(float)track.Width,(float)track.Height,rgb(241,245,249),Color(0,0,0,0),(float)track.Width/2);
	int thumbHeight=std::max(28,track.Height*track.Height/std::max(1,track.Height+maximum));
	int y=track.Y+(maximum?offset*(track.Height-thumbHeight)/maximum:0);
	Rect thumb(track.X,y,track.Width,thumbHeight);
	panel(g,(float)thumb.X,(float)thumb.Y,(float)thumb.Width,(float)thumb.Height,active?rgb(20,117,255):rgb(148,163,184),Color(0,0,0,0),(float)thumb.Width/2);
	return thumb;
}

static void drawContext(Graphics& g,int width,int height) {
	if(contextId.empty()) return;
	struct ContextItem {
		int kind;
		wchar_t glyphChar;
		std::wstring text;
		bool separatorAfter;
	};
	std::vector<ContextItem> items = {
		{ 15, 0xF07B, tr(L"Open folder", L"폴더 열기", L"打开文件夹", L"フォルダーを開く"), false },
		{ 16, 0xF521, tr(L"Set as main instance", L"메인 인스턴스로 지정", L"设为主实例", L"メインに設定"), true },
		{ 17, 0xF0C7, tr(L"Save as custom MC options", L"내 커스텀 MC 옵션으로 저장", L"保存为自定义 MC 选项", L"カスタムMCオプションとして保存"), false },
		{ 18, 0xF0C5, tr(L"Overwrite with custom MC options", L"내 커스텀 MC 옵션으로 덮어씌우기", L"应用自定义 MC 选项覆盖", L"カスタムMCオプションで上書き"), false },
		{ 19, 0xF1B2, tr(L"Save as custom Fabric settings", L"내 커스텀 패브릭 설정으로 저장", L"保存为自定义 Fabric 设置", L"カスタムFabric設定として保存"), false },
		{ 20, 0xF0C5, tr(L"Overwrite with custom Fabric settings", L"내 커스텀 패브릭 설정으로 덮어씌우기", L"应用自定义 Fabric 设置覆盖", L"カスタムFabric設定で上書き"), true },
		{ 21, 0xF019, tr(L"Download / Update mods (SilenceUtils & LucentClient)", L"SilenceUtils & LucentClient 다운로드/업데이트", L"下载/更新模组 (SilenceUtils & LucentClient)", L"MODダウンロード/更新 (SilenceUtils & LucentClient)"), false }
	};

	float maxTextW = 0.f;
	int separators = 0;
	for(const auto& item : items) {
		maxTextW = (std::max)(maxTextW, labelWidth(g, item.text, 13, FontWeight::Medium));
		if(item.separatorAfter) separators++;
	}

	int menuWidth = (int)maxTextW + 52;
	int menuHeight = 10 + (int)items.size() * 34 + separators * 7;
	contextRect.Width = menuWidth;
	contextRect.Height = menuHeight;
	contextRect.X = std::clamp(contextRect.X, 8, std::max(8, width - menuWidth - 8));
	contextRect.Y = std::clamp(contextRect.Y, 58, std::max(58, height - menuHeight - 10));
	if(contextRect.IntersectsWith(Rect(width - 322, 255, 202, 18))) {
		contextRect.Y = std::max(58, contextRect.Y - menuHeight);
	}

	panel(g, (float)contextRect.X + 2, (float)contextRect.Y + 3, (float)menuWidth, (float)menuHeight, rgb(0, 0, 0, 22), Color(0, 0, 0, 0), 10);
	panel(g, (float)contextRect.X, (float)contextRect.Y, (float)menuWidth, (float)menuHeight, rgb(255, 255, 255), rgb(226, 232, 240), 10);

	int curY = contextRect.Y + 5;
	for(const auto& item : items) {
		if(hoveredKind == item.kind) {
			panel(g, (float)contextRect.X + 5, (float)curY, (float)menuWidth - 10, 34, rgb(239, 246, 255), Color(0, 0, 0, 0), 6);
		}
		glyph(g, item.glyphChar, contextRect.X + 13, curY + 10, 14, rgb(71, 85, 105));
		label(g, item.text, (float)contextRect.X + 36, (float)curY, (float)menuWidth - 44, 34, 13, rgb(30, 41, 59), FontWeight::Medium);
		hit(contextRect.X + 5, curY, menuWidth - 10, 34, item.kind);
		curY += 34;
		if(item.separatorAfter) {
			SolidBrush sepBrush(rgb(226, 232, 240));
			g.FillRectangle(&sepBrush, contextRect.X + 10, curY + 3, menuWidth - 20, 1);
			curY += 7;
		}
	}
}

static void paint(Graphics& g,int width,int height) {
	clicks.clear(); optionHitOffset=0; optionHitBottom=0;
	g.SetSmoothingMode(SmoothingModeAntiAlias);
	g.SetTextRenderingHint(TextRenderingHintAntiAlias);

	rect(g,0,0,(float)width,(float)height,rgb(255,255,255));

	Color blue=rgb(20,117,255);
	Color gold=rgb(245,158,11);
	Color goldHover=rgb(217,119,6);
	Color muted=rgb(100,116,139);
	Color border=rgb(226,232,240);
	Color textDark=rgb(15,23,42);

	const auto homeText=tr(L"Home",L"메인",L"主页",L"メイン");
	const auto optionsText=tr(L"Options",L"옵션",L"设置",L"設定");
	float homeIconWidth=glyphWidth(g,0xF015,15), optionsIconWidth=glyphWidth(g,0xF013,15);
	float homeTextWidth=std::max(labelWidth(g,homeText,14,FontWeight::Medium),labelWidth(g,homeText,14,FontWeight::SemiBold));
	float optionsTextWidth=std::max(labelWidth(g,optionsText,14,FontWeight::Medium),labelWidth(g,optionsText,14,FontWeight::SemiBold));
	float homeWidth=12+homeIconWidth+6+homeTextWidth+12;
	float optionsX=24+homeWidth+6, optionsWidth=12+optionsIconWidth+6+optionsTextWidth+12;
	panel(g,24+tabPosition*(optionsX-24),12,homeWidth+(optionsWidth-homeWidth)*tabPosition,34,rgb(239,246,255),Color(0,0,0,0),8);

	Color t0Col=rgb((int)(20+(100-20)*tabPosition),(int)(117+(116-117)*tabPosition),(int)(255+(139-255)*tabPosition));
	glyph(g,0xF015,36,21,15,t0Col);
	label(g,homeText,36+homeIconWidth+6,12,homeTextWidth,34,14,t0Col,tabPosition<0.5f?FontWeight::SemiBold:FontWeight::Medium);
	hit(24,12,(int)homeWidth,34,1,0);

	Color t1Col=rgb((int)(100+(20-100)*tabPosition),(int)(116+(117-116)*tabPosition),(int)(139+(255-139)*tabPosition));
	glyph(g,0xF013,(int)optionsX+12,21,15,t1Col);
	label(g,optionsText,optionsX+12+optionsIconWidth+6,12,optionsTextWidth,34,14,t1Col,tabPosition>=0.5f?FontWeight::SemiBold:FontWeight::Medium);
	hit((int)optionsX,12,(int)optionsWidth,34,1,1);

	// Update Check Button (Top Right) with smooth hover
	float upHov=btnUpdateHover;
	Color upBg=rgb((int)(255-14*upHov),(int)(255-10*upHov),(int)(255-6*upHov));
	panel(g,(float)width-146,12,122,34,upBg,border,8);
	glyph(g,0xF021,width-136,21,14,muted);
	label(g,tr(L"Check updates",L"업데이트 확인",L"检查更新",L"更新を確認"),(float)width-118,12,86,34,12,rgb(71,85,105),FontWeight::Medium,1);
	hit(width-146,12,122,34,8);


	line(g,0,52,(float)width,rgb(241,245,249));

	if(optionsPage) {
		optionsScroll=std::clamp(optionsScroll,0,std::max(0,546-height));
		GraphicsState viewport=g.Save();
		g.SetClip(Rect(0,60,width,height-72));
		g.TranslateTransform(0,(float)-optionsScroll);
		optionHitOffset=-optionsScroll; optionHitBottom=height-12;
		// Options Page
		label(g,tr(L"General settings",L"일반 설정",L"常规设置",L"一般設定"),24,68,400,24,18,textDark,FontWeight::Bold);

		glyph(g,0xF0AC,24,103,18,muted);
		label(g,tr(L"Language",L"언어",L"语言",L"言語"),52,99,300,24,14,rgb(51,65,85),FontWeight::SemiBold);

		std::wstring lang=language==L"ko"?L"한국어":language==L"zh"?L"简体中文":language==L"ja"?L"日本語":L"English";
		bool langHover=hoveredKind==2 && hoveredIndex==0;
		panel(g,(float)width-244,94,220,34,langHover?rgb(248,250,252):rgb(255,255,255),langDropdownOpen?blue:rgb(203,213,225),6);
		label(g,lang,(float)width-232,94,170,34,13,textDark,FontWeight::Medium);
		glyph(g,langDropdownOpen?0xF077:0xF078,width-48,105,11,langDropdownOpen?blue:muted);
		hit(width-244,94,220,34,2,0);

		glyph(g,0xF07B,24,144,18,muted);
		label(g,tr(L"PrismSync settings directory",L"PrismSync 설정 경로",L"PrismSync 设置目录",L"PrismSync 設定フォルダー"),52,140,(float)width-96,22,13,rgb(71,85,105),FontWeight::SemiBold);

		panel(g,52,164,(float)width-76,34,rgb(248,250,252),border,6);
		label(g,settingsDir.wstring(),64,164,(float)width-130,34,12,muted,FontWeight::Regular);
		glyph(g,0xF07B,width-48,173,15,muted);
		hit(width-60,164,36,34,11);

		line(g,24,210,(float)width-48,border);

		label(g,tr(L"Choose items to copy",L"복사할 항목 선택",L"选择复制项目",L"コピーする項目の選択"),24,222,(float)width-48,24,17,textDark,FontWeight::Bold);

		const std::wstring names[]={
			tr(L"Minecraft settings",L"마인크래프트 설정",L"Minecraft 设置",L"Minecraft 設定"),
			tr(L"Sodium settings",L"소듐 설정",L"Sodium 设置",L"Sodium 設定"),
			tr(L"Mod configuration folder",L"모드 콘피그 폴더",L"模组配置文件夹",L"MOD 設定フォルダー"),
			tr(L"Resource packs",L"리소스팩",L"资源包",L"リソースパック"),
			tr(L"Shaders",L"셰이더",L"光影包",L"シェーダー"),
			tr(L"Saved worlds",L"세이브 월드",L"存档世界",L"ワールド"),
			tr(L"Screenshots",L"스크린샷",L"截图",L"スクリーンショット")
		};
		const std::wstring details[]={
			tr(L"options.txt and other Minecraft configuration files",L"options.txt 등 마인크래프트 설정 파일",L"options.txt 等 Minecraft 配置文件",L"options.txt などの設定ファイル"),
			tr(L"sodium configuration files",L"sodium 설정 파일",L"sodium 配置文件",L"sodium 設定ファイル"),
			tr(L"config folder (mod settings)",L"config 폴더 (모드 설정)",L"config 文件夹 (模组设置)",L"config フォルダー (MOD 設定)"),
			tr(L"resourcepacks folder",L"resourcepacks 폴더",L"resourcepacks 文件夹",L"resourcepacks フォルダー"),
			tr(L"shaderpacks folder",L"shaderpacks 폴더",L"shaderpacks 文件夹",L"shaderpacks フォルダー"),
			tr(L"saves folder",L"saves 폴더",L"saves 文件夹",L"saves フォルダー"),
			tr(L"screenshots folder",L"screenshots 폴더",L"screenshots 文件夹",L"screenshots フォルダー")
		};
		const wchar_t icons[]={0xF11B,0xF1B2,0xF07B,0xF03E,0xF6FC,0xF0C7,0xF030};

		int rowHeight=40;
		for(int i=0;i<7;i++) {
			int y=252+i*rowHeight;
			glyph(g,icons[i],24,y+9,16,muted);
			label(g,names[i],52,(float)y+2,(float)width-160,18,14,rgb(30,41,59),FontWeight::SemiBold);
			label(g,details[i],52,(float)y+20,(float)width-160,16,12,muted,FontWeight::Regular);

			float t=togglePosition[i];
			float trackX=(float)width-72, trackY_=(float)y+6, trackW=46.f, trackH=26.f;
			Color trackFill=rgb((int)(226+(37-226)*t),(int)(232+(99-232)*t),(int)(240+(235-240)*t));
			Color trackEdge=rgb((int)(203+(30-203)*t),(int)(213+(85-213)*t),(int)(225+(210-225)*t));
			panel(g,trackX,trackY_,trackW,trackH,trackFill,trackEdge,13.f);

			float knobX=trackX+3.f+20.f*t;
			float knobY=trackY_+3.f;
			panel(g,knobX,knobY+1.f,20.f,20.f,rgb(0,0,0,25),Color(0,0,0,0),10.f);
			panel(g,knobX,knobY,20.f,20.f,rgb(255,255,255),Color(0,0,0,0),10.f);

			hit(width-80,y,64,rowHeight-1,3,i);
			line(g,24,(float)y+rowHeight-1,(float)width-48,rgb(241,245,249));
		}

		// Floating Custom Language Dropdown Menu
		if(langDropdownOpen || langDropdownAnim>0.01f) {
			float dropX=(float)width-244, dropY=132.f, dropW=220.f, dropH=148.f*langDropdownAnim;
			GraphicsState dropState=g.Save();
			g.SetClip(RectF(dropX-4,dropY-4,dropW+8,dropH+8));
			panel(g,dropX+2,dropY+2,dropW,dropH,rgb(0,0,0,25),Color(0,0,0,0),8);
			panel(g,dropX,dropY,dropW,dropH,rgb(255,255,255),rgb(203,213,225),8);
			const wchar_t* langNames[]={L"English",L"한국어",L"简体中文",L"日本語"};
			const wchar_t* langCodes[]={L"en",L"ko",L"zh",L"ja"};
			for(int i=0;i<4;i++) {
				float itemY=dropY+i*36.f;
				bool itHover=hoveredKind==12 && hoveredIndex==i;
				bool itActive=language==langCodes[i];
				if(itHover) panel(g,dropX+4,itemY+2,dropW-8,32,rgb(241,245,249),Color(0,0,0,0),6);
				label(g,langNames[i],dropX+14,itemY,dropW-48,36,13,itActive?blue:textDark,itActive?FontWeight::SemiBold:FontWeight::Regular);
				if(itActive) glyph(g,0xF00C,width-52,(int)itemY+11,13,blue);
				hit((int)dropX,(int)itemY,(int)dropW,36,12,i);
			}
			g.Restore(dropState);
		}
		g.Restore(viewport); optionHitOffset=0; optionHitBottom=0;
		if(height<546) {
			optionTrack=Rect(width-10,66,5,height-84);
			optionThumb=scrollbar(g,optionTrack,optionsScroll,546-height,draggingOptions || hoveredKind==14);
			hit(width-16,60,16,height-72,14);
		}

		return;
	}

	// Prism Launcher Path Field
	label(g,tr(L"Prism Launcher directory",L"Prism Launcher 경로",L"Prism Launcher 目录",L"Prism Launcher フォルダー"),24,68,(float)width-48,20,13,rgb(30,41,59),FontWeight::SemiBold);
	panel(g,24,90,(float)width-48,38,rgb(255,255,255),border,8);
	glyph(g,0xF07B,38,100,15,muted);
	label(g,prismDir.wstring(),58,90,(float)width-110,38,12,muted,FontWeight::Regular);
	bool fldHover=hoveredKind==4;
	panel(g,(float)width-56,94,30,30,fldHover?rgb(241,245,249):rgb(255,255,255),fldHover?border:Color(0,0,0,0),6);
	glyph(g,0xF07B,width-49,101,15,rgb(51,65,85));
	hit(width-60,90,36,38,4);

	// Main Instance Card
	const Instance* main=lookup(mainId);
	if(main) {
		panel(g,24,140,(float)width-48,102,rgb(240,247,255),rgb(203,228,255),12);
		hit(24,140,width-48,102,17);
		instanceIcon(g,*main,38,151,80,10);

		// Measure Name
		FontFamily* nameFam=boldFamily?boldFamily.get():(semiboldFamily?semiboldFamily.get():regularFamily.get());
		FontFamily nameFallback(L"Segoe UI");
		Font font(nameFam?nameFam:&nameFallback,20.f,FontStyleRegular,UnitPixel);
		RectF layoutRect(132.f,151.f,(float)width-360.f,26.f);
		RectF bounds;
		StringFormat format(StringFormat::GenericTypographic());
		format.SetFormatFlags(StringFormatFlagsNoWrap|StringFormatFlagsMeasureTrailingSpaces);
		g.MeasureString(main->name.c_str(),-1,&font,layoutRect,&format,&bounds);

		const auto badgeText=tr(L"Main instance",L"메인 인스턴스",L"主实例",L"メインインスタンス");
		float badgeTextWidth=labelWidth(g,badgeText,11,FontWeight::SemiBold);
		float badgeW=8+11+4+badgeTextWidth+8;
		float nameWidth=std::min(bounds.Width+18.f,std::max(80.f,(float)width-132-224-badgeW-8));
		label(g,main->name,132,151,nameWidth,26,20,textDark,FontWeight::Bold);

		// Pill Badge with Crown
		float badgeX=132+nameWidth+8.f;
		panel(g,badgeX,154,badgeW,20,rgb(219,234,254),rgb(191,219,254),10);
		glyph(g,0xF521,(int)badgeX+8,158,11,blue);
		label(g,badgeText,badgeX+23,154,badgeTextWidth,20,11,blue,FontWeight::SemiBold);

		// Version
		label(g,main->version,132,179,(float)width-360,18,13,rgb(51,65,85),FontWeight::Regular);

		// Path with document icon
		std::wstring instPath=(instanceBase()/main->id).wstring();
		glyph(g,0xF15B,132,202,11,rgb(148,163,184));
		label(g,instPath,146,199,(float)width-370,18,12,rgb(148,163,184),FontWeight::Regular);

		// Change Main Button with smooth hover
		float chHov=btnChangeHover;
		Color chBg=choosingMain?rgb(254,243,199):rgb((int)(255-14*chHov),(int)(255-10*chHov),(int)(255-6*chHov));
		Color chEdge=choosingMain?gold:rgb((int)(226-23*chHov),(int)(232-19*chHov),(int)(240-15*chHov));
		panel(g,(float)width-212,171,176,40,chBg,chEdge,8);
		glyph(g,choosingMain?0xF00D:0xF362,width-198,183,15,choosingMain?goldHover:rgb(51,65,85));
		label(g,choosingMain?tr(L"Cancel",L"선택 취소",L"取消",L"キャンセル"):tr(L"Change main instance",L"다른 인스턴스로 변경",L"更改主实例",L"メインを変更"),(float)width-176,171,132,40,13,choosingMain?goldHover:rgb(51,65,85),FontWeight::Medium,1);
		hit(width-212,171,176,40,5);
	} else {
		panel(g,24,140,(float)width-48,102,rgb(248,250,252),border,12);
		label(g,tr(L"No instances found. Choose your Prism Launcher directory.",L"인스턴스를 찾지 못했어. Prism Launcher 경로를 확인해.",L"未找到实例，请选择 Prism Launcher 目录。",L"インスタンスが見つかりません。フォルダーを確認してください。"),40,176,(float)width-80,30,14,muted,FontWeight::Regular,1);
	}

	// Other Instances Section Header
	int count=0;
	for(auto& i:instances) if(visibleInstance(i)) count++;
	std::wstring otherTitle=choosingMain?tr(L"Choose a new main instance (Click to switch)",L"새 메인 인스턴스 선택 (클릭하면 바로 변경됩니다)",L"选择新的主实例（点击直接切换）",L"새로운 메인 선택 (클릭으로 즉시 변경)"):
		(tr(L"Other instances",L"다른 인스턴스들",L"其他实例",L"他のインスタンス")+L" ("+std::to_wstring(count)+L")");
	label(g,otherTitle,24,254,(float)width-380,24,16,choosingMain?goldHover:textDark,FontWeight::Bold);

	bool searchFocused=GetFocus()==searchWindow;
	panel(g,(float)width-354,250,244,28,rgb(248,250,252),searchFocused?blue:rgb(203,213,225),8);
	glyph(g,0xF002,width-344,257,14,muted);

	// Navigation Arrows (< >) with vector chevrons and smooth hover
	float lHov=navHoverLeft;
	Color lBg=rgb((int)(255-14*lHov),(int)(255-10*lHov),(int)(255-6*lHov));
	Color lEdge=rgb((int)(226-23*lHov),(int)(232-19*lHov),(int)(240-15*lHov));
	Color lIcon=rgb((int)(100-85*lHov),(int)(116-93*lHov),(int)(139-97*lHov));
	panel(g,(float)width-96,250,32,32,lBg,lEdge,8);
	drawChevron(g,(float)width-80,266,false,lIcon);
	hit(width-96,250,32,32,10,-1);

	float rHov=navHoverRight;
	Color rBg=rgb((int)(255-14*rHov),(int)(255-10*rHov),(int)(255-6*rHov));
	Color rEdge=rgb((int)(226-23*rHov),(int)(232-19*rHov),(int)(240-15*rHov));
	Color rIcon=rgb((int)(100-85*rHov),(int)(116-93*rHov),(int)(139-97*rHov));
	panel(g,(float)width-56,250,32,32,rBg,rEdge,8);
	drawChevron(g,(float)width-40,266,true,rIcon);
	hit(width-56,250,32,32,10,1);

	// Instances Grid Area
	contentWidth=std::max(0,count*(cardWidth+cardGap)-cardGap);
	scrollX=std::clamp(scrollX,0,maxScrollFor(width));
	scrollPosition=std::clamp(scrollPosition,0.f,(float)maxScrollFor(width));

	GraphicsState saved=g.Save();
	g.SetClip(Rect(24,listTop-4,width-48,listHeight+8));
	int index=0;
	for(auto& in:instances) {
		if(!visibleInstance(in)) continue;
		int x=24+index*(cardWidth+cardGap)-(int)std::lround(scrollPosition);
		bool selected=selectedId==in.id;
		float hov=cardHover[index<32?index:0];
		if(x+cardWidth>24 && x<width-24) {
			float cardY=(float)listTop-2.f*hov;
			if(hov>0.02f) panel(g,(float)x,cardY+3.f,(float)cardWidth,(float)cardHeight,rgb(0,0,0,(int)(18*hov)),Color(0,0,0,0),10.f);

			Color cardBg=choosingMain?rgb(254,(int)(243+8*(1.f-hov)),(int)(199+36*(1.f-hov))):(selected?rgb(239,246,255):rgb((int)(255-7*hov),(int)(255-5*hov),(int)(255-3*hov)));
			Color cardEdge=choosingMain?(hov>0.5f?goldHover:gold):(selected?blue:rgb((int)(226-23*hov),(int)(232-19*hov),(int)(240-15*hov)));
			float strokeW=(choosingMain || selected)?2.f:1.f;
			panel(g,(float)x,cardY,(float)cardWidth,(float)cardHeight,cardBg,cardEdge,10.f,strokeW);

			instanceIcon(g,in,x+20,(int)cardY+10,68,9);
			label(g,in.name,(float)x+4,cardY+82,(float)cardWidth-8,18,13,textDark,FontWeight::SemiBold,1);

			// Version with cube glyph centered
			FontFamily* vFam=mediumFamily?mediumFamily.get():(regularFamily?regularFamily.get():nullptr);
			const wchar_t* fallbackName=language==L"zh"?L"Microsoft YaHei UI":language==L"ja"?L"Yu Gothic UI":language==L"ko"?L"Malgun Gothic":L"Segoe UI";
			FontFamily fallback(fallbackName);
			Font vFont(vFam?vFam:&fallback,12.f,FontStyleRegular,UnitPixel);
			RectF vBounds;
			StringFormat vFmt(StringFormat::GenericTypographic());
			vFmt.SetFormatFlags(StringFormatFlagsNoWrap|StringFormatFlagsMeasureTrailingSpaces);
			g.MeasureString(in.version.c_str(),-1,&vFont,RectF(0,0,200,20),&vFmt,&vBounds);
			float totW=14.f+vBounds.Width;
			float sX=(float)x+((float)cardWidth-totW)/2.f;
			glyph(g,0xF1B2,(int)sX,(int)cardY+105,10,rgb(148,163,184));
			label(g,in.version,sX+14.f,cardY+102,vBounds.Width+4.f,18.f,12,rgb(100,116,139),FontWeight::Medium);

			if(selected && !choosingMain) {
				panel(g,(float)x+6,cardY+6,18,18,blue,blue,9);
				glyph(g,0xF00C,x+8,(int)cardY+8,10,rgb(255,255,255));
			} else if(choosingMain) {
				panel(g,(float)x+6,cardY+6,18,18,gold,gold,9);
				glyph(g,0xF00C,x+8,(int)cardY+8,10,rgb(255,255,255));
			}

			int left=std::max(24,x), right=std::min(width-24,x+cardWidth);
			hit(left,listTop,right-left,cardHeight,6,index);
		}
		index++;
	}
	g.Restore(saved);

	// Horizontal Scrollbar
	if(maxScrollFor(width)>0) {
		panel(g,24,(float)trackY,(float)width-48,4,rgb(241,245,249),Color(0,0,0,0),2);
		int tw,tx;
		scrollGeometry(width,tw,tx);
		panel(g,(float)tx,(float)trackY,(float)tw,4,rgb(203,213,225),Color(0,0,0,0),2);
		hit(24,trackY-3,width-48,12,7);
	}

	// Bottom Action Bar
	line(g,24,438,(float)width-48,border);

	if(choosingMain) {
		button(g,24,450,142,40,tr(L"Cancel",L"선택 취소",L"取消",L"キャンセル"),5,0,false,0xF00D,true,8);
		vline(g,178,454,32,rgb(226,232,240));
		glyph(g,0xF05A,192,460,18,goldHover);
		label(g,tr(L"Click any instance card above to immediately set it as main.",L"위 목록에서 인스턴스를 클릭하면 즉시 메인 인스턴스로 변경됩니다.",L"点击上方任意实例卡片即可直接设为主实例。",L"上のインスタンスをクリックすると即座にメインに設定されます。"),216,450,(float)width-236,40,13,goldHover,FontWeight::Medium);
	} else {
		bool hasTarget=busy || lookup(selectedId)!=nullptr;
		float apHov=btnApplyHover;
		Color apBg=hasTarget?(apHov>0.5f?rgb(0,98,233):blue):rgb(226,232,240);
		panel(g,24,450,142,40,apBg,apBg,8);
		Color apFg=hasTarget?rgb(255,255,255):rgb(148,163,184);
		glyph(g,0xF0C5,38,461,16,apFg);
		label(g,(busy?tr(L"Cancel",L"취소"):tr(L"Apply settings",L"설정 적용",L"应用设置",L"設定を適用")),58,450,98,40,14,apFg,FontWeight::SemiBold);
		hit(24,450,142,40,9,0);

		vline(g,178,454,32,rgb(226,232,240));
		const Instance* targetInst=lookup(selectedId);
		std::wstring desc;
		if(targetInst && main) {
			desc=tr((L"Copy settings from main instance ("+main->name+L") to selected instance ("+targetInst->name+L").").c_str(),
					(L"선택한 인스턴스("+targetInst->name+L")에 메인 인스턴스("+main->name+L")의 설정을 복사합니다.").c_str(),
					(L"将主实例 ("+main->name+L") 的设置复制到选定实例 ("+targetInst->name+L")。").c_str(),
					(L"メイン ("+main->name+L") の設定を選択したインスタンス ("+targetInst->name+L") へコピーします。").c_str());
		} else {
			desc=tr(L"Select an instance below to apply settings from the main instance.",L"메인 인스턴스의 설정을 적용할 대상 인스턴스를 아래에서 선택하세요.",L"请在下方选择要应用主实例设置的目标实例。",L"メインインスタンスの設定を適用するインスタンスを以下から選択してください。");
		}
		glyph(g,0xF05A,192,460,18,rgb(100,116,139));
		label(g,desc,216,450,(float)width-236,40,13,rgb(71,85,105),FontWeight::Regular);
	}

	if(!status.empty()) {
		label(g,status,24,492,(float)width-48,14,11,blue,FontWeight::Medium);
	}
	drawContext(g,width,height);
}

static int pageHeight() { return 506; }

static int outerHeight(int height) {
	RECT rectangle{0,0,0,(LONG)std::lround(height*dpiScale)};
	AdjustWindowRectExForDpi(&rectangle,WS_OVERLAPPEDWINDOW,FALSE,0,(UINT)std::lround(96*dpiScale));
	return rectangle.bottom-rectangle.top;
}

static LRESULT CALLBACK searchProc(HWND hwnd,UINT message,WPARAM wp,LPARAM lp) {
	if(message==WM_SETFOCUS || message==WM_KILLFOCUS) redraw(windowHandle);
	return CallWindowProcW(originalSearchProc,hwnd,message,wp,lp);
}

static void createSearch(HWND parent,HINSTANCE instance) {
	searchBrush=CreateSolidBrush(RGB(248,250,252));
	searchWindow=CreateWindowExW(0,L"EDIT",L"",WS_CHILD|WS_VISIBLE|WS_TABSTOP|ES_AUTOHSCROLL,0,0,0,0,parent,(HMENU)200,instance,nullptr);
	originalSearchProc=(WNDPROC)SetWindowLongPtrW(searchWindow,GWLP_WNDPROC,(LONG_PTR)searchProc);
	searchFont=CreateFontW(-(int)(13*dpiScale),0,0,0,FW_NORMAL,FALSE,FALSE,FALSE,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Segoe UI");
	SendMessageW(searchWindow,WM_SETFONT,(WPARAM)searchFont,TRUE);
	SendMessageW(searchWindow,0x1501,TRUE,(LPARAM)L"Search instances / 인스턴스 검색");
}

static bool chooseFolder(fs::path& path) {
	BROWSEINFOW bi{};
	bi.hwndOwner=windowHandle;
	std::wstring title=tr(L"Choose Prism Launcher directory",L"Prism Launcher 폴더 선택",L"选择 Prism Launcher 目录",L"Prism Launcher フォルダーを選択");
	bi.lpszTitle=title.c_str();
	bi.ulFlags=BIF_RETURNONLYFSDIRS|BIF_NEWDIALOGSTYLE;
	PIDLIST_ABSOLUTE pid=SHBrowseForFolderW(&bi);
	if(!pid) return false;
	wchar_t buf[MAX_PATH];
	bool ok=SHGetPathFromIDListW(pid,buf);
	CoTaskMemFree(pid);
	if(ok) path=buf;
	return ok;
}

static fs::path gameDir(const Instance& i) {
	if(!safeId(i.id)) throw std::runtime_error("Invalid instance ID");
	auto root=instanceBase()/i.id;
	syncer::validatePath(root);
	return fs::is_directory(root/L"minecraft")?root/L"minecraft":root/L".minecraft";
}


struct ReportState {
	std::wstring title,text,summary;
	ReportTone tone=ReportTone::Info;
	bool confirm=false,accepted=false,dragging=false;
	int scroll=0,maximum=0,dragOffset=0,hover=-1,focus=0;
	Rect track,thumb;
	std::vector<Click> buttons;
	std::unique_ptr<Bitmap> buffer;
};
static void paintReport(Graphics& g,int width,int height,ReportState& state) {
	g.SetSmoothingMode(SmoothingModeAntiAlias); g.SetTextRenderingHint(TextRenderingHintAntiAlias);
	rect(g,0,0,(float)width,(float)height,rgb(255,255,255));
	Color accent=state.tone==ReportTone::Success?rgb(22,163,74):state.tone==ReportTone::Warning?rgb(217,119,6):state.tone==ReportTone::Error?rgb(220,38,38):rgb(20,117,255);
	panel(g,24,22,36,36,Color(20,accent.GetR(),accent.GetG(),accent.GetB()),Color(0,0,0,0),18);
	glyph(g,state.tone==ReportTone::Success?0xF00C:state.tone==ReportTone::Warning?0xF071:state.tone==ReportTone::Error?0xF00D:0xF0C5,33,31,18,accent);
	label(g,state.title,72,20,(float)width-96,40,21,rgb(15,23,42),FontWeight::Bold);
	label(g,state.summary,24,68,(float)width-48,26,13,accent,FontWeight::Medium);
	Rect body(24,108,width-48,height-182);
	panel(g,(float)body.X,(float)body.Y,(float)body.Width,(float)body.Height,rgb(248,250,252),rgb(226,232,240),10);
	FontFamily fallback(language==L"zh"?L"Microsoft YaHei UI":language==L"ja"?L"Yu Gothic UI":language==L"ko"?L"Malgun Gothic":L"Segoe UI");
	Font font(regularFamily && language!=L"zh" && language!=L"ja"?regularFamily.get():&fallback,14.f,FontStyleRegular,UnitPixel);
	StringFormat format; format.SetFormatFlags(StringFormatFlagsLineLimit);
	std::vector<std::pair<std::wstring,int>> rows;
	std::wistringstream input(state.text); std::wstring text;
	int contentHeight=0;
	while(std::getline(input,text)) {
		if(!text.empty() && text.back()==L'\r') text.pop_back();
		if(text.empty()) { contentHeight+=8; rows.push_back({L"",8}); continue; }
		RectF bounds;
		g.MeasureString(text.c_str(),-1,&font,RectF(0,0,(float)body.Width-44,10000),&format,&bounds);
		int rowHeight=(int)std::ceil(bounds.Height)+12;
		rows.push_back({text,rowHeight}); contentHeight+=rowHeight;
	}
	state.maximum=std::max(0,contentHeight+24-body.Height);
	state.scroll=std::clamp(state.scroll,0,state.maximum);
	GraphicsState clip=g.Save(); g.SetClip(Rect(body.X+12,body.Y+8,body.Width-28,body.Height-16));
	int y=body.Y+12-state.scroll;
	for(const auto& [row,rowHeight]:rows) {
		if(!row.empty()) {
			SolidBrush brush(row.starts_with(L"오류") || row.starts_with(L"Error")?rgb(185,28,28):rgb(51,65,85));
			g.DrawString(row.c_str(),-1,&font,RectF((float)body.X+14,(float)y,(float)body.Width-44,(float)rowHeight),&format,&brush);
		}
		y+=rowHeight;
	}
	g.Restore(clip);
	state.track=Rect(width-36,body.Y+12,5,body.Height-24);
	if(state.maximum) state.thumb=scrollbar(g,state.track,state.scroll,state.maximum,state.dragging);
	state.buttons.clear();
	for(int i=0;i<(state.confirm?2:1);i++) {
		Rect box(width-24-132-(state.confirm?1-i:0)*144,height-54,132,36);
		bool primary=i==0, hovered=state.hover==i;
		panel(g,(float)box.X,(float)box.Y,(float)box.Width,(float)box.Height,primary?(hovered?rgb(0,98,233):rgb(20,117,255)):(hovered?rgb(241,245,249):rgb(255,255,255)),primary?rgb(20,117,255):rgb(203,213,225),8);
		const auto caption=primary?(state.confirm?tr(L"Apply settings",L"설정 적용",L"应用设置",L"設定を適用"):tr(L"Close",L"닫기",L"关闭",L"閉じる")):tr(L"Cancel",L"취소",L"取消",L"キャンセル");
		label(g,caption,(float)box.X,(float)box.Y,(float)box.Width,(float)box.Height,14,primary?rgb(255,255,255):rgb(51,65,85),FontWeight::SemiBold,1);
		if(state.focus==i) { Pen pen(primary?rgb(191,219,254):rgb(20,117,255),1.f); pen.SetDashStyle(DashStyleDash); g.DrawRectangle(&pen,Rect(box.X+3,box.Y+3,box.Width-6,box.Height-6)); }
		state.buttons.push_back({box,primary?IDOK:IDCANCEL,i});
	}
}
static LRESULT CALLBACK reportProc(HWND hwnd,UINT msg,WPARAM wp,LPARAM lp) {
	auto state=(ReportState*)GetWindowLongPtrW(hwnd,GWLP_USERDATA);
	if(msg==WM_CREATE) {
		state=(ReportState*)((CREATESTRUCTW*)lp)->lpCreateParams;
		SetWindowLongPtrW(hwnd,GWLP_USERDATA,(LONG_PTR)state); return 0;
	}
	if(!state) return DefWindowProcW(hwnd,msg,wp,lp);
	float scale=GetDpiForWindow(hwnd)/96.f;
	if(msg==WM_PAINT) {
		PAINTSTRUCT ps; HDC dc=BeginPaint(hwnd,&ps); RECT rc; GetClientRect(hwnd,&rc);
		if(rc.right>0 && rc.bottom>0) {
			if(!state->buffer || state->buffer->GetWidth()!=(UINT)rc.right || state->buffer->GetHeight()!=(UINT)rc.bottom)
				state->buffer=std::make_unique<Bitmap>(rc.right,rc.bottom,PixelFormat32bppRGB);
			Graphics back(state->buffer.get()); back.ScaleTransform(scale,scale);
			paintReport(back,(int)(rc.right/scale),(int)(rc.bottom/scale),*state);
			Graphics front(dc); front.DrawImage(state->buffer.get(),0,0);
		}
		EndPaint(hwnd,&ps); return 0;
	}
	if(msg==WM_ERASEBKGND) return 1;
	if(msg==WM_GETMINMAXINFO) { ((MINMAXINFO*)lp)->ptMinTrackSize={(LONG)(540*scale),(LONG)(330*scale)}; return 0; }
	if(msg==WM_DPICHANGED) { auto r=(RECT*)lp; SetWindowPos(hwnd,nullptr,r->left,r->top,r->right-r->left,r->bottom-r->top,SWP_NOZORDER|SWP_NOACTIVATE); return 0; }
	if(msg==WM_MOUSEWHEEL) { state->scroll=std::clamp(state->scroll-GET_WHEEL_DELTA_WPARAM(wp)*42/WHEEL_DELTA,0,state->maximum); InvalidateRect(hwnd,nullptr,FALSE); return 0; }
	if(msg==WM_LBUTTONDOWN) {
		int x=(int)(GET_X_LPARAM(lp)/scale), y=(int)(GET_Y_LPARAM(lp)/scale);
		for(const auto& button:state->buttons) if(button.r.Contains(x,y)) { SendMessageW(hwnd,WM_COMMAND,button.kind,0); return 0; }
		if(state->maximum && x>=state->track.X-6 && x<=state->track.X+11 && y>=state->track.Y && y<=state->track.GetBottom()) {
			state->dragging=true; state->dragOffset=state->thumb.Contains(x,y)?y-state->thumb.Y:state->thumb.Height/2;
			SetCapture(hwnd); SendMessageW(hwnd,WM_MOUSEMOVE,wp,lp);
		}
		return 0;
	}
	if(msg==WM_MOUSEMOVE) {
		int x=(int)(GET_X_LPARAM(lp)/scale), y=(int)(GET_Y_LPARAM(lp)/scale);
		if(state->dragging) state->scroll=std::clamp((y-state->track.Y-state->dragOffset)*state->maximum/std::max(1,state->track.Height-state->thumb.Height),0,state->maximum);
		int hover=-1; for(const auto& button:state->buttons) if(button.r.Contains(x,y)) hover=button.index;
		if(hover!=state->hover || state->dragging) { state->hover=hover; InvalidateRect(hwnd,nullptr,FALSE); }
		SetCursor(LoadCursor(nullptr,hover>=0?IDC_HAND:IDC_ARROW)); return 0;
	}
	if(msg==WM_LBUTTONUP || msg==WM_CAPTURECHANGED) { state->dragging=false; if(msg==WM_LBUTTONUP) ReleaseCapture(); return 0; }
	if(msg==WM_KEYDOWN) {
		if(wp==VK_ESCAPE) SendMessageW(hwnd,WM_COMMAND,IDCANCEL,0);
		else if(wp==VK_TAB) { state->focus=state->confirm?1-state->focus:0; InvalidateRect(hwnd,nullptr,FALSE); }
		else if(wp==VK_RETURN || wp==VK_SPACE) SendMessageW(hwnd,WM_COMMAND,state->focus?IDCANCEL:IDOK,0);
		else if(wp==VK_UP || wp==VK_DOWN || wp==VK_PRIOR || wp==VK_NEXT) {
			state->scroll=std::clamp(state->scroll+((wp==VK_UP || wp==VK_PRIOR)?-1:1)*((wp==VK_PRIOR || wp==VK_NEXT)?160:32),0,state->maximum); InvalidateRect(hwnd,nullptr,FALSE);
		}
		return 0;
	}
	if(msg==WM_COMMAND && (LOWORD(wp)==IDOK || LOWORD(wp)==IDCANCEL)) { state->accepted=LOWORD(wp)==IDOK; DestroyWindow(hwnd); return 0; }
	if(msg==WM_SIZE) { InvalidateRect(hwnd,nullptr,FALSE); return 0; }
	if(msg==WM_CLOSE) { DestroyWindow(hwnd); return 0; }
	return DefWindowProcW(hwnd,msg,wp,lp);
}
static bool report(const std::wstring& title,const std::wstring& text,bool confirm=false,ReportTone tone=ReportTone::Info,const std::wstring& summary=L"") {
	static bool registered=false;
	if(!registered) {
		WNDCLASSW wc{}; wc.lpfnWndProc=reportProc; wc.hInstance=GetModuleHandleW(nullptr);
		wc.lpszClassName=L"PrismSyncReport"; wc.hCursor=LoadCursor(nullptr,IDC_ARROW);
		RegisterClassW(&wc); registered=true;
	}
	ReportState state; state.title=title; state.text=text; state.summary=summary; state.tone=tone; state.confirm=confirm;
	int reportHeight=std::clamp(292+(int)std::count(text.begin(),text.end(),L'\n')*22,320,460);
	HWND dialog=CreateWindowExW(WS_EX_DLGMODALFRAME,L"PrismSyncReport",APP_TITLE.c_str(),WS_OVERLAPPEDWINDOW,
		CW_USEDEFAULT,CW_USEDEFAULT,(int)(740*dpiScale),(int)(reportHeight*dpiScale),windowHandle,nullptr,GetModuleHandleW(nullptr),&state);
	if(!dialog) return false;
	EnableWindow(windowHandle,FALSE); ShowWindow(dialog,SW_SHOW);
	MSG msg;
	while(IsWindow(dialog) && GetMessageW(&msg,nullptr,0,0)>0) {
		TranslateMessage(&msg); DispatchMessageW(&msg);
	}
	EnableWindow(windowHandle,TRUE); SetForegroundWindow(windowHandle);
	return state.accepted;
}

static void publishProgress(const fs::path& file,uint64_t bytes,uint64_t total,size_t done,size_t count) {
	auto now=GetTickCount64();
	if(now-lastProgress<100 && (!count || done!=count)) return;
	lastProgress=now;
	auto seconds=std::max(0.1,(now-workStarted)/1000.0);
	std::wstring text=std::to_wstring(done)+L" / "+std::to_wstring(count)+L" files  "+
		std::to_wstring(bytes/1024/1024)+L" / "+std::to_wstring(total/1024/1024)+L" MiB  "+
		std::to_wstring((int)(bytes/1024/1024/seconds))+L" MiB/s  "+file.wstring();
	if(!count) text=tr(L"Checking files: ",L"파일 확인 중 · ")+std::to_wstring(done)+L" · "+file.wstring();
	{ std::lock_guard lock(workMutex); workProgress=std::move(text); }
	PostMessageW(windowHandle,WORK_PROGRESS,0,0);
}
static void startWork(WorkKind kind,std::function<void(WorkEvent&)> operation) {
	if(busy) return;
	busy=true; optionsPage=false; contextId.clear(); langDropdownOpen=false; ShowWindow(searchWindow,SW_SHOW); cancelWork=false; workStarted=GetTickCount64(); lastProgress=0;
	status=tr(L"Working... Press Escape to cancel.",L"작업 중... Esc로 취소할 수 있어.");
	EnableWindow(searchWindow,FALSE);
	worker=std::thread([kind,operation=std::move(operation)] {
		auto event=std::make_unique<WorkEvent>(); event->kind=kind;
		try { operation(*event); }
		catch(const syncer::Cancelled&) { event->result.cancelled=true; }
		catch(const std::exception& e) { event->error=e.what(); }
		{ std::lock_guard lock(workMutex); completedWork=std::move(event); }
		PostMessageW(windowHandle,WORK_DONE,0,0);
	});
	redraw(windowHandle);
}
static void applyTo(const Instance& target) {
	const Instance* main=lookup(mainId);
	if(busy || !main || main->id==target.id) return;
	try {
		auto src=gameDir(*main),dst=gameDir(target);
		auto categories=enabled;
		startWork(WorkKind::Preview,[=](WorkEvent& event) {
			event.plan=syncer::prepare(src,dst,categories,cancelWork,syncer::mergeConfiguration,publishProgress);
		});
	} catch(const std::exception& e) { report(tr(L"Operation failed",L"작업 실패"),utf8ToWide(e.what()),false,ReportTone::Error); }
}
static void checkUpdates() {
	startWork(WorkKind::CheckUpdate,[](WorkEvent& event) { event.release=updater::latest(PRISM_VERSION,cancelWork); });
}
static void finishWork() {
	if(worker.joinable()) worker.join();
	std::unique_ptr<WorkEvent> event;
	{ std::lock_guard lock(workMutex); event=std::move(completedWork); }
	busy=false; EnableWindow(searchWindow,TRUE);
	if(closing) { DestroyWindow(windowHandle); return; }
	if(!event) return;
	status.clear();
	if(!event->error.empty()) { status=utf8ToWide(event->error); report(tr(L"Operation failed",L"작업 실패"),status,false,ReportTone::Error,tr(L"No further files were applied.",L"오류 내용을 확인한 뒤 다시 시도해.")); }
	else if(event->result.cancelled && event->kind!=WorkKind::Apply) status=tr(L"Cancelled",L"취소했어");
	else if(event->kind==WorkKind::Preview) {
		const auto& plan=event->plan;
		bool changed=!plan.files.empty(), errors=!plan.errors.empty();
		auto title=changed?tr(L"Review settings to apply",L"설정 적용 미리보기"):errors?tr(L"Unable to apply settings",L"설정을 적용할 수 없어"):tr(L"Everything is already up to date",L"이미 모든 설정이 같아");
		auto summary=tr(L"Changes: ",L"변경 예정 ")+std::to_wstring(plan.files.size())+tr(L" · Unchanged: ",L"개  ·  동일 ")+std::to_wstring(plan.unchanged)+tr(L" · Errors: ",L"개  ·  오류 ")+std::to_wstring(plan.errors.size())+tr(L"",L"개");
		std::wstring details=tr(L"Main instance: ",L"메인 인스턴스: ")+plan.source.wstring()+L"\n"+tr(L"Target instance: ",L"적용 대상: ")+plan.target.wstring()+L"\n\n";
		if(changed) details+=tr(L"Close Minecraft before applying. JSON/TOML formatting may change.\n",L"적용 전에 마인크래프트를 종료해. JSON/TOML의 주석과 서식은 달라질 수 있어.\n");
		for(const auto& file:plan.files) details+=(file.action=="CREATE"?tr(L"Create · ",L"새 파일 · "):file.action=="MERGE"?tr(L"Merge · ",L"설정 병합 · "):tr(L"Replace · ",L"파일 교체 · "))+file.relative.wstring()+L"\n";
		for(const auto& error:plan.errors) details+=tr(L"Error · ",L"오류 · ")+utf8ToWide(error)+L"\n";
		if(report(title,details,changed,errors?(changed?ReportTone::Warning:ReportTone::Error):changed?ReportTone::Info:ReportTone::Success,summary) && changed) {
			auto nextPlan=std::make_shared<syncer::Plan>(std::move(event->plan));
			startWork(WorkKind::Apply,[nextPlan](WorkEvent& next) {
				next.result=syncer::execute(*nextPlan,cancelWork,publishProgress);
				next.result.errors.insert(next.result.errors.end(),nextPlan->errors.begin(),nextPlan->errors.end());
			});
		}
	} else if(event->kind==WorkKind::Apply) {
		bool errors=!event->result.errors.empty(), cancelled=event->result.cancelled;
		auto title=cancelled?tr(L"Operation cancelled",L"작업을 취소했어"):errors?(event->result.completed?tr(L"Some settings could not be applied",L"일부 설정을 적용하지 못했어"):tr(L"Settings could not be applied",L"설정 적용 실패")):tr(L"Settings applied successfully",L"설정 적용 완료");
		status=tr(L"Completed: ",L"적용 완료 ")+std::to_wstring(event->result.completed)+tr(L" · Errors: ",L"개  ·  오류 ")+std::to_wstring(event->result.errors.size())+tr(L"",L"개");
		std::wstring details=cancelled?tr(L"Completed files stay applied. Unfinished files were not replaced.",L"완료한 파일은 적용됐고, 처리 중이던 파일은 교체하지 않았어."):errors?tr(L"Files listed below were not applied. Review the errors and retry.",L"아래 파일은 적용하지 못했어. 오류 내용을 확인한 뒤 다시 시도해."):tr(L"All selected changes were applied successfully.",L"선택한 변경 사항을 모두 정상적으로 적용했어.");
		for(const auto& error:event->result.errors) details+=L"\n\n"+tr(L"Error · ",L"오류 · ")+utf8ToWide(error);
		report(title,details,false,cancelled?ReportTone::Warning:errors?(event->result.completed?ReportTone::Warning:ReportTone::Error):ReportTone::Success,status);
	} else if(event->kind==WorkKind::CheckUpdate) {
		if(event->release.url.empty()) report(tr(L"Up to date",L"최신 버전이야"),tr(L"Already up to date.",L"현재 최신 버전이야."),false,ReportTone::Success);
		else if(MessageBoxW(windowHandle,(utf8ToWide(event->release.tag)+L"\n"+tr(L"Download and verify this update?",L"업데이트를 다운로드하고 검증할까?")).c_str(),L"PrismSync",MB_YESNO|MB_ICONQUESTION)==IDYES) {
			auto release=event->release; auto directory=settingsDir/L"updates";
			startWork(WorkKind::Download,[=](WorkEvent& next) {
				next.release=release;
				next.path=updater::download(release,directory,cancelWork,[&](uint64_t bytes) { publishProgress(L"Installer",bytes,release.size,0,1); });
			});
		}
	} else if(event->kind==WorkKind::Download) {
		if(MessageBoxW(windowHandle,tr(L"Installer verified. Close PrismSync and install now?",L"설치 파일 검증을 마쳤어. PrismSync를 닫고 설치할까?").c_str(),L"PrismSync",MB_YESNO|MB_ICONQUESTION)==IDYES) {
			try {
				updater::verify(event->path,event->release,cancelWork);
				if((INT_PTR)ShellExecuteW(windowHandle,L"open",event->path.c_str(),nullptr,nullptr,SW_SHOWNORMAL)<=32) throw std::runtime_error("Installer launch failed");
				PostMessageW(windowHandle,WM_CLOSE,0,0);
			} catch(const std::exception& e) { report(tr(L"Operation failed",L"작업 실패"),utf8ToWide(e.what()),false,ReportTone::Error); }
		}
	} else if(event->kind==WorkKind::UpdateMods) {
		report(event->modTitle, event->modDetails, false, event->modTone, event->modSummary);
	}
	redraw(windowHandle);
}

static void setScroll(int value,int width) {
	scrollX=std::clamp(value,0,maxScrollFor(width));
	if(!animations || draggingScroll) scrollPosition=(float)scrollX;
	redraw(windowHandle);
}

static const Instance* instanceAt(int x,int y) {
	for(auto it=clicks.rbegin();it!=clicks.rend();++it) {
		if(!it->r.Contains(x,y)) continue;
		if(it->kind==17) return lookup(mainId);
		if(it->kind==6) {
			int index=0;
			for(const auto& instance:instances) if(visibleInstance(instance) && index++==it->index) return &instance;
		}
	}
	return nullptr;
}
static void setMainInstance(const std::wstring& id) {
	if(!lookup(id)) return;
	mainId=id; selectedId.clear(); choosingMain=false; scrollX=0; scrollPosition=0; contextId.clear(); persist(); redraw(windowHandle);
}
static void openInstanceFolder(const Instance& instance) {
	try {
		auto path=instanceBase()/instance.id;
		syncer::validatePath(path);
		if((INT_PTR)ShellExecuteW(windowHandle,L"open",path.c_str(),nullptr,nullptr,SW_SHOWNORMAL)<=32)
			throw std::runtime_error("Unable to open instance folder");
	} catch(const std::exception& e) { report(tr(L"Unable to open folder",L"폴더를 열 수 없어"),utf8ToWide(e.what()),false,ReportTone::Error); }
}
static const wchar_t* FABRIC_CONFIG_FILES[] = {
	L"sodium-options.json",
	L"sodium-mixins.properties",
	L"sodium-fingerprint.json",
	L"sodium-extra-options.json",
	L"sodium-extra.properties"
};

static void saveCustomMcOptions(const Instance& instance) {
	try {
		auto src = gameDir(instance) / L"options.txt";
		if(!fs::exists(src)) {
			report(tr(L"Save failed", L"저장 실패"), tr(L"options.txt was not found in this instance.", L"해당 인스턴스에 options.txt 파일이 없어."), false, ReportTone::Error);
			return;
		}
		auto dstDir = settingsDir / L"custom_mc";
		fs::create_directories(dstDir);
		fs::copy_file(src, dstDir / L"options.txt", fs::copy_options::overwrite_existing);
		report(tr(L"Options saved", L"저장 완료"), tr(L"Custom MC options (options.txt) saved successfully.", L"내 커스텀 MC 옵션(options.txt)으로 저장했어."), false, ReportTone::Success);
	} catch(const std::exception& e) {
		report(tr(L"Save failed", L"저장 실패"), utf8ToWide(e.what()), false, ReportTone::Error);
	}
}

static void applyCustomMcOptions(const Instance& instance) {
	try {
		auto src = settingsDir / L"custom_mc" / L"options.txt";
		if(!fs::exists(src)) {
			report(tr(L"Apply failed", L"덮어씌우기 실패"), tr(L"No saved custom MC options found. Please save from an instance first.", L"저장된 커스텀 MC 옵션이 없어. 먼저 원하는 인스턴스에서 저장해 줘."), false, ReportTone::Error);
			return;
		}
		std::wstring msg = tr(L"Overwrite options.txt of '", L"'") + instance.name + tr(L"' with custom MC options?\nMake sure Minecraft is closed.", L"' 인스턴스의 options.txt를 내 커스텀 MC 옵션으로 덮어씌울까?\n마인크래프트가 실행 중이라면 종료하고 진행해.");
		if(!report(tr(L"Confirm overwrite", L"덮어씌우기 확인"), msg, true, ReportTone::Warning)) return;
		auto dst = gameDir(instance) / L"options.txt";
		fs::create_directories(dst.parent_path());
		fs::copy_file(src, dst, fs::copy_options::overwrite_existing);
		report(tr(L"Options applied", L"덮어씌우기 완료"), tr(L"Custom MC options applied to '", L"'") + instance.name + tr(L"' successfully.", L"' 인스턴스에 성공적으로 덮어씌웠어."), false, ReportTone::Success);
	} catch(const std::exception& e) {
		report(tr(L"Apply failed", L"덮어씌우기 실패"), utf8ToWide(e.what()), false, ReportTone::Error);
	}
}

static void saveCustomFabricConfig(const Instance& instance) {
	try {
		auto srcDir = gameDir(instance) / L"config";
		auto dstDir = settingsDir / L"custom_fabric";
		fs::create_directories(dstDir);
		int savedCount = 0;
		std::wstring fileList;
		for(auto name : FABRIC_CONFIG_FILES) {
			auto src = srcDir / name;
			if(fs::exists(src)) {
				fs::copy_file(src, dstDir / name, fs::copy_options::overwrite_existing);
				savedCount++;
				fileList += L"  - " + std::wstring(name) + L"\n";
			}
		}
		if(savedCount == 0) {
			report(tr(L"Save failed", L"저장 실패"), tr(L"No sodium fabric config files found in this instance.", L"해당 인스턴스 config 폴더에 sodium 관련 설정 파일이 없어."), false, ReportTone::Warning);
			return;
		}
		std::wstring msg = tr(L"Saved ", L"총 ") + std::to_wstring(savedCount) + tr(L" Fabric config file(s):\n\n", L"개의 패브릭 설정 파일을 저장했어:\n\n") + fileList;
		report(tr(L"Fabric settings saved", L"저장 완료"), msg, false, ReportTone::Success);
	} catch(const std::exception& e) {
		report(tr(L"Save failed", L"저장 실패"), utf8ToWide(e.what()), false, ReportTone::Error);
	}
}

static void applyCustomFabricConfig(const Instance& instance) {
	try {
		auto srcDir = settingsDir / L"custom_fabric";
		std::vector<const wchar_t*> available;
		for(auto name : FABRIC_CONFIG_FILES) {
			if(fs::exists(srcDir / name)) available.push_back(name);
		}
		if(available.empty()) {
			report(tr(L"Apply failed", L"덮어씌우기 실패"), tr(L"No saved custom Fabric settings found. Please save from an instance first.", L"저장된 커스텀 패브릭 설정이 없어. 먼저 원하는 인스턴스에서 저장해 줘."), false, ReportTone::Error);
			return;
		}
		std::wstring fileList;
		for(auto name : available) fileList += L"  - " + std::wstring(name) + L"\n";
		std::wstring msg = tr(L"Overwrite Fabric config of '", L"'") + instance.name + tr(L"' with custom settings?\n\nFiles to apply:\n", L"' 인스턴스의 패브릭 설정을 저장된 커스텀 설정으로 덮어씌울까?\n\n적용할 파일 목록:\n") + fileList + tr(L"\nMake sure Minecraft is closed.", L"\n마인크래프트가 실행 중이라면 종료하고 진행해.");
		if(!report(tr(L"Confirm overwrite", L"덮어씌우기 확인"), msg, true, ReportTone::Warning)) return;
		auto dstDir = gameDir(instance) / L"config";
		fs::create_directories(dstDir);
		for(auto name : available) {
			fs::copy_file(srcDir / name, dstDir / name, fs::copy_options::overwrite_existing);
		}
		report(tr(L"Fabric settings applied", L"덮어씌우기 완료"), tr(L"Successfully applied custom Fabric settings to '", L"'") + instance.name + tr(L"'.", L"' 인스턴스에 커스텀 패브릭 설정을 덮어씌웠어."), false, ReportTone::Success);
	} catch(const std::exception& e) {
		report(tr(L"Apply failed", L"덮어씌우기 실패"), utf8ToWide(e.what()), false, ReportTone::Error);
	}
}

static std::string cleanMcVer(std::string ver) {
	std::string out;
	for(char c : ver) out += (char)tolower((unsigned char)c);
	auto pos = out.find("minecraft");
	if(pos != std::string::npos) out.erase(pos, 9);
	pos = out.find("mc");
	if(pos != std::string::npos) out.erase(pos, 2);
	while(!out.empty() && (out.front()==' ' || out.front()=='\t' || out.front()=='-' || out.front()=='_')) out.erase(out.begin());
	while(!out.empty() && (out.back()==' ' || out.back()=='\t' || out.back()=='-' || out.back()=='_')) out.pop_back();
	return out;
}

static bool isMcVersionMatching(const std::string& assetMc, const std::string& currentMc) {
	std::string ca = cleanMcVer(assetMc);
	std::string cc = cleanMcVer(currentMc);
	if(ca.empty() || cc.empty()) return false;
	return ca == cc || ca.starts_with(cc) || cc.starts_with(ca);
}

static bool isVersionNewer(const std::string& candidate, const std::string& current) {
	auto split = [](const std::string& s) {
		std::vector<int> parts;
		size_t start = 0;
		while(start < s.size()) {
			auto dot = s.find('.', start);
			std::string token = s.substr(start, dot == std::string::npos ? std::string::npos : dot - start);
			std::string num;
			for(char c : token) if(c >= '0' && c <= '9') num += c;
			parts.push_back(num.empty() ? 0 : std::stoi(num));
			if(dot == std::string::npos) break;
			start = dot + 1;
		}
		return parts;
	};
	try {
		auto cParts = split(candidate);
		auto curParts = split(current);
		size_t len = (std::max)(cParts.size(), curParts.size());
		for(size_t i = 0; i < len; i++) {
			int cVal = i < cParts.size() ? cParts[i] : 0;
			int curVal = i < curParts.size() ? curParts[i] : 0;
			if(cVal > curVal) return true;
			if(cVal < curVal) return false;
		}
	} catch(...) {
		return false;
	}
	return false;
}

static void checkAndDownloadMods(const Instance& in) {
	if(busy) return;
	Instance target = in;
	startWork(WorkKind::UpdateMods, [target](WorkEvent& event) {
		auto game = gameDir(target);
		std::string mcVer = cleanMcVer(wideToUtf8(target.version));
		if(mcVer.empty() || mcVer == "minecraft" || mcVer.find("metadata") != std::string::npos) {
			mcVer = cleanMcVer(wideToUtf8(target.id));
		}
		if(mcVer.empty()) throw std::runtime_error("Instance Minecraft version could not be determined");

		auto modsDir = game / L"mods";
		fs::create_directories(modsDir);

		struct ModSpec {
			std::string name;
			std::string repo;
			std::vector<std::string> prefixes;
		};
		std::vector<ModSpec> specs = {
			{ "SilenceUtils", "SILENCE-SIMSOOL/SilenceUtils", { "silenceutils" } },
			{ "LucentClient", "SILENCE-SIMSOOL/Lucent-Client", { "lucentclient", "lucent-client" } }
		};

		static const std::regex FILENAME_PATTERN(
			R"(^([A-Za-z0-9_.-]+)-([0-9]+(?:\.[0-9]+)+)-mc([A-Za-z0-9_.-]+)\.jar$)",
			std::regex_constants::icase
		);

		std::vector<std::wstring> results;
		bool anyUpdated = false;

		for(const auto& spec : specs) {
			syncer::check(cancelWork);

			// 1. Scan existing jars in modsDir
			std::string installedVer;
			std::vector<fs::path> oldFiles;
			std::error_code ec;
			for(auto& entry : fs::directory_iterator(modsDir, ec)) {
				if(!entry.is_regular_file(ec)) continue;
				auto fname = wideToUtf8(entry.path().filename().wstring());
				std::string lowerName;
				for(char c : fname) lowerName += (char)tolower((unsigned char)c);
				if(!lowerName.ends_with(".jar")) continue;

				bool matchPrefix = false;
				for(const auto& p : spec.prefixes) {
					if(lowerName.starts_with(p)) { matchPrefix = true; break; }
				}
				if(!matchPrefix) continue;

				std::smatch m;
				if(std::regex_match(fname, m, FILENAME_PATTERN)) {
					std::string fileModVer = m[2].str();
					std::string fileMcVer = m[3].str();
					if(isMcVersionMatching(fileMcVer, mcVer)) {
						oldFiles.push_back(entry.path());
						if(installedVer.empty() || isVersionNewer(fileModVer, installedVer)) {
							installedVer = fileModVer;
						}
					}
				}
			}

			// 2. Fetch releases from GitHub API
			publishProgress(utf8ToWide(spec.name) + L": " + tr(L"Checking updates...", L"업데이트 확인 중..."), 0, 0, 0, 0);
			std::ostringstream body;
			std::wstring apiUrl = L"https://api.github.com/repos/" + utf8ToWide(spec.repo) + L"/releases";
			updater::fetch(apiUrl, body, 10 * 1024 * 1024, cancelWork);
			auto releasesJson = syncer::Json::parse(body.str());

			// 3. Find best asset
			struct BestAsset {
				std::string name;
				std::string version;
				std::string downloadUrl;
				uint64_t size = 0;
			};
			BestAsset best;
			if(releasesJson.is_array()) {
				for(const auto& rel : releasesJson) {
					if(rel.value("draft", false)) continue;
					auto assetsIt = rel.find("assets");
					if(assetsIt == rel.end() || !assetsIt->is_array()) continue;
					for(const auto& asset : *assetsIt) {
						std::string assetName = asset.value("name", "");
						std::string lowerAsset;
						for(char c : assetName) lowerAsset += (char)tolower((unsigned char)c);
						if(lowerAsset.find("-library") != std::string::npos || lowerAsset.find("-lite") != std::string::npos) continue;

						std::smatch m;
						if(std::regex_match(assetName, m, FILENAME_PATTERN)) {
							std::string modName = m[1].str();
							std::string modVer = m[2].str();
							std::string assetMc = m[3].str();
							bool modNameMatches = (_stricmp(modName.c_str(), spec.name.c_str()) == 0);
							if(spec.name == "LucentClient" && _stricmp(modName.c_str(), "Lucent-Client") == 0) modNameMatches = true;

							if(modNameMatches && isMcVersionMatching(assetMc, mcVer)) {
								if(best.name.empty() || isVersionNewer(modVer, best.version)) {
									best.name = assetName;
									best.version = modVer;
									best.downloadUrl = asset.value("browser_download_url", "");
									best.size = asset.value("size", (uint64_t)0);
								}
							}
						}
					}
				}
			}

			if(best.name.empty()) {
				results.push_back(utf8ToWide(spec.name) + L": " + tr(L"No release found for MC ", L"MC ") + utf8ToWide(mcVer) + tr(L"", L" 버전에 맞는 릴리즈가 없어."));
				continue;
			}

			if(!installedVer.empty() && !isVersionNewer(best.version, installedVer)) {
				results.push_back(utf8ToWide(spec.name) + L": " + tr(L"Already up to date (v", L"이미 최신 버전이야 (v") + utf8ToWide(installedVer) + L")");
				continue;
			}

			// 4. Download and update
			bool isUpdate = !installedVer.empty();
			auto targetJar = modsDir / utf8ToWide(best.name);
			auto tempJar = modsDir / utf8ToWide(best.name + ".part");

			publishProgress(utf8ToWide(best.name), 0, best.size, 0, 1);
			std::ofstream out(tempJar, std::ios::binary | std::ios::trunc);
			if(!out) throw std::runtime_error("Cannot create temp file: " + wideToUtf8(tempJar.wstring()));
			updater::fetch(utf8ToWide(best.downloadUrl), out, 500ull * 1024 * 1024, cancelWork, [&](uint64_t bytes) {
				publishProgress(utf8ToWide(best.name), bytes, best.size, 0, 1);
			});
			out.close();

			syncer::flush(tempJar);
			MoveFileExW(tempJar.c_str(), targetJar.c_str(), MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH);

			int cleaned = 0;
			for(const auto& oldPath : oldFiles) {
				if(_wcsicmp(oldPath.wstring().c_str(), targetJar.wstring().c_str()) != 0) {
					std::error_code ecRemove;
					fs::remove(oldPath, ecRemove);
					cleaned++;
				}
			}

			if(isUpdate) {
				results.push_back(utf8ToWide(spec.name) + L": v" + utf8ToWide(installedVer) + L" -> v" + utf8ToWide(best.version) + tr(L" updated", L" 업데이트 완료") + (cleaned > 0 ? tr(L" (old jar deleted)", L" (구버전 파일 삭제됨)") : L""));
			} else {
				results.push_back(utf8ToWide(spec.name) + L": v" + utf8ToWide(best.version) + tr(L" downloaded & installed", L" 다운로드 및 설치 완료"));
			}
			anyUpdated = true;
		}

		event.modTitle = tr(L"Mod Download & Update", L"모드 다운로드 및 업데이트");
		event.modSummary = tr(L"Instance: ", L"인스턴스: ") + target.name + tr(L" · MC Version: ", L" · MC 버전: ") + utf8ToWide(mcVer);
		event.modTone = anyUpdated ? ReportTone::Success : ReportTone::Info;
		std::wstring details;
		for(const auto& r : results) {
			details += L"• " + r + L"\n\n";
		}
		event.modDetails = details;
	});
}
static void setOptionsScroll(int value,int height) {
	optionsScroll=std::clamp(value,0,std::max(0,546-height)); langDropdownOpen=false; redraw(windowHandle);
}

static void interact(int x,int y,int width) {
	if(busy) {
		if(x>=24 && x<=166 && y>=450 && y<=490) { cancelWork=true; status=tr(L"Cancelling...",L"취소 중..."); }
		return;
	}
	if(!contextId.empty() && !contextRect.Contains(x,y)) { contextId.clear(); redraw(windowHandle); return; }
	if(langDropdownOpen && !(x>=width-244 && x<=width-24 && y>=96-optionsScroll && y<=280-optionsScroll)) {
		langDropdownOpen=false;
		redraw(windowHandle);
	}

	for(auto it=clicks.rbegin();it!=clicks.rend();++it) {
		if(!it->r.Contains(x,y)) continue;
		int kind=it->kind, index=it->index;
		switch(kind) {
		case 1: optionsPage=index==1; status.clear(); langDropdownOpen=false; ShowWindow(searchWindow,optionsPage?SW_HIDE:SW_SHOW); keyboardFocus=-1; contextId.clear(); break;
		case 2: langDropdownOpen=!langDropdownOpen; break;
		case 3: enabled[index]=!enabled[index]; persist(); break;
		case 4: { fs::path p; if(chooseFolder(p)){ prismDir=p; mainId.clear(); refresh(); scrollPosition=0; } } break;
		case 5: choosingMain=!choosingMain; selectedId.clear(); break;
		case 6: {
			int i=0;
			for(auto& in:instances) if(visibleInstance(in)) {
				if(i++==index) {
					if(choosingMain) {
						setMainInstance(in.id);
					} else {
						selectedId=in.id;
					}
					break;
				}
			}
		}break;
		case 7: {
			int tw,tx;
			scrollGeometry(width,tw,tx);
			draggingScroll=true;
			dragOffset=x>=tx && x<=tx+tw?x-tx:tw/2;
			setScroll((x-24-dragOffset)*maxScrollFor(width)/std::max(1,width-48-tw),width);
			SetCapture(windowHandle);
		}break;
		case 14: {
			RECT client; GetClientRect(windowHandle,&client);
			draggingOptions=true; optionDragOffset=optionThumb.Contains(x,y)?y-optionThumb.Y:optionThumb.Height/2;
			setOptionsScroll((y-optionTrack.Y-optionDragOffset)*std::max(0,546-(int)(client.bottom/dpiScale))/std::max(1,optionTrack.Height-optionThumb.Height),(int)(client.bottom/dpiScale));
			SetCapture(windowHandle);
		} break;
		case 15: { auto instance=lookup(contextId); contextId.clear(); if(instance) openInstanceFolder(*instance); } break;
		case 16: { auto id=contextId; contextId.clear(); setMainInstance(id); } break;
		case 17: { auto instance=lookup(contextId); contextId.clear(); if(instance) saveCustomMcOptions(*instance); } break;
		case 18: { auto instance=lookup(contextId); contextId.clear(); if(instance) applyCustomMcOptions(*instance); } break;
		case 19: { auto instance=lookup(contextId); contextId.clear(); if(instance) saveCustomFabricConfig(*instance); } break;
		case 20: { auto instance=lookup(contextId); contextId.clear(); if(instance) applyCustomFabricConfig(*instance); } break;
		case 21: { auto instance=lookup(contextId); contextId.clear(); if(instance) checkAndDownloadMods(*instance); } break;
		case 8: checkUpdates(); break;
		case 9: if(!choosingMain && lookup(selectedId)) applyTo(*lookup(selectedId)); break;
		case 10: setScroll(scrollX+index*(cardWidth+cardGap)*2,width); break;
		case 11: ShellExecuteW(windowHandle,L"open",settingsDir.c_str(),nullptr,nullptr,SW_SHOWNORMAL); break;
		case 12: {
			const wchar_t* codes[]={L"en",L"ko",L"zh",L"ja"};
			if(index>=0 && index<4) {
				language=codes[index];
				langDropdownOpen=false;
				persist();
			}
		}break;
		}
		redraw(windowHandle);
		return;
	}
}

static LRESULT CALLBACK wndProc(HWND hwnd,UINT msg,WPARAM wParam,LPARAM lParam) {
	switch(msg) {
	case WM_PAINT: {
		PAINTSTRUCT ps;
		HDC hdc=BeginPaint(hwnd,&ps);
		RECT rc;
		GetClientRect(hwnd,&rc);
		if(rc.right>0 && rc.bottom>0) {
			if(!paintBuffer || paintBuffer->GetWidth()!=(UINT)rc.right || paintBuffer->GetHeight()!=(UINT)rc.bottom)
				paintBuffer=std::make_unique<Bitmap>(rc.right,rc.bottom,PixelFormat32bppRGB);
			Graphics back(paintBuffer.get());
			back.ScaleTransform(dpiScale,dpiScale);
			paint(back,(int)(rc.right/dpiScale),(int)(rc.bottom/dpiScale));
			if(keyboardFocus>=0 && keyboardFocus<(int)clicks.size()) {
				Pen focus(rgb(20,117,255),1.f); focus.SetDashStyle(DashStyleDash);
				back.DrawRectangle(&focus,clicks[keyboardFocus].r);
			}
			Graphics g(hdc);
			g.DrawImage(paintBuffer.get(),0,0);
		}
		EndPaint(hwnd,&ps);
		return 0;
	}
	case WM_ERASEBKGND: return 1;
	case WM_GETMINMAXINFO: {
		auto info=(MINMAXINFO*)lParam;
		info->ptMinTrackSize={(LONG)(820*dpiScale),(LONG)outerHeight(pageHeight())};
		return 0;
	}
	case WM_LBUTTONDOWN: {
		RECT rc;
		GetClientRect(hwnd,&rc);
		auto clicked=contextId.empty()?instanceAt((int)(GET_X_LPARAM(lParam)/dpiScale),(int)(GET_Y_LPARAM(lParam)/dpiScale)):nullptr;
		lastClickedInstance=clicked?clicked->id:L"";
		SetFocus(hwnd); keyboardFocus=-1;
		interact((int)(GET_X_LPARAM(lParam)/dpiScale),(int)(GET_Y_LPARAM(lParam)/dpiScale),(int)(rc.right/dpiScale));
		return 0;
	}
	case WM_RBUTTONUP: {
		if(busy || optionsPage) return 0;
		int x=(int)(GET_X_LPARAM(lParam)/dpiScale), y=(int)(GET_Y_LPARAM(lParam)/dpiScale);
		auto instance=instanceAt(x,y);
		contextId=instance?instance->id:L""; contextRect=Rect(x,y,0,0); keyboardFocus=-1; redraw(hwnd); return 0;
	}
	case WM_LBUTTONDBLCLK: {
		if(!busy && !optionsPage) {
			auto instance=lookup(lastClickedInstance);
			if(instance) openInstanceFolder(*instance);
		}
		return 0;
	}
	case WM_KILLFOCUS:
		if(!contextId.empty()) { contextId.clear(); redraw(hwnd); }
		return 0;
	case WM_LBUTTONUP:
		if(draggingScroll || draggingOptions) { draggingScroll=false; draggingOptions=false; ReleaseCapture(); }
		return 0;
	case WM_CAPTURECHANGED:
		draggingScroll=false; draggingOptions=false;
		return 0;
	case WM_MOUSEMOVE: {
		int x=(int)(GET_X_LPARAM(lParam)/dpiScale),y=(int)(GET_Y_LPARAM(lParam)/dpiScale);
		if(draggingOptions) {
			RECT client; GetClientRect(hwnd,&client);
			setOptionsScroll((y-optionTrack.Y-optionDragOffset)*std::max(0,546-(int)(client.bottom/dpiScale))/std::max(1,optionTrack.Height-optionThumb.Height),(int)(client.bottom/dpiScale));
			return 0;
		}
		if(draggingScroll) {
			RECT rc;
			GetClientRect(hwnd,&rc);
			int tw,tx;
			scrollGeometry((int)(rc.right/dpiScale),tw,tx);
			setScroll((x-24-dragOffset)*maxScrollFor((int)(rc.right/dpiScale))/std::max(1,(int)(rc.right/dpiScale)-48-tw),(int)(rc.right/dpiScale));
			redraw(hwnd);
			return 0;
		}
		int kind=-1,index=-1;
		for(auto it=clicks.rbegin();it!=clicks.rend();++it) {
			if(it->r.Contains(x,y)) { kind=it->kind; index=it->index; break; }
		}
		SetCursor(LoadCursor(nullptr,kind<0?IDC_ARROW:IDC_HAND));
		if(kind!=hoveredKind || index!=hoveredIndex) {
			hoveredKind=kind;
			hoveredIndex=index;
			redraw(hwnd);
		}
		TRACKMOUSEEVENT track{sizeof(track),TME_LEAVE,hwnd,0};
		TrackMouseEvent(&track);
		return 0;
	}
	case WM_MOUSELEAVE:
		hoveredKind=-1;
		hoveredIndex=-1;
		redraw(hwnd);
		return 0;
	case WM_MOUSEWHEEL:
	case WM_MOUSEHWHEEL: {
		POINT pt{GET_X_LPARAM(lParam),GET_Y_LPARAM(lParam)};
		ScreenToClient(hwnd,&pt);
		pt.y=(LONG)(pt.y/dpiScale);
		if(optionsPage && msg==WM_MOUSEWHEEL) {
			RECT client; GetClientRect(hwnd,&client);
			setOptionsScroll(optionsScroll-GET_WHEEL_DELTA_WPARAM(wParam)*36/WHEEL_DELTA,(int)(client.bottom/dpiScale)); return 0;
		}
		if(!optionsPage && pt.y>=listTop && pt.y<trackY+24) {
			RECT rc;
			GetClientRect(hwnd,&rc);
			int delta=GET_WHEEL_DELTA_WPARAM(wParam);
			setScroll(scrollX+(msg==WM_MOUSEHWHEEL?delta:-delta)*90/WHEEL_DELTA,(int)(rc.right/dpiScale));
			redraw(hwnd);
		}
		return 0;
	}
	case WORK_PROGRESS: {
		std::lock_guard lock(workMutex); status=workProgress; redraw(hwnd); return 0;
	}
	case WORK_DONE: finishWork(); return 0;
	case WM_CTLCOLOREDIT:
		if((HWND)lParam==searchWindow) {
			SetTextColor((HDC)wParam,RGB(51,65,85));
			SetBkColor((HDC)wParam,RGB(248,250,252));
			return (LRESULT)searchBrush;
		}
		break;
	case WM_COMMAND:
		if((HWND)lParam==searchWindow && HIWORD(wParam)==EN_CHANGE) {
			int length=GetWindowTextLengthW(searchWindow);
			std::wstring text(length+1,L'\0'); GetWindowTextW(searchWindow,text.data(),length+1); text.resize(length);
			searchText=std::move(text); scrollX=0; scrollPosition=0; keyboardFocus=-1; redraw(hwnd);
		}
		return 0;
	case WM_DPICHANGED: {
		dpiScale=HIWORD(wParam)/96.f;
		if(searchFont) DeleteObject(searchFont);
		searchFont=CreateFontW(-(int)(13*dpiScale),0,0,0,FW_NORMAL,FALSE,FALSE,FALSE,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Segoe UI");
		SendMessageW(searchWindow,WM_SETFONT,(WPARAM)searchFont,TRUE);
		auto rect=(RECT*)lParam;
		SetWindowPos(hwnd,nullptr,rect->left,rect->top,rect->right-rect->left,rect->bottom-rect->top,SWP_NOZORDER|SWP_NOACTIVATE);
		return 0;
	}
	case WM_KEYDOWN:
		if(wParam==VK_ESCAPE && busy) { cancelWork=true; return 0; }
		if(busy) return 0;
		if(wParam==VK_ESCAPE && !contextId.empty()) { contextId.clear(); redraw(hwnd); return 0; }
		if(optionsPage && (wParam==VK_UP || wParam==VK_DOWN || wParam==VK_PRIOR || wParam==VK_NEXT)) {
			RECT client; GetClientRect(hwnd,&client);
			setOptionsScroll(optionsScroll+((wParam==VK_UP || wParam==VK_PRIOR)?-1:1)*((wParam==VK_PRIOR || wParam==VK_NEXT)?120:32),(int)(client.bottom/dpiScale)); return 0;
		}
		if(wParam=='F' && (GetKeyState(VK_CONTROL)&0x8000) && !optionsPage) { SetFocus(searchWindow); return 0; }
		if(wParam==VK_TAB && !clicks.empty()) {
			int count=(int)clicks.size();
			keyboardFocus=(keyboardFocus+((GetKeyState(VK_SHIFT)&0x8000)?count-1:1)+count)%count;
			redraw(hwnd); return 0;
		}
		if((wParam==VK_RETURN || wParam==VK_SPACE) && keyboardFocus>=0 && keyboardFocus<(int)clicks.size()) {
			auto r=clicks[keyboardFocus].r; RECT client; GetClientRect(hwnd,&client);
			interact(r.X+r.Width/2,r.Y+r.Height/2,(int)(client.right/dpiScale)); return 0;
		}
		if(!optionsPage && (wParam==VK_LEFT || wParam==VK_RIGHT)) {
			RECT rc;
			GetClientRect(hwnd,&rc);
			setScroll(scrollX+(wParam==VK_LEFT?-116:116),(int)(rc.right/dpiScale));
			return 0;
		}
		break;
	case WM_TIMER: {
		ULONGLONG now=GetTickCount64();
		float dt=(lastFrame>0 && now>=lastFrame)?(float)(now-lastFrame):10.f;
		if(dt>100.f) dt=10.f;
		lastFrame=now;
		bool changed=false;
		auto move=[&](float& value,float target,float speed) {
			if(std::abs(value-target)>.002f) {
				value+=(target-value)*(1.f-std::exp(-dt/speed));
				if(std::abs(value-target)<.004f) value=target;
				changed=true;
			}
		};
		move(tabPosition,optionsPage?1.f:0.f,70.f);
		move(scrollPosition,(float)scrollX,55.f);
		move(choosingMainAnim,choosingMain?1.f:0.f,70.f);
		move(langDropdownAnim,langDropdownOpen?1.f:0.f,50.f);
		for(int i=0;i<7;i++) move(togglePosition[i],enabled[i]?1.f:0.f,50.f);

		bool isHoverLeft=(hoveredKind==10 && hoveredIndex==-1);
		bool isHoverRight=(hoveredKind==10 && hoveredIndex==1);
		move(navHoverLeft,isHoverLeft?1.f:0.f,40.f);
		move(navHoverRight,isHoverRight?1.f:0.f,40.f);
		move(btnApplyHover,(hoveredKind==9)?1.f:0.f,40.f);
		move(btnChangeHover,(hoveredKind==5)?1.f:0.f,40.f);
		move(btnUpdateHover,(hoveredKind==8)?1.f:0.f,40.f);

		for(int i=0;i<32;i++) {
			bool h=(hoveredKind==6 && hoveredIndex==i);
			move(cardHover[i],h?1.f:0.f,45.f);
		}

		if(changed) InvalidateRect(hwnd,nullptr,FALSE);
		else KillTimer(hwnd,1);
		return 0;
	}
	case WM_SIZE:
		optionsScroll=std::clamp(optionsScroll,0,std::max(0,546-(int)(HIWORD(lParam)/dpiScale))); contextId.clear();
		if(searchWindow) MoveWindow(searchWindow,(int)(LOWORD(lParam)-322*dpiScale),(int)(255*dpiScale),(int)(202*dpiScale),(int)(18*dpiScale),TRUE);
		redraw(hwnd);
		return 0;
	case WM_CLOSE:
		if(busy) { closing=true; cancelWork=true; status=tr(L"Cancelling before closing...",L"작업을 취소한 뒤 종료 중..."); return 0; }
		DestroyWindow(hwnd); return 0;
	case WM_DESTROY:
		cancelWork=true;
		if(worker.joinable()) worker.join();
		KillTimer(hwnd,1);
		PostQuitMessage(0);
		return 0;
	}
	return DefWindowProcW(hwnd,msg,wParam,lParam);
}

int WINAPI wWinMain(HINSTANCE hInstance,HINSTANCE,LPWSTR,int nCmdShow) {
	SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
	CoInitializeEx(nullptr,COINIT_APARTMENTTHREADED);
	GdiplusStartupInput si;
	GdiplusStartup(&gdiplusToken,&si,nullptr);
	load();
	fontSetup();
	refresh();
	for(int i=0;i<7;i++) togglePosition[i]=enabled[i]?1.f:0.f;
	animations=true;
	WNDCLASSEXW wc{sizeof(wc)};
	wc.style=CS_DBLCLKS;
	wc.lpfnWndProc=wndProc;
	wc.hInstance=hInstance;
	wc.lpszClassName=L"PrismSyncWindow";
	wc.hCursor=LoadCursor(nullptr,IDC_ARROW);
	wc.hIcon=LoadIconW(hInstance,MAKEINTRESOURCEW(1));
	wc.hbrBackground=(HBRUSH)(COLOR_WINDOW+1);
	RegisterClassExW(&wc);
	dpiScale=GetDpiForSystem()/96.f;
	windowHandle=CreateWindowExW(0,wc.lpszClassName,APP_TITLE.c_str(),WS_OVERLAPPEDWINDOW|WS_CLIPCHILDREN|WS_VISIBLE,CW_USEDEFAULT,CW_USEDEFAULT,(int)(900*dpiScale),outerHeight(pageHeight()),nullptr,nullptr,hInstance,nullptr);
	dpiScale=GetDpiForWindow(windowHandle)/96.f;
	createSearch(windowHandle,hInstance);
	RECT client; GetClientRect(windowHandle,&client);
	SendMessageW(windowHandle,WM_SIZE,0,MAKELPARAM(client.right,client.bottom));
	lastFrame=GetTickCount64();
	SetTimer(windowHandle,1,10,nullptr);
	ShowWindow(windowHandle,nCmdShow);
	UpdateWindow(windowHandle);
	MSG msg;
	while(GetMessageW(&msg,nullptr,0,0)>0) {
		if(msg.hwnd==searchWindow && msg.message==WM_KEYDOWN && (msg.wParam==VK_TAB || msg.wParam==VK_ESCAPE)) {
			SetFocus(windowHandle); continue;
		}
		TranslateMessage(&msg);
		DispatchMessageW(&msg);
	}
	if(searchFont) DeleteObject(searchFont);
	if(searchBrush) DeleteObject(searchBrush);
	paintBuffer.reset();
	iconCache.clear();
	iconFamily.reset();
	regularFamily.reset();
	mediumFamily.reset();
	semiboldFamily.reset();
	boldFamily.reset();
	iconFonts.reset();
	boldColl.reset();
	semiColl.reset();
	medColl.reset();
	privateFonts.reset();
	GdiplusShutdown(gdiplusToken);
	CoUninitialize();
	return 0;
}