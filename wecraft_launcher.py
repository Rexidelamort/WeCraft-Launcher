"""
WeCraft - Launcher Minecraft - Python + Tkinter
Dépendance : pip install -U minecraft-launcher-lib   (version 8 ou plus récente)
Facultatif : pip install pillow   (icônes des mods en jpg / webp, logo plus net)

Principe : déposez un dossier d'instance dans le dossier « instances » (%APPDATA%/.wecraft/instances) :
un bouton LANCER apparaît automatiquement. Les instances CurseForge, Modrinth ou Prism
(version + mod loader lus automatiquement) restent aussi utilisables en mode manuel. Au clic sur LANCER, il installe si besoin la version et
le loader, crée (ou met à jour) le profil « WECRAFT - <instance> » dans le
launcher officiel avec le dossier de jeu de l'instance, puis ouvre le launcher officiel. La connexion
Microsoft et le lancement du jeu restent gérés par le launcher officiel.
"""
import base64
import ctypes
import hashlib
import importlib
import io
import json
import math
import os
import re
import shutil
import sqlite3
import stat
import subprocess
import sys
import uuid
import threading
import urllib.error
import urllib.parse
import urllib.request
import time
import tkinter as tk
import tkinter.font as tkfont
import webbrowser
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

import minecraft_launcher_lib as mll

LOADERS = {"Vanilla": None, "Fabric": "fabric", "Forge": "forge",
           "NeoForge": "neoforge", "Quilt": "quilt"}

SYSTEM_MC_DIR = mll.utils.get_minecraft_directory()   # .minecraft officiel : jamais modifié
MC_DIR = SYSTEM_MC_DIR.replace("minecraft", "wecraft")  # réglages + instance par défaut
_OLD_DIR = Path(SYSTEM_MC_DIR.replace("minecraft", "mon_launcher"))  # ancien nom : réglages repris
CONFIG_FILE = Path(MC_DIR) / "launcher_config.json"
if not CONFIG_FILE.exists() and (_OLD_DIR / "launcher_config.json").exists():
    try:
        CONFIG_FILE.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(_OLD_DIR / "launcher_config.json", CONFIG_FILE)
    except Exception:
        pass
FROZEN = getattr(sys, "frozen", False)  # True quand le launcher est un .exe (PyInstaller)
APP_DIR = Path(sys.executable).parent if FROZEN else Path(__file__).resolve().parent
INSTANCES_DIR = Path(MC_DIR) / "instances"  # %APPDATA%/.wecraft/instances : un sous-dossier = une instance
RES_DIR = Path(getattr(sys, "_MEIPASS", APP_DIR))  # assets/ et fonts/ intégrés au .exe

# Mises à jour automatiques via les « Releases » GitHub (dépôt PUBLIC)
APP_VERSION = "1.2.0"  # mis à jour automatiquement par le workflow GitHub à chaque release
GITHUB_REPO = "Rexidelamort/WeCraft-Launcher"  # rempli automatiquement par le workflow GitHub

# Charte WeCraft : noir spatial, blanc chaud, dégradé braise, bleu étoilé
BG, PANEL, FG = "#05060C", "#0F1424", "#EEECE4"
MUTED, BORDER, FIELD = "#7F89A8", "#1C2340", "#080B15"
EMBER1, EMBER2, BLUE = "#FF5A36", "#FFB84D", "#6F8DFF"
ACCENT, AMBER = EMBER1, EMBER2
CUSTOM_MARK = "★ "  # préfixe des versions déjà installées (modées / personnalisées)


# ---------------------------------------------------------------- utilitaires
LOADER_NAMES = {"neoforge": "NeoForge", "forge": "Forge", "fabric": "Fabric", "quilt": "Quilt"}


def parse_loader(text, mc_version=None):
    """'forge-47.2.0' -> ('Forge', '47.2.0') ; 'fabric-0.15.7-1.20.1' -> ('Fabric', '0.15.7')."""
    text = (text or "").strip().lower()
    for key, nice in LOADER_NAMES.items():  # neoforge est testé avant forge
        if text.startswith(key):
            ver = text[len(key):].lstrip("-_ ") or None
            if ver and mc_version and ver.endswith("-" + mc_version):
                ver = ver[: -len(mc_version) - 1]
            return nice, ver
    return None, None


def read_curseforge(folder):
    d = json.loads((folder / "minecraftinstance.json").read_text(encoding="utf-8"))
    base = d.get("baseModLoader") or {}
    mc = d.get("gameVersion") or base.get("minecraftVersion")
    loader, lv = parse_loader(base.get("name"), mc)
    return d.get("name") or folder.name, mc, loader, lv


def read_prism(inst_dir):
    pack = json.loads((inst_dir / "mmc-pack.json").read_text(encoding="utf-8"))
    uids = {"net.minecraftforge": "Forge", "net.neoforged": "NeoForge",
            "net.fabricmc.fabric-loader": "Fabric", "org.quiltmc.quilt-loader": "Quilt"}
    mc = loader = lv = None
    for comp in pack.get("components", []):
        if comp.get("uid") == "net.minecraft":
            mc = comp.get("version")
        elif comp.get("uid") in uids:
            loader, lv = uids[comp["uid"]], comp.get("version")
    name = inst_dir.name
    try:
        m = re.search(r"^name=(.*)$", (inst_dir / "instance.cfg").read_text(encoding="utf-8"), re.M)
        name = m.group(1).strip() if m else name
    except Exception:
        pass
    return name, mc, loader, lv


def read_modrinth_db(db_file, profiles_dir):
    """Lit la base SQLite de l'app Modrinth (lecture seule)."""
    out = []
    con = sqlite3.connect(db_file.as_uri() + "?mode=ro", uri=True)
    try:
        con.row_factory = sqlite3.Row
        for r in con.execute("SELECT * FROM profiles").fetchall():
            keys = r.keys()
            get = lambda k: r[k] if k in keys else None
            loader = LOADER_NAMES.get(str(get("mod_loader") or "").lower())
            lv = get("mod_loader_version")
            out.append((profiles_dir / str(get("path")), get("name") or get("path"),
                        get("game_version"), loader, str(lv) if lv not in (None, "", "None") else None))
    finally:
        con.close()
    return out


def detect_instances():
    """Cherche les instances CurseForge, Modrinth et Prism (+ le .minecraft officiel) et lit leur
    version de Minecraft et leur mod loader. Seuls les emplacements habituels sont scannés."""
    home = Path.home()
    if sys.platform.startswith("win"):
        appdata = Path(os.environ.get("APPDATA", home / "AppData" / "Roaming"))
        prism, modrinth = appdata / "PrismLauncher", appdata / "ModrinthApp"
    elif sys.platform == "darwin":
        support = home / "Library" / "Application Support"
        prism, modrinth = support / "PrismLauncher", support / "com.modrinth.theseus"
    else:
        share = home / ".local" / "share"
        prism, modrinth = share / "PrismLauncher", share / "ModrinthApp"

    found = []

    def add(source, name, path, mc=None, loader=None, lv=None):
        found.append({"source": source, "name": name, "path": Path(path),
                      "version": mc, "loader": loader, "loader_version": lv})

    official = Path(SYSTEM_MC_DIR)
    if official.is_dir():
        add("Minecraft officiel", ".minecraft", official)

    # CurseForge : <dossier>/curseforge/minecraft/Instances/<nom>/minecraftinstance.json
    cf_roots = [home / "curseforge" / "minecraft" / "Instances",
                home / "Documents" / "curseforge" / "minecraft" / "Instances"]
    for cf in (c for c in cf_roots if c.is_dir()):
        for inst in sorted(cf.iterdir()):
            if not inst.is_dir():
                continue
            try:
                name, mc, loader, lv = read_curseforge(inst)
                add("CurseForge", name, inst, mc, loader, lv)
            except Exception:
                if any((inst / n).exists() for n in ("mods", "saves", "options.txt")):
                    add("CurseForge", inst.name, inst)

    # Modrinth : base app.db (sinon simple scan des dossiers)
    profiles_dir = modrinth / "profiles"
    try:
        for folder, name, mc, loader, lv in read_modrinth_db(modrinth / "app.db", profiles_dir):
            if folder.is_dir():
                add("Modrinth", name, folder, mc, loader, lv)
    except Exception:
        if profiles_dir.is_dir():
            for inst in sorted(profiles_dir.iterdir()):
                if inst.is_dir():
                    add("Modrinth", inst.name, inst)

    # Prism : <instances>/<nom>/{minecraft|.minecraft} + mmc-pack.json
    inst_root = prism / "instances"
    if inst_root.is_dir():
        for inst in sorted(inst_root.iterdir()):
            game = next((inst / n for n in ("minecraft", ".minecraft") if (inst / n).is_dir()), None)
            if not game:
                continue
            try:
                name, mc, loader, lv = read_prism(inst)
                add("Prism", name, game, mc, loader, lv)
            except Exception:
                add("Prism", inst.name, game)
    return found



def read_local_instance(folder):
    """Instance déposée dans « instances/ » : version et loader lus dans les fichiers présents
    (CurseForge, Prism, export CurseForge, export Modrinth) ou dans « wecraft.json » (prioritaire)."""
    inst = {"name": folder.name, "folder": folder, "path": folder, "version": None,
            "loader": None, "loader_version": None, "ram": None, "source": "WeCraft"}
    try:
        if (folder / "mmc-pack.json").exists():  # Prism : le jeu est dans le sous-dossier minecraft
            _, mc, loader, lv = read_prism(folder)
            inst.update(version=mc, loader=loader, loader_version=lv)
            game = next((folder / n for n in ("minecraft", ".minecraft") if (folder / n).is_dir()), None)
            if game:
                inst["path"] = game
        elif (folder / "minecraftinstance.json").exists():
            _, mc, loader, lv = read_curseforge(folder)
            inst.update(version=mc, loader=loader, loader_version=lv)
        elif (folder / "manifest.json").exists():  # export de modpack CurseForge
            mcd = json.loads((folder / "manifest.json").read_text(encoding="utf-8")).get("minecraft", {})
            loaders = mcd.get("modLoaders") or []
            main = next((l for l in loaders if l.get("primary")), loaders[0] if loaders else {})
            loader, lv = parse_loader(main.get("id"), mcd.get("version"))
            inst.update(version=mcd.get("version"), loader=loader, loader_version=lv)
        elif (folder / "modrinth.index.json").exists():  # export .mrpack
            deps = json.loads((folder / "modrinth.index.json").read_text(encoding="utf-8")).get("dependencies", {})
            inst["version"] = deps.get("minecraft")
            for key, nice in (("neoforge", "NeoForge"), ("forge", "Forge"),
                              ("fabric-loader", "Fabric"), ("quilt-loader", "Quilt")):
                if key in deps:
                    inst["loader"], inst["loader_version"] = nice, str(deps[key])
                    break
    except Exception:
        pass
    try:  # réglages propres à WeCraft : ils priment sur tout le reste
        cfg = json.loads((folder / "wecraft.json").read_text(encoding="utf-8"))
        if cfg.get("name"):
            inst["name"] = str(cfg["name"])
        if cfg.get("version"):
            inst["version"] = str(cfg["version"])
        if "loader" in cfg:
            inst["loader"] = cfg["loader"]
        if "loader_version" in cfg:
            inst["loader_version"] = cfg["loader_version"] or None
        if cfg.get("ram"):
            inst["ram"] = int(cfg["ram"])
    except Exception:
        pass
    if inst["loader"] not in LOADERS or inst["loader"] == "Vanilla":
        inst["loader"] = None
    if not inst["loader"]:
        inst["loader_version"] = None
    return inst


_LOCAL_CACHE = {}  # dossier -> (date de modification, instance lue) : évite de tout relire toutes les 3 s


def scan_instances():
    """Sous-dossiers de « instances/ » (ceux qui commencent par . ou _ sont ignorés).
    Seuls les dossiers nouveaux ou modifiés sont relus : reste rapide avec des milliers d'instances."""
    try:
        INSTANCES_DIR.mkdir(parents=True, exist_ok=True)
        with os.scandir(INSTANCES_DIR) as it:
            entries = sorted((e for e in it if e.is_dir() and not e.name.startswith((".", "_"))),
                             key=lambda e: e.name.lower())
    except Exception:
        return []
    out, seen = [], set()
    for e in entries:
        try:
            mtime = e.stat().st_mtime_ns
        except OSError:
            continue
        seen.add(e.path)
        hit = _LOCAL_CACHE.get(e.path)
        if hit and hit[0] == mtime:
            out.append(dict(hit[1]))
        else:
            inst = read_local_instance(Path(e.path))
            _LOCAL_CACHE[e.path] = (mtime, dict(inst))
            out.append(inst)
    for k in [k for k in _LOCAL_CACHE if k not in seen]:
        del _LOCAL_CACHE[k]
    return out



# ---- Toutes les instances (dossier WeCraft + CurseForge / Modrinth / Prism) et réglages perso
META_FILE = Path(MC_DIR) / "instances_meta.json"  # nom affiché, masquée, version/loader/RAM forcés
SOURCE_ORDER = {"WeCraft": 0, "CurseForge": 1, "Modrinth": 2, "Prism": 3}
PAGE_SIZE = 20  # instances affichées par page (reste fluide même avec 10 000 instances)
SORTS = ("Source puis nom", "Nom (A-Z)", "Nom (Z-A)", "Version (récente)", "Version (ancienne)")
SOURCE_LABEL = {"WeCraft": "WECRAFT", "CurseForge": "CURSEFORGE", "Modrinth": "MODRINTH", "Prism": "PRISM"}


def meta_key(folder):
    return os.path.normcase(str(folder))


def load_meta():
    try:
        data = json.loads(META_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def update_meta(folder, set=None, remove=()):
    """Enregistre des réglages pour une instance sans jamais modifier son dossier."""
    meta = load_meta()
    entry = meta.setdefault(meta_key(folder), {})
    entry.update(set or {})
    for k in remove:
        entry.pop(k, None)
    if not entry:
        meta.pop(meta_key(folder), None)
    META_FILE.parent.mkdir(parents=True, exist_ok=True)
    META_FILE.write_text(json.dumps(meta, indent=2, ensure_ascii=False), encoding="utf-8")


def forget_meta(folder):
    meta = load_meta()
    if meta.pop(meta_key(folder), None) is not None:
        META_FILE.write_text(json.dumps(meta, indent=2, ensure_ascii=False), encoding="utf-8")


def detect_external():
    """Instances CurseForge, Modrinth et Prism trouvées sur le PC."""
    out = []
    try:
        found = detect_instances()
    except Exception:
        return out
    for d in found:
        if d["source"] not in SOURCE_ORDER:
            continue  # le « .minecraft » officiel n'est pas listé ici
        path = Path(d["path"])
        out.append({"name": d["name"], "folder": path.parent if d["source"] == "Prism" else path,
                    "path": path, "version": d["version"], "loader": d["loader"],
                    "loader_version": d["loader_version"], "ram": None, "source": d["source"]})
    return out


def apply_meta(instances):
    """Applique nom affiché, masquage et réglages forcés (fichier instances_meta.json)."""
    meta = load_meta()
    for i in instances:
        m = meta.get(meta_key(i["folder"]), {})
        if m.get("version"):
            i["version"] = str(m["version"])
        if "loader" in m:
            i["loader"] = m["loader"]
        if "loader_version" in m:
            i["loader_version"] = m["loader_version"] or None
        if m.get("ram"):
            i["ram"] = int(m["ram"])
        if i["loader"] not in LOADERS or i["loader"] == "Vanilla":
            i["loader"] = None
        if not i["loader"]:
            i["loader_version"] = None
        i["display"] = (m.get("name") or "").strip() or i["name"]
        i["hidden"] = bool(m.get("hidden"))
        i["_hay"] = f"{i['display']} {i['name']} {i['version'] or ''} {i['loader'] or 'vanilla'} {i['source']}".lower()
    return instances


def safe_to_delete(folder):
    """Garde-fou : on ne supprime qu'un vrai dossier d'instance, jamais un dossier système."""
    try:
        p = Path(folder).resolve()
        home = Path.home().resolve()
        protected = {home, Path(MC_DIR).resolve(), INSTANCES_DIR.resolve(), Path(SYSTEM_MC_DIR).resolve()}
        return (p.is_dir() and len(p.parts) >= 4
                and not any(q == p or p in q.parents for q in protected | {home}))
    except Exception:
        return False


def remove_tree(folder):
    def fix(func, path, _exc):  # fichiers en lecture seule (Windows)
        os.chmod(path, stat.S_IWRITE)
        func(path)
    try:
        shutil.rmtree(folder, onexc=fix)
    except TypeError:  # Python < 3.12
        shutil.rmtree(folder, onerror=fix)


PROFILE_NAME = "WECRAFT"
# Selon la version du launcher officiel, les profils sont dans l'un ou l'autre de ces fichiers
PROFILE_FILES = ("launcher_profiles.json", "launcher_profiles_microsoft_store.json")


def default_instance_name(game_dir):
    """Nom d'instance déduit du dossier (si on ne le connaît pas par CurseForge/Modrinth/Prism)."""
    p = Path(game_dir)
    if p.name.lower() in ("minecraft", ".minecraft") and p.parent.name:
        return p.parent.name
    return p.name.lstrip(".") or p.name


def profile_name_for(instance_name):
    """Nom du profil : « WECRAFT - <instance> »."""
    return f"{PROFILE_NAME} - {instance_name}"


def set_profile(base_dir, name, version_id, game_dir, ram):
    """Crée le profil « WECRAFT - <instance> » dans le launcher officiel, ou met à jour
    l'existant (nom, version, dossier de jeu) : dossier de jeu (gameDir) + version à lancer, pour démarrer sur le bon modpack."""
    base = Path(base_dir)
    files = [base / n for n in PROFILE_FILES if (base / n).exists()]
    if not files:
        raise RuntimeError(
            "Profils du launcher officiel introuvables.\n"
            "Ouvrez une fois le launcher officiel de Minecraft, fermez-le, puis réessayez."
        )
    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.000Z")
    for f in files:
        backup = f.with_name(f.name + ".bak_wecraft")
        if not backup.exists():
            shutil.copy(f, backup)  # sauvegarde de sécurité (une seule fois)
        data = json.loads(f.read_text(encoding="utf-8"))
        profiles = data.setdefault("profiles", {})
        # Un seul profil WeCraft : on retrouve celui déjà créé (quel que soit le nom de l'instance
        # qu'il porte) et on le met à jour : nom, version et dossier de jeu.
        ours = [p for p in profiles.values()
                if str(p.get("name", "")).lower().startswith((PROFILE_NAME.lower(), "mon lanceur"))]
        prof = next((p for p in ours if p.get("name") == name), None)
        if prof is None and ours:
            prof = max(ours, key=lambda p: p.get("lastUsed", ""))
        if prof is None:
            prof = profiles[uuid.uuid4().hex] = {"name": name, "created": now}
        prof["name"] = name
        prof.update(type="custom", lastVersionId=version_id, gameDir=str(game_dir), lastUsed=now)
        # La RAM n'est modifiée que si les arguments Java sont absents ou sont ceux de ce launcher
        if not prof.get("javaArgs") or re.fullmatch(r"-Xmx\d+G", prof["javaArgs"]):
            prof["javaArgs"] = f"-Xmx{ram}G"
        f.write_text(json.dumps(data, indent=2), encoding="utf-8")


# Processus du launcher officiel (version classique / version Microsoft Store)
OFFICIAL_LAUNCHER_PROCESSES = ("MinecraftLauncher.exe", "Minecraft.exe")


def _run_quiet(cmd):
    """Commande sans fenêtre. stdin=DEVNULL est indispensable dans un .exe « windowed »,
    sinon Windows renvoie « handle invalide » et la commande ne part jamais."""
    return subprocess.run(cmd, stdin=subprocess.DEVNULL, capture_output=True, text=True, errors="ignore",
                          creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))


def _win_running(name):
    return name.lower() in _run_quiet(["tasklist", "/FI", f"IMAGENAME eq {name}", "/NH"]).stdout.lower()


def close_official_launcher(timeout=8):
    """Ferme le launcher officiel (sans toucher à une partie en cours : seul le processus du
    launcher est arrêté). Renvoie (réussi, message)."""
    try:
        if sys.platform.startswith("win"):
            running = [n for n in OFFICIAL_LAUNCHER_PROCESSES if _win_running(n)]
            if not running:
                return True, "Launcher officiel déjà fermé."
            for n in running:
                _run_quiet(["taskkill", "/F", "/IM", n])
            deadline = time.monotonic() + timeout
            while time.monotonic() < deadline:
                if not any(_win_running(n) for n in running):
                    time.sleep(1.5)  # laisse Windows libérer les fichiers
                    return True, "Launcher officiel fermé."
                time.sleep(0.5)
            return False, "Le launcher officiel ne se ferme pas : fermez-le à la main."
        if sys.platform == "darwin":
            _run_quiet(["osascript", "-e", 'tell application "Minecraft" to quit'])
        else:
            for cmd in (["pkill", "-x", "minecraft-launcher"], ["flatpak", "kill", "com.mojang.Minecraft"]):
                if shutil.which(cmd[0]):
                    _run_quiet(cmd)
        time.sleep(1.5)
        return True, "Launcher officiel fermé."
    except Exception as e:
        return False, f"Impossible de fermer le launcher officiel ({e}) : fermez-le à la main."


def open_official_launcher():
    """Ouvre le launcher officiel (version Microsoft Store ou classique). False si échec."""
    try:
        if sys.platform.startswith("win"):
            for env, default in (("ProgramFiles(x86)", r"C:\Program Files (x86)"),
                                 ("ProgramFiles", r"C:\Program Files")):
                exe = Path(os.environ.get(env, default)) / "Minecraft Launcher" / "MinecraftLauncher.exe"
                if exe.exists():
                    subprocess.Popen([str(exe)])
                    return True
            subprocess.Popen(["explorer.exe",
                              r"shell:AppsFolder\Microsoft.4297127D64EC6_8wekyb3d8bbwe!Minecraft"])
            return True
        if sys.platform == "darwin":
            return subprocess.run(["open", "-a", "Minecraft"]).returncode == 0
        for cmd in (["minecraft-launcher"], ["flatpak", "run", "com.mojang.Minecraft"]):
            if shutil.which(cmd[0]):
                subprocess.Popen(cmd)
                return True
    except Exception:
        pass
    return False




# ---------------------------------------------------------------- mises à jour (GitHub)
def version_tuple(text):
    return tuple(int(x) for x in re.findall(r"\d+", str(text))[:4])


def _http(url, timeout=10):
    return urllib.request.urlopen(
        urllib.request.Request(url, headers={"User-Agent": "WeCraft-Launcher",
                                             "Accept": "application/vnd.github+json"}),
        timeout=timeout)


def fetch_latest_release():
    """Dernière release publiée sur GitHub : version, notes, .exe et son empreinte SHA-256."""
    with _http(f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest") as r:
        d = json.load(r)
    assets = d.get("assets", [])
    exe = next((a for a in assets if a["name"].lower().endswith(".exe")), None)
    sha = None
    if exe:
        digest = exe.get("digest") or ""
        if digest.startswith("sha256:"):
            sha = digest[7:]
        else:
            side = next((a for a in assets if a["name"].lower() == exe["name"].lower() + ".sha256"), None)
            if side:
                with _http(side["browser_download_url"]) as r:
                    sha = r.read().decode().split()[0]
    return {"version": d["tag_name"].lstrip("vV"), "notes": (d.get("body") or "").strip(),
            "page": d["html_url"], "url": exe["browser_download_url"] if exe else None,
            "size": exe["size"] if exe else 0, "sha256": sha}


def explain_update_error(e):
    if isinstance(e, urllib.error.HTTPError):
        if e.code == 404:
            return (f"Aucune release trouvée sur « {GITHUB_REPO} ».\nVérifiez que le dépôt est public, "
                    "que ce nom est exact et qu'une release est publiée (pas en brouillon).")
        if e.code in (403, 429):
            return "Limite de requêtes GitHub atteinte, réessayez dans une heure."
        return f"Erreur GitHub {e.code}."
    return f"Connexion impossible ({e})."


def download_update(info, dest, progress=lambda done, total: None):
    """Télécharge le nouvel .exe et vérifie son SHA-256 avant de le garder."""
    h, done = hashlib.sha256(), 0
    try:
        with _http(info["url"], timeout=30) as r, open(dest, "wb") as f:
            total = int(r.headers.get("Content-Length") or info.get("size") or 0)
            while True:
                chunk = r.read(65536)
                if not chunk:
                    break
                f.write(chunk)
                h.update(chunk)
                done += len(chunk)
                progress(done, total)
        if h.hexdigest().lower() != info["sha256"].lower():
            raise RuntimeError("Le fichier téléchargé est corrompu ou a été modifié : mise à jour annulée.")
    except Exception:
        Path(dest).unlink(missing_ok=True)
        raise
    return dest


def apply_update(new_exe):
    """Windows : un petit script attend la fermeture du launcher, remplace l'.exe puis le relance."""
    cur = Path(sys.executable)
    bat = cur.with_name("wecraft_update.bat")
    bat.write_text(
        "@echo off\r\n"
        f'set "CUR={cur}"\r\nset "NEW={new_exe}"\r\n'
        "for /l %%i in (1,1,60) do (\r\n"
        "  timeout /t 1 /nobreak >nul\r\n"
        '  move /Y "%NEW%" "%CUR%" >nul 2>&1\r\n'
        "  if not errorlevel 1 goto done\r\n"
        ")\r\n"
        "exit /b 1\r\n"
        ":done\r\n"
        'start "" "%CUR%"\r\n'
        '(goto) 2>nul & del "%~f0"\r\n', encoding="utf-8")
    env = {k: v for k, v in os.environ.items() if not k.startswith("_PYI") and k != "_MEIPASS2"}
    subprocess.Popen(["cmd", "/c", str(bat)], env=env, close_fds=True,
                     creationflags=0x00000008 | 0x08000000)  # DETACHED_PROCESS | CREATE_NO_WINDOW


# ---------------------------------------------------------------- bibliothèque de mods (Modrinth)
MODRINTH_API = "https://api.modrinth.com/v2"
MODRINTH_CDN = "https://cdn.modrinth.com/"  # les mods ne sont téléchargés que depuis ce serveur
MODRINTH_LOADERS = {"Fabric": ["fabric"], "Forge": ["forge"], "NeoForge": ["neoforge"],
                    "Quilt": ["quilt", "fabric"]}  # Quilt accepte aussi les mods Fabric
MP_CATEGORIES = ("adventure", "cursed", "decoration", "economy", "equipment", "food", "game-mechanics", "library",
                 "magic", "management", "minigame", "mobs", "optimization", "social", "storage", "technology",
                 "transportation", "utility", "worldgen")
MP_SORTS = {"Pertinence": None, "Téléchargements": "downloads", "Favoris": "follows",
            "Plus récents": "newest", "Mis à jour": "updated"}
MP_PAGE = 20  # résultats ajoutés à chaque « Charger plus » (et retirés à chaque « Réduire »)
MP_VIEWS = {"tiles": "Tuiles", "table": "Tableau", "list": "Liste"}
LOADER_COLORS = {"fabric": "#E8B77C", "forge": "#8E9CFF", "neoforge": "#FF8A4C", "quilt": "#C084FC"}
CATEGORY_FR = {
    "optimization": "Optimisation", "decoration": "Décoration", "library": "Bibliothèque",
    "utility": "Utilitaire", "technology": "Technologie", "adventure": "Aventure", "magic": "Magie",
    "storage": "Stockage", "equipment": "Équipement", "food": "Nourriture", "game-mechanics": "Mécaniques",
    "mobs": "Créatures", "worldgen": "Génération", "transportation": "Transport", "social": "Social",
    "economy": "Économie", "cursed": "Maudit", "management": "Gestion", "minigame": "Mini-jeu",
}


def modrinth_get(path, params=None):
    """Requête GET sur l'API Modrinth (gratuite, sans clé ; User-Agent obligatoire)."""
    url = MODRINTH_API + path + ("?" + urllib.parse.urlencode(params) if params else "")
    req = urllib.request.Request(url, headers={"User-Agent": f"{GITHUB_REPO}/{APP_VERSION}"})
    with urllib.request.urlopen(req, timeout=20) as r:
        return json.load(r)


def explain_modrinth_error(e):
    if isinstance(e, urllib.error.HTTPError):
        if e.code == 429:
            return "Trop de requêtes envoyées à Modrinth : patientez une minute puis réessayez."
        return f"Modrinth a répondu par une erreur ({e.code})."
    if isinstance(e, urllib.error.URLError):
        return "Connexion à Modrinth impossible : vérifiez votre connexion internet."
    return str(e)


def modrinth_search(query, mc, loader, offset=0, limit=20, categories=(), envs=(), sort=None):
    """Recherche de mods. categories : toutes obligatoires ; envs : « client » et/ou « server »."""
    facets = [["project_type:mod"], [f"versions:{mc}"], [f"categories:{l}" for l in MODRINTH_LOADERS[loader]]]
    facets += [[f"categories:{c}"] for c in categories]
    facets += [[f"{e}_side:required", f"{e}_side:optional"] for e in envs]
    return modrinth_get("/search", {"query": query, "facets": json.dumps(facets), "limit": limit,
                                    "offset": offset, "index": sort or ("relevance" if query else "downloads")})


def short_count(n):
    n = int(n or 0)
    return f"{n / 1e6:.1f}M" if n >= 1e6 else f"{n / 1e3:.0f}k" if n >= 1e3 else str(n)


def safe_folder_name(name):
    clean = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "", name).strip(" .")[:60]
    if not clean or clean.upper() in {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)),
                                      *(f"LPT{i}" for i in range(1, 10))}:
        clean = f"Modpack {clean}".strip()
    return clean


def download_mod_file(url, dest, sha512=None, sha1=None):
    """Télécharge un mod puis vérifie son empreinte (SHA-512, sinon SHA-1) : sinon il est supprimé."""
    if not url.startswith(MODRINTH_CDN):
        raise RuntimeError("Adresse de téléchargement non autorisée.")
    h512, h1 = hashlib.sha512(), hashlib.sha1()
    req = urllib.request.Request(url, headers={"User-Agent": f"{GITHUB_REPO}/{APP_VERSION}"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r, open(dest, "wb") as f:
            while True:
                chunk = r.read(65536)
                if not chunk:
                    break
                f.write(chunk)
                h512.update(chunk)
                h1.update(chunk)
        if sha512:
            ok = h512.hexdigest().lower() == sha512.lower()
        else:
            ok = bool(sha1) and h1.hexdigest().lower() == sha1.lower()
        if not ok:
            raise RuntimeError(f"Fichier corrompu ou modifié : {Path(dest).name}")
    except Exception:
        Path(dest).unlink(missing_ok=True)
        raise


def resolve_modpack(mc, loader, roots, fetch=modrinth_get):
    """Choisit la meilleure version compatible de chaque mod demandé, puis ajoute récursivement
    ses dépendances « required ». Renvoie (liste de fichiers à télécharger, avertissements)."""
    loaders = MODRINTH_LOADERS[loader]
    titles = {r["project_id"]: r["title"] for r in roots}
    chosen, warnings, incompatible, required_by = {}, [], [], {}
    queue = deque((r["project_id"], False) for r in roots)

    def pick(pid):
        versions = fetch(f"/project/{pid}/version",
                         {"loaders": json.dumps(loaders), "game_versions": json.dumps([mc])})
        for kind in ("release", "beta", "alpha"):  # on préfère toujours une version stable
            found = [v for v in versions if v.get("version_type") == kind]
            if found:
                return max(found, key=lambda v: v.get("date_published", ""))
        return None

    while queue:
        pid, is_dep = queue.popleft()
        if pid in chosen:
            continue
        try:
            v = pick(pid)
        except Exception as e:
            v = None
            warnings.append(f"« {titles.get(pid, pid)} » : version introuvable ({e}).")
        files = (v or {}).get("files") or []
        f = next((x for x in files if x.get("primary")), files[0] if files else None)
        if not v or not f or not str(f.get("url", "")).startswith(MODRINTH_CDN):
            chosen[pid] = None
            if v is None:
                if not any(f"« {titles.get(pid, pid)} » :" in w for w in warnings):  # pas de doublon d'erreur
                    warnings.append(f"« {titles.get(pid, pid)} » : aucune version pour Minecraft {mc} ({loader}).")
            else:
                warnings.append(f"« {titles.get(pid, pid)} » : fichier indisponible ou non autorisé, ignoré.")
            continue
        hashes = f.get("hashes") or {}
        chosen[pid] = {"project_id": pid, "version_id": v["id"], "version": v.get("version_number", ""),
                       "filename": Path(f["filename"]).name, "url": f["url"], "size": f.get("size", 0),
                       "sha512": hashes.get("sha512"), "sha1": hashes.get("sha1"), "dependency": is_dep}
        for dep in v.get("dependencies", []):
            dp, kind = dep.get("project_id"), dep.get("dependency_type")
            if not dp and dep.get("version_id"):
                try:
                    dp = fetch(f"/version/{dep['version_id']}").get("project_id")
                except Exception:
                    dp = None
            if dp and kind == "required":
                queue.append((dp, True))
                required_by.setdefault(dp, set()).add(pid)
            elif dp and kind == "incompatible":
                incompatible.append((dp, pid))

    plan, seen = [], set()
    for item in chosen.values():
        if item and item["filename"] not in seen:  # deux projets ne peuvent pas partager un fichier
            seen.add(item["filename"])
            plan.append(item)
    ids = [i["project_id"] for i in plan]
    try:  # noms lisibles pour les dépendances ajoutées automatiquement
        for k in range(0, len(ids), 100):
            for p in fetch("/projects", {"ids": json.dumps(ids[k:k + 100])}):
                titles.setdefault(p["id"], p["title"])
    except Exception:
        pass
    for item in plan:
        item["title"] = titles.get(item["project_id"], item["filename"])
    in_pack = {i["project_id"] for i in plan}
    for item in plan:  # « dépendance de ... » : quels mods du pack ont besoin de celui-ci
        item["required_by"] = sorted(p for p in required_by.get(item["project_id"], ())
                                     if p in in_pack and p != item["project_id"])
    for dp, by in incompatible:
        if dp in in_pack:
            warnings.append(f"Incompatibilité : « {titles.get(by, by)} » ne fonctionne pas avec « {titles.get(dp, dp)} ».")
    return plan, warnings


def build_modpack(folder, name, mc, loader, roots, progress=lambda done, total, msg: None,
                  fetch=modrinth_get, download=download_mod_file):
    """Crée l'instance : dossier + mods téléchargés (4 en parallèle) + réglages WeCraft."""
    progress(0, 0, "Recherche des versions compatibles et des dépendances...")
    plan, warnings = resolve_modpack(mc, loader, roots, fetch)
    if not plan:
        raise RuntimeError("Aucun de ces mods n'existe pour cette version de Minecraft et ce loader.\n"
                           + "\n".join(warnings))
    folder = Path(folder)
    mods_dir = folder / "mods"
    mods_dir.mkdir(parents=True)
    try:
        done = 0
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = {pool.submit(download, i["url"], mods_dir / i["filename"], i["sha512"], i["sha1"]): i
                       for i in plan}
            for fut in as_completed(futures):
                fut.result()
                done += 1
                progress(done, len(plan), futures[fut]["filename"])
        (folder / "wecraft.json").write_text(json.dumps({"version": mc, "loader": loader}, indent=2),
                                             encoding="utf-8")
        (folder / "wecraft_modpack.json").write_text(json.dumps(
            {"name": name, "minecraft": mc, "loader": loader, "source": "modrinth",
             "mods": [{k: i[k] for k in ("project_id", "version_id", "title", "version", "filename", "dependency", "required_by")}
                      for i in plan]}, indent=2, ensure_ascii=False), encoding="utf-8")
    except Exception:
        shutil.rmtree(folder, ignore_errors=True)  # pas d'instance à moitié créée
        raise
    deps = sum(1 for i in plan if i["dependency"])
    return {"count": len(plan), "deps": deps, "warnings": warnings}

def de_name(name):
    """« de Create », « d'Apotheosis » : élision devant une voyelle."""
    return ("d'" if name[:1].lower() in "aeiouyàâéèêîôû" else "de ") + name


def join_fr(items):
    """['A'] -> 'A' ; ['A', 'B'] -> 'A et B' ; ['A', 'B', 'C'] -> 'A, B et C'."""
    items = list(items)
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " et " + items[-1]


def pack_graph(old, keep, plan):
    """Qui reste dans un modpack, et qui a besoin de qui.
    old : mods déjà enregistrés ; keep : ids des mods choisis par l'utilisateur ;
    plan : {id: [ids des mods qui le requièrent]} pour les mods ajoutés (ou redemandés) par la modification.
    Une dépendance disparaît quand tous les mods qui la requéraient ont disparu ; sans information
    (anciens modpacks) elle est conservée. Renvoie (vivants, parents)."""
    edges = {}
    for m in old:
        edges.setdefault(m["project_id"], set()).update(m.get("required_by") or [])
    for pid, req in plan.items():
        edges.setdefault(pid, set()).update(req)
    alive = set(keep) | set(plan)
    changed = True
    while changed:
        changed = False
        for m in old:
            pid = m["project_id"]
            if pid not in alive and m.get("dependency") and (not edges[pid] or edges[pid] & alive):
                alive.add(pid)
                changed = True
    parents = {pid: sorted(p for p in edges.get(pid, ()) if p in alive and p != pid) for pid in alive}
    return alive, parents


def pack_rows(old, selected, plan_items=None):
    """Lignes de « Mon modpack » : mods choisis, dépendances, et dépendances qui ne serviront plus.
    plan_items : {id: mod} résolus pour les mods ajoutés (None = pas encore calculé)."""
    items = plan_items or {}
    keep = [m["project_id"] for m in selected]
    alive, parents = pack_graph(old, keep, {pid: i.get("required_by") or [] for pid, i in items.items()})
    titles = {m["project_id"]: m.get("title") or m.get("filename") or m["project_id"] for m in old}
    titles.update({pid: i.get("title") or pid for pid, i in items.items()})
    titles.update({m["project_id"]: m["title"] for m in selected})

    def names(pid):
        return sorted(titles.get(p, p) for p in parents.get(pid, ()))

    old_ids = {m["project_id"] for m in old}
    rows = []
    for m in selected:
        pid = m["project_id"]
        missing = plan_items is not None and pid not in old_ids and pid not in items
        rows.append({"id": pid, "title": titles[pid], "kind": "missing" if missing else "root",
                     "parents": names(pid)})
    shown = set(keep)
    for m in old:  # dépendances déjà dans le modpack
        pid = m["project_id"]
        if m.get("dependency") and pid not in shown:
            shown.add(pid)
            rows.append({"id": pid, "title": titles[pid], "kind": "dep" if pid in alive else "orphan",
                         "parents": names(pid)})
    for pid, i in items.items():  # dépendances qui vont être ajoutées
        if i.get("dependency") and pid not in shown:
            shown.add(pid)
            rows.append({"id": pid, "title": titles[pid], "kind": "dep", "parents": names(pid)})
    return rows


def pack_note(row):
    """Petit texte entre parenthèses affiché à côté d'un mod du modpack : (texte, couleur)."""
    if row["kind"] == "missing":
        return "(introuvable pour cette version et ce loader)", EMBER1
    if row["kind"] == "orphan":
        return "(dépendance devenue inutile : sera retirée)", EMBER2
    if row["kind"] == "dep":
        if row["parents"]:
            return f"(dépendance {join_fr([de_name(n) for n in row['parents']])})", BLUE
        return "(dépendance automatique)", BLUE
    if row["parents"]:
        return f"(aussi requis par {join_fr(row['parents'])})", MUTED
    return "", MUTED


def apply_modpack_edit(folder, meta, selected, progress=lambda done, total, msg: None,
                       fetch=modrinth_get, download=download_mod_file):
    """Modifie un modpack WeCraft : télécharge les mods ajoutés (dernière version compatible + dépendances
    requises) puis supprime les mods retirés, ainsi que les dépendances que plus aucun mod ne requiert.
    Les mods déjà présents ne sont ni touchés ni mis à jour. Rien n'est supprimé si un téléchargement échoue."""
    folder = Path(folder)
    mods_dir = folder / "mods"
    mc, loader = meta["minecraft"], meta["loader"]
    old = list(meta.get("mods", []))
    old_ids = {m["project_id"] for m in old}
    keep = {m["project_id"] for m in selected}
    new_roots = [m for m in selected if m["project_id"] not in old_ids]

    plan, warnings, found_rb = [], [], {}
    if new_roots:
        progress(0, 0, "Recherche des versions compatibles et des dépendances...")
        found, warnings = resolve_modpack(mc, loader, new_roots, fetch)
        if not found:
            raise RuntimeError("Aucun des mods ajoutés n'existe pour cette version de Minecraft et ce loader.\n"
                               + "\n".join(warnings))
        used = {m["filename"] for m in old}
        for item in found:
            if item["project_id"] in old_ids:  # déjà dans le modpack : seul « qui le requiert » est mis à jour
                found_rb[item["project_id"]] = item.get("required_by", [])
                continue
            if item["filename"] in used or (mods_dir / item["filename"]).exists():
                warnings.append(f"« {item['title']} » : un fichier du même nom existe déjà dans « mods », ignoré.")
                continue
            plan.append(item)
    plan_ids = {i["project_id"] for i in plan}
    edges_new = {i["project_id"]: [p for p in i.get("required_by", []) if p in plan_ids] for i in plan}
    edges_new.update({pid: [p for p in rb if p in plan_ids] for pid, rb in found_rb.items()})
    alive, parents = pack_graph(old, keep, edges_new)
    removed = [m for m in old if m["project_id"] not in alive]

    mods_dir.mkdir(parents=True, exist_ok=True)
    try:
        done = 0
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = {pool.submit(download, i["url"], mods_dir / i["filename"], i["sha512"], i["sha1"]): i
                       for i in plan}
            for fut in as_completed(futures):
                fut.result()
                done += 1
                progress(done, len(plan), futures[fut]["filename"])
    except Exception:
        for i in plan:  # on annule : rien de ce qui vient d'être téléchargé ne reste
            (mods_dir / i["filename"]).unlink(missing_ok=True)
        raise

    failed = []
    for m in removed:
        try:
            (mods_dir / Path(m["filename"]).name).unlink(missing_ok=True)
        except OSError:
            failed.append(m)
            warnings.append(f"« {m.get('title') or m['filename']} » : fichier impossible à supprimer "
                            "(jeu ouvert ?), supprimez-le à la main.")
    gone = [m for m in removed if m not in failed]
    gone_ids = {m["project_id"] for m in gone}
    kept = []
    for m in old:
        if m["project_id"] in gone_ids:
            continue
        m = dict(m)
        pid = m["project_id"]
        if pid in keep:
            m["dependency"] = False  # un ancien « dépendance » choisi à la main devient un vrai mod du pack
        if pid in alive and ("required_by" in m or edges_new.get(pid)):
            m["required_by"] = parents.get(pid, [])
        kept.append(m)
    keys = ("project_id", "version_id", "title", "version", "filename", "dependency")
    kept += [dict({k: i[k] for k in keys}, required_by=parents.get(i["project_id"], [])) for i in plan]
    tmp = folder / "wecraft_modpack.json.tmp"
    tmp.write_text(json.dumps(dict(meta, mods=kept), indent=2, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, folder / "wecraft_modpack.json")
    return {"added": sum(1 for i in plan if not i["dependency"]), "deps": sum(1 for i in plan if i["dependency"]),
            "removed": sum(1 for m in gone if not m.get("dependency")),
            "pruned": sum(1 for m in gone if m.get("dependency")), "warnings": warnings}


# ------------------------------------------------------------------ style WeCraft
def lerp_color(c1, c2, t):
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(round(x + (y - x) * t) for x, y in zip(a, b))


def load_local_fonts():
    """Windows : charge les .ttf du dossier « fonts » (Unbounded, Inter, JetBrains Mono)."""
    if not sys.platform.startswith("win"):
        return
    for ttf in list((RES_DIR / "fonts").glob("*.ttf")) + list((RES_DIR / "fonts").glob("*.otf")):
        try:
            ctypes.windll.gdi32.AddFontResourceExW(str(ttf), 0x10, 0)  # FR_PRIVATE
        except Exception:
            pass


class GradientBar(tk.Canvas):
    """Filet dégradé braise."""
    def __init__(self, master, height=3):
        super().__init__(master, height=height, bg=BG, highlightthickness=0, bd=0)
        self.bind("<Configure>", lambda e: self.draw())

    def draw(self):
        self.delete("all")
        w, h = max(self.winfo_width(), 2), int(self["height"])
        for x in range(w):
            self.create_line(x, 0, x, h, fill=lerp_color(EMBER1, EMBER2, x / (w - 1)))


class GradientButton(tk.Canvas):
    """Bouton d'action principal : dégradé braise #FF5A36 -> #FFB84D, coins arrondis."""
    def __init__(self, master, text, command, font, height=50, radius=12, width=None, bg=BG):
        extra = {"width": width} if width else {}
        super().__init__(master, height=height, bg=bg, highlightthickness=0, bd=0, cursor="hand2", **extra)
        self.text, self.command, self.font, self.radius = text, command, font, radius
        self.state, self.hover, self.pressed, self.muted = "normal", False, False, False
        self.bind("<Configure>", lambda e: self.draw())
        self.bind("<Enter>", lambda e: self._set(hover=True))
        self.bind("<Leave>", lambda e: self._set(hover=False, pressed=False))
        self.bind("<ButtonPress-1>", lambda e: self._set(pressed=True))
        self.bind("<ButtonRelease-1>", self._release)

    def _set(self, **kw):
        self.__dict__.update(kw)
        self.draw()

    def _release(self, _e):
        was = self.pressed
        self._set(pressed=False)
        if was and self.hover and self.state == "normal":
            self.command()

    def config(self, **kw):
        if "state" in kw:
            self.state = kw.pop("state")
            self.configure(cursor="hand2" if self.state == "normal" else "arrow")
            self.draw()
        if kw:
            super().configure(**kw)
    configure = config

    def set_label(self, text, muted=False):
        self.text, self.muted = text, muted
        self.draw()

    def draw(self):
        self.delete("all")
        w, h, r = max(self.winfo_width(), 2 * self.radius + 2), int(self["height"]), self.radius
        off = self.state != "normal"
        for x in range(w):
            d = r - x if x < r else x - (w - 1 - r) if x > w - 1 - r else 0
            inset = r - math.sqrt(max(r * r - d * d, 0)) if d > 0 else 0
            if off:
                col = BORDER
            elif self.muted:  # bouton « secondaire » (ex. mod déjà ajouté)
                col = lerp_color("#161D36", "#FFFFFF", 0.08) if self.hover else "#161D36"
            else:
                col = lerp_color(EMBER1, EMBER2, x / (w - 1))
                if self.pressed:
                    col = lerp_color(col, "#000000", 0.18)
                elif self.hover:
                    col = lerp_color(col, "#FFFFFF", 0.14)
            self.create_line(x, inset, x, h - inset, fill=col)
        self.create_text(w // 2, h // 2, text=self.text, font=self.font,
                         fill=MUTED if off else (FG if self.muted else "#1A0A04"))

class GlobeButton(tk.Canvas):
    """Petit bouton « globe internet », dessiné à la main (pas de police d'emoji requise)."""
    def __init__(self, master, command, size=32, bg=PANEL):
        super().__init__(master, width=size, height=size, bg=bg, highlightthickness=0, bd=0, cursor="hand2")
        self.command, self.size, self.hover = command, size, False
        self.bind("<Enter>", lambda e: self._set(True))
        self.bind("<Leave>", lambda e: self._set(False))
        self.bind("<ButtonRelease-1>", self._release)
        self.draw()

    def _set(self, hover):
        self.hover = hover
        self.draw()

    def _release(self, e):
        if 0 <= e.x < self.size and 0 <= e.y < self.size:
            self.command()

    def draw(self):
        self.delete("all")
        s, col = self.size, EMBER2 if self.hover else MUTED
        self.create_rectangle(0, 0, s - 1, s - 1, fill="#1E2748" if self.hover else "#161D36",
                              outline=EMBER1 if self.hover else BORDER)
        m = s * 0.24
        x0, y0, x1, y1 = m, m, s - m, s - m
        cx, cy, r = s / 2, s / 2, (s - 2 * m) / 2
        self.create_oval(x0, y0, x1, y1, outline=col, width=1.4)                    # cercle
        self.create_oval(cx - r * 0.45, y0, cx + r * 0.45, y1, outline=col)          # méridien
        self.create_line(cx, y0, cx, y1, fill=col)                                   # axe
        self.create_line(x0, cy, x1, cy, fill=col)                                   # équateur
        for dy in (-r * 0.5, r * 0.5):                                               # parallèles
            w = math.sqrt(r * r - dy * dy)
            self.create_line(cx - w, cy + dy, cx + w, cy + dy, fill=col)


class TileGrid:
    """Range des tuiles dans une grille dont le nombre de colonnes suit la largeur disponible."""
    def __init__(self, host, min_width=240):
        self.host, self.min_width = host, min_width
        self.tiles, self._sig, self._cols = [], None, 0

    def add(self, tile):
        self.tiles.append(tile)  # placée dans la grille par layout()

    def layout(self, width=None):
        if not self.tiles:
            return
        width = width or self.host.winfo_width()
        cols = max(1, (width - 12) // self.min_width)
        sig = (cols, len(self.tiles))
        if sig == self._sig:
            return
        self._sig = sig
        for c in range(max(cols, self._cols)):
            self.host.columnconfigure(c, weight=1 if c < cols else 0, uniform="tile" if c < cols else "")
        self._cols = cols
        for i, t in enumerate(self.tiles):
            t.grid(row=i // cols, column=i % cols, sticky="nsew", padx=4, pady=4)


# ------------------------------------------------------------------ interface
class Launcher(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("WeCraft")
        self.geometry("560x860")
        self.minsize(560, 640)
        self.resizable(True, True)  # redimensionnable, maximisable, plein écran (F11)
        self.fullscreen = False
        self.configure(bg=BG)
        self.apply_style()

        Path(MC_DIR).mkdir(parents=True, exist_ok=True)
        self.config_data = self.load_config()
        self.all_versions = []
        self.loader_support = {}  # cache : loader -> versions MC compatibles
        self.loader_version = self.config_data.get("loader_version")  # imposée par l'instance détectée
        self.instance_name = self.config_data.get("instance_name")    # nom CurseForge/Modrinth/Prism

        self.busy = False
        self.card_buttons = []
        self._inst_sig = None
        self._instances, self._ext, self._ext_time = [], None, 0.0
        self._scanning, self._queued, self._search_job, self.page = False, None, None, 0
        self.mp_hits, self.mp_selected, self.mp_last = [], [], None  # onglet Modpacks
        self._mp_busy = self._mp_searching = False
        self.mp_card_btns, self._mp_more, self.mp_total = {}, None, 0
        self._mp_icons, self._icon_sem = {}, threading.Semaphore(4)
        self._mp_auto, self._pack_h = False, 84
        self._mp_dirty, self._mp_job, self.mp_filters_open = False, None, False
        self.mp_grid = self.mp_pack_grid = self.inst_grid = None  # grilles des modes « Tuiles »
        self.mp_pre, self._pre_gen, self._pre_job, self._http_cache = None, 0, None, {}
        self.mp_edit, self._mp_notice, self._ram_dialog = None, None, None
        view = self.config_data.get("mp_view")
        self.mp_view = tk.StringVar(value=view if view in MP_VIEWS else "list")
        self.set_app_icon()
        self.build_ui()
        self.load_versions()
        self.check_updates()
        self.refresh_instances(force=True)
        self.after(3000, self.poll_instances)

    # ---------- Mises à jour ----------
    def check_updates(self, manual=False):
        """Au démarrage : silencieux. Via le lien en bas de fenêtre (manual) : dit toujours ce qui se passe."""
        def worker():
            try:
                info = fetch_latest_release()
            except Exception as e:
                try:  # trace dans %APPDATA%/.wecraft/update.log
                    with open(Path(MC_DIR) / "update.log", "a", encoding="utf-8") as f:
                        f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')}  {GITHUB_REPO}  {e!r}\n")
                except Exception:
                    pass
                if manual:
                    msg = explain_update_error(e)
                    self.after(0, lambda: messagebox.showwarning("Mises à jour", msg))
                return
            if version_tuple(info["version"]) > version_tuple(APP_VERSION):
                self.after(0, lambda: self.show_update(info))
            elif manual:
                self.after(0, lambda: messagebox.showinfo(
                    "Mises à jour", f"WeCraft est à jour (v{APP_VERSION}). Dernière version publiée : v{info['version']}."))

        threading.Thread(target=worker, daemon=True).start()

    def show_update(self, info):
        auto = FROZEN and sys.platform.startswith("win") and info["url"] and info["sha256"]
        win = tk.Toplevel(self)
        win.title("Mise à jour WeCraft")
        win.geometry(f"460x340+{self.winfo_x() + 50}+{self.winfo_y() + 120}")
        win.configure(bg=BG)
        win.resizable(False, False)
        win.transient(self)
        tk.Label(win, text="MISE À JOUR DISPONIBLE", bg=BG, fg=FG,
                 font=(self.f_display, 13, "bold")).pack(pady=(18, 2))
        tk.Label(win, text=f"v{APP_VERSION}  →  v{info['version']}", bg=BG, fg=EMBER2,
                 font=(self.f_mono, 10, "bold")).pack()
        GradientBar(win).pack(fill="x", padx=20, pady=10)
        notes = info["notes"][:500] + ("..." if len(info["notes"]) > 500 else "")
        tk.Label(win, text=notes or "Nouvelle version du launcher.", bg=BG, fg=MUTED, justify="left",
                 anchor="nw", wraplength=410, font=(self.f_body, 10)).pack(fill="x", padx=24)
        bar = ttk.Progressbar(win, mode="determinate", style="Ember.Horizontal.TProgressbar")
        state = tk.Label(win, text="", bg=BG, fg=EMBER2, font=(self.f_mono, 9))
        bottom = tk.Frame(win, bg=BG)
        bottom.pack(side="bottom", fill="x", padx=20, pady=16)
        state.pack(side="bottom")
        bar.pack(side="bottom", fill="x", padx=24, pady=6)

        def go():
            if not auto:
                webbrowser.open(info["page"])
                win.destroy()
                return
            btn.config(state="disabled")
            later.state(["disabled"])
            dest = Path(sys.executable).with_name("WeCraft_update.exe")

            def progress(done, total):
                def _do():
                    bar["maximum"], bar["value"] = (total or 1), done
                    state.config(text=f"Téléchargement... {done * 100 // total}%" if total else "Téléchargement...")
                self.after(0, _do)

            def worker():
                try:
                    download_update(info, dest, progress)
                    self.after(0, lambda: state.config(text="Redémarrage..."))
                    apply_update(dest)
                    self.after(500, self.destroy)
                except Exception as exc:
                    err = str(exc)  # « exc » disparaît à la fin du bloc except : on garde le texte

                    def fail():
                        messagebox.showerror("Mise à jour", f"Échec de la mise à jour :\n{err}", parent=win)
                        btn.config(state="normal")
                        later.state(["!disabled"])
                    self.after(0, fail)

            threading.Thread(target=worker, daemon=True).start()

        btn = GradientButton(bottom, text="METTRE À JOUR" if auto else "VOIR LA MISE À JOUR",
                             command=go, font=(self.f_display, 10, "bold"), height=42)
        btn.pack(side="left", fill="x", expand=True)
        later = ttk.Button(bottom, text="Plus tard", command=win.destroy)
        later.pack(side="left", padx=(10, 0))

    # ---------- Configuration ----------
    def load_config(self):
        try:
            return json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
        except Exception:
            return {}

    def save_config(self):
        self.config_data.update(
            {
                "version": self.version_var.get(),
                "ram": self.ram_var.get(),
                "releases_only": self.release_var.get(),
                "loader": self.loader_var.get(),
                "game_dir": self.game_dir_var.get(),
                "loader_version": self.loader_version,
                "instance_name": self.instance_name,
                "instance_info": self.info_var.get(),
                "mp_view": self.mp_view.get(),
            }
        )
        CONFIG_FILE.write_text(json.dumps(self.config_data), encoding="utf-8")

    def game_dir(self):
        """Dossier de l'instance : mods, saves, resourcepacks, options.txt..."""
        return self.game_dir_var.get().strip() or MC_DIR

    # ---------- Interface ----------
    def set_app_icon(self):
        """Logo de la fenêtre et de la barre des tâches (assets/wecraft.ico ou wecraft_icon.png)."""
        ico = next((p for p in (RES_DIR / "assets" / "wecraft.ico", RES_DIR / "wecraft.ico") if p.exists()), None)
        try:
            if ico and sys.platform.startswith("win"):
                self.iconbitmap(default=str(ico))
                return
        except tk.TclError:
            pass
        try:
            self._icon = self.load_image("wecraft_icon.png", height=128)
            if self._icon:
                self.iconphoto(True, self._icon)
        except Exception:
            pass

    def apply_style(self):
        """Charte WeCraft : Unbounded (titres), Inter (texte), JetBrains Mono (données)."""
        load_local_fonts()
        fams = set(tkfont.families(self))
        pick = lambda *names: next((n for n in names if n in fams), None)
        self.f_display = pick("Unbounded", "Segoe UI Black", "Arial Black", "Helvetica Neue", "DejaVu Sans") or "Helvetica"
        self.f_body = pick("Inter", "Segoe UI", "Helvetica Neue", "Helvetica", "DejaVu Sans") or "Helvetica"
        self.f_mono = pick("JetBrains Mono", "Cascadia Mono", "Consolas", "Menlo", "DejaVu Sans Mono") or "Courier"
        self.font_family, self.font_size = self.f_body, 10  # utilisés par la liste d'instances
        body, mono, disp = self.f_body, self.f_mono, self.f_display

        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure(".", background=BG, foreground=FG, font=(body, 10), troughcolor=FIELD,
                     bordercolor=BORDER, lightcolor=BG, darkcolor=BG, focuscolor=BG)
        st.configure("TLabel", background=BG, foreground=FG)
        st.configure("Title.TLabel", foreground=FG, font=(disp, 24, "bold"))
        st.configure("Sub.TLabel", foreground=BLUE, font=(mono, 8))
        st.configure("Status.TLabel", foreground=EMBER2, background=PANEL, font=(mono, 9), padding=(10, 7))

        # Cartes
        st.configure("Card.TFrame", background=PANEL)
        st.configure("Card.TLabel", background=PANEL, foreground=FG)
        st.configure("Muted.TLabel", background=PANEL, foreground=MUTED, font=(mono, 8))
        st.configure("Card.TLabelframe", background=PANEL, bordercolor=BORDER, borderwidth=1,
                     relief="solid", lightcolor=PANEL, darkcolor=PANEL)
        st.configure("Card.TLabelframe.Label", background=PANEL, foreground=BLUE, font=(mono, 8, "bold"))

        # Boutons secondaires
        st.configure("TButton", background="#161D36", foreground=FG, borderwidth=1, relief="flat",
                     padding=(12, 7), bordercolor=BORDER, lightcolor="#161D36", darkcolor="#161D36",
                     font=(body, 10, "bold"))
        st.map("TButton",
               background=[("pressed", EMBER1), ("active", "#1E2748")],
               bordercolor=[("active", EMBER1)],
               foreground=[("pressed", "#1A0A04"), ("disabled", MUTED)])

        # Cases à cocher : sur le thème « clam » la coche est noire par défaut, donc invisible sur
        # fond sombre. « indicatorforeground » donne sa couleur à la coche (braise).
        for name, bg, fg, size in (("Bar.TCheckbutton", BG, MUTED, 8), ("Card.TCheckbutton", PANEL, FG, 10)):
            st.configure(name, background=bg, foreground=fg, font=(mono if size == 8 else body, size),
                         indicatorbackground=FIELD, indicatorforeground=EMBER2,
                         upperbordercolor=BORDER, lowerbordercolor=BORDER, indicatormargin=(1, 1, 6, 1))
            st.map(name,
                   background=[("active", bg)],
                   foreground=[("active", FG)],
                   indicatorbackground=[("disabled", BORDER), ("pressed", "#161D36"), ("!disabled", FIELD)],
                   indicatorforeground=[("disabled", MUTED), ("!disabled", EMBER2)],
                   upperbordercolor=[("selected", EMBER1), ("!selected", BORDER)],
                   lowerbordercolor=[("selected", EMBER1), ("!selected", BORDER)])
        st.configure("TCombobox", fieldbackground=FIELD, background="#161D36", foreground=FG,
                     arrowcolor=EMBER2, bordercolor=BORDER, selectbackground=FIELD,
                     selectforeground=FG, padding=5)
        st.map("TCombobox", fieldbackground=[("readonly", FIELD)], foreground=[("readonly", FG)],
               selectbackground=[("readonly", FIELD)], selectforeground=[("readonly", FG)],
               bordercolor=[("focus", EMBER1)])
        st.configure("TEntry", fieldbackground=FIELD, foreground=EMBER2, bordercolor=BORDER,
                     insertcolor=EMBER2, padding=5, font=(mono, 9))
        st.map("TEntry", fieldbackground=[("readonly", FIELD)], foreground=[("readonly", EMBER2)])
        st.configure("Card.Horizontal.TScale", background=PANEL, troughcolor=FIELD, bordercolor=BORDER)
        st.configure("Vertical.TScrollbar", background="#161D36", troughcolor=BG, bordercolor=BG,
                     arrowcolor=EMBER2, lightcolor="#161D36", darkcolor="#161D36")
        st.map("Vertical.TScrollbar", background=[("active", "#1E2748")])
        st.configure("Ember.Horizontal.TProgressbar", troughcolor=FIELD, background="#FF7A3D",
                     bordercolor=BORDER, lightcolor="#FF7A3D", darkcolor="#FF7A3D", thickness=8)

        # Liste déroulante des menus (popdown)
        self.option_add("*TCombobox*Listbox.background", PANEL)
        self.option_add("*TCombobox*Listbox.foreground", FG)
        self.option_add("*TCombobox*Listbox.selectBackground", EMBER1)
        self.option_add("*TCombobox*Listbox.selectForeground", "#1A0A04")
        self.option_add("*TCombobox*Listbox.font", (body, 10))

    def load_image(self, name, width=None, height=None):
        """Charge une image de assets/ (ou à côté du script), redimensionnée proprement."""
        path = next((p for p in (RES_DIR / "assets" / name, RES_DIR / name) if p.exists()), None)
        if not path:
            return None
        try:
            from PIL import Image, ImageTk  # pip install pillow : meilleur rendu
            im = Image.open(path).convert("RGBA")
            if width:
                height = round(im.height * width / im.width)
            elif height:
                width = round(im.width * height / im.height)
            return ImageTk.PhotoImage(im.resize((width, height), Image.LANCZOS))
        except ImportError:
            img = tk.PhotoImage(file=str(path))
            f = max(1, round((img.width() / width) if width else (img.height() / height)))
            return img.subsample(f)
        except Exception:
            return None

    def build_ui(self):
        pad = {"padx": 14, "pady": 5}

        # En-tête : phénix + wordmark (dossier assets/), sinon titre en texte
        self.logo = self.load_image("wecraft_logo.png", height=68)
        self.wordmark = self.load_image("wecraft_wordmark.png", width=240)
        if self.logo:
            ttk.Label(self, image=self.logo).pack(pady=(12, 0))
        if self.wordmark:
            ttk.Label(self, image=self.wordmark).pack(pady=(8, 0))
        else:
            ttk.Label(self, text="WECRAFT", style="Title.TLabel").pack(pady=(12, 0))
        ttk.Label(self, text="MINECRAFT · INSTANCE LAUNCHER", style="Sub.TLabel").pack(pady=(5, 8))
        GradientBar(self).pack(fill="x", padx=14, pady=(0, 6))

        self.fs_label = tk.Label(self, text="PLEIN ÉCRAN · F11", bg=BG, fg=MUTED, cursor="hand2",
                                 font=(self.f_mono, 8))
        self.fs_label.place(relx=1.0, x=-14, y=8, anchor="ne")
        self.fs_label.bind("<Button-1>", self.toggle_fullscreen)
        self.fs_label.bind("<Enter>", lambda e: self.fs_label.config(fg=EMBER2))
        self.fs_label.bind("<Leave>", lambda e: self.fs_label.config(fg=MUTED))

        # Onglets
        tabs = tk.Frame(self, bg=BG)
        tabs.pack(fill="x", padx=16, pady=(2, 2))
        self.tab_labels = {}
        for key, text in (("instances", "MES INSTANCES"), ("modpack", "MODPACKS"), ("manual", "MANUEL")):
            lbl = tk.Label(tabs, text=text, bg=BG, fg=MUTED, cursor="hand2",
                           font=(self.f_display, 9, "bold"))
            lbl.pack(side="left", padx=(0, 20))
            lbl.bind("<Button-1>", lambda e, k=key: self.show_tab(k))
            self.tab_labels[key] = lbl

        # Bas de fenêtre (packé avant le contenu pour rester toujours visible)
        ver = tk.Label(self, text=f"v{APP_VERSION}  ·  rechercher une mise à jour", bg=BG, fg=MUTED,
                       cursor="hand2", font=(self.f_mono, 8))
        ver.pack(side="bottom", pady=(4, 8))
        ver.bind("<Button-1>", lambda e: self.check_updates(manual=True))
        ver.bind("<Enter>", lambda e: ver.config(fg=EMBER2))
        ver.bind("<Leave>", lambda e: ver.config(fg=MUTED))
        tk.Label(self, text="Fermez le launcher officiel avant de cliquer.", bg=BG, fg=MUTED,
                 font=(self.f_mono, 8)).pack(side="bottom")
        self.progress = ttk.Progressbar(self, mode="determinate", style="Ember.Horizontal.TProgressbar")
        self.progress.pack(side="bottom", fill="x", padx=14, pady=6)
        self.status = ttk.Label(self, text="> Prêt.", style="Status.TLabel", wraplength=500)
        self.status.pack(side="bottom", fill="x", padx=14)

        # RAM par défaut (mémorisée) : elle se règle dans la fenêtre qui s'ouvre au moment de lancer
        self.ram_var = tk.IntVar(value=self.config_data.get("ram", 4))

        content = tk.Frame(self, bg=BG)
        content.pack(fill="both", expand=True)
        self.instances_frame = tk.Frame(content, bg=BG)
        self.manual_frame = tk.Frame(content, bg=BG)
        self.modpack_frame = tk.Frame(content, bg=BG)

        # ---------- Onglet « Mes instances » ----------
        mono8 = (self.f_mono, 8)
        self.top_row = tk.Frame(self.instances_frame, bg=BG)
        self.top_row.pack(fill="x", padx=14, pady=(4, 0))
        tk.Label(self.top_row, text="RECHERCHE", bg=BG, fg=MUTED, font=mono8).pack(side="left", padx=(0, 8))
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(self.top_row, textvariable=self.search_var)
        self.search_entry.pack(side="left", fill="x", expand=True)
        self.filter_btn = ttk.Button(self.top_row, text="Filtres ▾", command=self.toggle_filters)
        self.filter_btn.pack(side="left", padx=(8, 0))
        self.inst_view_btn = ttk.Button(self.top_row, text="",
                                        command=lambda: self.show_view_menu(self.inst_view_btn))
        self.inst_view_btn.pack(side="left", padx=(8, 0))
        self.search_var.trace_add("write", lambda *_: self.schedule_filter())
        self.search_entry.bind("<Escape>", lambda e: (self.search_var.set(""), "break")[1])
        self.bind_all("<Control-f>", lambda e: (self.show_tab("instances"), self.search_entry.focus_set(),
                                                self.search_entry.select_range(0, "end")))

        # Panneau de filtres (replié par défaut)
        self.filters_open = False
        self.filter_panel = tk.Frame(self.instances_frame, bg=PANEL, highlightthickness=1,
                                     highlightbackground=BORDER)
        fp = self.filter_panel
        for c in range(3):
            fp.columnconfigure(c, weight=1, uniform="f")
        self.src_var, self.ldr_var = tk.StringVar(value="Toutes"), tk.StringVar(value="Tous")
        self.ver_var, self.sort_var = tk.StringVar(value="Toutes"), tk.StringVar(value=SORTS[0])
        self.show_hidden = tk.BooleanVar(value=False)

        def combo(label, var, values, col, row):
            tk.Label(fp, text=label, bg=PANEL, fg=MUTED, font=mono8).grid(
                row=row * 2, column=col, sticky="w", padx=8, pady=(6, 0))
            cb = ttk.Combobox(fp, textvariable=var, values=values, state="readonly", width=10)
            cb.grid(row=row * 2 + 1, column=col, sticky="we", padx=8, pady=(0, 4))
            cb.bind("<<ComboboxSelected>>", lambda e: self.apply_filter())
            return cb

        combo("SOURCE", self.src_var, ["Toutes", "WeCraft", "CurseForge", "Modrinth", "Prism"], 0, 0)
        combo("LOADER", self.ldr_var, ["Tous"] + list(LOADERS), 1, 0)
        self.ver_box = combo("VERSION", self.ver_var, ["Toutes"], 2, 0)
        combo("TRI", self.sort_var, list(SORTS), 0, 1)
        ttk.Checkbutton(fp, text="Voir les masquées", variable=self.show_hidden, style="Card.TCheckbutton",
                        command=self.apply_filter).grid(row=3, column=1, sticky="w", padx=8, pady=(0, 6))
        ttk.Button(fp, text="Réinitialiser", command=self.reset_filters).grid(
            row=3, column=2, sticky="we", padx=8, pady=(0, 6))

        wrap = tk.Frame(self.instances_frame, bg=BG)
        wrap.pack(fill="both", expand=True, padx=14, pady=(6, 0))
        canvas = tk.Canvas(wrap, bg=BG, highlightthickness=0, bd=0)
        sb = ttk.Scrollbar(wrap, orient="vertical", command=canvas.yview)
        self.cards = tk.Frame(canvas, bg=BG)
        win_id = canvas.create_window((0, 0), window=self.cards, anchor="nw")
        self.cards.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(win_id, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.cards_canvas = canvas
        canvas.bind("<Configure>", lambda e: self.inst_grid and self.inst_grid.layout(e.width), add="+")
        self.bind_all("<MouseWheel>", self.on_wheel)

        bar = tk.Frame(self.instances_frame, bg=BG)
        bar.pack(fill="x", padx=14, pady=(6, 0))
        ttk.Button(bar, text="Dossier instances", command=self.open_instances_dir).pack(side="left")
        ttk.Button(bar, text="Actualiser",
                   command=lambda: self.refresh_instances(force=True, rescan=True)).pack(side="left", padx=6)
        pag = tk.Frame(bar, bg=BG)
        pag.pack(side="right")
        self.prev_btn = ttk.Button(pag, text="◀", width=3, command=lambda: self.go_page(-1))
        self.prev_btn.pack(side="left")
        self.page_label = tk.Label(pag, text="1 / 1", bg=BG, fg=FG, width=11, font=(self.f_mono, 9, "bold"))
        self.page_label.pack(side="left")
        self.next_btn = ttk.Button(pag, text="▶", width=3, command=lambda: self.go_page(1))
        self.next_btn.pack(side="left")
        self.count_label = tk.Label(self.instances_frame, text="", bg=BG, fg=MUTED, font=mono8)
        self.count_label.pack(pady=(6, 0))

        # ---------- Onglet « Manuel » ----------
        m = self.manual_frame
        box = ttk.LabelFrame(m, style="Card.TLabelframe", text="Instance (dossier avec vos mods, mondes...)")
        box.pack(fill="x", **pad)
        self.game_dir_var = tk.StringVar(value=self.config_data.get("game_dir", MC_DIR))
        ttk.Entry(box, textvariable=self.game_dir_var, state="readonly").pack(
            fill="x", padx=8, pady=(8, 2)
        )
        self.info_var = tk.StringVar(value=self.config_data.get("instance_info", ""))
        ttk.Label(box, textvariable=self.info_var, style="Muted.TLabel", wraplength=500).pack(anchor="w", padx=8)
        row = ttk.Frame(box, style="Card.TFrame")
        row.pack(fill="x", padx=8, pady=(0, 8))
        ttk.Button(row, text="Parcourir...", command=self.choose_dir).pack(side="left")
        ttk.Button(row, text="CurseForge / Modrinth", command=self.detect_dialog).pack(side="left", padx=6)
        ttk.Button(row, text="Par défaut", command=self.use_default_dir).pack(side="left")

        box = ttk.LabelFrame(m, style="Card.TLabelframe", text="Version")
        box.pack(fill="x", **pad)
        self.version_var = tk.StringVar(value=self.config_data.get("version", ""))
        self.version_box = ttk.Combobox(box, textvariable=self.version_var, state="readonly")
        self.version_box.pack(fill="x", padx=8, pady=(8, 2))
        self.version_box.bind("<<ComboboxSelected>>", self.on_manual_change)
        ttk.Label(
            box, text=f"{CUSTOM_MARK.strip()} = déjà installée (Forge, Fabric...)", style="Muted.TLabel",
        ).pack(anchor="w", padx=8)

        self.release_var = tk.BooleanVar(value=self.config_data.get("releases_only", True))
        ttk.Checkbutton(
            box, style="Card.TCheckbutton", text="Versions stables uniquement", variable=self.release_var,
            command=self.filter_versions,
        ).pack(anchor="w", padx=8)

        row = ttk.Frame(box, style="Card.TFrame")
        row.pack(fill="x", padx=8, pady=(4, 8))
        ttk.Label(row, text="Mod loader :", style="Card.TLabel").pack(side="left")
        saved = self.config_data.get("loader", "Vanilla")
        self.loader_var = tk.StringVar(value=saved if saved in LOADERS else "Vanilla")
        loader_box = ttk.Combobox(
            row, textvariable=self.loader_var, values=list(LOADERS), state="readonly", width=12
        )
        loader_box.pack(side="left", padx=8)
        loader_box.bind("<<ComboboxSelected>>", self.on_manual_change)

        ttk.Button(m, text="Ouvrir le dossier de l'instance", command=self.open_folder).pack(**pad)
        self.launch_btn = GradientButton(
            m, text="▶  LANCER L'INSTANCE", command=lambda: self.play(then_launch=True),
            font=(self.f_display, 12, "bold"),
        )
        self.launch_btn.pack(fill="x", padx=14, pady=(10, 6))

        # ---------- Onglet « Modpacks » (bibliothèque de mods Modrinth) ----------
        mp = self.modpack_frame
        mono8 = (self.f_mono, 8)
        form = self.mp_form = tk.Frame(mp, bg=BG)
        form.pack(fill="x", padx=14, pady=(4, 0))
        form.columnconfigure(0, weight=3)
        form.columnconfigure(1, weight=2)
        form.columnconfigure(2, weight=2)
        self.mp_name_var = tk.StringVar(value="Mon modpack")
        self.mp_ver_var = tk.StringVar(value="1.20.1")
        self.mp_loader_var = tk.StringVar(value="Fabric")
        for col, label in enumerate(("NOM DU MODPACK", "MINECRAFT", "LOADER")):
            tk.Label(form, text=label, bg=BG, fg=MUTED, font=mono8).grid(row=0, column=col, sticky="w", padx=(0, 8))
        self.mp_name_entry = ttk.Entry(form, textvariable=self.mp_name_var)
        self.mp_name_entry.grid(row=1, column=0, sticky="we", padx=(0, 8))
        self.mp_ver_box = ttk.Combobox(form, textvariable=self.mp_ver_var, width=9, postcommand=self.fill_mp_versions)
        self.mp_ver_box.grid(row=1, column=1, sticky="we", padx=(0, 8))
        self.mp_loader_box = ttk.Combobox(form, textvariable=self.mp_loader_var, values=list(MODRINTH_LOADERS),
                                          state="readonly", width=9)
        self.mp_loader_box.grid(row=1, column=2, sticky="we")

        # Bandeau visible uniquement pendant la modification d'un modpack WeCraft
        self.mp_edit_bar = tk.Frame(mp, bg=PANEL, highlightthickness=1, highlightbackground=EMBER1)
        self.mp_edit_label = tk.Label(self.mp_edit_bar, text="", bg=PANEL, fg=EMBER2, anchor="w",
                                      font=(self.f_mono, 9, "bold"))
        self.mp_edit_label.pack(side="left", fill="x", expand=True, padx=10, pady=6)
        ttk.Button(self.mp_edit_bar, text="Annuler la modification", command=self.mp_exit_edit).pack(
            side="right", padx=8, pady=4)

        srch = tk.Frame(mp, bg=BG)
        srch.pack(fill="x", padx=14, pady=(8, 0))
        tk.Label(srch, text="MODS", bg=BG, fg=MUTED, font=mono8).pack(side="left", padx=(0, 8))
        self.mp_query = tk.StringVar()
        qentry = ttk.Entry(srch, textvariable=self.mp_query)
        qentry.pack(side="left", fill="x", expand=True)
        qentry.bind("<Return>", lambda e: self.mp_search())
        ttk.Button(srch, text="Rechercher", command=self.mp_search).pack(side="left", padx=(8, 0))
        self.mp_filter_btn = ttk.Button(srch, text="Filtres ▾", command=self.toggle_mp_filters)
        self.mp_filter_btn.pack(side="left", padx=(8, 0))
        self.mp_view_btn = ttk.Button(srch, text="", command=self.show_view_menu)
        self.mp_view_btn.pack(side="left", padx=(8, 0))
        self.update_view_button()

        self.mp_icon_hint = tk.Label(mp, text="⚠ Certaines icônes ne s'affichent pas (Pillow n'est pas installé) : "
                                              "cliquez ici pour l'installer.", bg=BG, fg=EMBER2, cursor="hand2",
                                     anchor="w", justify="left", wraplength=500, font=(self.f_mono, 8))
        self.mp_icon_hint.bind("<Button-1>", lambda e: self.install_pillow())
        self._icon_hint_shown = False
        area = self.mp_area = tk.Frame(mp, bg=BG)
        area.pack(fill="both", expand=True, padx=14, pady=(8, 0))
        self.mp_side = tk.Frame(area, bg=PANEL, width=215, highlightthickness=1, highlightbackground=BORDER)
        self.mp_side.pack_propagate(False)  # volontairement non affiché tant que « Filtres » n'est pas cliqué
        self.build_mp_filters()
        self.mp_rf = rf = tk.Frame(area, bg=BG)
        rf.pack(side="left", fill="both", expand=True)
        self.mp_canvas, self.mp_cards = self.make_scroll_area(rf)
        self.mp_canvas.bind("<Configure>", lambda e: self.mp_grid and self.mp_grid.layout(e.width), add="+")
        self.mp_body = tk.Frame(self.mp_cards, bg=BG)
        self.mp_body.pack(fill="x")
        tk.Label(self.mp_body, text="Chargement des mods populaires...", bg=BG, fg=MUTED,
                 font=(self.f_body, 10)).pack(pady=40)

        self.mp_pack_label = tk.Label(mp, text="", bg=BG, fg=BLUE, anchor="w", font=mono8)
        self.mp_pack_label.pack(fill="x", padx=14, pady=(8, 2))
        pf = tk.Frame(mp, bg=BG)
        pf.pack(fill="x", padx=14)
        self.mp_pack_canvas, self.mp_pack_cards = self.make_scroll_area(pf, height=self._pack_h)
        self.mp_pack_canvas.bind("<Configure>", lambda e: self.mp_pack_grid and self.mp_pack_grid.layout(e.width),
                                 add="+")
        self.mp_create_btn = GradientButton(mp, text="CRÉER L'INSTANCE", command=self.mp_create,
                                            font=(self.f_display, 11, "bold"), height=44)
        self.mp_create_btn.pack(fill="x", padx=14, pady=(8, 4))
        tk.Label(mp, text="Dépendances requises ajoutées automatiquement · Source : Modrinth", bg=BG, fg=MUTED,
                 font=mono8).pack(pady=(0, 2))
        self.refresh_mp_pack()
        self.mp_ver_var.trace_add("write", lambda *_: self.mp_changed())
        self.mp_loader_var.trace_add("write", lambda *_: self.mp_changed())

        self.tab = None
        self.show_tab("instances")
        self.bind("<F11>", self.toggle_fullscreen)
        self.bind("<Escape>", self.exit_fullscreen)
        self.bind("<Configure>", self.on_resize)
        self.fs_label.lift()

    # ---------- Modpacks (Modrinth) ----------
    def fill_mp_versions(self):
        """Remplit la liste des versions à l'ouverture (elle est chargée en arrière-plan au démarrage)."""
        ids = [v["id"] for v in self.all_versions if v["type"] == "release"]
        if ids:
            self.mp_ver_box["values"] = ids

    def make_scroll_area(self, parent, height=None, bg=BG):
        """Zone défilante (canvas + barre + cadre intérieur). Renvoie (canvas, cadre)."""
        canvas = tk.Canvas(parent, bg=bg, highlightthickness=0, bd=0, **({"height": height} if height else {}))
        sb = ttk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        inner = tk.Frame(canvas, bg=bg)
        win_id = canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(win_id, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        return canvas, inner

    # ---------- Plein écran, redimensionnement, molette ----------
    def set_fullscreen(self, on):
        self.fullscreen = on
        self.attributes("-fullscreen", on)
        self.fs_label.config(text="QUITTER LE PLEIN ÉCRAN · F11" if on else "PLEIN ÉCRAN · F11")

    def toggle_fullscreen(self, _e=None):
        self.set_fullscreen(not self.fullscreen)
        return "break"

    def exit_fullscreen(self, e=None):
        if self.fullscreen:
            self.set_fullscreen(False)

    def on_resize(self, e):
        """Plus la fenêtre est haute, plus la liste « Mon modpack » peut l'être aussi."""
        if e.widget is not self:
            return
        h = 84 if e.height < 950 else 170
        if h != self._pack_h:
            self._pack_h = h
            self.mp_pack_canvas.config(height=h)

    def on_wheel(self, e):
        if self.tab not in ("instances", "modpack"):
            return
        canvas = self.cards_canvas if self.tab == "instances" else self.mp_canvas
        if self.tab == "modpack":
            try:
                w = self.winfo_containing(e.x_root, e.y_root)
            except KeyError:
                w = None
            while w is not None:
                if w is self.mp_pack_canvas or w is self.mp_side_canvas:
                    canvas = w
                    break
                w = w.master
        canvas.yview_scroll(int(-e.delta / 120), "units")

    # ---------- Modpacks (Modrinth) : cartes de mods ----------
    # ---------- « Mon modpack » : mods choisis + dépendances ----------
    def cached_get(self, path, params=None):
        """Requêtes Modrinth mémorisées 10 minutes (le calcul des dépendances les refait souvent)."""
        key = (path, json.dumps(params, sort_keys=True) if params else "")
        hit = self._http_cache.get(key)
        if hit and time.monotonic() - hit[0] < 600:
            return hit[1]
        data = modrinth_get(path, params)
        self._http_cache[key] = (time.monotonic(), data)
        return data

    def mp_changed(self):
        """La sélection (ou la version / le loader) a changé : on recalcule les dépendances."""
        self.mp_pre = None
        self._pre_gen += 1  # un calcul en cours devient obsolète
        self.refresh_mp_pack()
        if self._pre_job:
            self.after_cancel(self._pre_job)
        self._pre_job = self.after(400, self.run_preview)

    def run_preview(self):
        """Cherche (en arrière-plan) les dépendances des mods ajoutés pour les montrer avant la création."""
        self._pre_job = None
        old = self.mp_edit["meta"]["mods"] if self.mp_edit else []
        old_ids = {m["project_id"] for m in old}
        roots = [dict(m) for m in self.mp_selected if m["project_id"] not in old_ids]
        if not roots:
            self.mp_pre = {}
            self.refresh_mp_pack()
            return
        mc, loader = self.mp_ver_var.get().strip(), self.mp_loader_var.get()
        if not mc or loader not in MODRINTH_LOADERS:
            self.mp_pre = False
            self.refresh_mp_pack()
            return
        gen = self._pre_gen

        def worker():
            try:
                plan, _warnings = resolve_modpack(mc, loader, roots, self.cached_get)
                result = {i["project_id"]: i for i in plan}
            except Exception:
                result = False
            self.after(0, lambda: self.preview_done(gen, result))

        threading.Thread(target=worker, daemon=True).start()

    def preview_done(self, gen, result):
        if gen != self._pre_gen:
            return  # la sélection a changé entre-temps
        self.mp_pre = result
        self.refresh_mp_pack()

    def wrap_labels(self, frame, pairs):
        """Adapte le retour à la ligne de plusieurs textes à la largeur de leur cadre."""
        last = {"w": 0}

        def relayout(e):
            if e.width == last["w"]:
                return
            last["w"] = e.width
            for label, margin in pairs:
                label.config(wraplength=max(90, e.width - margin))

        frame.bind("<Configure>", relayout)

    def pack_x(self, parent, pid, bg):
        x = tk.Label(parent, text="✕", bg=bg, fg=MUTED, cursor="hand2", padx=8, font=(self.f_body, 10, "bold"))
        x.bind("<Button-1>", lambda e, p=pid: self.mp_remove_id(p))
        x.bind("<Enter>", lambda e, w=x: w.config(fg=EMBER1))
        x.bind("<Leave>", lambda e, w=x: w.config(fg=MUTED))
        return x

    def refresh_mp_pack(self):
        for w in self.mp_pack_cards.winfo_children():
            w.destroy()
        old = self.mp_edit["meta"]["mods"] if self.mp_edit else []
        old_ids = {m["project_id"] for m in old}
        new_roots = [m for m in self.mp_selected if m["project_id"] not in old_ids]
        rows = pack_rows(old, self.mp_selected, self.mp_pre if isinstance(self.mp_pre, dict) else None)
        mode = self.mp_view.get()
        self.mp_pack_grid = None
        if mode == "tiles":
            host = tk.Frame(self.mp_pack_cards, bg=BG)
            host.pack(fill="x")
            self.mp_pack_grid = TileGrid(host, 210)
        elif mode == "table" and rows:
            self.build_pack_header()
        build = {"list": self.build_pack_row, "tiles": self.build_pack_tile, "table": self.build_pack_trow}[mode]
        for r in rows:
            build(r)
        if self.mp_pack_grid:
            self.mp_pack_grid.layout(self.mp_pack_canvas.winfo_width())
        hint = None
        if not rows:
            hint = "Aucun mod pour l'instant : cliquez sur AJOUTER."
        elif self.mp_pre is None and new_roots:
            hint = "Calcul des dépendances..."
        elif self.mp_pre is False and new_roots:
            hint = "Dépendances non calculées (connexion ?) : elles seront ajoutées à la création."
        if hint:
            tk.Label(self.mp_pack_cards, text=hint, bg=BG, fg=MUTED, font=(self.f_body, 9)).pack(anchor="w", pady=6)
        n, d = len(self.mp_selected), sum(1 for r in rows if r["kind"] == "dep")
        text = f"MON MODPACK  ·  {n} mod{'s' if n > 1 else ''}"
        if d:
            text += f"  ·  {d} dépendance{'s' if d > 1 else ''}"
        self.mp_pack_label.config(text=text + "  (✕ pour retirer)")
        for pid in list(self.mp_card_btns):
            self.update_mp_button(pid)

    def pack_style(self, r):
        """(fond, retirable) : les mods choisis se retirent avec ✕, les dépendances se gèrent toutes seules."""
        root = r["kind"] in ("root", "missing")
        return (PANEL if root else FIELD), root

    # -- Mode « Liste »
    def build_pack_row(self, r):
        bg, removable = self.pack_style(r)
        note, color = pack_note(r)
        row = tk.Frame(self.mp_pack_cards, bg=bg, highlightthickness=1, highlightbackground=BORDER)
        row.pack(fill="x", padx=(0, 6), pady=2)
        if removable:
            self.pack_x(row, r["id"], bg).pack(side="right")
        body = tk.Frame(row, bg=bg)
        body.pack(side="left", fill="x", expand=True, padx=10, pady=4)
        tk.Label(body, text=r["title"], bg=bg, fg=FG, anchor="w", font=(self.f_body, 10)).pack(fill="x")
        if note:
            lbl = tk.Label(body, text=note, bg=bg, fg=color, anchor="w", justify="left", wraplength=300,
                           font=(self.f_body, 8))
            lbl.pack(fill="x")
            self.wrap_labels(row, [(lbl, 60)])

    # -- Mode « Tuiles »
    def build_pack_tile(self, r):
        bg, removable = self.pack_style(r)
        note, color = pack_note(r)
        t = tk.Frame(self.mp_pack_grid.host, bg=bg, highlightthickness=1, highlightbackground=BORDER)
        self.mp_pack_grid.add(t)
        top = tk.Frame(t, bg=bg)
        top.pack(fill="x", padx=8, pady=(6, 2))
        if removable:
            self.pack_x(top, r["id"], bg).pack(side="right", anchor="n")
        title = tk.Label(top, text=r["title"], bg=bg, fg=FG, anchor="w", justify="left", wraplength=150,
                         font=(self.f_body, 10, "bold"))
        title.pack(side="left", fill="x", expand=True)
        pairs = [(title, 50)]
        if note:
            lbl = tk.Label(t, text=note, bg=bg, fg=color, anchor="nw", justify="left", wraplength=180,
                           font=(self.f_body, 8))
            lbl.pack(fill="x", padx=8, pady=(0, 6))
            pairs.append((lbl, 20))
        self.wrap_labels(t, pairs)

    # -- Mode « Tableau »
    def pack_cols(self, row):
        row.columnconfigure(0, weight=2)
        row.columnconfigure(1, weight=3)
        row.columnconfigure(2, minsize=34)

    def build_pack_header(self):
        row = tk.Frame(self.mp_pack_cards, bg=BG)
        row.pack(fill="x", padx=(0, 6))
        self.pack_cols(row)
        for col, text in ((0, "MOD"), (1, "DÉTAIL")):
            tk.Label(row, text=text, bg=BG, fg=MUTED, anchor="w", font=(self.f_mono, 8)).grid(
                row=0, column=col, sticky="we", padx=8)

    def build_pack_trow(self, r):
        bg, removable = self.pack_style(r)
        note, color = pack_note(r)
        row = tk.Frame(self.mp_pack_cards, bg=bg, highlightthickness=1, highlightbackground=BORDER)
        row.pack(fill="x", padx=(0, 6), pady=1)
        self.pack_cols(row)
        tk.Label(row, text=r["title"], bg=bg, fg=FG, anchor="w", width=1, font=(self.f_body, 10)).grid(
            row=0, column=0, sticky="we", padx=8, pady=4)
        tk.Label(row, text=note, bg=bg, fg=color, anchor="w", width=1, font=(self.f_body, 8)).grid(
            row=0, column=1, sticky="we", padx=8)
        if removable:
            self.pack_x(row, r["id"], bg).grid(row=0, column=2, sticky="e")

    def update_mp_button(self, pid):
        btn = self.mp_card_btns.get(pid)
        if not btn:
            return
        added = any(m["project_id"] == pid for m in self.mp_selected)
        try:
            btn.set_label("✓ AJOUTÉ" if added else "AJOUTER", muted=added)
        except tk.TclError:
            self.mp_card_btns.pop(pid, None)

    # ---------- Filtres ----------
    def build_mp_filters(self):
        """Panneau latéral (comme Modrinth) : tri, environnement, catégories. Défile s'il est trop haut."""
        self.mp_side_canvas, side = self.make_scroll_area(self.mp_side, bg=PANEL)
        self.mp_cat_vars = {c: tk.BooleanVar() for c in MP_CATEGORIES}
        self.mp_env_client, self.mp_env_server = tk.BooleanVar(), tk.BooleanVar()
        self.mp_sort_var = tk.StringVar(value=next(iter(MP_SORTS)))

        def head(text):
            tk.Label(side, text=text, bg=PANEL, fg=BLUE, anchor="w", font=(self.f_mono, 8, "bold")).pack(
                fill="x", padx=10, pady=(12, 4))

        def check(text, var):
            ttk.Checkbutton(side, text=text, variable=var, style="Card.TCheckbutton",
                            command=self.on_mp_filter).pack(anchor="w", padx=10, pady=1)

        head("TRIER PAR")
        cb = ttk.Combobox(side, textvariable=self.mp_sort_var, values=list(MP_SORTS), state="readonly")
        cb.pack(fill="x", padx=10)
        cb.bind("<<ComboboxSelected>>", lambda e: self.on_mp_filter())
        head("ENVIRONNEMENT")
        check("Client", self.mp_env_client)
        check("Serveur", self.mp_env_server)
        head("CATÉGORIES")
        for c in MP_CATEGORIES:
            check(CATEGORY_FR.get(c, c.capitalize()), self.mp_cat_vars[c])
        ttk.Button(side, text="Réinitialiser", command=self.reset_mp_filters).pack(fill="x", padx=10, pady=14)

    def mp_filter_count(self):
        return (sum(v.get() for v in self.mp_cat_vars.values()) + int(self.mp_env_client.get())
                + int(self.mp_env_server.get()) + int(self.mp_sort_var.get() != next(iter(MP_SORTS))))

    def update_mp_filter_button(self):
        n = self.mp_filter_count()
        self.mp_filter_btn.config(text=f"Filtres{f' ({n})' if n else ''} {'▴' if self.mp_filters_open else '▾'}")

    def toggle_mp_filters(self):
        self.mp_filters_open = not self.mp_filters_open
        if self.mp_filters_open:
            self.mp_side.pack(side="left", fill="y", padx=(0, 8), before=self.mp_rf)
        else:
            self.mp_side.pack_forget()
        self.update_mp_filter_button()

    def on_mp_filter(self):
        """Une case cochée relance la recherche (après 0,35 s sans nouveau clic)."""
        self.update_mp_filter_button()
        if self._mp_job:
            self.after_cancel(self._mp_job)
        self._mp_job = self.after(350, self.mp_search)

    def reset_mp_filters(self):
        for v in self.mp_cat_vars.values():
            v.set(False)
        self.mp_env_client.set(False)
        self.mp_env_server.set(False)
        self.mp_sort_var.set(next(iter(MP_SORTS)))
        self.on_mp_filter()

    # ---------- Affichage : tuiles / tableau / liste ----------
    def update_view_button(self):
        text = f"Vue : {MP_VIEWS[self.mp_view.get()]} ▾"
        for b in (self.mp_view_btn, self.inst_view_btn):
            b.config(text=text)

    def show_view_menu(self, widget=None):
        m = tk.Menu(self, tearoff=0, bg=PANEL, fg=FG, activebackground=EMBER1, activeforeground="#1A0A04",
                    selectcolor=EMBER2, bd=0, relief="flat", font=(self.f_body, 10))
        for key, label in MP_VIEWS.items():
            m.add_radiobutton(label=label, value=key, variable=self.mp_view, command=self.on_mp_view)
        w = widget or self.mp_view_btn
        try:
            m.tk_popup(w.winfo_rootx(), w.winfo_rooty() + w.winfo_height())
        finally:
            m.grab_release()

    def on_mp_view(self):
        """Un seul réglage d'affichage pour tout : mods à télécharger, mods du modpack, instances."""
        self.update_view_button()
        try:
            self.save_config()
        except Exception:
            pass
        if self.mp_hits:
            self.mp_render(0)
            self.mp_canvas.yview_moveto(0)
        self.refresh_mp_pack()
        self.apply_filter(reset_page=False, force=True)
        self.cards_canvas.yview_moveto(0)

    def mp_render(self, start=0):
        """Affiche les résultats dans le mode choisi. start=0 : tout redessiner ; sinon ajoute la suite."""
        mode = self.mp_view.get()
        if start == 0:
            for w in self.mp_body.winfo_children():
                w.destroy()
            self.mp_card_btns, self.mp_grid = {}, TileGrid(self.mp_body)
            if not self.mp_hits:
                tk.Label(self.mp_body, text="Aucun mod trouvé pour cette recherche, cette version et ce loader.",
                         bg=BG, fg=MUTED, font=(self.f_body, 10)).pack(pady=40)
                return
            if mode == "table":
                self.build_table_header()
        build = {"list": self.build_mod_card, "tiles": self.build_mod_tile, "table": self.build_mod_row}[mode]
        for h in self.mp_hits[start:]:
            build(h)
        if mode == "tiles":
            self.mp_grid.layout(self.mp_canvas.winfo_width())

    # ---------- Recherche ----------
    def mp_search(self, more=False):
        self._mp_job = None
        mc, loader = self.mp_ver_var.get().strip(), self.mp_loader_var.get()
        if not mc:
            messagebox.showinfo("Modpack", "Indiquez la version de Minecraft.")
            return
        if self._mp_searching:
            if not more:
                self._mp_dirty = True  # relancée dès que la recherche en cours est finie
            return
        query = self.mp_query.get().strip()
        cats = tuple(c for c in MP_CATEGORIES if self.mp_cat_vars[c].get())
        envs = tuple(e for e, v in (("client", self.mp_env_client), ("server", self.mp_env_server)) if v.get())
        sort = MP_SORTS[self.mp_sort_var.get()]
        key = (query, mc, loader, cats, envs, sort)
        offset = len(self.mp_hits) if more and self.mp_last == key else 0
        self._mp_searching = True
        self.set_status("Recherche sur Modrinth...")

        def worker():
            hits, total, err = [], 0, None
            try:
                data = modrinth_search(query, mc, loader, offset, categories=cats, envs=envs, sort=sort)
                hits, total = data.get("hits", []), data.get("total_hits", 0)
            except Exception as exc:
                err = explain_modrinth_error(exc)
            self.after(0, lambda: self.mp_search_done(hits, total, err, key, offset))

        threading.Thread(target=worker, daemon=True).start()

    def mp_search_done(self, hits, total, err, key, offset):
        self._mp_searching = False
        if err:
            self.set_status("Recherche impossible.")
            messagebox.showwarning("Modrinth", err)
            return
        if self._mp_dirty:  # les filtres ont changé pendant la recherche : on recommence
            self._mp_dirty = False
            self.mp_search()
            return
        start = 0 if offset == 0 else len(self.mp_hits)
        self.mp_hits = hits if offset == 0 else self.mp_hits + hits
        if offset == 0:
            self.mp_canvas.yview_moveto(0)
        self.mp_render(start)
        self.mp_last, self.mp_total = key, total
        self.update_mp_more()
        self.set_status(f"{len(self.mp_hits)} sur {total} mods pour Minecraft {key[1]} ({key[2]}).")

    def update_mp_more(self):
        """Boutons sous la liste : « Réduire » (retire le dernier lot) et « Charger plus »."""
        if self._mp_more is not None:
            self._mp_more.destroy()
            self._mp_more = None
        n = len(self.mp_hits)
        more, less = n < self.mp_total, n > MP_PAGE
        if not (more or less):
            return
        bar = self._mp_more = tk.Frame(self.mp_cards, bg=BG)
        bar.pack(pady=10)
        if less:
            ttk.Button(bar, text="▲ Réduire la liste", command=self.mp_less).pack(side="left", padx=4)
        if more:
            ttk.Button(bar, text="▼ Charger plus de résultats",
                       command=lambda: self.mp_search(more=True)).pack(side="left", padx=4)

    def mp_less(self):
        """Retire le dernier lot de résultats affichés (jamais en dessous du premier lot)."""
        n = len(self.mp_hits)
        if n <= MP_PAGE:
            return
        self.mp_hits = self.mp_hits[:max(MP_PAGE, ((n - 1) // MP_PAGE) * MP_PAGE)]
        self.mp_render(0)
        self.update_mp_more()
        self.mp_canvas.update_idletasks()
        self.mp_canvas.yview_moveto(1.0)  # on reste en bas, à côté des boutons
        self.set_status(f"{len(self.mp_hits)} sur {self.mp_total} mods affichés.")

    def mod_tags(self, h):
        """Pastilles d'un mod : environnement, catégories, loaders (comme sur Modrinth)."""
        tags = []
        client = h.get("client_side") in ("required", "optional")
        server = h.get("server_side") in ("required", "optional")
        if client and server:
            tags.append(("Client ou serveur", FG))
        elif client:
            tags.append(("Client", FG))
        elif server:
            tags.append(("Serveur", FG))
        cats = h.get("display_categories") or h.get("categories") or []
        tags += [(CATEGORY_FR.get(c, c.replace("-", " ").capitalize()), MUTED)
                 for c in cats if c not in LOADER_COLORS][:3]
        tags += [(LOADER_NAMES[c], LOADER_COLORS[c]) for c in (h.get("categories") or []) if c in LOADER_COLORS]
        return tags

    def mod_icon(self, parent, h, size, font_size):
        """Cadre carré avec la lettre du mod ; l'image la remplace une fois téléchargée."""
        box = tk.Frame(parent, bg=FIELD, width=size, height=size)
        box.pack_propagate(False)
        label = tk.Label(box, text=(h.get("title") or "?")[:1].upper(), bg=FIELD, fg=EMBER2,
                         font=(self.f_display, font_size, "bold"))
        label.pack(fill="both", expand=True)
        self.load_mod_icon(h.get("icon_url"), label, size)
        return box

    def mod_globe(self, parent, h, size):
        return GlobeButton(parent, command=lambda hh=h: self.open_mod_page(hh), size=size)

    def open_mod_page(self, h):
        """Ouvre la page du mod sur Modrinth (description, galerie, versions, liens...)."""
        ident = urllib.parse.quote(str(h.get("slug") or h.get("project_id") or ""), safe="")
        if ident:
            webbrowser.open(f"https://modrinth.com/mod/{ident}")
            self.set_status(f"Page de « {h.get('title') or 'ce mod'} » ouverte dans le navigateur.")

    def mod_button(self, parent, h, width, height, font_size):
        btn = GradientButton(parent, text="AJOUTER", bg=PANEL, width=width, height=height,
                             font=(self.f_display, font_size, "bold"), command=lambda hh=h: self.mp_toggle(hh))
        self.mp_card_btns[h["project_id"]] = btn
        self.update_mp_button(h["project_id"])
        return btn

    # -- Mode « Liste »
    def build_mod_card(self, h):
        card = tk.Frame(self.mp_body, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        card.pack(fill="x", padx=(0, 6), pady=4)
        self.mod_icon(card, h, 56, 16).pack(side="left", padx=12, pady=12, anchor="n")

        right = tk.Frame(card, bg=PANEL)
        right.pack(side="right", padx=12, pady=12, anchor="n")
        tk.Label(right, text=f"↓ {short_count(h.get('downloads'))}   ♥ {short_count(h.get('follows'))}",
                 bg=PANEL, fg=FG, font=(self.f_mono, 9, "bold")).pack(anchor="e")
        actions = tk.Frame(right, bg=PANEL)
        actions.pack(anchor="e", pady=(8, 0))
        self.mod_globe(actions, h, 34).pack(side="left", padx=(0, 6))
        self.mod_button(actions, h, 112, 34, 9).pack(side="left")

        mid = tk.Frame(card, bg=PANEL)
        mid.pack(side="left", fill="x", expand=True, pady=12)
        head = tk.Frame(mid, bg=PANEL)
        head.pack(fill="x")
        tk.Label(head, text=h.get("title") or "?", bg=PANEL, fg=FG, font=(self.f_display, 10, "bold")).pack(side="left")
        tk.Label(head, text=f"  par {h.get('author') or '?'}", bg=PANEL, fg=MUTED,
                 font=(self.f_body, 9)).pack(side="left")
        text = (h.get("description") or "").strip()
        desc = tk.Label(mid, text=text if len(text) <= 170 else text[:167] + "...", bg=PANEL, fg=MUTED,
                        justify="left", anchor="w", wraplength=300, font=(self.f_body, 9))
        desc.pack(fill="x", pady=(3, 6))
        chips = tk.Frame(mid, bg=PANEL)
        chips.pack(fill="x")
        pills = [tk.Label(chips, text=t, bg="#161D36", fg=c, font=(self.f_mono, 8), padx=7, pady=2)
                 for t, c in self.mod_tags(h)]
        last = {"w": 0}

        def relayout(e):
            """Adapte le retour à la ligne de la description et des pastilles à la largeur."""
            if e.width == last["w"]:
                return
            last["w"] = e.width
            desc.config(wraplength=max(160, e.width - 10))
            x = row = col = 0
            for p in pills:
                w = p.winfo_reqwidth() + 5
                if col and x + w > e.width:
                    row, col, x = row + 1, 0, 0
                p.grid(row=row, column=col, sticky="w", padx=(0, 5), pady=(0, 3))
                x, col = x + w, col + 1

        mid.bind("<Configure>", relayout)

    # -- Mode « Tuiles »
    def build_mod_tile(self, h):
        t = tk.Frame(self.mp_body, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        self.mp_grid.add(t)  # placée dans la grille par TileGrid.layout()
        top = tk.Frame(t, bg=PANEL)
        top.pack(fill="x", padx=10, pady=(10, 4))
        self.mod_icon(top, h, 48, 14).pack(side="left", anchor="n")
        txt = tk.Frame(top, bg=PANEL)
        txt.pack(side="left", fill="x", expand=True, padx=(10, 0))
        title = tk.Label(txt, text=h.get("title") or "?", bg=PANEL, fg=FG, anchor="w", justify="left",
                         wraplength=150, font=(self.f_display, 9, "bold"))
        title.pack(fill="x")
        tk.Label(txt, text=f"par {h.get('author') or '?'}", bg=PANEL, fg=MUTED, anchor="w",
                 font=(self.f_body, 9)).pack(fill="x")
        tk.Label(txt, text=f"↓ {short_count(h.get('downloads'))}   ♥ {short_count(h.get('follows'))}",
                 bg=PANEL, fg=FG, anchor="w", font=(self.f_mono, 8, "bold")).pack(fill="x")
        text = (h.get("description") or "").strip()
        desc = tk.Label(t, text=text if len(text) <= 110 else text[:107] + "...", bg=PANEL, fg=MUTED,
                        justify="left", anchor="nw", wraplength=200, font=(self.f_body, 9))
        desc.pack(fill="both", expand=True, padx=10, pady=(2, 4))
        bottom = tk.Frame(t, bg=PANEL)
        bottom.pack(fill="x", padx=10, pady=(0, 10))
        self.mod_globe(bottom, h, 30).pack(side="left")
        self.mod_button(bottom, h, 80, 30, 8).pack(side="left", fill="x", expand=True, padx=(6, 0))
        last = {"w": 0}

        def relayout(e):
            if e.width == last["w"]:
                return
            last["w"] = e.width
            desc.config(wraplength=max(120, e.width - 24))
            title.config(wraplength=max(90, e.width - 24 - 58))

        t.bind("<Configure>", relayout)

    # -- Mode « Tableau »
    def table_cols(self, row):
        for col, (weight, minsize) in enumerate(((0, 44), (1, 0), (0, 96), (0, 66), (0, 58), (0, 36), (0, 108))):
            row.columnconfigure(col, weight=weight, minsize=minsize)

    def build_table_header(self):
        row = tk.Frame(self.mp_body, bg=BG)
        row.pack(fill="x", padx=(0, 6), pady=(0, 2))
        self.table_cols(row)
        for col, text, anchor in ((1, "MOD", "w"), (2, "AUTEUR", "w"), (3, "↓", "e"), (4, "♥", "e")):
            tk.Label(row, text=text, bg=BG, fg=MUTED, anchor=anchor, font=(self.f_mono, 8)).grid(
                row=0, column=col, sticky="we", padx=4)

    def build_mod_row(self, h):
        row = tk.Frame(self.mp_body, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        row.pack(fill="x", padx=(0, 6), pady=1)
        self.table_cols(row)
        self.mod_icon(row, h, 32, 11).grid(row=0, column=0, padx=(8, 4), pady=5)
        tk.Label(row, text=h.get("title") or "?", bg=PANEL, fg=FG, anchor="w", width=1,
                 font=(self.f_body, 10, "bold")).grid(row=0, column=1, sticky="we", padx=4)
        author = h.get("author") or "?"
        tk.Label(row, text=author if len(author) <= 14 else author[:13] + "…", bg=PANEL, fg=MUTED, anchor="w",
                 font=(self.f_body, 9)).grid(row=0, column=2, sticky="w", padx=4)
        tk.Label(row, text=short_count(h.get("downloads")), bg=PANEL, fg=FG, anchor="e",
                 font=(self.f_mono, 9)).grid(row=0, column=3, sticky="e", padx=4)
        tk.Label(row, text=short_count(h.get("follows")), bg=PANEL, fg=MUTED, anchor="e",
                 font=(self.f_mono, 9)).grid(row=0, column=4, sticky="e", padx=4)
        self.mod_globe(row, h, 28).grid(row=0, column=5, sticky="e", padx=2)
        self.mod_button(row, h, 96, 28, 8).grid(row=0, column=6, sticky="e", padx=(4, 8))

    def load_mod_icon(self, url, label, size=56):
        """Télécharge l'icône en arrière-plan (4 à la fois), uniquement depuis le serveur Modrinth.
        Pas d'icône (projet sans image) : la première lettre du mod reste affichée."""
        if not url or not str(url).startswith(MODRINTH_CDN):
            return
        cached = self._mp_icons.get((url, size))
        if cached:
            label.config(image=cached, text="")
            label.image = cached
            return

        def worker():
            raw = None
            for attempt in range(2):  # un second essai si le réseau a eu un raté
                try:
                    with self._icon_sem:
                        req = urllib.request.Request(url, headers={"User-Agent": f"{GITHUB_REPO}/{APP_VERSION}"})
                        with urllib.request.urlopen(req, timeout=15) as r:
                            raw = r.read(2_000_000)
                    break
                except Exception:
                    time.sleep(1.5)
            if raw:
                self.after(0, lambda: self.set_mod_icon(url, raw, label, size))

        threading.Thread(target=worker, daemon=True).start()

    def set_mod_icon(self, url, raw, label, size=56):
        try:
            photo = self._mp_icons.get((url, size))
            if photo is None:
                try:
                    from PIL import Image, ImageTk  # pip install pillow : png, jpg, webp, gif...
                    im = Image.open(io.BytesIO(raw)).convert("RGBA").resize((size, size), Image.LANCZOS)
                    photo = ImageTk.PhotoImage(im)
                except ImportError:  # sans Pillow : seulement png / gif
                    try:
                        img = tk.PhotoImage(data=base64.b64encode(raw))
                        f = max(1, round(img.width() / size))
                        photo = img.subsample(f) if f > 1 else img
                    except tk.TclError:  # jpg / webp... : illisible sans Pillow
                        self.show_icon_hint()
                        return
                self._mp_icons[(url, size)] = photo  # mémorisée même si la carte n'existe plus
            if label.winfo_exists():
                label.config(image=photo, text="")
                label.image = photo
        except Exception:
            pass  # icône illisible (svg...) : la lettre reste affichée

    def show_icon_hint(self):
        if not self._icon_hint_shown:
            self._icon_hint_shown = True
            self.mp_icon_hint.pack(fill="x", padx=14, pady=(6, 0), before=self.mp_area)

    def install_pillow(self):
        """Installe Pillow (décodage des icônes jpg / webp) après accord de l'utilisateur."""
        if getattr(sys, "frozen", False):  # application empaquetée : pas de pip disponible
            messagebox.showinfo("Icônes", "Installez Pillow avec :\n    pip install pillow\npuis relancez WeCraft.")
            return
        if not messagebox.askyesno("Installer Pillow", "WeCraft va exécuter :\n    pip install pillow\n\n"
                                   "(quelques secondes, connexion internet requise). Continuer ?", parent=self):
            return
        self.set_status("Installation de Pillow...")

        def worker():
            try:
                r = subprocess.run([sys.executable, "-m", "pip", "install", "pillow"], capture_output=True,
                                   text=True, timeout=300, creationflags=0x08000000 if os.name == "nt" else 0)
                ok, out = r.returncode == 0, (r.stderr or r.stdout or "")[-400:]
            except Exception as exc:
                ok, out = False, str(exc)
            self.after(0, lambda: self.pillow_done(ok, out))

        threading.Thread(target=worker, daemon=True).start()

    def pillow_done(self, ok, out):
        if not ok:
            self.set_status("Installation de Pillow impossible.")
            messagebox.showwarning("Pillow", f"L'installation a échoué :\n{out}\n\nEssayez à la main : pip install pillow")
            return
        importlib.invalidate_caches()
        self.set_status("Pillow installé : chargement des icônes...")
        self.mp_icon_hint.pack_forget()
        self._icon_hint_shown = False
        if self.mp_hits:
            self.mp_render(0)  # les icônes manquantes sont redemandées

    def mp_toggle(self, h):
        pid = h["project_id"]
        if any(m["project_id"] == pid for m in self.mp_selected):
            self.mp_remove_id(pid)
        else:
            self.mp_selected.append({"project_id": pid, "title": h["title"]})
            self.mp_changed()

    def mp_remove_id(self, pid):
        self.mp_selected = [m for m in self.mp_selected if m["project_id"] != pid]
        self.mp_changed()

    def mp_progress(self, done, total, msg):
        def _do():
            if total:
                self.progress["maximum"], self.progress["value"] = total, done
                self.set_status(f"Téléchargement {done}/{total} · {msg}")
            else:
                self.set_status(msg)
        self.after(0, _do)

    def mp_notice(self, mc, loader, ok_text, on_ok):
        """Petite bulle d'information affichée avant de créer / enregistrer."""
        if self._mp_notice is not None and self._mp_notice.winfo_exists():
            self._mp_notice.lift()
            return
        win = self._mp_notice = self.small_dialog("À savoir", 460, 360)
        tk.Label(win, text="À SAVOIR", bg=BG, fg=FG, font=(self.f_display, 12, "bold")).pack(pady=(16, 2))
        GradientBar(win).pack(fill="x", padx=20, pady=8)
        bubble = tk.Frame(win, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        bubble.pack(fill="x", padx=20, pady=(0, 10))
        tk.Label(bubble, text=f"Chaque mod choisi est téléchargé dans sa dernière version sortie compatible "
                              f"avec Minecraft {mc} ({loader}), en version stable si possible.",
                 bg=PANEL, fg=FG, justify="left", anchor="w", wraplength=390,
                 font=(self.f_body, 10)).pack(fill="x", padx=12, pady=(12, 6))
        tk.Label(bubble, text="Pour utiliser une autre version d'un mod, il faudra la chercher vous-même sur "
                              "internet (bouton globe sur la carte du mod), puis la déposer dans le dossier "
                              "« mods » de l'instance à la place du fichier d'origine.",
                 bg=PANEL, fg=MUTED, justify="left", anchor="w", wraplength=390,
                 font=(self.f_body, 10)).pack(fill="x", padx=12, pady=(0, 12))
        row = tk.Frame(win, bg=BG)
        row.pack(fill="x", padx=20, pady=6)

        def confirm():
            win.destroy()
            on_ok()

        GradientButton(row, text=ok_text, command=confirm, font=(self.f_display, 9, "bold"),
                       height=40).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Annuler", command=win.destroy).pack(side="left", padx=(8, 0))
        win.bind("<Escape>", lambda e: win.destroy())
        try:
            win.grab_set()
        except tk.TclError:
            pass

    def mp_create(self):
        if self._mp_busy:
            return
        if self.mp_edit:
            self.mp_save_edit()
            return
        name = self.mp_name_var.get().strip()
        mc, loader = self.mp_ver_var.get().strip(), self.mp_loader_var.get()
        if not name or not mc:
            messagebox.showinfo("Modpack", "Indiquez un nom et une version de Minecraft.")
            return
        if not self.mp_selected:
            messagebox.showinfo("Modpack", "Ajoutez d'abord au moins un mod (bouton AJOUTER dans les résultats).")
            return
        folder = INSTANCES_DIR / safe_folder_name(name)
        if folder.exists():
            messagebox.showwarning("Nom déjà utilisé", f"Une instance « {folder.name} » existe déjà.\nChoisissez un autre nom.")
            return
        self.mp_notice(mc, loader, "CRÉER L'INSTANCE", lambda: self.mp_start_create(folder, name, mc, loader))

    def mp_start_create(self, folder, name, mc, loader):
        if self._mp_busy:
            return
        if folder.exists():
            messagebox.showwarning("Nom déjà utilisé", f"Une instance « {folder.name} » existe déjà.\nChoisissez un autre nom.")
            return
        self._mp_busy = True
        self.mp_create_btn.config(state="disabled")
        self.progress["value"] = 0
        roots = list(self.mp_selected)

        def worker():
            result, err = None, None
            try:
                result = build_modpack(folder, name, mc, loader, roots, self.mp_progress)
            except Exception as exc:
                err = explain_modrinth_error(exc)
            self.after(0, lambda: self.mp_done(result, err, folder.name))

        threading.Thread(target=worker, daemon=True).start()

    def mp_done(self, result, err, folder_name):
        self._mp_busy = False
        self.mp_create_btn.config(state="normal")
        if err:
            self.set_status("Création annulée.")
            messagebox.showerror("Modpack", f"L'instance n'a pas pu être créée :\n{err}")
            return
        self.set_status(f"Instance « {folder_name} » créée.")
        msg = f"Instance « {folder_name} » créée avec {result['count']} mods"
        if result["deps"]:
            msg += f" (dont {result['deps']} dépendances ajoutées automatiquement)"
        msg += ".\nElle apparaît dans « MES INSTANCES » avec son bouton LANCER."
        if result["warnings"]:
            msg += "\n\nÀ vérifier :\n- " + "\n- ".join(result["warnings"])
        self.mp_selected = []
        self.mp_changed()
        self.reset_filters()
        self.search_var.set(folder_name)
        self.refresh_instances(force=True)
        self.show_tab("instances")
        messagebox.showinfo("Modpack créé", msg)

    # ---------- Modifier un modpack WeCraft ----------
    def edit_modpack(self, inst):
        """Recharge un modpack créé par WeCraft dans l'onglet Modpacks pour y ajouter / retirer des mods.
        Version de Minecraft et loader restent figés (les mods existants en dépendent)."""
        folder = Path(inst["folder"])
        try:
            meta = json.loads((folder / "wecraft_modpack.json").read_text(encoding="utf-8"))
            mc, loader, mods = meta["minecraft"], meta["loader"], list(meta["mods"])
            if loader not in MODRINTH_LOADERS:
                raise ValueError(loader)
        except Exception:
            messagebox.showerror("Modpack", "Les informations de ce modpack sont illisibles "
                                            "(wecraft_modpack.json) : il ne peut pas être modifié ici.")
            return
        if self._mp_busy or self.busy:
            messagebox.showinfo("Modpack", "Une opération est en cours : réessayez dans un instant.")
            return
        if self.mp_selected and not self.mp_edit and not messagebox.askyesno(
                "Modifier le modpack", "Votre sélection de mods en cours (non créée) sera remplacée.\nContinuer ?",
                parent=self):
            return
        self.mp_edit = {"folder": folder, "meta": meta, "display": inst["display"]}
        self.mp_selected = [{"project_id": m["project_id"], "title": m.get("title") or m["filename"]}
                            for m in mods if not m.get("dependency")]
        self.mp_pre = None
        self.mp_name_var.set(inst["display"])
        self.mp_ver_var.set(mc)
        self.mp_loader_var.set(loader)
        self.mp_name_entry.config(state="readonly")
        self.mp_ver_box.config(state="disabled")
        self.mp_loader_box.config(state="disabled")
        self.mp_edit_label.config(text=f"MODIFICATION  ·  {inst['display']}  ({mc} · {loader})")
        self.mp_edit_bar.pack(fill="x", padx=14, pady=(4, 0), before=self.mp_form)
        self.mp_create_btn.set_label("ENREGISTRER LES MODIFICATIONS")
        self.mp_changed()
        self._mp_auto = True
        self.show_tab("modpack")
        self.mp_search()

    def mp_exit_edit(self):
        if not self.mp_edit:
            return
        self.mp_edit = None
        self.mp_edit_bar.pack_forget()
        self.mp_name_entry.config(state="normal")
        self.mp_ver_box.config(state="normal")
        self.mp_loader_box.config(state="readonly")
        self.mp_name_var.set("Mon modpack")
        self.mp_create_btn.set_label("CRÉER L'INSTANCE")
        self.mp_selected = []
        self.mp_changed()

    def mp_save_edit(self):
        ed = self.mp_edit
        meta = ed["meta"]
        if not self.mp_selected:
            messagebox.showinfo("Modpack", "Un modpack doit contenir au moins un mod.\n"
                                           "Pour le supprimer, utilisez ⚙ > Supprimer dans « Mes instances ».")
            return
        if not ed["folder"].is_dir():
            messagebox.showerror("Modpack", "Le dossier de ce modpack n'existe plus.")
            return
        old_ids = {m["project_id"] for m in meta["mods"]}
        old_roots = {m["project_id"] for m in meta["mods"] if not m.get("dependency")}
        keep = {m["project_id"] for m in self.mp_selected}
        if keep == old_roots:
            messagebox.showinfo("Modpack", "Aucune modification à enregistrer.")
            return
        go = lambda: self.mp_start_edit(list(self.mp_selected))
        if keep - old_ids:  # des mods sont ajoutés : même information que pour une création
            self.mp_notice(meta["minecraft"], meta["loader"], "ENREGISTRER", go)
        else:
            go()

    def mp_start_edit(self, selected):
        ed = self.mp_edit
        if not ed or self._mp_busy:
            return
        self._mp_busy = True
        self.mp_create_btn.config(state="disabled")
        self.progress["value"] = 0

        def worker():
            result, err = None, None
            try:
                result = apply_modpack_edit(ed["folder"], ed["meta"], selected, self.mp_progress)
            except Exception as exc:
                err = explain_modrinth_error(exc)
            self.after(0, lambda: self.mp_edit_done(result, err, ed["display"]))

        threading.Thread(target=worker, daemon=True).start()

    def mp_edit_done(self, result, err, display):
        self._mp_busy = False
        self.mp_create_btn.config(state="normal")
        self.progress["value"] = 0
        if err:  # rien n'a été modifié : on reste en mode modification
            self.set_status("Modification annulée.")
            messagebox.showerror("Modpack", f"Les modifications n'ont pas pu être enregistrées :\n{err}")
            return
        parts = []
        if result["added"]:
            parts.append(f"{result['added']} mod{'s' if result['added'] > 1 else ''} ajouté{'s' if result['added'] > 1 else ''}"
                         + (f" (+ {result['deps']} dépendance{'s' if result['deps'] > 1 else ''})" if result["deps"] else ""))
        if result["removed"]:
            parts.append(f"{result['removed']} retiré{'s' if result['removed'] > 1 else ''}")
        if result["pruned"]:
            parts.append(f"{result['pruned']} dépendance{'s' if result['pruned'] > 1 else ''} devenue"
                         f"{'s' if result['pruned'] > 1 else ''} inutile{'s' if result['pruned'] > 1 else ''} retirée"
                         f"{'s' if result['pruned'] > 1 else ''}")
        msg = f"Modpack « {display} » mis à jour : " + (", ".join(parts) or "réglages enregistrés") + "."
        if result["warnings"]:
            msg += "\n\nÀ vérifier :\n- " + "\n- ".join(result["warnings"])
        self.set_status(f"Modpack « {display} » mis à jour.")
        self.mp_exit_edit()
        self.refresh_instances(force=True, rescan=True)
        self.show_tab("instances")
        messagebox.showinfo("Modpack modifié", msg)

    # ---------- Onglets et instances ----------
    def show_tab(self, tab):
        self.tab = tab
        frames = {"instances": self.instances_frame, "modpack": self.modpack_frame, "manual": self.manual_frame}
        for frame in frames.values():
            frame.pack_forget()
        frames[tab].pack(fill="both", expand=True)
        if tab == "modpack" and not self._mp_auto:  # mods populaires affichés dès la première ouverture
            self._mp_auto = True
            self.after(150, self.mp_search)
        for key, lbl in self.tab_labels.items():
            lbl.config(fg=FG if key == tab else MUTED,
                       font=(self.f_display, 9, "bold") + (("underline",) if key == tab else ()))

    def open_instances_dir(self):
        INSTANCES_DIR.mkdir(parents=True, exist_ok=True)
        webbrowser.open(INSTANCES_DIR.as_uri())

    def poll_instances(self):
        self.refresh_instances()
        self.after(3000, self.poll_instances)

    def refresh_instances(self, force=False, rescan=False):
        """Relit les instances EN ARRIÈRE-PLAN (la fenêtre ne se fige jamais, même avec des milliers) :
        « instances/ » toutes les 3 s (seuls les dossiers modifiés sont relus),
        CurseForge / Modrinth / Prism toutes les 60 s ou via « Actualiser »."""
        if self._scanning:
            if force or rescan:  # rejoué dès que le scan en cours est fini
                old = self._queued or (False, False)
                self._queued = (old[0] or force, old[1] or rescan)
            return
        do_ext = rescan or self._ext is None or time.monotonic() - self._ext_time > 60
        ext_cache = self._ext or []
        self._scanning = True

        def worker():
            try:
                if rescan:
                    _LOCAL_CACHE.clear()
                local = scan_instances()
                ext = detect_external() if do_ext else None
                base = [dict(e) for e in (ext if ext is not None else ext_cache)]
                insts = apply_meta(local + base)
                insts.sort(key=lambda i: (SOURCE_ORDER.get(i["source"], 9), i["display"].lower()))
            except Exception:
                insts, ext = None, None
            self.after(0, lambda: self._scan_done(insts, ext, force))

        threading.Thread(target=worker, daemon=True).start()

    def _scan_done(self, insts, ext, force):
        self._scanning = False
        if ext is not None:
            self._ext, self._ext_time = ext, time.monotonic()
        if insts is not None:
            self._instances = insts
            versions = sorted({i["version"] for i in insts if i["version"]}, key=version_tuple, reverse=True)
            self.ver_box["values"] = ["Toutes"] + versions
            if self.ver_var.get() not in ["Toutes"] + versions:
                self.ver_var.set("Toutes")
            self.apply_filter(reset_page=False, force=force)
        if self._queued:
            f, r = self._queued
            self._queued = None
            self.refresh_instances(force=f, rescan=r)

    def find_instance(self, folder):
        return next((i for i in self._instances if meta_key(i["folder"]) == meta_key(folder)), None)

    # ---------- Recherche, filtres, tri, pagination ----------
    def schedule_filter(self):
        if self._search_job:
            self.after_cancel(self._search_job)
        self._search_job = self.after(200, self.apply_filter)  # attend la fin de la frappe

    def toggle_filters(self):
        self.filters_open = not self.filters_open
        if self.filters_open:
            self.filter_panel.pack(fill="x", padx=14, pady=(6, 0), after=self.top_row)
        else:
            self.filter_panel.pack_forget()
        self.update_filter_button()

    def active_filters(self):
        return sum([self.src_var.get() != "Toutes", self.ldr_var.get() != "Tous", self.ver_var.get() != "Toutes",
                    self.sort_var.get() != SORTS[0], self.show_hidden.get()])

    def update_filter_button(self):
        n = self.active_filters()
        self.filter_btn.config(text=f"Filtres{f' ({n})' if n else ''} {'▴' if self.filters_open else '▾'}")

    def reset_filters(self):
        self.search_var.set("")
        self.src_var.set("Toutes")
        self.ldr_var.set("Tous")
        self.ver_var.set("Toutes")
        self.sort_var.set(SORTS[0])
        self.show_hidden.set(False)
        self.apply_filter()

    def go_page(self, delta):
        self.page = max(0, self.page + delta)
        self.apply_filter(reset_page=False)
        self.cards_canvas.yview_moveto(0)

    def apply_filter(self, reset_page=True, force=False):
        """Filtre + trie la liste en mémoire puis n'affiche que la page courante."""
        self._search_job = None
        if reset_page:
            self.page = 0
        words = self.search_var.get().lower().split()
        src, ldr, ver = self.src_var.get(), self.ldr_var.get(), self.ver_var.get()
        hidden_ok = self.show_hidden.get()
        res = [i for i in self._instances
               if (hidden_ok or not i["hidden"])
               and (src == "Toutes" or i["source"] == src)
               and (ldr == "Tous" or (i["loader"] or "Vanilla") == ldr)
               and (ver == "Toutes" or i["version"] == ver)
               and all(w in i["_hay"] for w in words)]
        sort = self.sort_var.get()
        if sort in ("Nom (A-Z)", "Nom (Z-A)"):
            res.sort(key=lambda i: i["display"].lower(), reverse=sort == "Nom (Z-A)")
        elif sort.startswith("Version"):
            res.sort(key=lambda i: (version_tuple(i["version"]) if i["version"] else (), i["display"].lower()),
                     reverse=sort == "Version (récente)")
        total, pages = len(res), max(1, -(-len(res) // PAGE_SIZE))
        self.page = min(self.page, pages - 1)
        shown = res[self.page * PAGE_SIZE:(self.page + 1) * PAGE_SIZE]

        everything = len(self._instances)
        self.count_label.config(text=(f"{total} instance{'s' if total > 1 else ''}" if total == everything
                                      else f"{total} sur {everything} instances"))
        self.page_label.config(text=f"{self.page + 1} / {pages}")
        self.prev_btn.state(["!disabled"] if self.page > 0 else ["disabled"])
        self.next_btn.state(["!disabled"] if self.page < pages - 1 else ["disabled"])
        self.update_filter_button()

        sig = (self.mp_view.get(), self.page, [(i["display"], i["hidden"], i["source"], str(i["path"]), i["version"], i["loader"],
                            i["loader_version"], i["ram"]) for i in shown])
        if force or sig != self._inst_sig:
            self._inst_sig = sig
            self.render_instances(shown, filtered=bool(words) or self.active_filters() > 0)

    def render_instances(self, insts, filtered=False):
        for w in self.cards.winfo_children():
            w.destroy()
        self.card_buttons = []
        self.inst_grid = None
        if not insts:
            if self._instances and filtered:
                text = "Aucune instance ne correspond.\n\nModifiez la recherche ou cliquez sur « Filtres » puis « Réinitialiser »."
            elif self._instances:
                text = "Toutes vos instances sont masquées.\nOuvrez « Filtres » et cochez « Voir les masquées »."
            else:
                text = ("Aucune instance pour le moment.\n\nCréez-en une dans CurseForge, Modrinth ou Prism\n"
                        "(détectés automatiquement), ou copiez un dossier dans\n« Dossier instances » : "
                        "elle apparaît ici toute seule.")
            tk.Label(self.cards, text=text, bg=BG, fg=MUTED, font=(self.f_body, 10),
                     justify="center").pack(pady=40)
            return
        mode = self.mp_view.get()  # même réglage d'affichage que pour les mods
        if mode == "tiles":
            host = tk.Frame(self.cards, bg=BG)
            host.pack(fill="x", padx=(0, 6))
            self.inst_grid = TileGrid(host, 250)
        elif mode == "table":
            self.build_inst_header()
        build = {"list": self.build_card, "tiles": self.build_inst_tile, "table": self.build_inst_row}[mode]
        for inst in insts:
            build(inst)
        if self.inst_grid:
            self.inst_grid.layout(self.cards_canvas.winfo_width())

    def inst_info(self, inst):
        """Textes d'une instance : (titre, ligne de détail, couleur du détail)."""
        title = inst["display"] + ("  (masquée)" if inst["hidden"] else "")
        detail = " · ".join(x for x in (inst["version"], inst["loader"], inst["loader_version"],
                                        f"{inst['ram']} Go" if inst["ram"] else None) if x)
        tag = SOURCE_LABEL.get(inst["source"], inst["source"].upper())
        line = f"{tag}  ·  {detail or 'version inconnue : cliquez sur RÉGLER'}"
        return title, line, MUTED if inst["hidden"] else (BLUE if detail else EMBER2)

    def inst_buttons(self, parent, inst, width, height, font_size):
        """Boutons ⚙ et LANCER / RÉGLER d'une instance (à placer par l'appelant)."""
        gear = ttk.Button(parent, text="⚙", width=3)
        gear.config(command=lambda i=inst, w=gear: self.show_menu(i, w))
        btn = GradientButton(parent, text="LANCER" if inst["version"] else "RÉGLER", bg=PANEL, width=width,
                             height=height, font=(self.f_display, font_size, "bold"),
                             command=lambda i=inst: self.play_instance(i))
        btn.config(state="disabled" if self.busy else "normal")
        self.card_buttons.append(btn)
        return gear, btn

    # -- Mode « Liste »
    def build_card(self, inst):
        title, line, color = self.inst_info(inst)
        card = tk.Frame(self.cards, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        card.pack(fill="x", padx=(0, 6), pady=4)
        gear, btn = self.inst_buttons(card, inst, 112, 38, 9)
        gear.pack(side="right", padx=(0, 10))
        btn.pack(side="right", padx=8, pady=10)
        left = tk.Frame(card, bg=PANEL)
        left.pack(side="left", fill="x", expand=True, padx=12, pady=10)
        tk.Label(left, text=title, bg=PANEL, fg=MUTED if inst["hidden"] else FG, anchor="w",
                 font=(self.f_display, 11, "bold")).pack(fill="x")
        tk.Label(left, text=line, bg=PANEL, anchor="w", fg=color, font=(self.f_mono, 8)).pack(fill="x")

    # -- Mode « Tuiles »
    def build_inst_tile(self, inst):
        title, line, color = self.inst_info(inst)
        t = tk.Frame(self.inst_grid.host, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        self.inst_grid.add(t)
        name = tk.Label(t, text=title, bg=PANEL, fg=MUTED if inst["hidden"] else FG, anchor="w", justify="left",
                        wraplength=200, font=(self.f_display, 10, "bold"))
        name.pack(fill="x", padx=12, pady=(12, 2))
        info = tk.Label(t, text=line, bg=PANEL, fg=color, anchor="nw", justify="left", wraplength=200,
                        font=(self.f_mono, 8))
        info.pack(fill="both", expand=True, padx=12)
        bottom = tk.Frame(t, bg=PANEL)
        bottom.pack(fill="x", padx=12, pady=12)
        gear, btn = self.inst_buttons(bottom, inst, 80, 34, 9)
        gear.pack(side="left")
        btn.pack(side="left", fill="x", expand=True, padx=(8, 0))
        self.wrap_labels(t, [(name, 24), (info, 24)])

    # -- Mode « Tableau »
    def inst_cols(self, row):
        for col, (weight, minsize) in enumerate(((1, 0), (0, 92), (0, 130), (0, 96), (0, 46))):
            row.columnconfigure(col, weight=weight, minsize=minsize)

    def build_inst_header(self):
        row = tk.Frame(self.cards, bg=BG)
        row.pack(fill="x", padx=(0, 6), pady=(0, 2))
        self.inst_cols(row)
        for col, text in ((0, "NOM"), (1, "SOURCE"), (2, "VERSION · LOADER")):
            tk.Label(row, text=text, bg=BG, fg=MUTED, anchor="w", font=(self.f_mono, 8)).grid(
                row=0, column=col, sticky="we", padx=(10 if col == 0 else 4, 4))

    def build_inst_row(self, inst):
        title, _line, color = self.inst_info(inst)
        row = tk.Frame(self.cards, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        row.pack(fill="x", padx=(0, 6), pady=1)
        self.inst_cols(row)
        tk.Label(row, text=title, bg=PANEL, fg=MUTED if inst["hidden"] else FG, anchor="w", width=1,
                 font=(self.f_body, 10, "bold")).grid(row=0, column=0, sticky="we", padx=(10, 4), pady=8)
        tk.Label(row, text=SOURCE_LABEL.get(inst["source"], inst["source"].upper()), bg=PANEL, fg=MUTED,
                 anchor="w", font=(self.f_mono, 8)).grid(row=0, column=1, sticky="w", padx=4)
        ver = " · ".join(x for x in (inst["version"], inst["loader"]) if x) or "version inconnue"
        tk.Label(row, text=ver, bg=PANEL, fg=color, anchor="w", font=(self.f_mono, 8)).grid(
            row=0, column=2, sticky="w", padx=4)
        gear, btn = self.inst_buttons(row, inst, 88, 28, 8)
        btn.grid(row=0, column=3, sticky="e", padx=4, pady=6)
        gear.grid(row=0, column=4, sticky="e", padx=(0, 8))

    def show_menu(self, inst, widget):
        m = tk.Menu(self, tearoff=0, bg=PANEL, fg=FG, activebackground=EMBER1, activeforeground="#1A0A04",
                    bd=0, relief="flat", font=(self.f_body, 10))
        m.add_command(label="Réglages (version, loader, RAM)...", command=lambda: self.configure_instance(inst))
        if inst["source"] == "WeCraft" and (Path(inst["folder"]) / "wecraft_modpack.json").is_file():
            m.add_command(label="Modifier le modpack (mods)...", command=lambda: self.edit_modpack(inst))
        m.add_command(label="Renommer...", command=lambda: self.rename_instance(inst))
        m.add_command(label="Ouvrir le dossier", command=lambda: webbrowser.open(inst["folder"].as_uri()))
        m.add_separator()
        m.add_command(label="Afficher à nouveau" if inst["hidden"] else "Masquer",
                      command=lambda: self.toggle_hidden(inst))
        m.add_command(label="Supprimer...", command=lambda: self.delete_instance(inst))
        try:
            m.tk_popup(widget.winfo_rootx(), widget.winfo_rooty() + widget.winfo_height())
        finally:
            m.grab_release()

    def small_dialog(self, title, width, height):
        win = tk.Toplevel(self)
        win.title(title)
        win.geometry(f"{width}x{height}+{self.winfo_x() + 70}+{self.winfo_y() + 140}")
        win.configure(bg=BG)
        win.resizable(False, False)
        win.transient(self)
        return win

    def toggle_hidden(self, inst):
        if inst["hidden"]:
            update_meta(inst["folder"], remove=["hidden"])
        else:
            update_meta(inst["folder"], set={"hidden": True})
        self.refresh_instances(force=True)

    def rename_instance(self, inst):
        win = self.small_dialog("Renommer l'instance", 420, 220)
        tk.Label(win, text="RENOMMER", bg=BG, fg=FG, font=(self.f_display, 12, "bold")).pack(pady=(16, 2))
        GradientBar(win).pack(fill="x", padx=20, pady=8)
        tk.Label(win, text="NOUVEAU NOM", bg=BG, fg=MUTED, anchor="w", font=(self.f_mono, 8)).pack(fill="x", padx=24)
        var = tk.StringVar(value=inst["display"])
        entry = ttk.Entry(win, textvariable=var)
        entry.pack(fill="x", padx=24, pady=(0, 6))
        entry.focus_set()
        entry.select_range(0, "end")
        tk.Label(win, text="Seul le nom affiché dans WeCraft change : le dossier de l'instance\n"
                 "n'est pas renommé. Champ vide = nom d'origine.", bg=BG, fg=MUTED, justify="left",
                 anchor="w", font=(self.f_mono, 8)).pack(fill="x", padx=24)

        def save(_e=None):
            name = var.get().strip()[:60]
            if name and name != inst["name"]:
                update_meta(inst["folder"], set={"name": name})
            else:
                update_meta(inst["folder"], remove=["name"])
            win.destroy()
            self.refresh_instances(force=True)

        entry.bind("<Return>", save)
        win.bind("<Escape>", lambda e: win.destroy())
        row = tk.Frame(win, bg=BG)
        row.pack(fill="x", padx=24, pady=12)
        GradientButton(row, text="ENREGISTRER", command=save, font=(self.f_display, 9, "bold"),
                       height=38).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Annuler", command=win.destroy).pack(side="left", padx=(8, 0))

    def delete_instance(self, inst):
        """Suppression définitive du dossier, uniquement après confirmation (réponse par défaut : Non)."""
        if self.busy:
            messagebox.showinfo("Suppression", "Un lancement est en cours : réessayez dans un instant.")
            return
        folder = inst["folder"]
        if not safe_to_delete(folder):
            messagebox.showerror("Suppression refusée", f"Ce dossier ne peut pas être supprimé ici :\n{folder}")
            return
        msg = (f"Supprimer définitivement « {inst['display']} » ?\n\n"
               f"Le dossier suivant et TOUT son contenu (mods, mondes, captures, options...) sera effacé :\n"
               f"{folder}\n\nCette action est irréversible.")
        if inst["source"] != "WeCraft":
            msg += (f"\n\nCette instance vient de {inst['source']} : elle disparaîtra aussi de cette application. "
                    "Pour seulement la cacher dans WeCraft, choisissez « Masquer » à la place.")
        if not messagebox.askyesno("Supprimer l'instance", msg, icon="warning", default="no", parent=self):
            return
        self.set_status(f"Suppression de « {inst['display']} »...")

        def worker():
            try:
                remove_tree(folder)
                forget_meta(folder)
                self.after(0, lambda: (self.set_status(f"Instance « {inst['display']} » supprimée."),
                                       self.refresh_instances(force=True, rescan=True)))
            except Exception as exc:
                err = str(exc)
                self.after(0, lambda: (self.set_status("Suppression incomplète."),
                                       messagebox.showerror("Suppression", f"Impossible de tout supprimer :\n{err}"),
                                       self.refresh_instances(force=True, rescan=True)))

        threading.Thread(target=worker, daemon=True).start()

    def play_instance(self, inst):
        if not inst["version"]:
            self.configure_instance(inst, then_launch=True)
            return
        self.ask_ram(inst["display"], inst["ram"] or int(float(self.ram_var.get())),
                     lambda ram: self.start_instance(inst, ram))

    def start_instance(self, inst, ram):
        if self.busy:
            return
        self.ram_var.set(ram)  # devient la RAM proposée par défaut la prochaine fois
        if inst["ram"] and inst["ram"] != ram:  # l'instance avait sa propre RAM : on la met à jour
            try:
                update_meta(inst["folder"], set={"ram": ram})
            except Exception:
                pass
            self.refresh_instances(force=True)
        loader = inst["loader"] if inst["loader"] in LOADERS else "Vanilla"
        self.save_config()
        params = dict(
            version=inst["version"], custom=False, game_dir=str(inst["path"]), loader_name=loader,
            ram=ram, then_launch=True,
            loader_version=inst["loader_version"] if loader != "Vanilla" else None,
            force=False, profile=profile_name_for(inst["display"]),
        )
        self.set_buttons("disabled")
        threading.Thread(target=self.play_worker, kwargs=params, daemon=True).start()

    def configure_instance(self, inst, then_launch=False):
        """Réglages d'une instance (version, loader, RAM), enregistrés par WeCraft : le dossier
        de l'instance n'est jamais modifié."""
        win = self.small_dialog("Réglages de l'instance", 420, 330)
        tk.Label(win, text=inst["display"], bg=BG, fg=FG, font=(self.f_display, 12, "bold")).pack(pady=(16, 2))
        GradientBar(win).pack(fill="x", padx=20, pady=8)

        def field(label):
            tk.Label(win, text=label, bg=BG, fg=MUTED, anchor="w", font=(self.f_mono, 8)).pack(fill="x", padx=24)

        field("VERSION DE MINECRAFT")
        ver_var = tk.StringVar(value=inst["version"] or "")
        versions = [v["id"] for v in self.all_versions if v["type"] == "release"]
        ttk.Combobox(win, textvariable=ver_var, values=versions).pack(fill="x", padx=24, pady=(0, 8))
        field("MOD LOADER")
        loader_var = tk.StringVar(value=inst["loader"] or "Vanilla")
        ttk.Combobox(win, textvariable=loader_var, values=list(LOADERS), state="readonly").pack(
            fill="x", padx=24, pady=(0, 8))
        field("RAM (Go)")
        ram_var = tk.StringVar(value=str(inst["ram"]) if inst["ram"] else "Défaut")
        ttk.Combobox(win, textvariable=ram_var, values=["Défaut"] + [str(i) for i in range(1, 17)],
                     state="readonly").pack(fill="x", padx=24, pady=(0, 10))

        def save():
            version = ver_var.get().strip()
            if not version:
                messagebox.showinfo("Version", "Indiquez la version de Minecraft.", parent=win)
                return
            loader = loader_var.get()
            keep_lv = (version == inst["version"] and (loader if loader != "Vanilla" else None) == inst["loader"])
            changes = {"version": version, "loader": loader,
                       "loader_version": inst["loader_version"] if keep_lv else None}
            if ram_var.get().isdigit():
                changes["ram"] = int(ram_var.get())
            try:
                update_meta(inst["folder"], set=changes, remove=[] if "ram" in changes else ["ram"])
            except Exception as e:
                messagebox.showerror("Erreur", f"Impossible d'enregistrer : {e}", parent=win)
                return
            win.destroy()
            self.refresh_instances(force=True)
            if then_launch:
                self.play_instance(dict(
                    inst, version=version, loader=None if loader == "Vanilla" else loader,
                    loader_version=changes["loader_version"] if loader != "Vanilla" else None,
                    ram=changes.get("ram")))

        row = tk.Frame(win, bg=BG)
        row.pack(fill="x", padx=24, pady=4)
        GradientButton(row, text="ENREGISTRER" + (" ET LANCER" if then_launch else ""), command=save,
                       font=(self.f_display, 9, "bold"), height=38).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Dossier", command=lambda: webbrowser.open(inst["folder"].as_uri())).pack(
            side="left", padx=(8, 0))

    def ask_ram(self, name, initial, on_ok):
        """Fenêtre qui s'ouvre au moment de lancer : on règle la RAM, puis on lance avec on_ok(ram)."""
        if self._ram_dialog is not None and self._ram_dialog.winfo_exists():
            self._ram_dialog.lift()
            return
        win = self._ram_dialog = self.small_dialog("Lancer", 440, 300)
        tk.Label(win, text="MÉMOIRE (RAM)", bg=BG, fg=FG, font=(self.f_display, 12, "bold")).pack(pady=(16, 2))
        tk.Label(win, text=name, bg=BG, fg=BLUE, font=(self.f_mono, 9)).pack()
        GradientBar(win).pack(fill="x", padx=20, pady=8)
        box = ttk.LabelFrame(win, style="Card.TLabelframe", text="Mémoire allouée")
        box.pack(fill="x", padx=20, pady=6)
        var = tk.IntVar(value=min(16, max(1, int(initial))))
        label = ttk.Label(box, text="", style="Card.TLabel", font=(self.f_mono, 10, "bold"))
        label.pack(side="right", padx=8)

        def show(*_):
            label.config(text=f"{int(float(var.get()))} Go")

        ttk.Scale(box, style="Card.Horizontal.TScale", from_=1, to=16, variable=var, command=show).pack(
            side="left", fill="x", expand=True, padx=8, pady=8)
        show()
        tk.Label(win, text="Conseil : 4 Go en vanilla, 6 à 8 Go avec beaucoup de mods.", bg=BG, fg=MUTED,
                 font=(self.f_mono, 8)).pack(anchor="w", padx=22)
        row = tk.Frame(win, bg=BG)
        row.pack(fill="x", padx=20, pady=14)

        def go(_e=None):
            ram = int(float(var.get()))
            win.destroy()
            on_ok(ram)

        GradientButton(row, text="▶  LANCER", command=go, font=(self.f_display, 10, "bold"),
                       height=42).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Annuler", command=win.destroy).pack(side="left", padx=(8, 0))
        win.bind("<Return>", go)
        win.bind("<Escape>", lambda e: win.destroy())
        win.focus_set()
        try:
            win.grab_set()
        except tk.TclError:
            pass

    def open_folder(self):
        path = Path(self.game_dir())
        path.mkdir(parents=True, exist_ok=True)
        webbrowser.open(path.as_uri())

    def set_status(self, text):
        self.after(0, lambda: self.status.config(text="> " + text))

    def set_progress(self, value, maximum=None):
        def _do():
            if maximum:
                self.progress["maximum"] = maximum
            self.progress["value"] = value
        self.after(0, _do)

    # ---------- Choix du dossier ----------
    def choose_dir(self):
        path = filedialog.askdirectory(title="Choisissez le dossier de l'instance")
        if path:
            self.game_dir_var.set(path)
            self.instance_name = None
            self.clear_instance_info()
            self.save_config()

    def use_default_dir(self):
        self.game_dir_var.set(MC_DIR)
        self.instance_name = None
        self.clear_instance_info()
        self.save_config()

    def clear_instance_info(self):
        self.loader_version = None
        self.info_var.set("")

    def on_manual_change(self, *_):
        """Changement manuel de version/loader : on oublie la version de loader de l'instance."""
        self.clear_instance_info()
        self.on_loader_change()

    def detect_dialog(self):
        found = detect_instances()
        if not found:
            messagebox.showinfo(
                "Instances",
                "Aucune instance trouvée aux emplacements habituels (CurseForge, Modrinth, Prism).\n"
                "Utilisez « Parcourir... ».",
            )
            return
        win = tk.Toplevel(self)
        win.title("Mes instances")
        win.geometry(f"700x340+{self.winfo_x() + 30}+{self.winfo_y() + 80}")
        win.configure(bg=BG)
        win.transient(self)
        ttk.Label(
            win, text="Double-clic sur une instance : version et loader réglés automatiquement.",
            style="Sub.TLabel",
        ).pack(pady=6)
        lb = tk.Listbox(
            win, bg=PANEL, fg=FG, selectbackground=EMBER1, selectforeground="#1A0A04", relief="flat",
            highlightthickness=1, highlightbackground=BORDER, highlightcolor=EMBER1,
            font=(self.f_mono, 9), activestyle="none",
        )
        lb.pack(fill="both", expand=True, padx=10, pady=4)
        for inst in found:
            detail = " ".join(x for x in (inst["version"], inst["loader"], inst["loader_version"]) if x)
            lb.insert("end", f"[{inst['source']}] {inst['name']}   -   {detail or 'version inconnue'}")

        def pick(_event=None):
            if lb.curselection():
                self.apply_instance(found[lb.curselection()[0]])
                win.destroy()

        lb.bind("<Double-Button-1>", pick)
        ttk.Button(win, text="Utiliser cette instance", command=pick).pack(pady=8)

    def apply_instance(self, inst):
        """Règle dossier, version et loader d'après une instance CurseForge/Modrinth/Prism."""
        self.game_dir_var.set(str(inst["path"]))
        self.instance_name = inst["name"]
        notes = []
        loader = inst["loader"] if inst["loader"] in LOADERS else None
        self.loader_var.set(loader or "Vanilla")
        self.loader_version = inst["loader_version"] if loader else None
        mc = inst["version"]
        if mc:
            if not re.fullmatch(r"\d+\.\d+(\.\d+)?", mc):
                self.release_var.set(False)  # snapshot / version spéciale
            self.version_var.set(mc)
        else:
            notes.append("version de Minecraft non trouvée : choisissez-la")
        detail = " ".join(x for x in (mc, loader, self.loader_version) if x)
        self.info_var.set(f"{inst['source']} : {inst['name']}  ({detail or '?'})" +
                          (" - " + ", ".join(notes) if notes else ""))
        self.save_config()
        self.on_loader_change()

    # ---------- Versions ----------
    def load_versions(self):
        def worker():
            try:
                self.all_versions = mll.utils.get_version_list()
            except Exception:
                # Hors ligne : uniquement les versions déjà installées
                self.all_versions = [
                    {"id": v["id"], "type": "release"}
                    for v in mll.utils.get_installed_versions(SYSTEM_MC_DIR)
                ]
            self.after(0, self.on_loader_change)

        threading.Thread(target=worker, daemon=True).start()

    def on_loader_change(self, *_):
        """Récupère les versions de Minecraft compatibles avec le loader choisi."""
        loader_id = LOADERS[self.loader_var.get()]
        if loader_id is None or loader_id in self.loader_support:
            self.filter_versions()
            return
        self.set_status("Récupération des versions compatibles...")

        def worker():
            try:
                loader = mll.mod_loader.get_mod_loader(loader_id)
                self.loader_support[loader_id] = set(loader.get_minecraft_versions(False))
            except Exception:
                pass  # hors ligne : on garde la liste complète
            self.after(0, self.filter_versions)
            self.set_status("Prêt.")

        threading.Thread(target=worker, daemon=True).start()

    def installed_custom_versions(self):
        """Versions déjà installées dans le dossier du launcher mais absentes du catalogue Mojang."""
        known = {v["id"] for v in self.all_versions}
        try:
            installed = mll.utils.get_installed_versions(SYSTEM_MC_DIR)
        except Exception:
            return []
        return [v["id"] for v in installed if v["id"] not in known]

    def filter_versions(self):
        only_rel = self.release_var.get()
        supported = self.loader_support.get(LOADERS[self.loader_var.get()])
        ids = [
            v["id"] for v in self.all_versions
            if (not only_rel or v["type"] == "release")
            and (supported is None or v["id"] in supported)
        ]
        values = [CUSTOM_MARK + v for v in self.installed_custom_versions()] + ids
        self.version_box["values"] = values
        if values and self.version_var.get() not in values:
            self.version_var.set(values[0])

    # ---------- Lancement ----------
    def play(self, then_launch=False, force=False, ram=None):
        label = self.version_var.get()
        if not label:
            messagebox.showinfo("Version", "Choisissez une version (ou une instance).")
            return
        if then_launch and ram is None:  # lancer : on règle la RAM d'abord
            self.ask_ram(label.removeprefix(CUSTOM_MARK), int(float(self.ram_var.get())),
                         lambda r: self.play(then_launch, force, ram=r))
            return
        if ram is not None:
            self.ram_var.set(ram)
        self.save_config()
        # Les valeurs de l'interface sont lues ici (thread principal)
        params = dict(
            version=label.removeprefix(CUSTOM_MARK),
            custom=label.startswith(CUSTOM_MARK),
            game_dir=self.game_dir(),
            loader_name=self.loader_var.get(),
            ram=int(float(self.ram_var.get())),
            then_launch=then_launch,
            loader_version=self.loader_version,
            force=force,
            profile=profile_name_for(self.instance_name or default_instance_name(self.game_dir())),
        )
        self.set_buttons("disabled")
        threading.Thread(target=self.play_worker, kwargs=params, daemon=True).start()

    def set_buttons(self, state):
        self.busy = state == "disabled"
        for b in [self.launch_btn] + self.card_buttons:
            try:
                b.config(state=state)
            except tk.TclError:
                pass  # carte supprimée entre-temps

    def start_official(self, profile=PROFILE_NAME):
        if open_official_launcher():
            self.set_status(f"Profil « {profile} » prêt : cliquez sur Jouer dans le launcher officiel.")
        else:
            self.set_status("Impossible d'ouvrir le launcher officiel.")
            messagebox.showinfo(
                "Launcher officiel",
                f"Le profil « {profile} » est prêt, mais je n'ai pas pu ouvrir le launcher "
                "officiel.\nOuvrez-le vous-même et choisissez ce profil.",
            )

    def install_java(self, version_id, callback):
        """Java adapté à la version (nécessaire à l'installeur Forge/NeoForge)."""
        try:
            info = mll.runtime.get_version_runtime_information(version_id, SYSTEM_MC_DIR)
            if info:
                self.set_status("Préparation de Java...")
                mll.runtime.install_jvm_runtime(info["name"], SYSTEM_MC_DIR, callback=callback)
                return mll.runtime.get_executable_path(info["name"], SYSTEM_MC_DIR)
        except Exception:
            pass
        return None  # Java du système

    def ensure_loader(self, loader_name, version, loader_version, callback, force):
        """Installe le mod loader si besoin et renvoie l'identifiant de version à lancer."""
        loader_key = LOADERS[loader_name]
        loader = mll.mod_loader.get_mod_loader(loader_key)
        installed = {v["id"] for v in mll.utils.get_installed_versions(SYSTEM_MC_DIR)}
        try:
            if not loader.is_minecraft_version_supported(version):
                raise RuntimeError(f"{loader_name} ne supporte pas Minecraft {version}.")
            chosen = None
            if loader_version:  # version exacte demandée par l'instance
                avail = loader.get_loader_versions(version, False)
                chosen = next((v for v in avail
                               if v == loader_version or v.endswith("-" + loader_version)), None)
                if chosen is None:
                    self.set_status(f"{loader_name} {loader_version} introuvable : dernière version utilisée.")
            if chosen is None:
                chosen = loader.get_latest_loader_version(version)
        except RuntimeError:
            raise
        except Exception:
            # Hors ligne : on réutilise un loader déjà installé pour cette version
            local = [i for i in installed if loader_key in i.lower() and version in i]
            if local:
                return sorted(local)[-1]
            raise

        installed_id = loader.get_installed_version(version, chosen)
        if installed_id in installed and not force:
            return installed_id
        java_exe = self.install_java(version, callback)
        self.set_status(f"Installation de {loader_name} (peut prendre un moment)...")
        return loader.install(version, SYSTEM_MC_DIR, loader_version=chosen,
                              callback=callback, java=java_exe)

    def play_worker(self, version, custom, game_dir, loader_name, ram, then_launch,
                    loader_version=None, force=False, profile=PROFILE_NAME):
        try:
            Path(game_dir).mkdir(parents=True, exist_ok=True)
            # 1) Priorité : fermer le launcher officiel (il réécrirait sinon ses profils)
            self.set_status("Fermeture du launcher officiel...")
            closed, msg = close_official_launcher()
            self.set_status(msg)
            if not closed:
                self.after(0, lambda: messagebox.showwarning("Launcher officiel", msg))
            callback = {
                "setStatus": self.set_status,
                "setProgress": lambda v: self.set_progress(v),
                "setMax": lambda m: self.set_progress(0, m),
            }
            launch_id = version
            if not custom:
                installed = {v["id"] for v in mll.utils.get_installed_versions(SYSTEM_MC_DIR)}
                if force or version not in installed:
                    self.set_status(f"Installation de {version}...")
                    mll.install.install_minecraft_version(version, SYSTEM_MC_DIR, callback=callback)
                if LOADERS[loader_name]:
                    launch_id = self.ensure_loader(loader_name, version, loader_version, callback, force)

            self.set_status(f"Mise à jour du profil « {profile} »...")
            set_profile(SYSTEM_MC_DIR, profile, launch_id, game_dir, ram)
            self.set_progress(0)
            self.set_status(f"Profil « {profile} » prêt ({launch_id})")
            if then_launch:
                self.after(0, lambda: self.start_official(profile))
        except Exception as exc:
            err = str(exc)
            self.after(0, lambda: messagebox.showerror("Erreur", err))
            self.set_status("Erreur.")
        finally:
            self.after(0, lambda: self.set_buttons("normal"))


if __name__ == "__main__":
    try:  # Windows : icône du launcher dans la barre des tâches (au lieu de celle de Python)
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("WeCraft.Launcher")
    except Exception:
        pass
    Launcher().mainloop()
