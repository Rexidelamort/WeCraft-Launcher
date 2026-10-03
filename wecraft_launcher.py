"""
WeCraft - Launcher Minecraft - Python + Tkinter
Dépendance : pip install -U minecraft-launcher-lib   (version 8 ou plus récente)

Principe : ce launcher utilise vos instances CurseForge, Modrinth ou Prism (version +
mod loader lus automatiquement). Au clic sur LANCER, il installe si besoin la version et
le loader, crée (ou met à jour) le profil « WECRAFT - <instance> » dans le
launcher officiel avec le dossier de jeu de l'instance, puis ouvre le launcher officiel. La connexion
Microsoft et le lancement du jeu restent gérés par le launcher officiel.
"""
import ctypes
import hashlib
import json
import math
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import uuid
import threading
import urllib.request
import time
import tkinter as tk
import tkinter.font as tkfont
import webbrowser
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
RES_DIR = Path(getattr(sys, "_MEIPASS", APP_DIR))  # assets/ et fonts/ intégrés au .exe

# Mises à jour automatiques via les « Releases » GitHub (dépôt PUBLIC)
APP_VERSION = "1.0.0"  # mis à jour automatiquement par le workflow GitHub à chaque release
GITHUB_REPO = "TON-PSEUDO/WeCraft-Launcher"  # <-- À MODIFIER : « pseudo/nom-du-depot »

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
    def __init__(self, master, text, command, font, height=50, radius=12):
        super().__init__(master, height=height, bg=BG, highlightthickness=0, bd=0, cursor="hand2")
        self.text, self.command, self.font, self.radius = text, command, font, radius
        self.state, self.hover, self.pressed = "normal", False, False
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

    def draw(self):
        self.delete("all")
        w, h, r = max(self.winfo_width(), 2 * self.radius + 2), int(self["height"]), self.radius
        off = self.state != "normal"
        for x in range(w):
            d = r - x if x < r else x - (w - 1 - r) if x > w - 1 - r else 0
            inset = r - math.sqrt(max(r * r - d * d, 0)) if d > 0 else 0
            if off:
                col = BORDER
            else:
                col = lerp_color(EMBER1, EMBER2, x / (w - 1))
                if self.pressed:
                    col = lerp_color(col, "#000000", 0.18)
                elif self.hover:
                    col = lerp_color(col, "#FFFFFF", 0.14)
            self.create_line(x, inset, x, h - inset, fill=col)
        self.create_text(w // 2, h // 2, text=self.text, font=self.font,
                         fill=MUTED if off else "#1A0A04")

# ------------------------------------------------------------------ interface
class Launcher(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("WeCraft")
        self.geometry("560x800")
        self.resizable(False, False)
        self.configure(bg=BG)
        self.apply_style()

        Path(MC_DIR).mkdir(parents=True, exist_ok=True)
        self.config_data = self.load_config()
        self.all_versions = []
        self.loader_support = {}  # cache : loader -> versions MC compatibles
        self.loader_version = self.config_data.get("loader_version")  # imposée par l'instance détectée
        self.instance_name = self.config_data.get("instance_name")    # nom CurseForge/Modrinth/Prism

        self.build_ui()
        self.load_versions()
        self.check_updates()

    # ---------- Mises à jour ----------
    def check_updates(self):
        def worker():
            try:
                info = fetch_latest_release()
            except Exception:
                return  # hors ligne, pas de release, dépôt privé... : on ignore en silence
            if version_tuple(info["version"]) > version_tuple(APP_VERSION):
                self.after(0, lambda: self.show_update(info))

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
                except Exception as e:
                    def fail():
                        messagebox.showerror("Mise à jour", f"Échec de la mise à jour :\n{e}", parent=win)
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
            }
        )
        CONFIG_FILE.write_text(json.dumps(self.config_data), encoding="utf-8")

    def game_dir(self):
        """Dossier de l'instance : mods, saves, resourcepacks, options.txt..."""
        return self.game_dir_var.get().strip() or MC_DIR

    # ---------- Interface ----------
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

        st.configure("Card.TCheckbutton", background=PANEL, foreground=FG, indicatorcolor=FIELD,
                     indicatorbackground=FIELD, font=(body, 10))
        st.map("Card.TCheckbutton", background=[("active", PANEL)], indicatorcolor=[("selected", EMBER1)])
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
        self.logo = self.wordmark = None
        self.logo = self.load_image("wecraft_logo.png", height=86)
        self.wordmark = self.load_image("wecraft_wordmark.png", width=260)
        if self.logo:
            ttk.Label(self, image=self.logo).pack(pady=(14, 0))
        if self.wordmark:
            ttk.Label(self, image=self.wordmark).pack(pady=(10, 0))
        else:
            ttk.Label(self, text="WECRAFT", style="Title.TLabel").pack(pady=(14, 0))
        ttk.Label(self, text="MINECRAFT · INSTANCE LAUNCHER", style="Sub.TLabel").pack(pady=(6, 10))
        GradientBar(self).pack(fill="x", padx=14, pady=(0, 6))

        # Instance
        box = ttk.LabelFrame(self, style="Card.TLabelframe", text="Instance (dossier avec vos mods, mondes...)")
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

        # Version
        box = ttk.LabelFrame(self, style="Card.TLabelframe", text="Version")
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

        # RAM
        box = ttk.LabelFrame(self, style="Card.TLabelframe", text="Mémoire (RAM)")
        box.pack(fill="x", **pad)
        self.ram_var = tk.IntVar(value=self.config_data.get("ram", 4))
        self.ram_text = ttk.Label(box, text="", style="Card.TLabel", font=(self.f_mono, 10, "bold"))
        self.ram_text.pack(side="right", padx=8)
        ttk.Scale(
            box, style="Card.Horizontal.TScale", from_=1, to=16, variable=self.ram_var, command=self.on_ram
        ).pack(side="left", fill="x", expand=True, padx=8, pady=8)
        self.on_ram()

        ttk.Button(self, text="Ouvrir le dossier de l'instance", command=self.open_folder).pack(**pad)

        # Progression
        self.status = ttk.Label(self, text="> Prêt.", style="Status.TLabel", wraplength=500)
        self.status.pack(fill="x", padx=14)
        self.progress = ttk.Progressbar(self, mode="determinate", style="Ember.Horizontal.TProgressbar")
        self.progress.pack(fill="x", padx=14, pady=6)

        self.launch_btn = GradientButton(
            self, text="▶  LANCER L'INSTANCE", command=lambda: self.play(then_launch=True),
            font=(self.f_display, 12, "bold"),
        )
        self.launch_btn.pack(fill="x", padx=14, pady=(10, 6))
        tk.Label(
            self, text="Fermez le launcher officiel avant de cliquer.", bg=BG, fg=MUTED,
            font=(self.f_mono, 8),
        ).pack()
        tk.Label(self, text=f"v{APP_VERSION}", bg=BG, fg=MUTED, font=(self.f_mono, 8)).pack(pady=(6, 8))

    def on_ram(self, *_):
        self.ram_text.config(text=f"{int(float(self.ram_var.get()))} Go")

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
    def play(self, then_launch=False, force=False):
        label = self.version_var.get()
        if not label:
            messagebox.showinfo("Version", "Choisissez une version (ou une instance).")
            return
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
        self.launch_btn.config(state=state)

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
        except Exception as e:
            self.after(0, lambda: messagebox.showerror("Erreur", str(e)))
            self.set_status("Erreur.")
        finally:
            self.after(0, lambda: self.set_buttons("normal"))


if __name__ == "__main__":
    Launcher().mainloop()
