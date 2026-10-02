"""Écrit le numéro de version (ex. tag v1.2.0 -> 1.2.0) dans wecraft_launcher.py. Utilisé par GitHub Actions."""
import pathlib
import re
import sys

version = sys.argv[1].lstrip("vV")
path = pathlib.Path("wecraft_launcher.py")
text = path.read_text(encoding="utf-8")
text, n = re.subn(r'APP_VERSION = "[^"]*"', f'APP_VERSION = "{version}"', text)
assert n == 1, "APP_VERSION introuvable"
path.write_text(text, encoding="utf-8")
print("APP_VERSION =", version)
