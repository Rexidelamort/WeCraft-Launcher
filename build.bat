@echo off
rem Compilation locale (test) : donne dist\WeCraft.exe
pip install pyinstaller minecraft-launcher-lib pillow
if not exist fonts mkdir fonts
pyinstaller --onefile --windowed --icon assets/wecraft.ico --name WeCraft --add-data "assets;assets" --add-data "fonts;fonts" wecraft_launcher.py
pause
