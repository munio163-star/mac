# -*- mode: python ; coding: utf-8 -*-
import sys, os

a = Analysis(
    ['FotoPIMmac.py'],
    pathex=['.'],
    binaries=[],
    datas=[
        ('ikona.icns', '.'),
    ],
    hiddenimports=[
        'customtkinter',
        'PIL._tkinter_finder',
        'pyvips',
        'numpy',
        'send2trash',
        'tkinterdnd2',
    ],
    hookspath=[],
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
)

pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name='FotoPIM',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    console=False,
)

coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=False,
    name='FotoPIM',
)

app = BUNDLE(
    coll,
    name='FotoPIM.app',
    icon='ikona.icns',
    bundle_identifier='com.fotopim.app',
    info_plist={
        'NSHighResolutionCapable': True,
        'CFBundleShortVersionString': '1.0',
    },
)
