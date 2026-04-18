from __future__ import annotations

import tkinter as tk
import customtkinter as ctk
from tkinter import filedialog, messagebox, ttk
from tkinter.colorchooser import askcolor
import os
import io
import json
import sys
import threading
import queue
import re
import concurrent.futures
import unicodedata
from concurrent.futures import ThreadPoolExecutor
from send2trash import send2trash

IS_WINDOWS = sys.platform == 'win32'
IS_MACOS = sys.platform == 'darwin'
if IS_WINDOWS:
    import ctypes
import functools
from dataclasses import dataclass, field, asdict
from typing import Optional, Callable, Dict, List, Tuple, Any, Union
from pathlib import Path
from enum import Enum
import logging
import gc
import time
import multiprocessing


# Konfiguracja logowania - początkowo tylko konsola
LOG_FILE = "fotopim.log"
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s: %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Funkcja do włączania/wyłączania logowania do pliku
def set_file_logging(enable: bool) -> None:
    """Włącza lub wyłącza zapis logów do pliku."""
    root_logger = logging.getLogger()

    # Usuń istniejący FileHandler (jeśli istnieje)
    for handler in root_logger.handlers[:]:
        if isinstance(handler, logging.FileHandler):
            handler.close()
            root_logger.removeHandler(handler)

    # Dodaj FileHandler tylko jeśli włączone
    if enable:
        file_handler = logging.FileHandler(LOG_FILE, encoding='utf-8')
        file_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s: %(message)s'))
        file_handler.setLevel(logging.INFO)
        root_logger.addHandler(file_handler)

# === BIBLIOTEKA DO DRAG & DROP Z SYSTEMU ===
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
except ImportError:
    import tkinter.messagebox
    root = tk.Tk()
    root.withdraw()
    tk.messagebox.showerror("Błąd", "Brakuje biblioteki tkinterdnd2.\nZainstaluj ją komendą:\npip install tkinterdnd2")
    sys.exit(1)

# Próba importu bibliotek graficznych
HAS_PYVIPS = False
try:
    from PIL import Image, ImageChops, ImageTk, ImageDraw, UnidentifiedImageError
    # Wyłącz limit wielkości dla olbrzymich zdjęć, aby nie rzucał błędem "DecompressionBombError"
    Image.MAX_IMAGE_PIXELS = None
    
    # GŁÓWNA ZMIANA: Superszybki silnik strumieniowy
    try:
        os.environ["VIPS_CONCURRENCY"] = "2"
        os.environ["VIPS_MAX_MEM"] = "2000000000" # 2GB limit dla alokacji
        import pyvips
        # Zwiększamy limity zasobów dla dużych obrazów
        pyvips.cache_set_max_mem(500 * 1024 * 1024)  # 500 MB
        pyvips.cache_set_max(100)
        HAS_PYVIPS = True
    except (ImportError, OSError) as e:
        HAS_PYVIPS = False
        logger.warning(f"PyVips niedostępny (używam Pillow): {e}")

except ImportError as e:
    import tkinter.messagebox
    root = tk.Tk()
    root.withdraw()
    tk.messagebox.showerror("Błąd", f"Brakuje bibliotek.\nZainstaluj je komendą:\npip install Pillow\n\nSzczegóły: {e}")
    sys.exit(1)

# Funkcja pomocnicza: Szybka konwersja małego obrazu PyVips do formatu PIL (tylko dla GUI)
def vips_to_pil(vips_img):
    if not HAS_PYVIPS:
        return None
    
    try:
        # 1. Konwersja CMYK → sRGB (produkuje 3 kanały RGB)
        if vips_img.interpretation == 'cmyk':
            vips_img = vips_img.colourspace('srgb')

        # 2. Spłaszczenie kanałów alpha (RGBA/GrayA → 3 kanały RGB)
        if vips_img.bands in [2, 4]:
            vips_img = vips_img.flatten(background=[255, 255, 255])

        # 3. Konwersja grayscale do RGB (tylko jeśli nadal 1 kanał)
        if vips_img.bands == 1:
            vips_img = vips_img.colourspace('srgb')
        elif vips_img.bands != 3:
            # Fallback dla nietypowych przypadków
            vips_img = vips_img.colourspace('srgb')

        # 4. Zapewnienie formatu 8-bitowego (zabezpieczenie przed TIFF/PNG 16-bit)
        if vips_img.format == 'ushort':
            vips_img = (vips_img / 256).cast('uchar')
        elif vips_img.format != 'uchar':
            vips_img = vips_img.cast('uchar')

        # 5. Na wszelki wypadek ucięcie nadmiarowych kanałów jeśli srgb nie zadziałało jak chcemy
        if vips_img.bands > 3:
            vips_img = vips_img.extract_band(0, n=3)

        mem = vips_img.write_to_memory()
        # Pillow ≥ 8.0 automatycznie kopiuje dane z bytes buffer - copy() niepotrzebne
        return Image.frombytes("RGB", (vips_img.width, vips_img.height), mem)
    except Exception as e:
        logger.exception(f"Błąd konwersji Vips do PIL")
        return None




# ===== STAŁE KONFIGURACYJNE =====

class ConfigConstants:
    MAX_FILE_SIZE: float = 2.99 * 1024 * 1024  # Maksymalny rozmiar pliku JPG w bajtach
    MAX_IMAGE_SIDE: int = 3000  # Maksymalny bok obrazu
    MIN_IMAGE_SIZE: int = 500  # Minimalny rozmiar obrazu
    DEFAULT_MARGIN: int = 0  # Domyślny margines
    DEFAULT_THRESHOLD: int = 10  # Domyślny próg bieli
    PREVIEW_TARGET_WIDTH: int = 300  # Docelowa szerokość podglądu
    THUMBNAIL_SIZE: int = 150  # Rozmiar miniatury
    PREVIEW_MAX_W: int = 880  # Maksymalna szerokość podglądu w osobnym oknie
    PREVIEW_MAX_H: int = 600  # Maksymalna wysokość podglądu w osobnym oknie
    CHECKBOX_WIDTH: int = 40  # Szerokość bocznej przestrzeni (checkboxa)
    CHECKBOX_BOX_SIZE: int = 28  # Rozmiar pola checkboxa
    COL_NAME = "Name"
    COL_SIZE = "Size"
    COL_RESOLUTION = "Resolution"
    COL_NEWNAME = "NewName"


# ===== MODELE DANYCH =====

class UserAbortException(Exception):
    """Zgłaszane, gdy użytkownik ręcznie przerywa proces."""
    pass

@dataclass
class ProcessingParams:
    """Parametry przetwarzania obrazów."""
    margin: int = ConfigConstants.DEFAULT_MARGIN
    threshold: int = ConfigConstants.DEFAULT_THRESHOLD
    max_side: int = ConfigConstants.MAX_IMAGE_SIDE
    min_size: int = ConfigConstants.MIN_IMAGE_SIZE
    max_mb: float = 2.99
    output_format: str = "JPG"  # <--- DODANO TĘ LINIĘ
    # Checkboxy dla parametrów - domyślnie wszystkie włączone (True)
    use_margin: bool = True
    use_max_side: bool = True
    use_min_size: bool = True
    use_max_mb: bool = True


@dataclass
class FileTask:
    """Zadanie przetwarzania pojedynczego pliku."""
    source_path: str
    target_name: str
    threshold: int = ConfigConstants.DEFAULT_THRESHOLD
    crop: Optional[Tuple[float, float, float, float]] = None
    item_id: str = ""      # ID w Treeview
    is_large: bool = False # Czy plik ma powyżej 10MB
    eraser_strokes: Optional[List[List[Tuple[float, float, int, int, int, str]]]] = None
    rotation: int = 0      # 0=0°, 1=90°, 2=180°, 3=270°


@dataclass
class AppearanceSettings:
    """Ustawienia wyglądu aplikacji."""
    font_size_left_panel: int = 11  # Rozmiar czcionki lewego panelu
    font_size_table_header: int = 11  # Rozmiar czcionki nagłówków tabeli
    thumb_size: int = 50
    dark_mode: bool = False
    light_preview_bg: str = "#d0d0d0"
    light_font_color: str = "black"
    dark_font_color: str = "white"
    enable_debug_logging: bool = False  # Włączanie logowania diagnostycznego
    fullscreen_hq: bool = False  # Włącza ładowanie miniatur pod rozdzielczość monitora
    button_colors: Dict[str, str] = field(default_factory=dict)
    button_text_colors: Dict[str, str] = field(default_factory=dict)
    font_family: str = "Arial"
    font_bold: bool = False


@dataclass
class NamingSettings:
    """Ustawienia nazewnictwa plików."""
    raw_name: str = ""
    clean_name: str = ""
    start_number: str = "1"

    def get_parsed_start_number(self) -> Tuple[str, int, int]:
        """Zwraca (prefix, start_num, padding) z pola start_number."""
        match = re.search(r'(.*?)(\d+)$', self.start_number)
        if match:
            prefix = match.group(1)
            num_part = match.group(2)
            padding = len(num_part)
            start_num = int(num_part)
            return prefix, start_num, padding
        return self.start_number, 1, 1


@dataclass
class AppConfig:
    """Konfiguracja aplikacji."""
    input_folder: str = ""
    output_folder: str = ""
    processing: ProcessingParams = field(default_factory=ProcessingParams)
    appearance: AppearanceSettings = field(default_factory=AppearanceSettings)
    naming: NamingSettings = field(default_factory=NamingSettings)
    column_widths: Dict[str, int] = field(default_factory=dict)
    display_columns: List[str] = field(default_factory=lambda: [ConfigConstants.COL_SIZE, ConfigConstants.COL_RESOLUTION, ConfigConstants.COL_NEWNAME])
    window_geometry: str = "1400x850"
    fullscreen: bool = False
    left_panel_width: int = 378
    preview_panel_width: int = 300

    def to_dict(self) -> Dict[str, Any]:
        """Konwertuje config do słownika."""
        return {
            "input": str(self.input_folder),
            "output": str(self.output_folder),
            "margin": str(self.processing.margin),
            "threshold": str(self.processing.threshold),
            "max_side": str(self.processing.max_side),
            "min_size": str(self.processing.min_size),
            "max_mb": str(self.processing.max_mb),
            "output_format": self.processing.output_format,  # <--- DODANO TĘ LINIĘ
            "use_margin": self.processing.use_margin,
            "use_max_side": self.processing.use_max_side,
            "use_min_size": self.processing.use_min_size,
            "use_max_mb": self.processing.use_max_mb,
            "font_size_left_panel": self.appearance.font_size_left_panel,
            "font_size_table_header": self.appearance.font_size_table_header,
            "thumb_size": self.appearance.thumb_size,
            "dark_mode": self.appearance.dark_mode,
            "enable_debug_logging": self.appearance.enable_debug_logging,
            "fullscreen_hq": self.appearance.fullscreen_hq,
            "font_bold": self.appearance.font_bold,
            "column_widths": self.column_widths,
            "display_columns": self.display_columns,
            "window_geometry": self.window_geometry,
            "fullscreen": self.fullscreen,
            "left_panel_width": self.left_panel_width,
            "preview_panel_width": self.preview_panel_width,
            "light_preview_bg": self.appearance.light_preview_bg,
            "light_font_color": self.appearance.light_font_color,
            "dark_font_color": self.appearance.dark_font_color,
            "button_colors": self.appearance.button_colors,
            "button_text_colors": self.appearance.button_text_colors,
            "font_family": self.appearance.font_family,
            "naming": {
                "raw_name": self.naming.raw_name,
                "clean_name": self.naming.clean_name,
                "start_number": self.naming.start_number
            }
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> AppConfig:
        """Tworzy config ze słownika."""
        processing = ProcessingParams(
            margin=int(data.get("margin", ConfigConstants.DEFAULT_MARGIN)),
            threshold=int(data.get("threshold", ConfigConstants.DEFAULT_THRESHOLD)),
            max_side=int(data.get("max_side", ConfigConstants.MAX_IMAGE_SIDE)),
            min_size=int(data.get("min_size", ConfigConstants.MIN_IMAGE_SIZE)),
            max_mb=float(data.get("max_mb", 2.99)),
            output_format=data.get("output_format", "JPG"),  # <--- DODANO TĘ LINIĘ
            use_margin=data.get("use_margin", True),
            use_max_side=data.get("use_max_side", True),
            use_min_size=data.get("use_min_size", True),
            use_max_mb=data.get("use_max_mb", True),
        )

        appearance = AppearanceSettings(
            font_size_left_panel=data.get("font_size_left_panel", 11),
            font_size_table_header=data.get("font_size_table_header", 11),
            thumb_size=data.get("thumb_size", 50),
            dark_mode=data.get("dark_mode", False),
            light_preview_bg=data.get("light_preview_bg", "#d0d0d0"),
            light_font_color=data.get("light_font_color", "black"),
            dark_font_color=data.get("dark_font_color", "white"),
            enable_debug_logging=data.get("enable_debug_logging", False),
            fullscreen_hq=data.get("fullscreen_hq", False),
            font_bold=data.get("font_bold", False),
            button_colors=data.get("button_colors", {}),
            button_text_colors=data.get("button_text_colors", {}),
            font_family=data.get("font_family", "Arial")
        )

        naming_data = data.get("naming", {})
        naming = NamingSettings(
            raw_name=naming_data.get("raw_name", ""),
            clean_name=naming_data.get("clean_name", ""),
            start_number=naming_data.get("start_number", "1")
        )

        return cls(
            input_folder=str(data.get("input", "")),
            output_folder=str(data.get("output", "")),
            processing=processing,
            appearance=appearance,
            naming=naming,
            column_widths=data.get("column_widths", {}),
            display_columns=data.get("display_columns", [ConfigConstants.COL_SIZE, ConfigConstants.COL_RESOLUTION, ConfigConstants.COL_NEWNAME]),
            window_geometry=data.get("window_geometry", "1400x850"),
            fullscreen=data.get("fullscreen", False),
            left_panel_width=data.get("left_panel_width", 378),
            preview_panel_width=data.get("preview_panel_width", 300)
        )


# ===== FUNKCJE POMOCNICZE =====

def resource_path(relative_path: str) -> str:
    """Get absolute path to resource, works for dev and for PyInstaller."""
    try:
        # PyInstaller creates a temp folder and stores path in _MEIPASS
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")

    return os.path.join(base_path, relative_path)

# ===== PRZETWARZANIE OBRAZÓW =====



def trim_whitespace(
    img: Any,
    bg_color: Optional[list] = None,
    margin: int = 0,
    threshold: int = 10
) -> Any:
    """Kadruje białe znaki używając najlepszego dostępnego silnika."""
    bg_color = bg_color or [255, 255, 255]
    if HAS_PYVIPS and isinstance(img, pyvips.Image):
        return trim_whitespace_vips(img, bg_color, margin, threshold)
    
    # Fallback do Pillow (bez NumPy)
    img_pil = img if isinstance(img, Image.Image) else vips_to_pil(img)
    if not img_pil: return img
    
    return trim_whitespace_pil(img_pil, bg_color, margin, threshold)

def trim_whitespace_vips(img, bg_color, margin, threshold):
    # 1. Konwersja przestrzeni barw
    if img.interpretation == 'cmyk':
        img = img.colourspace('srgb')

    if img.bands in [2, 4]:
        img = img.flatten(background=bg_color)

    if img.bands == 1:
        img_work = img.colourspace('srgb')
    else:
        img_work = img

    # --- UODPORNIENIE NA SZUM TŁA (Wykrywanie ramki na mniejszej skali) ---
    scale = 1.0
    max_dim = max(img_work.width, img_work.height)
    if max_dim > 1000:
        scale = 800.0 / max_dim
        # Skalujemy (uśrednia to szum i artefakty kompresji, naprawiając wykrywanie tła)
        img_small = img_work.resize(scale, kernel="linear")
    else:
        img_small = img_work

    diff = (img_small - bg_color).abs()
    if diff.bands > 1:
        diff = diff.bandmean() * diff.bands

    mask = diff > threshold

    try:
        # Szukamy koordynatów cięcia na miniaturze
        left_s, top_s, width_s, height_s = mask.find_trim(threshold=128, background=[0])

        # Przeliczamy koordynaty z powrotem do rozmiaru oryginalnego obrazu
        left = int(left_s / scale)
        top = int(top_s / scale)
        width = int(width_s / scale)
        height = int(height_s / scale)

        # Zabezpieczenie przed ucięciem pikseli granicznych przy niedokładności skalowania
        padding = int(1.0 / scale) + 1 if scale < 1.0 else 0

        new_left = max(0, left - margin - padding)
        new_top = max(0, top - margin - padding)
        new_right = min(img.width, left + width + margin + padding)
        new_bottom = min(img.height, top + height + margin + padding)

        # Kadrujemy oryginalny (wielki) obraz
        img_mem = img.copy_memory()
        return img_mem.crop(new_left, new_top, new_right - new_left, new_bottom - new_top)
    except pyvips.Error as e:
        logger.warning(f"PyVips trim error (find_trim failed): {e}")
        raise

def trim_whitespace_pil(img, bg_color=None, margin=0, threshold=10):
    """Fallback trimowania oparty na Pillow ImageChops z odpornością na szum."""
    bg_color = bg_color or [255, 255, 255]

    if img.mode != 'RGB':
        img = img.convert('RGB')

    # --- UODPORNIENIE NA SZUM TŁA ---
    scale = 1.0
    max_dim = max(img.width, img.height)
    if max_dim > 1000:
        scale = 800.0 / max_dim
        # Skalowanie w dół naturalnie "rozmywa" ostre, pojedyncze brudne piksele szumu
        img_small = img.resize((int(img.width * scale), int(img.height * scale)), Image.Resampling.BILINEAR)
    else:
        img_small = img

    bg = Image.new('RGB', img_small.size, tuple(bg_color))
    diff = ImageChops.difference(img_small, bg)

    if threshold > 0:
        diff = diff.convert('L')
        diff = diff.point(lambda p: 255 if p > threshold else 0)

    bbox_small = diff.getbbox()
    if bbox_small:
        left_s, top_s, right_s, bottom_s = bbox_small

        # Przeliczenie do skali oryginału
        left = int(left_s / scale)
        top = int(top_s / scale)
        right = int(right_s / scale)
        bottom = int(bottom_s / scale)

        # Zapas dla uniknięcia wcięcia w krawędź przedmiotu
        padding = int(1.0 / scale) + 1 if scale < 1.0 else 0

        left = max(0, left - margin - padding)
        top = max(0, top - margin - padding)
        right = min(img.width, right + margin + padding)
        bottom = min(img.height, bottom + margin + padding)

        return img.crop((left, top, right, bottom))
    return img

def resize_if_needed(img, max_side=3000):
    if HAS_PYVIPS and isinstance(img, pyvips.Image):
        w, h = img.width, img.height
        if w > max_side or h > max_side:
            scale = max_side / max(w, h)
            return img.resize(scale, kernel="lanczos3")
        return img
    
    # Pillow version
    w, h = img.size
    if w > max_side or h > max_side:
        scale = max_side / max(w, h)
        return img.resize((int(w * scale), int(h * scale)), Image.Resampling.LANCZOS)
    return img

def pad_to_min_size(img, min_size=500, bg_color=None):
    bg_color = bg_color or [255, 255, 255]
    if HAS_PYVIPS and isinstance(img, pyvips.Image):
        w, h = img.width, img.height
        new_w, new_h = max(w, min_size), max(h, min_size)
        if (w, h) == (new_w, new_h): return img
        return img.embed((new_w - w) // 2, (new_h - h) // 2, new_w, new_h, extend="background", background=bg_color)
    
    # Pillow version
    w, h = img.size
    new_w, new_h = max(w, min_size), max(h, min_size)
    if (w, h) == (new_w, new_h): return img
    bg = Image.new("RGB", (new_w, new_h), tuple(bg_color))
    bg.paste(img, ((new_w - w) // 2, (new_h - h) // 2))
    return bg

def apply_crop_to_image(img, crop):
    if HAS_PYVIPS and isinstance(img, pyvips.Image):
        w, h = img.width, img.height
        left, top = int(crop[0] * w), int(crop[1] * h)
        right, bottom = int(crop[2] * w), int(crop[3] * h)
        right, bottom = max(right, left + 1), max(bottom, top + 1)
        return img.crop(left, top, right - left, bottom - top)
    
    # Pillow version
    w, h = img.size
    left, top = int(crop[0] * w), int(crop[1] * h)
    right, bottom = int(crop[2] * w), int(crop[3] * h)
    right, bottom = max(right, left + 1), max(bottom, top + 1)
    return img.crop((left, top, right, bottom))


def apply_rotation_and_eraser_to_pil(pil_img, file_data):
    """Wspólna logika rotacji i gumki dla obrazów PIL.

    Args:
        pil_img: Obraz PIL do przetworzenia
        file_data: Obiekt FileTask z danymi rotacji i gumki

    Returns:
        Przetworzony obraz PIL (RGB)
    """
    from PIL import ImageDraw, Image

    eraser_strokes = getattr(file_data, "eraser_strokes", None)
    rotation = getattr(file_data, "rotation", 0) if hasattr(file_data, "rotation") else 0

    if rotation:
        angle = rotation * 90
        pil_img = pil_img.rotate(angle, expand=True, fillcolor=(255, 255, 255))

    if eraser_strokes:
        pil_img = pil_img.convert("RGB")
        w, h = pil_img.size
        fill_color = (255, 255, 255)

        trim_thresh = getattr(file_data, "threshold", ConfigConstants.DEFAULT_THRESHOLD)

        for stroke in eraser_strokes:
            draw = ImageDraw.Draw(pil_img)
            for px, py, esize, pw, ph, *rest in stroke:
                eraser_shape = rest[0] if rest else "square"

                cx = int((px / pw) * w)
                cy = int((py / ph) * h)
                cs = int((esize / pw) * w)
                r = cs / 2.0

                if eraser_shape == "circle":
                    draw.ellipse([cx-r, cy-r, cx+r, cy+r], fill=fill_color)
                else:
                    draw.rectangle([cx-r, cy-r, cx+r, cy+r], fill=fill_color)

            pil_img = trim_whitespace_pil(pil_img, threshold=trim_thresh)
            w, h = pil_img.size

    return pil_img


def batch_trim_and_convert_files(
    file_list: List[FileTask],
    output_folder: str,
    margin: int,
    threshold: int,
    max_side: int,
    min_size: int,
    max_mb: float,
    output_format: str = "JPG",  # <--- DODANY ARGUMENT
    use_margin: bool = True,
    use_max_side: bool = True,
    use_min_size: bool = True,
    use_max_mb: bool = True,
    progress_callback: Callable[[Optional[int], Optional[str]], None] = lambda p, m: None,
    file_progress_callback: Callable[[str, str], None] = lambda id, status: None,
    stop_event: Optional[threading.Event] = None
) -> None:
    """Wydajne przetwarzanie masowe (PyVips / Pillow)."""
    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    total = len(file_list)
    if total == 0:
        progress_callback(100, "Brak plików na liście.")
        return

    # ROZPOCZĘCIJ POMIAR CZASU PRZETWARZANIA BATCHA
    batch_start_time = time.time()
    logger.info(f"ROZPOCZĘTO PRZETWARZANIE BATCHA: {total} plików")

    completed_count = 0
    progress_lock = threading.Lock()

    def check_abort():
        if stop_event and stop_event.is_set():
            raise UserAbortException()

    def process_single_file(file_data: FileTask) -> None:
        try:
            check_abort()
        except UserAbortException:
            return
        nonlocal completed_count
        source_path = file_data.source_path
        target_name = file_data.target_name

        logger.info(f"Przetwarzam: {target_name} z {source_path}")

        if file_data.item_id:
            file_progress_callback(file_data.item_id, 'start')

        # Flaga dla statusu zapisu i obiekt obrazu
        file_saved = False
        img = None
        out_path = None

        try:
            # 1. Silnik PyVips (Szybki)
            if HAS_PYVIPS:
                try:
                    ext = os.path.splitext(source_path)[1].lower()
                    tiff_exts = ['.tif', '.tiff']
                    try:
                        if ext in tiff_exts:
                            # Próba najlepsza: unlimited + tile_height (tryb losowy dla bezpieczeństwa przy trim)
                            try:
                                img = pyvips.Image.new_from_file(source_path,
                                                                   tile_height=256, unlimited=True)
                            except pyvips.Error:
                                try:
                                    img = pyvips.Image.new_from_file(source_path, unlimited=True)
                                except pyvips.Error:
                                    img = pyvips.Image.new_from_file(source_path)
                        else:
                            # Dla JPG, PNG - maksymalna prędkość sekwencyjna z pamięci RAM
                            img = pyvips.Image.new_from_file(source_path, memory=True, access='sequential')
                    except pyvips.Error:
                        raise
                    check_abort()

                    actual_margin = margin if use_margin else 0
                    img = trim_whitespace(img, margin=actual_margin, threshold=file_data.threshold)
                    check_abort()

                    # Przeniesiono blok kadrowania niżej, aby gumka była nakładana w odpowiednim układzie współrzędnych

                    # ROTACJA i GUMKA - wspólne przetwarzanie przez PIL
                    needs_pil_conversion = (hasattr(file_data, "rotation") and file_data.rotation) or getattr(file_data, "eraser_strokes", None)

                    if needs_pil_conversion:
                        pil_img = vips_to_pil(img)
                        if pil_img:
                            pil_img = apply_rotation_and_eraser_to_pil(pil_img, file_data)
                            # Konwersja z powrotem do PyVips
                            mem = pil_img.tobytes()
                            w, h = pil_img.size
                            img = pyvips.Image.new_from_memory(mem, w, h, 3, "uchar")
                            img = img.copy(interpretation="srgb")
                    
                    # CROP (wykonywany po gumce i rotacji, aby zachować spójność współrzędnych)
                    if file_data.crop:
                        img = apply_crop_to_image(img, file_data.crop)
                        img = trim_whitespace(img, margin=actual_margin, threshold=file_data.threshold)
                    if use_max_side: img = resize_if_needed(img, max_side=max_side)
                    if use_min_size: img = pad_to_min_size(img, min_size=min_size)
                    check_abort()

                    if img.interpretation == 'cmyk':
                        img = img.colourspace('srgb')

                    if img.bands in [2, 4]: # RGBA / GrayA
                        img = img.flatten(background=[255, 255, 255])
                    
                    if img.interpretation != 'srgb':
                        img = img.colourspace('srgb')

                    base, _ = os.path.splitext(target_name)
                    fmt = output_format.lower()
                    out_path = os.path.join(output_folder, base + f".{fmt}")
                    max_file_size = max_mb * 1024 * 1024

                    if fmt in ["jpg", "jpeg"]:
                        if use_max_mb:
                            current_q = 100
                            img.jpegsave(out_path, Q=current_q, optimize_coding=True, strip=True)
                            while os.path.getsize(out_path) > max_file_size and current_q > 10:
                                check_abort()
                                current_q -= 10
                                img.jpegsave(out_path, Q=current_q, optimize_coding=True, strip=True)
                        else:
                            img.jpegsave(out_path, Q=100, optimize_coding=True, strip=True)
                    elif fmt == "webp":
                        if use_max_mb:
                            current_q = 100
                            img.webpsave(out_path, Q=current_q, strip=True)
                            while os.path.getsize(out_path) > max_file_size and current_q > 10:
                                check_abort()
                                current_q -= 10
                                img.webpsave(out_path, Q=current_q, strip=True)
                        else:
                            img.webpsave(out_path, Q=100, strip=True)
                    elif fmt == "png":
                        img.pngsave(out_path, compression=9, strip=True)
                    elif fmt == "avif":
                        try:
                            if use_max_mb:
                                current_q = 100
                                img.heifsave(out_path, Q=current_q)
                                while os.path.getsize(out_path) > max_file_size and current_q > 10:
                                    check_abort()
                                    current_q -= 10
                                    img.heifsave(out_path, Q=current_q)
                            else:
                                img.heifsave(out_path, Q=100)
                        except Exception:
                            img.magicksave(out_path)
                    elif fmt in ["tiff", "tif"]:
                        img.tiffsave(out_path, compression='deflate', strip=True)
                    else:
                        img.write_to_file(out_path)
                    
                    file_saved = True
                    logger.info(f"Zapisano (PyVips): {out_path}")

                except Exception as e:
                    logger.warning(f"Błąd PyVips przy pliku {os.path.basename(source_path)}: {e}, używam Pillow jako fallback")
                    if 'img' in locals() and img: del img
                    img = None

            # 2. Silnik Pillow (jeśli PyVips się nie udał lub nie jest dostępny)
            if not file_saved:
                from PIL import Image
                with Image.open(source_path) as img_raw:
                    img = img_raw.convert("RGB")
                check_abort()

                actual_margin = margin if use_margin else 0
                img = trim_whitespace(img, margin=actual_margin, threshold=file_data.threshold)
                check_abort()

                # Przeniesiono blok kadrowania niżej

                # ROTACJA i GUMKA - wspólne przetwarzanie przez funkcję pomocniczą
                img = apply_rotation_and_eraser_to_pil(img, file_data)

                # CROP (wykonywany po gumce i rotacji)
                if file_data.crop:
                    img = apply_crop_to_image(img, file_data.crop)
                    img = trim_whitespace(img, margin=actual_margin, threshold=file_data.threshold)
                    
                if use_max_side: img = resize_if_needed(img, max_side=max_side)
                if use_min_size: img = pad_to_min_size(img, min_size=min_size)
                check_abort()

                img = img.convert("RGB")
                base, _ = os.path.splitext(target_name)
                fmt = output_format.lower()
                out_path = os.path.join(output_folder, base + f".{fmt}")
                max_file_size = max_mb * 1024 * 1024

                if fmt in ["jpg", "jpeg"]:
                    if use_max_mb:
                        current_q = 100
                        img.save(out_path, "JPEG", quality=current_q, optimize=True)
                        while os.path.getsize(out_path) > max_file_size and current_q > 10:
                            check_abort()
                            current_q -= 10
                            img.save(out_path, "JPEG", quality=current_q, optimize=True)
                    else:
                        img.save(out_path, "JPEG", quality=100, optimize=True)
                elif fmt == "webp":
                    if use_max_mb:
                        current_q = 100
                        img.save(out_path, "WEBP", quality=current_q)
                        while os.path.getsize(out_path) > max_file_size and current_q > 10:
                            check_abort()
                            current_q -= 10
                            img.save(out_path, "WEBP", quality=current_q)
                    else:
                        img.save(out_path, "WEBP", quality=100)
                elif fmt == "png":
                    img.save(out_path, "PNG", optimize=True)
                elif fmt == "avif":
                    img.save(out_path, "AVIF", quality=100)
                elif fmt in ["tiff", "tif"]:
                    img.save(out_path, "TIFF", compression="tiff_deflate")
                else:
                    img.save(out_path)
                
                file_saved = True
                logger.info(f"Zapisano (Pillow): {out_path}")

        except UserAbortException:
            if out_path and os.path.exists(out_path):
                try: os.remove(out_path)
                except OSError: pass
            if file_data.item_id:
                file_progress_callback(file_data.item_id, 'abort')
            return
        except Exception as e:
            logger.exception(f"Nieoczekiwany błąd przy {os.path.basename(source_path)}")
            if file_data.item_id:
                file_progress_callback(file_data.item_id, 'abort')

        if file_saved:
            if file_data.item_id:
                file_progress_callback(file_data.item_id, 'done')
        
        with progress_lock:
            completed_count += 1
            percent = int((completed_count / total) * 100)
            progress_callback(percent, None)

    # Jeden zjednoczony wątek wielordzeniowy (PyVips sam zrównolegla pracę wewnątrz!)
    cpu_count = multiprocessing.cpu_count() or 4

    # OPTYMALIZACJA: Różne strategie dla PyVips vs Pillow
    if HAS_PYVIPS:
        # PyVips używa wielowątkowości WEWNĘTRZ (libvips). Lepiej 2-3 pliki naraz
        # z pełną mocą, niż 10 plików walczących o cache CPU.
        workers = min(3, max(1, cpu_count // 3))
    else:
        # Pillow jest jednowątkowy dla pojedynczego zdjęcia - potrzebuje więcej wątków
        workers = max(1, (cpu_count * 3) // 4)

    executor = concurrent.futures.ThreadPoolExecutor(max_workers=workers)
    futures = []
    
    try:
        for task in file_list:
            if stop_event and stop_event.is_set():
                break
            futures.append(executor.submit(process_single_file, task))
        
        # Czekaj na zakończenie już uruchomionych zadań, ale sprawdzaj stop_event
        for future in concurrent.futures.as_completed(futures):
            # Tu future.result() mogłoby rzucać wyjątki, ale łapiemy je wewnątrz process_single_file
            if stop_event and stop_event.is_set():
                break
    finally:
        is_aborted = stop_event and stop_event.is_set()

        if is_aborted:
            # Użytkownik zatrzymał: zdejmijmy niezaczęte zadania z kolejki!
            for f in futures:
                f.cancel()

            # Zatrzymaj wszystkie spinery dla zadań które się nie zakończyły
            for task in file_list:
                if task.item_id:
                    try:
                        file_progress_callback(task.item_id, 'abort')
                    except Exception:
                        pass

        # Wywołujemy shutdown nie czekając na te które "zawiesiły się" lub mocno przeliczają vips'em,
        # Python 3.9+ ma param cancel_futures=True, poniżej uderzamy failover bez czekania.
        try:
            executor.shutdown(wait=not is_aborted, cancel_futures=is_aborted)
        except TypeError:
            # Starsze wersje Pythona < 3.9 nie mają parametru cancel_futures
            executor.shutdown(wait=not is_aborted)
            
        # Wyczyść ile się da cache ZAWSZE PO shutdownie
        if HAS_PYVIPS:
            # Wymuś zapis/flush przed czyszczeniem jeśli to możliwe
            try:
                pyvips.cache_set_max(0)
                pyvips.cache_set_max_mem(0)
            except Exception:
                pass
        gc.collect()

    # OBLICZ I WYŚWIETL CZAS PRZETWARZANIA
    batch_elapsed_time = time.time() - batch_start_time
    minutes = int(batch_elapsed_time // 60)
    seconds = int(batch_elapsed_time % 60)
    time_str = f"{minutes}m {seconds}s"

    if stop_event and stop_event.is_set():
        progress_callback(0, f"Zatrzymano (Czas: {time_str})")
        logger.info(f"PRZETWARZANIE ZATRZYMANE po: {time_str}")
    else:
        progress_callback(100, f"Zakończono (Czas: {time_str})")
        logger.info(f"PRZETWARZANIE UKOŃCZONE: {total} plików w czasie: {time_str}")


# ===== FUNKCJE TEKSTOWE I POMOCNICZE =====

def format_size(size: int) -> str:
    """Formatuje rozmiar pliku w bajtach do czytelnej postaci."""
    power = 1024
    n = size
    power_labels = {0: 'B', 1: 'KB', 2: 'MB', 3: 'GB', 4: 'TB'}
    count = 0
    while n >= power and count < len(power_labels) - 1:
        n /= power
        count += 1

    if count == 0:
        return f"{int(n)} {power_labels[count]}"
    # Zaokrąglij do 1 miejsca po przecinku - 2.99 → 3.0
    return f"{round(n, 1):.1f} {power_labels[count]}"


def slugify_pl(text: str) -> str:
    """Zamienia polskie znaki i formatuje tekst jako slug (URL-friendly)."""
    if not text:
        return ""
    pl_map = {
        'ą': 'a', 'ć': 'c', 'ę': 'e', 'ł': 'l', 'ń': 'n', 'ó': 'o', 'ś': 's', 'ź': 'z', 'ż': 'z',
        'Ą': 'A', 'Ć': 'C', 'Ę': 'E', 'Ł': 'L', 'Ń': 'N', 'Ó': 'O', 'Ś': 'S', 'Ź': 'Z', 'Ż': 'Z'
    }
    for k, v in pl_map.items():
        text = text.replace(k, v)
    text = unicodedata.normalize('NFKD', text).encode('ascii', 'ignore').decode('utf-8')
    text = re.sub(r'[^a-zA-Z0-9]', '-', text)
    text = re.sub(r'-+', '-', text)
    return text

# ===== MENEDŻER KONFIGURACJI =====

class ConfigManager:
    """Zarządza zapisywaniem i wczytywaniem konfiguracji aplikacji."""

    CONFIG_FILE: str = "config.json"

    def __init__(self, root: tk.Tk, logger: logging.Logger):
        """Inicjalizuje menedżer konfiguracji.

        Args:
            root: Główne okno aplikacji (dla timerów)
            logger: Logger do logowania błędów
        """
        self.root = root
        self.logger = logger
        self._config_save_timer = None
        self.enable_debug_logging = False  # Flaga dla logowania diagnostycznego
        self._last_sash_positions = {}
        self.saved_col_widths = {}

    def get_last_sash_position(self, idx: int) -> Optional[int]:
        """Zwraca ostatnią zapisaną pozycję sash."""
        return self._last_sash_positions.get(idx)

    def set_last_sash_position(self, idx: int, pos: int) -> None:
        """Aktualizuje pozycję podzielnika."""
        self._last_sash_positions[idx] = pos

    def schedule_config_save(self, save_callback: Callable[[], None], delay_ms: int = 500) -> None:
        """Planuje zapis konfiguracji z debouncingiem.

        Args:
            save_callback: Funkcja do wywołania po zapisaniu
            delay_ms: Opóźnienie w milisekundach
        """
        if self._config_save_timer:
            self.root.after_cancel(self._config_save_timer)
        self._config_save_timer = self.root.after(delay_ms, save_callback)

    def load_config(self) -> Optional[AppConfig]:
        """Wczytuje konfigurację z pliku.

        Returns:
            AppConfig lub None jeśli plik nie istnieje lub wystąpił błąd
        """
        if not os.path.exists(self.CONFIG_FILE):
            return None

        try:
            with open(self.CONFIG_FILE, encoding='utf-8') as f:
                data = json.load(f)
                config = AppConfig.from_dict(data)
                self.saved_col_widths = config.column_widths
                return config
        except (IOError, OSError, json.JSONDecodeError, ValueError) as e:
            self.logger.error(f"Błąd wczytywania konfiguracji: {e}")
            return None

    def save_config(self, config: AppConfig) -> None:
        """Zapisuje konfigurację do pliku.

        Args:
            config: Obiekt AppConfig do zapisania
        """
        try:
            with open(self.CONFIG_FILE, "w", encoding='utf-8') as f:
                json.dump(config.to_dict(), f, indent=2)
        except (IOError, OSError) as e:
            self.logger.error(f"Błąd zapisu konfiguracji: {e}")

    def capture_column_widths(self, tree: ttk.Treeview, all_columns: Tuple[str, ...]) -> Dict[str, int]:
        """Pobiera aktualne szerokości kolumn z Treeview.

        Args:
            tree: Widget Treeview
            all_columns: Krotka z nazwami kolumn

        Returns:
            Słownik z nazwami kolumn i ich szerokościami
        """
        col_widths = {}
        try:
            col_widths["#0"] = int(tree.column("#0", "width"))
            for col in all_columns:
                col_widths[col] = int(tree.column(col, "width"))
        except Exception as e:
            self.logger.debug(f"Błąd pobierania szerokości kolumn: {e}")
        return col_widths

    def restore_layout_state(
        self,
        main_paned: tk.PanedWindow,
        left_panel_width: int,
        preview_panel_width: int
    ) -> None:
        """Przywraca zapisane szerokości paneli po pełnym załadowaniu okna.

        Args:
            main_paned: Główny widget PanedWindow
            left_panel_width: Szerokość lewego panelu
            preview_panel_width: Szerokość panelu podglądu
        """
        try:
            main_paned.update_idletasks()
            total_width = main_paned.winfo_width()

            if self.enable_debug_logging:
                self.logger.info(f"restore_layout_state: total_width={total_width}, left_panel_width={left_panel_width}, preview_panel_width={preview_panel_width}")

            if total_width < 200:
                self.logger.warning(f"PanedWindow width too small: {total_width}, skipping restoration")
                return

            sash_0_pos = left_panel_width
            sash_1_pos = total_width - preview_panel_width

            if self.enable_debug_logging:
                self.logger.info(f"Calculated sash positions: sash_0_pos={sash_0_pos}, sash_1_pos={sash_1_pos}")

            if sash_0_pos < 10 or sash_1_pos < 10 or sash_1_pos >= total_width - 10:
                self.logger.warning(f"Invalid sash positions: sash0={sash_0_pos}, sash1={sash_1_pos}, total_width={total_width}")
                return

            main_paned.sash_place(0, sash_0_pos, 0)
            main_paned.sash_place(1, sash_1_pos, 0)

            if self.enable_debug_logging:
                self.logger.info(f"Sash positions applied successfully")
            main_paned.update_idletasks()
        except Exception as e:
            self.logger.exception(f"Błąd przywracania układu")


# ===== MENEDŻER DRAG & DROP =====

class DragDropHandler:
    """Obsługa drag & drop w Treeview i zewnętrznych plików."""

    def __init__(
        self,
        tree: ttk.Treeview,
        root: tk.Tk,
        logger: logging.Logger,
        thumbnails: Dict[str, Any],
        valid_ext: Tuple[str, ...],
        get_is_processing_callback: Callable[[], bool],
        process_files_callback: Callable[[List[str]], None],
        show_preview_callback: Callable[[str], None],
        toggle_lifestyle_callback: Callable[[str], None],
        sort_column_callback: Callable[[str], None],
        swap_columns_callback: Callable[[str, str], None],
        apply_names_callback: Callable[[], None],
        set_manual_order_callback: Callable[[], None] = None,
        # Callbacki do odczytu zmiennych Tkinter w głównym wątku
        get_margin_callback: Callable[[], int] = None,
        get_threshold_callback: Callable[[], int] = None,
        get_use_margin_callback: Callable[[], bool] = None
    ):
        """Inicjalizuje handler drag & drop.

        Args:
            tree: Widget Treeview
            root: Główne okno aplikacji
            logger: Logger do logowania
            thumbnails: Słownik miniatur
            valid_ext: Krotka dozwolonych rozszerzeń
            get_is_processing_callback: Funkcja zwracająca czy trwa przetwarzanie
            process_files_callback: Funkcja przetwarzająca upuszczone pliki
            show_preview_callback: Funkcja pokazująca podgląd
            toggle_lifestyle_callback: Funkcja przełączająca checkbox
            sort_column_callback: Funkcja sortująca kolumnę
            swap_columns_callback: Funkcja zamieniająca kolumny
            apply_names_callback: Funkcja stosująca nazwy po przesunięciu
            set_manual_order_callback: Funkcja ustawiająca flagę ręcznej kolejności
            get_margin_callback: Funkcja zwracająca wartość margin
            get_threshold_callback: Funkcja zwracająca wartość threshold
            get_use_margin_callback: Funkcja zwracająca wartość use_margin
        """
        self.tree = tree
        self.root = root
        self.logger = logger
        self.thumbnails = thumbnails
        self.valid_ext = valid_ext

        self.get_is_processing = get_is_processing_callback
        self.process_files = process_files_callback
        self.show_preview = show_preview_callback
        self.toggle_lifestyle = toggle_lifestyle_callback
        self.sort_column = sort_column_callback
        self.swap_columns = swap_columns_callback
        self.apply_names = apply_names_callback
        self.set_manual_order = set_manual_order_callback

        # Callbacki do odczytu zmiennych Tkinter (bezpieczne dla wątków)
        self.get_margin = get_margin_callback or (lambda: 0)
        self.get_threshold = get_threshold_callback or (lambda: 10)
        self.get_use_margin = get_use_margin_callback or (lambda: True)

        self.drag_item: Optional[str] = None
        self.drag_col: Optional[str] = None
        self.drag_toplevel: Optional[tk.Toplevel] = None


    def on_drop_files(self, event) -> None:
        """Obsługa upuszczenia plików z zewnątrz."""
        if self.get_is_processing():
            self.logger.warning(f"Drag & drop zablokowany - is_processing={self.get_is_processing()}")
            return

        files = self.root.tk.splitlist(event.data)
        paths_to_process = []
        for p in files:
            if os.path.isdir(p):
                try:
                    for f in os.listdir(p):
                        if f.lower().endswith(self.valid_ext):
                            paths_to_process.append(os.path.join(p, f))
                except OSError as e:
                    self.logger.error(f"Błąd odczytu folderu {p}: {e}")
            elif os.path.isfile(p):
                if p.lower().endswith(self.valid_ext):
                    paths_to_process.append(p)

        self.logger.info(f"Drag & drop: znaleziono {len(paths_to_process)} plików")
        if paths_to_process:
            # Odczytaj zmienne Tkinter w głównym wątku
            sorted_paths = sorted(paths_to_process)
            margin = self.get_margin()
            threshold = self.get_threshold()
            use_margin = self.get_use_margin()

            # Uruchom przetwarzanie w osobnym wątku z parametrami
            threading.Thread(
                target=self.process_files,
                args=(sorted_paths,),
                kwargs={'margin': margin, 'threshold': threshold, 'use_margin': use_margin},
                daemon=True
            ).start()

    def show_drag_ghost(self, item_id: str, event) -> None:
        """Pokazuje wizualizację przeciąganego elementu."""
        if self.drag_toplevel:
            self.drag_toplevel.destroy()

        photo = self.thumbnails.get(item_id)
        if not photo:
            return

        self.drag_toplevel = tk.Toplevel(self.root)
        self.drag_toplevel.overrideredirect(True)
        self.drag_toplevel.attributes('-alpha', 0.6)
        self.drag_toplevel.attributes("-topmost", True)

        lbl = tk.Label(self.drag_toplevel, image=photo, bg="gray")
        lbl.image = photo
        lbl.pack()

        self.drag_toplevel.geometry(f"+{event.x_root + 15}+{event.y_root + 15}")

    def on_left_click(self, event) -> Optional[str]:
        """Obsługa kliknięcia lewym przyciskiem myszy.

        Returns:
            "break" jeśli zdarzenie zostało obsłużone, None inaczej
        """
        region = self.tree.identify_region(event.x, event.y)

        if region == "heading":
            col_id = self.tree.identify_column(event.x)
            # Jeśli kliknięto w nagłówek #0, system obsłuży to przez command
            # Ale musimy zapobiec sortowaniu dla #0
            if col_id != "#0":
                self.drag_col = col_id
                self.tree.config(cursor="sb_h_double_arrow")
                return "break"

        item = self.tree.identify_row(event.y)
        if not item:
            return None

        bbox = self.tree.bbox(item, column="#0")
        if bbox:
            relative_x = event.x - bbox[0]
            if 0 <= relative_x <= ConfigConstants.CHECKBOX_WIDTH:
                self.toggle_lifestyle(item)
                self.root.after(50, lambda: self.show_preview(item))
                return "break"

        ctrl_pressed = (event.state & 0x0004) != 0
        shift_pressed = (event.state & 0x0001) != 0

        if ctrl_pressed or shift_pressed:
            self.root.after(50, lambda: self.show_preview(item))
            return None

        self.drag_item = item
        self.root.after(50, lambda: self.show_preview(item))
        return None

    def on_drag_motion(self, event) -> None:
        """Obsługa ruchu podczas przeciągania."""
        # Obsługa przeciągania kolumn
        if self.drag_col:
            return

        # Obsługa przeciągania wierszy
        if self.drag_item and not self.drag_toplevel:
            self.show_drag_ghost(self.drag_item, event)
            self.tree.config(cursor="fleur")

        if self.drag_toplevel:
            self.drag_toplevel.geometry(f"+{event.x_root + 15}+{event.y_root + 15}")

            y = event.y
            height = self.tree.winfo_height()
            scroll_margin = 30

            if y < scroll_margin:
                self.tree.yview_scroll(-1, "units")
            elif y > height - scroll_margin:
                self.tree.yview_scroll(1, "units")

            target_item = self.tree.identify_row(event.y)
            if target_item and target_item != self.drag_item:
                self.tree.selection_set(target_item)

    def on_drag_release(self, event) -> None:
        """Obsługa zwolnienia przycisku myszy."""
        self.tree.config(cursor="")
        if self.drag_toplevel:
            self.drag_toplevel.destroy()
            self.drag_toplevel = None

        region = self.tree.identify_region(event.x, event.y)

        if self.drag_col:
            # Pobierz kolumnę nad którą puszczono mysz
            target_col_id = self.tree.identify_column(event.x)
            if target_col_id:
                if target_col_id == self.drag_col:
                    if region == "heading":
                        self.sort_column(self.drag_col)
                elif target_col_id != "#0":
                    self.swap_columns(self.drag_col, target_col_id)
            self.drag_col = None
            return

        if self.drag_item:
            target_item = self.tree.identify_row(event.y)
            if target_item and target_item != self.drag_item:
                try:
                    self.tree.move(self.drag_item, self.tree.parent(self.drag_item), self.tree.index(target_item))
                    self.apply_names()
                    # Oznacz że ręczna kolejność została ustawiona
                    if self.set_manual_order:
                        self.set_manual_order()
                except Exception as e:
                    self.logger.debug(f"Błąd podczas przesuwania elementu: {e}")
            self.drag_item = None


# ===== MENEDŻER MINIATUR =====

class ThumbnailManager:
    """Zarządza tworzeniem i aktualizacją miniatur."""

    def __init__(
        self,
        tree: ttk.Treeview,
        logger: logging.Logger,
        thumb_size_var: tk.IntVar,
        dark_mode_var: Callable[[], bool],
        thumbnails: Dict[str, Any],
        lifestyle_states: Dict[str, bool]
    ):
        """Inicjalizuje menedżer miniatur.

        Args:
            tree: Widget Treeview
            logger: Logger do logowania
            thumb_size_var: Zmienna rozmiaru miniatur
            dark_mode_var: Funkcja zwracająca czy tryb ciemny jest aktywny
            thumbnails: Słownik miniatur
            lifestyle_states: Słownik stanów checkboxów
        """
        self.tree = tree
        self.logger = logger
        self.thumb_size_var = thumb_size_var
        self.dark_mode_var = dark_mode_var
        self.thumbnails = thumbnails
        self.lifestyle_states = lifestyle_states
        self.data_lock = threading.Lock()

    def create_composite_thumbnail(self, img_pil, is_checked, spinner_angle: Optional[int] = None) -> ImageTk.PhotoImage:
        """Tworzy miniaturę z checkboxem lifestyle lub obracającym się kółkiem ładowania."""
        thumb_size = self.thumb_size_var.get()
        img_copy = img_pil.copy()
        img_copy.thumbnail((thumb_size, thumb_size))

        box_size = 28
        canvas_height = max(thumb_size, box_size)
        total_width = ConfigConstants.CHECKBOX_WIDTH + thumb_size
        composite = Image.new("RGBA", (total_width, canvas_height), (255, 255, 255, 0))

        draw = ImageDraw.Draw(composite)

        box_x = 2
        box_y = (canvas_height - box_size) // 2

        # Pobieranie trybu ciemnego (dark_mode_var to funkcja zwracająca bool)
        is_dark = self.dark_mode_var()
        outline_color = "#aaaaaa" if is_dark else "black"

        # Rysowanie ramki kwadratu
        draw.rectangle([box_x, box_y, box_x + box_size, box_y + box_size], outline=outline_color, width=2)

        if spinner_angle is not None:
            # TRYB ŁADOWANIA: Rysujemy tło i obracający się spinner (łuk)
            bg_fill = (43, 43, 43, 255) if is_dark else (255, 255, 255, 255)
            draw.rectangle([box_x + 1, box_y + 1, box_x + box_size - 1, box_y + box_size - 1], fill=bg_fill)

            margin = 5
            arc_bbox = [box_x + margin, box_y + margin, box_x + box_size - margin, box_y + box_size - margin]

            # Subtelne tło kółka (pełne kółko)
            circle_bg = "#555555" if is_dark else "#dddddd"
            draw.ellipse(arc_bbox, outline=circle_bg, width=2)

            # Kręcący się niebieski element (wycinek 100 stopni)
            draw.arc(arc_bbox, start=spinner_angle, end=spinner_angle + 100, fill="#007bff", width=2)

        elif is_checked:
            # TRYB LIFESTYLE: Rysujemy zielonego ptaszka
            line_w = 4
            check_color = "#28a745"
            points = [(box_x + 5, box_y + 14), (box_x + 12, box_y + 22), (box_x + 24, box_y + 6)]
            try:
                # Rysuj ptaszka - joint="curve" jest tylko w Pillow 10+, używamy wersji kompatybilnej
                draw.line(points, fill=check_color, width=line_w)
            except Exception as e:
                # Fallback - rysuj ptaszka po linijkach
                draw.line([points[0], points[1]], fill=check_color, width=line_w)
                draw.line([points[1], points[2]], fill=check_color, width=line_w)

        img_x = ConfigConstants.CHECKBOX_WIDTH
        img_y = (canvas_height - img_copy.height) // 2
        composite.paste(img_copy, (img_x, img_y))
        return ImageTk.PhotoImage(composite)

    def update_thumbnail_in_tree(self, item_id, photo) -> None:
        """Aktualizuje miniaturę w drzewie."""
        if self.tree.exists(item_id):
            self.tree.item(item_id, image=photo)

    def get_lifestyle_state(self, item_id) -> bool:
        """Pobiera stan lifestyle dla elementu."""
        return self.lifestyle_states.get(item_id, False)

    def set_lifestyle_state(self, item_id, state: bool) -> None:
        """Ustawia stan lifestyle dla elementu."""
        with self.data_lock:
            self.lifestyle_states[item_id] = state


# ===== MENEDŻER PODGLĄDU =====

class PreviewManager:
    """Zarządza asynchronicznym ładowaniem i wyświetlaniem podglądów."""

    def __init__(
        self,
        root: tk.Tk,
        preview_canvas: tk.Canvas,
        logger: logging.Logger,
        get_threshold_callback: Callable[[], int]
    ):
        """Inicjalizuje menedżer podglądu.

        Args:
            root: Główne okno aplikacji
            preview_canvas: Canvas do wyświetlania podglądu
            logger: Logger do logowania
            get_threshold_callback: Funkcja zwracająca wartość progu
        """
        self.root = root
        self.preview_canvas = preview_canvas
        self.logger = logger
        self.get_threshold = get_threshold_callback

        self.preview_cache: Dict[str, Tuple[Any, int, int]] = {}
        self.preloaded_pil_previews: Dict[str, Any] = {}
        self.preview_loading: bool = False
        self.current_preview_item: Optional[str] = None
        self.preview_req_id: int = 0
        self.preview_image_ref: Optional[Any] = None
        self.preview_image_window: Optional[int] = None

        # Executor dla podglądu - max 1 wątek, kontrolowane kolejkowanie
        self.preview_executor = ThreadPoolExecutor(max_workers=1, thread_name_prefix="preview")
        self.current_preview_future: Optional[concurrent.futures.Future] = None

    def clear_cache_for_item(self, item_id: str, keep_orig: bool = False, clear_preloaded: bool = True) -> None:
        """Czyści cache dla danego elementu."""
        try:
            keys_to_delete = [k for k in list(self.preview_cache.keys())
                              if k.startswith(f"{item_id}_")]
            if keep_orig:
                keys_to_delete = [k for k in keys_to_delete if not k.endswith("_orig")]
                
            for key in keys_to_delete:
                del self.preview_cache[key]
                
            if clear_preloaded and not keep_orig and item_id in self.preloaded_pil_previews:
                del self.preloaded_pil_previews[item_id]
        except Exception as e:
            self.logger.exception(f"Błąd czyszczenia cache")

    def get_cache(self) -> Dict[str, Tuple[Any, int, int]]:
        """Zwraca słownik cache."""
        return self.preview_cache

    def get_preloaded(self) -> Dict[str, Any]:
        """Zwraca słownik preloaded previews."""
        return self.preloaded_pil_previews

    def is_loading(self) -> bool:
        """Zwraca czy trwa ładowanie."""
        return self.preview_loading

    def set_loading(self, value: bool) -> None:
        """Ustawia flagę ładowania."""
        self.preview_loading = value

    def new_request_id(self) -> int:
        """Generuje nowe ID żądania i inkrementuje licznik."""
        self.preview_req_id += 1
        return self.preview_req_id

    def get_current_request_id(self) -> int:
        """Zwraca aktualne ID żądania."""
        return self.preview_req_id

    def submit_preview_task(self, func, *args) -> None:
        """Zgłasza zadanie podglądu do executora, anuluje poprzednie.

        Args:
            func: Funkcja do wykonania
            *args: Argumenty funkcji
        """
        # Anuluj poprzednie zadanie jeśli istnieje i jeszcze nie zostało ukończone
        if self.current_preview_future is not None:
            if not self.current_preview_future.done():
                self.current_preview_future.cancel()

        # Zgłoś nowe zadanie
        self.current_preview_future = self.preview_executor.submit(func, *args)

    def shutdown(self) -> None:
        """Zamyka executor podglądu."""
        try:
            self.preview_executor.shutdown(wait=False)
        except Exception:
            pass


# ===== KLASA GUI =====

class ImageProcessorApp:
    """Główna klasa aplikacji przetwarzającej obrazy."""

    VALID_EXT: Tuple[str, ...] = (".jpg", ".jpeg", ".png", ".webp", ".bmp", ".avif", ".tiff", ".tif")

    # Stałe nazw kolumn treeview
    COL_NAME = ConfigConstants.COL_NAME
    COL_SIZE = ConfigConstants.COL_SIZE
    COL_RESOLUTION = ConfigConstants.COL_RESOLUTION
    COL_NEWNAME = ConfigConstants.COL_NEWNAME

    def __init__(self, root: tk.Tk) -> None:
        """Inicjalizuje aplikację."""
        self.root = root
        self.root.title("FotoPIM")

        # Stan pełnoekranowy
        self.fullscreen: bool = False

        # === IKONA APLIKACJI ===
        self.icon_path = None
        try:
            if IS_MACOS:
                self.icon_path = resource_path("ikona.icns")
                if os.path.exists(self.icon_path):
                    from PIL import Image as _PILImage
                    _icon_img = _PILImage.open(self.icon_path)
                    self._app_icon_photo = ImageTk.PhotoImage(_icon_img)
                    self.root.iconphoto(True, self._app_icon_photo)
                else:
                    logger.debug(f"Plik ikony nie istnieje: {self.icon_path}")
            else:
                self.icon_path = resource_path("ikona.ico")
                if os.path.exists(self.icon_path):
                    self.root.iconbitmap(self.icon_path)
                else:
                    logger.debug(f"Plik ikony nie istnieje: {self.icon_path}")
        except Exception as e:
            logger.debug(f"Nie udało się załadować ikony: {e}")

        self.root.geometry("1400x850")

        # Przełączanie pełnego ekranu (F11)
        self.root.bind('<F11>', self.toggle_fullscreen)

        # Zmienne parametrów
        self.input_folder: tk.StringVar = tk.StringVar()
        self.output_folder: tk.StringVar = tk.StringVar()
        self.margin_var: tk.StringVar = tk.StringVar(value="0")
        self.threshold_var: tk.StringVar = tk.StringVar(value="10")
        self.max_side_var: tk.StringVar = tk.StringVar(value="3000")
        self.min_size_var: tk.StringVar = tk.StringVar(value="500")
        self.max_mb_var: tk.StringVar = tk.StringVar(value="2.99")

        # Zmienna formatu zapisu:
        self.output_format_var: tk.StringVar = tk.StringVar(value="JPG")
        
        def on_format_change(*_):
            self.schedule_config_save()
            if hasattr(self, 'apply_names'):
                self.apply_names()
                
        self.output_format_var.trace_add("write", on_format_change)

        # Checkboxy dla parametrów - domyślnie wszystkie włączone
        self.use_margin_var = tk.BooleanVar(value=True)
        self.use_max_side_var = tk.BooleanVar(value=True)
        self.use_min_size_var = tk.BooleanVar(value=True)
        self.use_max_mb_var = tk.BooleanVar(value=True)

        # Rejestracja zdarzeń dla checkboxów zabezpieczona przed wyciekiem referencji pętli
        for var, callback in [
            (self.use_margin_var, self.on_margin_checkbox_changed),
            (self.use_max_side_var, self.on_max_side_checkbox_changed),
            (self.use_min_size_var, self.on_min_size_checkbox_changed),
            (self.use_max_mb_var, self.on_max_mb_checkbox_changed)
        ]:
            var.trace_add("write", lambda *_, cb=callback: cb())

        # Zmienne wyglądu
        self.thumb_size_var: tk.IntVar = tk.IntVar(value=50)
        self.font_size_left_panel_var: tk.IntVar = tk.IntVar(value=11)
        self.font_size_table_header_var: tk.IntVar = tk.IntVar(value=11)
        self.font_family_var: tk.StringVar = tk.StringVar(value="Arial")
        self.font_bold_var: tk.BooleanVar = tk.BooleanVar(value=False)
        self.font_bold_var.trace_add("write", lambda *_: self.on_font_bold_changed())
        
        self.fullscreen_hq_var: tk.BooleanVar = tk.BooleanVar(value=False)
        self.dark_mode: bool = False
        self.light_preview_bg: str = "#d0d0d0"
        self.light_font_color: str = "black"
        self.dark_font_color: str = "white"
        self.button_text_colors: Dict[str, str] = {}
        self._widget_to_name: Dict[Any, str] = {} # Mapowanie O(1) do kolorów przycisków
        
        self.debug_logging_var: tk.BooleanVar = tk.BooleanVar(value=False)
        self.enable_debug_logging: bool = False  # Flaga kontrolująca logowanie diagnostyczne

        # Zmienne nazewnictwa
        self.clean_name_var: tk.StringVar = tk.StringVar()
        self.clean_name_var.trace_add("write", lambda *_: self.apply_names())
        # Śledzenie ręcznie edytowanych nazw - te nie będą nadpisywane przez apply_names
        self._manually_edited_names: set = set()
        self._tooltip_hide_timer: Optional[str] = None  # Timer do ukrywania tooltipa

        # Zmienna: Numer startowy
        self.start_number_var: tk.StringVar = tk.StringVar(value="1")
        self.start_number_var.trace_add("write", lambda *_: self.apply_names())

        self.processing_thread: Optional[threading.Thread] = None
        self.data_lock: threading.Lock = threading.Lock()
        self.thumbnails: Dict[str, Any] = {}
        self.source_images: Dict[str, Any] = {}
        self.lifestyle_states: Dict[str, bool] = {}
        self.item_thresholds: Dict[str, int] = {}
        self.item_crops: Dict[str, Tuple[float, float, float, float]] = {}
        self.item_rotations: Dict[str, int] = {}  # 0=0°, 1=90°, 2=180°, 3=270°
        self.crop_mode_active: bool = False
        self.crop_lines: Dict[str, int] = {}
        self.crop_dragging: Optional[str] = None
        self.crop_original_coords: Dict[str, float] = {}

        # Gumka
        self.eraser_mode_active: bool = False
        self.eraser_size: int = 20
        self.eraser_shape: str = "square"  # "square" or "circle"
        self.eraser_strokes: Dict[str, List[List[Tuple[float, float, int, int, int, str]]]] = {} # [ (x, y, rozmiar, img_w, img_h, shape), ... ]
        self.current_eraser_stroke: List[Tuple[float, float, int, int, int, str]] = []
        self.eraser_rect_id = None

        self.preview_img_x: int = 0
        self.preview_img_y: int = 0
        self.preview_img_w: int = 0
        self.preview_img_h: int = 0

        # Zmienna do obsługi Master Checkbox (Zaznacz wszystko)
        self.all_lifestyle_checked: bool = False

        # Sortowanie (drag & drop obsługuje DragDropHandler)
        self.sort_reverse: Dict[str, bool] = {}
        self.manual_order_enabled: bool = False  # Flag: czy ręczne przesunięcie wyłącza sortowanie

        # Inicjalizacja atrybutów dla widoku podglądu i trybu fullscreen

        self._fs_toplevel: Optional[ctk.CTkToplevel] = None

        # DragDropHandler i ThumbnailManager będą utworzone w create_widgets() po utworzeniu tree
        self.drag_drop_handler: Optional[DragDropHandler] = None
        self.thumbnail_manager: Optional[ThumbnailManager] = None

        # ThreadPoolExecutor do generowania miniaturek (ogranicza liczbę wątków)
        self.thumbnail_executor = concurrent.futures.ThreadPoolExecutor(max_workers=4, thread_name_prefix="thumbs")

        # Timer dla tymczasowych komunikatów statusu
        self._status_timer = None

        # saved_col_widths jest teraz zarządzane przez ConfigManager
        # self.config_manager.saved_col_widths

        self.display_columns: List[str] = [self.COL_SIZE, self.COL_RESOLUTION, self.COL_NEWNAME]

        # PreviewManager będzie utworzony w setup_preview_panel() po utworzeniu preview_canvas
        self.preview_manager: Optional[PreviewManager] = None

        # Te atrybuty są nadal używane bezpośrednio przez ImageProcessorApp
        self.tree: Optional[ttk.Treeview] = None
        self.preview_frame: Optional[tk.Frame] = None
        self.preview_canvas: Optional[tk.Canvas] = None
        self.preview_image_label: Optional[tk.Label] = None
        self.name_entry: Optional[ctk.CTkEntry] = None
        self.appearance_menubutton: Optional[tk.Menubutton] = None
        self.button_colors: Dict[str, str] = {}
        self.btn_browse_in: Optional[ctk.CTkButton] = None
        self.btn_browse_out: Optional[ctk.CTkButton] = None
        self.btn_delete_input: Optional[ctk.CTkButton] = None
        self.btn_delete_output: Optional[ctk.CTkButton] = None
        self.active_spinners: Dict[str, Any] = {}
        self._spinner_frames_cache: Dict[str, List[Any]] = {}

        self.preview_image_ref: Optional[Any] = None
        self.preview_panel_width: int = 300
        self.left_panel_width: int = 378
        self._is_initializing: bool = True
        self.current_preview_item: Optional[str] = None

        self.tooltip_window: Optional[tk.Toplevel] = None
        self.tooltip_label: Optional[ctk.CTkLabel] = None
        self.last_col_id: Optional[str] = None

        # Lista widgetów w lewym panelu, których czcionki trzeba aktualizować
        self.left_panel_font_widgets: List[Any] = []

        # Menedżer konfiguracji
        self.config_manager = ConfigManager(self.root, logger)

        # Upewnij się że is_processing jest False przed załadowaniem configu
        self.is_processing = False
        if self.enable_debug_logging:
            logger.info(f"__init__ BEFORE load_config: _is_initializing={self._is_initializing}, left_panel_width={self.left_panel_width}, preview_panel_width={self.preview_panel_width}")
        self.load_config()
        if self.enable_debug_logging:
            logger.info(f"__init__ AFTER load_config: left_panel_width={self.left_panel_width}, preview_panel_width={self.preview_panel_width}")
        self.create_widgets()
        if self.enable_debug_logging:
            logger.info(f"__init__ AFTER create_widgets: left_panel_width={self.left_panel_width}, preview_panel_width={self.preview_panel_width}")
        self.apply_theme()

        # Drugie korekta pozycji sashów po pełnym renderowaniu (dla pewności)
        self.root.after(500, self.restore_layout_state)

        self.processing_queue: queue.Queue = queue.Queue()
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        self.theme_update_timer: Optional[str] = None
        self.stop_event: threading.Event = threading.Event()

        # Śledzenie przetworzonych plików do usunięcia
        self.processed_source_files: List[str] = []  # Ścieżki źródłowe z folderu wejściowego
        self.processed_output_files: List[str] = []  # Ścieżki wyjściowe z bieżącej sesji

    def on_font_bold_changed(self) -> None:
        if hasattr(self, "root") and hasattr(self, "tree"):
            self.apply_theme()
            self.schedule_config_save()

    def on_margin_checkbox_changed(self) -> None:
        """Odświeża wszystkie miniatury po zmianie checkboxa marginesu."""
        if not self.tree:
            return
        items = self.tree.get_children()
        if items:
            threading.Thread(target=self.regenerate_thumbnails_thread, args=(items,), daemon=True).start()

    def on_max_side_checkbox_changed(self) -> None:
        """Obsługa zmiany checkboxa Max bok - zapisuje konfigurację."""
        self.schedule_config_save()

    def on_min_size_checkbox_changed(self) -> None:
        """Obsługa zmiany checkboxa Min rozmiar - zapisuje konfigurację."""
        self.schedule_config_save()

    def on_max_mb_checkbox_changed(self) -> None:
        """Obsługa zmiany checkboxa Max mb - zapisuje konfigurację."""
        self.schedule_config_save()

    def on_debug_logging_changed(self) -> None:
        """Obsługa zmiany checkboxa logowania diagnostycznego."""
        self.enable_debug_logging = self.debug_logging_var.get()
        self.config_manager.enable_debug_logging = self.debug_logging_var.get()
        # Włącz/wyłącz logowanie do pliku
        set_file_logging(self.enable_debug_logging)
        self.schedule_config_save()
        logger.info(f"Debug logging {'enabled' if self.enable_debug_logging else 'disabled'}")

    def apply_windows_dark_title_bar(self) -> None:
        """Stosuje ciemny pasek tytułu Windows."""
        if not IS_WINDOWS:
            return
        try:
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id())
            value = 1 if self.dark_mode else 0
            ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 20, ctypes.byref(ctypes.c_int(value)), 4)
        except Exception as e:
            logger.debug(f"Nie udało się ustawić ciemnego paska tytułu: {e}")

    def apply_theme(self) -> None:
        """Stosuje motyw (jasny/ciemny) do całej aplikacji."""
        # Set customtkinter appearance mode
        ctk.set_appearance_mode("Dark" if self.dark_mode else "Light")

        style = ttk.Style(self.root)
        style.theme_use('clam')
        try:
            style.layout('Treeview.Item',
                 [('Treeitem.padding', {'sticky': 'nswe', 'children': [
                     ('Treeitem.image', {'side': 'left', 'sticky': ''}),
                     ('Treeitem.text', {'sticky': 'nswe'})
                 ]})]
            )
        except Exception:
            pass

        current_font_size_left_panel = self.font_size_left_panel_var.get()
        current_font_size_table_header = self.font_size_table_header_var.get()
        current_thumb_size = self.thumb_size_var.get()
        min_row_h = max(current_thumb_size + 10, 40)

        if self.dark_mode:
            # === DARK MODE ===
            bg_color = "#2b2b2b"
            fg_color = getattr(self, 'dark_font_color', "white")
            select_bg = "#007bff"

            font_fam = self.font_family_var.get()
            # Styluj tylko Treeview i pozostałe ttk widgety
            style.configure("Treeview", background="#333333", fieldbackground="#333333", foreground="white", font=(font_fam, current_font_size_table_header), rowheight=min_row_h, borderwidth=0, indent=0)
            style.configure("Treeview.Heading", background="#444444", foreground="white", font=(font_fam, current_font_size_table_header, 'bold'), borderwidth=1)
            style.map("Treeview", background=[('selected', select_bg)], foreground=[('selected', 'white')])

        else:
            # === LIGHT MODE ===
            bg_color = "#f0f0f0"
            fg_color = self.light_font_color
            select_bg = "#0078d7"

            font_fam = self.font_family_var.get()
            font_weight = "bold" if getattr(self, "font_bold_var", None) and self.font_bold_var.get() else "normal"
            # Styluj tylko Treeview i pozostałe ttk widgety
            style.configure("Treeview", background="white", fieldbackground="white", foreground=fg_color, font=(font_fam, current_font_size_table_header, font_weight), rowheight=min_row_h, indent=0)
            style.configure("Treeview.Heading", background="#e1e1e1", foreground=fg_color, font=(font_fam, current_font_size_table_header, 'bold'))
            style.map("Treeview", background=[('selected', select_bg)], foreground=[('selected', 'white')])

        # Zachowaj style dla ttk.Button (Treeview toolbar itp.)
        font_fam = self.font_family_var.get()
        font_weight = "bold" if getattr(self, "font_bold_var", None) and self.font_bold_var.get() else "normal"
        style.configure("Success.TButton", background="#28a745", foreground="white", font=(font_fam, current_font_size_left_panel, font_weight))
        style.map("Success.TButton", background=[('active', '#218838')])
        style.configure("Warning.TButton", background="#ffc107", foreground="black", font=(font_fam, current_font_size_left_panel, font_weight))
        style.map("Warning.TButton", background=[('active', '#e0a800')])
        style.configure("Primary.TButton", background="#007bff", foreground="white", font=(font_fam, current_font_size_left_panel, font_weight))
        style.map("Primary.TButton", background=[('active', '#0056b3')])

        # Toggle button style
        toggle_bg = "#444444" if self.dark_mode else "#e1e1e1"
        toggle_fg = "white" if self.dark_mode else self.light_font_color
        toggle_active_bg = "#555555" if self.dark_mode else "#d1d1d1"
        style.configure("Toggle.TButton", background=toggle_bg, foreground=toggle_fg, font=(font_fam, current_font_size_left_panel, font_weight), relief="flat", borderwidth=0)
        style.map("Toggle.TButton", background=[('active', toggle_active_bg)], foreground=[('active', toggle_fg)])

        self.root.config(bg=bg_color)

        # Update preview panel background color
        if self.preview_frame:
            preview_bg = "#333333" if self.dark_mode else self.light_preview_bg
            frame_color = "#666666" if self.dark_mode else "#cccccc"

            # Dla customtkinter frame - użyj fg_color
            self.preview_frame.configure(fg_color=preview_bg)

            if self.preview_canvas:
                self.preview_canvas.config(bg=preview_bg, highlightbackground=frame_color)

            # Tło pod samym zdjęciem
            if self.preview_image_label:
                try:
                    self.preview_image_label.configure(fg_color=preview_bg)
                except Exception as e:
                    logger.debug(f"Nie udało się zaktualizować koloru tła podglądu: {e}")

        # Wymuś natychmiastowe odświeżenie wszystkich widgetów przed operacjami czasochłonnymi
        self.root.update_idletasks()

        self.apply_windows_dark_title_bar()

        # Odśwież miniatury i podgląd po zakończeniu przełączania motywu
        if self.current_preview_item:
            self.show_preview(self.current_preview_item)

        self.refresh_thumbnails_display()

        # Update fonts for all widgets in left panel
        self.update_left_panel_fonts()

        # Aktualizuj motyw nagłówka
        self._update_header_theme()

    def toggle_dark_mode(self) -> None:
        """Przełącza między trybem ciemnym a jasnym."""
        self.dark_mode = not self.dark_mode
        ctk.set_appearance_mode("Dark" if self.dark_mode else "Light")
        self.apply_theme()

    def toggle_fullscreen(self, _=None) -> None:
        """Przełącza tryb pełnoekranowy."""
        self.fullscreen = not self.fullscreen
        self.root.attributes('-fullscreen', self.fullscreen)

    def update_left_panel_fonts(self) -> None:
        """Aktualizuje czcionki i kolory wszystkich widgetów w lewym panelu."""
        current_font_size = self.font_size_left_panel_var.get()
        font_fam = self.font_family_var.get()
        font_weight = "bold" if self.font_bold_var.get() else "normal"
        fg_color = getattr(self, 'dark_font_color', "white") if self.dark_mode else self.light_font_color
        
        def update_widget(widget):
            try:
                if isinstance(widget, ctk.CTkLabel):
                    widget.configure(font=ctk.CTkFont(family=font_fam, size=current_font_size, weight=font_weight), text_color=fg_color)
                elif isinstance(widget, ctk.CTkButton):
                    # O(1) lookup zamiast przeszukiwania __dict__
                    btn_key = self._widget_to_name.get(widget)
                    custom_text_color = self.button_text_colors.get(btn_key) if btn_key else None
                    
                    font_obj = ctk.CTkFont(family=font_fam, size=current_font_size, weight=font_weight)
                    if custom_text_color:
                        widget.configure(font=font_obj, text_color=custom_text_color)
                    else:
                        widget.configure(font=font_obj)
                elif isinstance(widget, ctk.CTkCheckBox):
                    widget.configure(font=ctk.CTkFont(family=font_fam, size=current_font_size, weight=font_weight), text_color=fg_color)
                elif isinstance(widget, ctk.CTkEntry):
                    widget.configure(font=ctk.CTkFont(family=font_fam, size=current_font_size, weight=font_weight), text_color=fg_color)
                elif isinstance(widget, ctk.CTkOptionMenu):
                    opt_fg = "#444444" if self.dark_mode else "#e0e0e0"
                    opt_btn = "#555555" if self.dark_mode else "#cccccc"
                    opt_hover = "#666666" if self.dark_mode else "#bbbbbb"
                    drop_fg = "#333333" if self.dark_mode else "#ffffff"
                    drop_hover = "#555555" if self.dark_mode else "#eeeeee"
                    widget.configure(
                        font=ctk.CTkFont(family=font_fam, size=current_font_size, weight=font_weight), 
                        text_color=fg_color,
                        dropdown_font=ctk.CTkFont(family=font_fam, size=current_font_size, weight=font_weight),
                        dropdown_text_color=fg_color,
                        fg_color=opt_fg,
                        button_color=opt_btn,
                        button_hover_color=opt_hover,
                        dropdown_fg_color=drop_fg,
                        dropdown_hover_color=drop_hover
                    )
            except Exception as e:
                logger.debug(f"Nie udało się zaktualizować wyglądu widgetu: {e}")

            # Rekurencyjnie sprawdź dzieci
            if hasattr(widget, 'winfo_children'):
                for child in widget.winfo_children():
                    update_widget(child)

        update_widget(self.root)

    def choose_bg_color(self) -> None:
        """Otwiera okno wyboru koloru tła podglądu."""
        current = getattr(self, 'light_preview_bg', '#d0d0d0')
        color = askcolor(color=current, title="Wybierz tło podglądu (Tryb Jasny)")[1]
        if color:
            self.light_preview_bg = color
            if not self.dark_mode:
                self.apply_theme()
            self.schedule_config_save()

    def choose_font_color(self) -> None:
        """Otwiera okno wyboru koloru czcionki."""
        mode_str = "Tryb Ciemny" if self.dark_mode else "Tryb Jasny"
        current = getattr(self, 'dark_font_color', 'white') if self.dark_mode else getattr(self, 'light_font_color', 'black')
        color = askcolor(color=current, title=f"Wybierz kolor czcionki ({mode_str})")[1]
        if color:
            if self.dark_mode:
                self.dark_font_color = color
            else:
                self.light_font_color = color
            self.apply_theme()
            self.schedule_config_save()

    def schedule_theme_update(self, delay_ms: int = 400) -> None:
        """Planuje aktualizację motywu z opóźnieniem."""
        if self.theme_update_timer:
            self.root.after_cancel(self.theme_update_timer)
        self.theme_update_timer = self.root.after(delay_ms, self.apply_theme)

    def on_tree_hover(self, event) -> None:
        region = self.tree.identify_region(event.x, event.y)
        if region == "heading":
            column_id = self.tree.identify_column(event.x)
            
            if column_id == getattr(self, 'last_col_id', None):
                return 
            
            self.last_col_id = column_id
            
            # Pobieramy logiczne ID kolumny
            logical_col = self.tree.column(column_id, option='id')
            
            if logical_col == self.COL_RESOLUTION:
                self.show_tooltip("Rozdzielczość zdjęcia po kadrowaniu", event.x_root, event.y_root)
            elif logical_col == self.COL_SIZE:
                self.show_tooltip("Rozmiar oryginalnego pliku", event.x_root, event.y_root)
            elif column_id == "#0":
                self.show_tooltip("Zaznacza wszystkie okna", event.x_root, event.y_root)
            else:
                self.hide_tooltip()
        else:
            if getattr(self, 'last_col_id', None) is not None:
                self.last_col_id = None
                self.hide_tooltip()

    def show_tooltip(self, text: str, x: int, y: int) -> None:
        if self._tooltip_hide_timer:
            self.root.after_cancel(self._tooltip_hide_timer)
            self._tooltip_hide_timer = None
        # 1. Inicjalizacja okna jeśli nie istnieje
        if self.tooltip_window is None or not self.tooltip_window.winfo_exists():
            self.tooltip_window = tk.Toplevel(self.root)
            self.tooltip_window.wm_overrideredirect(True)
            self.tooltip_window.withdraw()  # Ukryj na starcie
            self.tooltip_window.attributes("-topmost", True)

            self.tooltip_label = ctk.CTkLabel(
                self.tooltip_window,
                text=text,
                corner_radius=3,
                padx=4,
                pady=2,
                font=(self.font_family_var.get(), 9),
                fg_color="#333333",
                text_color="white"
            )
            self.tooltip_label.pack()

        # 2. Aktualizacja stylów i treści
        bg = "#333333" if self.dark_mode else "#ffffca"
        fg = "white" if self.dark_mode else "black"
        
        if self.tooltip_label:
            self.tooltip_label.configure(text=text, fg_color=bg, text_color=fg)

        # 3. Pozycjonowanie i pokazywanie
        self.tooltip_window.wm_geometry(f"+{x+15}+{y+15}")
        self.tooltip_window.deiconify()
        self.tooltip_window.lift()

    def hide_tooltip(self) -> None:
        if self._tooltip_hide_timer:
            self.root.after_cancel(self._tooltip_hide_timer)
            
        def do_hide():
            if getattr(self, 'tooltip_window', None) and self.tooltip_window.winfo_exists():
                self.tooltip_window.withdraw()
                
        self._tooltip_hide_timer = self.root.after(100, do_hide)

    def add_context_menu(self, widget) -> None:
        menu = tk.Menu(self.root, tearoff=0)

        def cut_text():
            try:
                sel = widget.selection_get()
                if sel:
                    widget.clipboard_clear()
                    widget.clipboard_append(sel)
                    widget.delete("sel.first", "sel.last")
            except Exception as e:
                logger.debug(f"Nie udało się wyciąć tekstu: {e}")

        def copy_text():
            try:
                sel = widget.selection_get()
                if sel:
                    widget.clipboard_clear()
                    widget.clipboard_append(sel)
            except Exception as e:
                logger.debug(f"Nie udało się skopiować tekstu: {e}")

        def paste_text():
            try:
                text = widget.clipboard_get()
                if text:
                    widget.insert("insert", text)
                    # Dla pola name_entry uruchom logikę poprawy nazwy
                    if self.name_entry and widget is self.name_entry:
                        # Poczekaj aż widget zaktualizuje zmienną
                        self.root.after(50, self.process_pasted_text)
            except Exception as e:
                logger.debug(f"Nie udało się wkleić tekstu: {e}")

        menu.add_command(label="Wytnij", command=cut_text)
        menu.add_command(label="Kopiuj", command=copy_text)
        menu.add_command(label="Wklej", command=paste_text)

        def show_menu(event):
            menu.tk_popup(event.x_root, event.y_root)
            return "break"
        widget.bind("<Button-3>", show_menu)

    def make_scale_draggable(self, scale_widget) -> None:
        drag_data = {'active': False, 'scale': scale_widget}

        def on_press(event):
            drag_data['active'] = True
            update_value(event)

        def on_motion(event):
            if drag_data['active']:
                update_value(event)

        def on_release(event):
            drag_data['active'] = False

        def update_value(event):
            widget = drag_data['scale']
            try:
                x = widget.winfo_rootx()
                width = widget.winfo_width()
                rel_x = (event.x_root - x) / width
                rel_x = max(0.0, min(1.0, rel_x))
                from_val = widget.cget('from')
                to_val = widget.cget('to')
                new_val = from_val + rel_x * (to_val - from_val)
                widget.set(new_val)
            except Exception as e:
                logger.debug(f"Błąd aktualizacji suwaka: {e}")

        scale_widget.bind('<ButtonPress-1>', on_press)
        scale_widget.bind('<B1-Motion>', on_motion)
        scale_widget.bind('<ButtonRelease-1>', on_release)

    def _create_label(self, parent, text, **kwargs) -> ctk.CTkLabel:
        """Tworzy CTkLabel i dodaje do listy śledzenia czcionek."""
        fg_color = "white" if self.dark_mode else self.light_font_color
        if 'text_color' not in kwargs:
            kwargs['text_color'] = fg_color
        label = ctk.CTkLabel(parent, text=text, **kwargs)
        self.left_panel_font_widgets.append(label)
        return label

    def _create_button(self, parent, text, var_name=None, **kwargs) -> ctk.CTkButton:
        """Tworzy CTkButton i dodaje do listy śledzenia czcionek."""
        button = ctk.CTkButton(parent, text=text, **kwargs)
        self.left_panel_font_widgets.append(button)
        if var_name:
            setattr(self, var_name, button)
            self._widget_to_name[button] = var_name
        return button

    def _create_checkbox(self, parent, **kwargs) -> ctk.CTkCheckBox:
        """Tworzy CTkCheckBox i dodaje do listy śledzenia czcionek."""
        fg_color = "white" if self.dark_mode else self.light_font_color
        if 'text_color' not in kwargs:
            kwargs['text_color'] = fg_color
        checkbox = ctk.CTkCheckBox(parent, **kwargs)
        self.left_panel_font_widgets.append(checkbox)
        return checkbox

    def _create_entry(self, parent, **kwargs) -> ctk.CTkEntry:
        """Tworzy CTkEntry i dodaje do listy śledzenia czcionek."""
        fg_color = "white" if self.dark_mode else self.light_font_color
        if 'text_color' not in kwargs:
            kwargs['text_color'] = fg_color
        entry = ctk.CTkEntry(parent, **kwargs)
        self.left_panel_font_widgets.append(entry)
        return entry

    def _create_option_menu(self, parent, **kwargs) -> ctk.CTkOptionMenu:
        """Tworzy CTkOptionMenu i dodaje do listy śledzenia czcionek."""
        fg_color = "white" if self.dark_mode else self.light_font_color
        if 'text_color' not in kwargs:
            kwargs['text_color'] = fg_color
        menu = ctk.CTkOptionMenu(parent, **kwargs)
        self.left_panel_font_widgets.append(menu)
        return menu

    def _create_appearance_dropdown_menu(self) -> None:
        """Tworzy menu rozwijane wyglądu."""
        appearance_menu = tk.Menu(self.appearance_menubutton, tearoff=0)
        self.appearance_menubutton.config(menu=appearance_menu)

        # Opcje rozmiaru
        appearance_menu.add_command(label="Rozmiar czcionki panelu...", command=functools.partial(
            self._open_size_dialog, "Rozmiar czcionki panelu", 8, 20, self.font_size_left_panel_var))
        appearance_menu.add_command(label="Rozmiar czcionki nagłówków...", command=functools.partial(
            self._open_size_dialog, "Rozmiar czcionki nagłówków", 8, 20, self.font_size_table_header_var))
        appearance_menu.add_command(label="Rozmiar miniatur...", command=functools.partial(
            self._open_size_dialog, "Rozmiar miniatur", 20, 150, self.thumb_size_var))

        appearance_menu.add_separator()

        def choose_font_family():
            from tkinter import simpledialog
            fonts = ["Arial", "Calibri", "Comic Sans MS", "Consolas", "Courier New", "Georgia", "Helvetica", "Impact", "Lato", "Montserrat", "Open Sans", "Roboto", "Segoe UI", "Tahoma", "Times New Roman", "Trebuchet MS", "Verdana"]
            if IS_MACOS:
                fonts = [f for f in fonts if f not in ("Segoe UI", "Impact")] + ["SF Pro", "Helvetica Neue", "Menlo", "Monaco"]
            
            original_font = self.font_family_var.get()
            original_bold = self.font_bold_var.get()
            
            dialog = tk.Toplevel(self.root)
            dialog.title("Wybór czcionki")
            dialog.geometry("300x450")
            dialog.transient(self.root)
            dialog.grab_set()

            top_frame = ctk.CTkFrame(dialog, fg_color="transparent")
            top_frame.pack(fill=tk.X, padx=10, pady=(10, 0))
            
            bold_cb = ctk.CTkCheckBox(top_frame, text="Pogrubienie", variable=self.font_bold_var, command=self.apply_theme)
            bold_cb.pack(side=tk.LEFT, pady=5)

            listbox = tk.Listbox(dialog, font=(self.font_family_var.get(), 12))
            listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            for f in fonts:
                listbox.insert(tk.END, f)
                
            def on_select(*args):
                selection = listbox.curselection()
                if selection:
                    selected_font = fonts[selection[0]]
                    self.font_family_var.set(selected_font)
                    listbox.configure(font=(selected_font, 12, "bold" if self.font_bold_var.get() else "normal"))
                    self.apply_theme()
                    
            listbox.bind("<<ListboxSelect>>", on_select)
            listbox.bind("<KeyRelease-Up>", on_select)
            listbox.bind("<KeyRelease-Down>", on_select)
            
            def apply_selection():
                selection = listbox.curselection()
                if selection:
                    selected_font = fonts[selection[0]]
                    self.font_family_var.set(selected_font)
                    self.apply_theme()
                    self.schedule_config_save()
                dialog.destroy()
                
            def cancel_selection():
                self.font_family_var.set(original_font)
                self.font_bold_var.set(original_bold)
                self.apply_theme()
                dialog.destroy()
                
            dialog.protocol("WM_DELETE_WINDOW", cancel_selection)
                
            btn_frame = ctk.CTkFrame(dialog, fg_color="transparent")
            btn_frame.pack(pady=10, fill=tk.X)
            
            btn_apply = ctk.CTkButton(btn_frame, text="Zastosuj", command=apply_selection, fg_color="#28a745", hover_color="#218838")
            btn_apply.pack(side=tk.LEFT, expand=True, padx=10)
            
            btn_cancel = ctk.CTkButton(btn_frame, text="Anuluj", command=cancel_selection, fg_color="#dc3545", hover_color="#c82333")
            btn_cancel.pack(side=tk.RIGHT, expand=True, padx=10)
            
            # Wypośrodkowanie okna
            dialog.update_idletasks()
            x = self.root.winfo_x() + (self.root.winfo_width() // 2) - (dialog.winfo_width() // 2)
            y = self.root.winfo_y() + (self.root.winfo_height() // 2) - (dialog.winfo_height() // 2)
            dialog.geometry(f"+{x}+{y}")

        appearance_menu.add_command(label="Czcionka aplikacji...", command=choose_font_family)
        
        # Opcje trybu
        appearance_menu.add_command(label="Dark/Light", command=self.toggle_dark_mode)
        appearance_menu.add_command(label="Kolory przycisków...", command=self._open_button_color_dialog)
        appearance_menu.add_command(label="Kolor czcionki...", command=self.choose_font_color)
        appearance_menu.add_command(label="Kolor tła...", command=self.choose_bg_color)

        # Separator
        appearance_menu.add_separator()

        # Checkbox logowania diagnostycznego
        appearance_menu.add_checkbutton(
            label="Logowanie diagnostyczne",
            variable=self.debug_logging_var,
            command=self.on_debug_logging_changed
        )
        
        # Checkbox jakości podglądu HQ
        appearance_menu.add_checkbutton(
            label="Wysoka jakość pełnego ekranu (Wolniejsze ladowanie do programu)",
            variable=self.fullscreen_hq_var,
            command=self.on_fullscreen_hq_changed
        )

    def on_fullscreen_hq_changed(self) -> None:
        """Obsługa zmiany parametru Fullscreen HQ."""
        self.schedule_config_save()

    def _update_header_theme(self) -> None:
        """Aktualizuje kolory przycisku menu zgodnie z motywem."""
        if not self.appearance_menubutton:
            return

        if self.dark_mode:
            fg_color = "#ffffff"
            btn_bg = "#3e3e3e"
            btn_active = "#555555"
        else:
            fg_color = self.light_font_color
            btn_bg = "#e0e0e0"
            btn_active = "#d0d0d0"

        # Aktualizuj przycisk menu
        try:
            self.appearance_menubutton.config(
                bg=btn_bg,
                fg=fg_color,
                activebackground=btn_active,
                activeforeground=fg_color
            )
        except Exception as e:
            logger.debug(f"Nie udało się zaktualizować motywu nagłówka: {e}")



    def _open_size_dialog(self, title, min_val, max_val, current_var) -> None:
        """Otwiera okno dialogowe do ustawiania rozmiaru z suwakiem."""
        dialog = tk.Toplevel(self.root)
        dialog.title(title)
        dialog.geometry("300x120")
        dialog.transient(self.root)
        dialog.grab_set()

        # Pobierz wartość początkową
        current_value = current_var.get()

        # Label z wartością
        value_label = tk.Label(dialog, text=f"Wartość: {current_value}", font=(self.font_family_var.get(), 12))
        value_label.pack(pady=20)

        # Suwak
        def on_slider_change(val):
            value = int(float(val))
            value_label.config(text=f"Wartość: {value}")
            current_var.set(value)
            self.apply_theme()

        slider = tk.Scale(dialog, from_=min_val, to=max_val, orient=tk.HORIZONTAL,
                         command=on_slider_change, showvalue=0, length=250)
        slider.set(current_value)
        slider.pack(pady=10)

        # Zamknij okno po zamknięciu (kliknięcie X)
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)

        # Centruj okno
        dialog.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - (dialog.winfo_width() // 2)
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - (dialog.winfo_height() // 2)
        dialog.geometry(f"+{x}+{y}")

    def apply_button_colors(self) -> None:
        """Stosuje zapisane przez użytkownika kolory do poszczególnych przycisków."""
        # usunięto hasattr
        
        buttons_map = {
            "load_btn": getattr(self, "load_btn", None),
            "start_btn": getattr(self, "start_btn", None),
            "btn_delete_input": getattr(self, "btn_delete_input", None),
            "btn_delete_output": getattr(self, "btn_delete_output", None),
            "btn_crop_mode": getattr(self, "btn_crop_mode", None),
            "btn_reset_crop": getattr(self, "btn_reset_crop", None),
            "btn_browse_in": getattr(self, "btn_browse_in", None),
            "btn_browse_out": getattr(self, "btn_browse_out", None),
            "appearance_menubutton": getattr(self, "appearance_menubutton", None)
        }
        
        for btn_name, widget in buttons_map.items():
            if widget:
                # Kolor Tła
                if btn_name in self.button_colors:
                    color = self.button_colors[btn_name]
                    try:
                        if btn_name == "appearance_menubutton":
                            widget.config(bg=color, activebackground=color)
                        else:
                            widget.configure(fg_color=color, hover_color=color)
                    except Exception as e:
                        logger.debug(f"Błąd zmiany koloru przycisku {btn_name}: {e}")
                
                # Kolor Czcionki
                if btn_name in self.button_text_colors:
                    text_color = self.button_text_colors[btn_name]
                    try:
                        if btn_name == "appearance_menubutton":
                            widget.config(fg=text_color)
                        else:
                            widget.configure(text_color=text_color)
                    except Exception as e:
                        logger.debug(f"Błąd zmiany koloru tekstu przycisku {btn_name}: {e}")

    def _open_button_color_dialog(self) -> None:
        """Otwiera okno dialogowe do wyboru koloru poszczególnych przycisków."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Kolory pojedynczych przycisków")
        dialog.geometry("480x280")
        dialog.transient(self.root)
        dialog.grab_set()

        buttons = {
            "Załaduj zdjęcia": "load_btn",
            "Start": "start_btn",
            "Usuń wejście": "btn_delete_input",
            "Usuń wyjście": "btn_delete_output",
            "Kadrowanie": "btn_crop_mode",
            "Cofnij kadrowanie": "btn_reset_crop",
            "Wybierz wejście": "btn_browse_in",
            "Wybierz wyjście": "btn_browse_out",
            "Wygląd": "appearance_menubutton"
        }
        
        default_colors = {
            "load_btn": "#007bff",
            "start_btn": "#28a745",
            "btn_delete_input": "#dc3545",
            "btn_delete_output": "#dc3545",
            "btn_crop_mode": "#6c757d",
            "btn_reset_crop": "#dc3545",
            "btn_browse_in": "#3B8ED0",
            "btn_browse_out": "#3B8ED0",
            "appearance_menubutton": "#3e3e3e" if self.dark_mode else "#e0e0e0"
        }

        default_hovers = {
            "load_btn": "#0056b3",
            "start_btn": "#218838",
            "btn_delete_input": "#c82333",
            "btn_delete_output": "#c82333",
            "btn_crop_mode": "#5a6268",
            "btn_reset_crop": "#c82333",
            "btn_browse_in": "#36719F",
            "btn_browse_out": "#36719F",
            "appearance_menubutton": "#555555" if self.dark_mode else "#d0d0d0"
        }

        default_text_colors = {
            "load_btn": "white",
            "start_btn": "white",
            "btn_delete_input": "white",
            "btn_delete_output": "white",
            "btn_crop_mode": "white",
            "btn_reset_crop": "white",
            "btn_browse_in": "white",
            "btn_browse_out": "white",
            "appearance_menubutton": self.dark_font_color if self.dark_mode else self.light_font_color
        }

        selected_label = tk.StringVar(value=list(buttons.keys())[0])

        top_frame = ctk.CTkFrame(dialog, fg_color="transparent")
        top_frame.pack(fill=tk.X, padx=20, pady=20)

        ctk.CTkLabel(top_frame, text="Wybierz przycisk:").pack(side=tk.LEFT, padx=(0, 10))
        dropdown = ctk.CTkOptionMenu(top_frame, variable=selected_label, values=list(buttons.keys()))
        dropdown.pack(side=tk.LEFT, fill=tk.X, expand=True)

        type_label = tk.StringVar(value="Tło")
        type_dropdown = ctk.CTkOptionMenu(top_frame, variable=type_label, values=["Tło", "Tekst"])
        type_dropdown.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(10, 0))

        mid_frame = ctk.CTkFrame(dialog, fg_color="transparent")
        mid_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)

        preview_btn = ctk.CTkButton(mid_frame, text="Podgląd Koloru", state="disabled")
        preview_btn.pack(pady=10)

        def update_preview(*args):
            btn_key = buttons[selected_label.get()]
            curr_bg = self.button_colors.get(btn_key, default_colors[btn_key])
            curr_fg = self.button_text_colors.get(btn_key, "white")
            
            try:
                preview_btn.configure(fg_color=curr_bg, text_color=curr_fg)
            except Exception:
                pass

        selected_label.trace_add("write", update_preview)
        type_label.trace_add("write", update_preview)
        update_preview()

        def set_color():
            btn_key = buttons[selected_label.get()]
            is_text = type_label.get() == "Tekst"
            
            if is_text:
                curr_color = self.button_text_colors.get(btn_key, "white")
            else:
                curr_color = self.button_colors.get(btn_key, default_colors[btn_key])
                
            color = askcolor(color=curr_color, title=f"Wybierz kolor")[1]
            if color:
                if is_text:
                    self.button_text_colors[btn_key] = color
                else:
                    self.button_colors[btn_key] = color
                update_preview()
                self.apply_button_colors()
                self.schedule_config_save()

        def reset_color():
            btn_key = buttons[selected_label.get()]
            is_text = type_label.get() == "Tekst"
            
            if is_text:
                if btn_key in self.button_text_colors:
                    del self.button_text_colors[btn_key]
            else:
                if btn_key in self.button_colors:
                    del self.button_colors[btn_key]
                    
            update_preview()
            widget = getattr(self, btn_key, None)
            if widget:
                try:
                    if btn_key == "appearance_menubutton":
                        self._update_header_theme()
                        # Dla pewności uaktualnijmy też sam font wywołaniem globalnej polityki
                        self.update_left_panel_fonts()
                    else:
                        if is_text:
                            widget.configure(text_color=default_text_colors[btn_key])
                        else:
                            widget.configure(fg_color=default_colors[btn_key], hover_color=default_hovers[btn_key])
                except Exception as e:
                    logger.debug(f"Błąd przywracania domyślnego koloru: {e}")
                self.schedule_config_save()

        def start_pipette():
            if not IS_WINDOWS:
                return
            dialog.withdraw()
            try:
                import ctypes
                from PIL import ImageGrab
            except ImportError:
                messagebox.showerror("Błąd", "Brakuje wymaganych bibliotek.")
                dialog.deiconify()
                return

            class POINT(ctypes.Structure):
                _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]

            self.root.config(cursor="crosshair")
            
            # Musimy poczekać aż LPM zostanie puszczony po kliknięciu w "Pipeta"
            state_dict = {"released": False}

            def check_mouse_loop():
                try:
                    # Sprawdzenie Left Mouse Button
                    state_lmb = ctypes.windll.user32.GetAsyncKeyState(0x01)
                    is_pressed = (state_lmb & 0x8000) != 0

                    if not state_dict["released"]:
                        if not is_pressed:
                            state_dict["released"] = True
                        self.root.after(20, check_mouse_loop)
                        return

                    # Sprawdzenie ESC (anulowanie)
                    state_esc = ctypes.windll.user32.GetAsyncKeyState(0x1B)
                    if (state_esc & 0x8000) != 0:
                        self.root.config(cursor="")
                        dialog.deiconify()
                        return

                    if is_pressed:
                        pt = POINT()
                        ctypes.windll.user32.GetCursorPos(ctypes.byref(pt))
                        x, y = pt.x, pt.y
                        
                        try:
                            # Pobierany jest 1 px ze współrzędnych bez spowalniania całego systemu
                            img = ImageGrab.grab(bbox=(x, y, x+1, y+1))
                            rgb = img.getpixel((0, 0))
                            color_hex = f"#{rgb[0]:02x}{rgb[1]:02x}{rgb[2]:02x}"
                            
                            btn_key = buttons[selected_label.get()]
                            is_text = type_label.get() == "Tekst"
                            
                            if is_text:
                                self.button_text_colors[btn_key] = color_hex
                            else:
                                self.button_colors[btn_key] = color_hex
                                
                            update_preview()
                            self.apply_button_colors()
                            self.schedule_config_save()
                        except Exception as e:
                            logger.debug(f"Błąd pipety ImageGrab: {e}")
                        
                        self.root.config(cursor="")
                        dialog.deiconify()
                        return

                    self.root.after(20, check_mouse_loop)
                except Exception as e:
                    logger.debug(f"Pętle pipety błąd: {e}")
                    self.root.config(cursor="")
                    dialog.deiconify()

            self.root.after(50, check_mouse_loop)

        btn_frame = ctk.CTkFrame(dialog, fg_color="transparent")
        btn_frame.pack(fill=tk.X, padx=20, pady=10)
        
        pick_btn = ctk.CTkButton(btn_frame, text="Paleta", command=set_color)
        pick_btn.pack(side=tk.LEFT, padx=3, expand=True)
        pipette_btn = ctk.CTkButton(btn_frame, text="Pipeta", command=start_pipette, fg_color="#17a2b8", hover_color="#138496")
        pipette_btn.pack(side=tk.LEFT, padx=3, expand=True)
        if not IS_WINDOWS:
            pipette_btn.pack_forget()
        reset_btn = ctk.CTkButton(btn_frame, text="Domyślny", command=reset_color, fg_color="#dc3545", hover_color="#c82333")
        reset_btn.pack(side=tk.LEFT, padx=3, expand=True)

        dialog.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - (dialog.winfo_width() // 2)
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - (dialog.winfo_height() // 2)
        dialog.geometry(f"+{x}+{y}")

    def create_widgets(self) -> None:
        self.setup_main_layout()
        self.setup_left_panel()
        self.setup_center_panel()
        self.setup_preview_panel()
        self.setup_event_bindings()
        self.apply_button_colors()

    def setup_main_layout(self) -> None:
        # Używamy tk.PanedWindow zamiast ttk.PanedWindow, ponieważ tk.PanedWindow
        # obsługuje metodę sashpos() potrzebną do zapisu/przywracania szerokości paneli
        self.main_paned = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, sashwidth=4, sashrelief=tk.RAISED)
        self.main_paned.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)

        # --- LEWY PANEL (ustawienia) ---
        self.left_frame = ctk.CTkFrame(self.main_paned, width=self.left_panel_width, corner_radius=0)
        self.main_paned.add(self.left_frame, minsize=200, sticky="nsew")

        # --- ŚRODKOWY PANEL (lista plików) ---
        self.center_frame = ctk.CTkFrame(self.main_paned, corner_radius=0)
        self.main_paned.add(self.center_frame, minsize=300, sticky="nsew")

        # --- PRAWY PANEL (podgląd) ---
        self.preview_frame = ctk.CTkFrame(self.main_paned, width=self.preview_panel_width, corner_radius=0)
        self.main_paned.add(self.preview_frame, minsize=150, sticky="nsew")

        # Initial sash positioning - opóźnione, aby okno miało czas na pełne wyrenderowanie
        self.root.update_idletasks()
        try:
            total_width = self.main_paned.winfo_width()
            if self.enable_debug_logging:
                logger.info(f"setup_main_layout initial sash: total_width={total_width}, left_panel_width={self.left_panel_width}, preview_panel_width={self.preview_panel_width}")
            if total_width > 100:
                sash_0_pos = self.left_panel_width
                sash_1_pos = total_width - self.preview_panel_width
                if self.enable_debug_logging:
                    logger.info(f"setup_main_layout calling sash_place(0, {sash_0_pos}, 0) and sash_place(1, {sash_1_pos}, 0)")
                self.main_paned.sash_place(0, sash_0_pos, 0)
                self.main_paned.sash_place(1, sash_1_pos, 0)
        except Exception as e:
            logger.debug(f"Nie udało się ustawić początkowych pozycji sashów: {e}")

    def setup_left_panel(self) -> None:
        self.setup_input_section()
        self.setup_naming_section()
        self.setup_params_section()
        self.setup_processing_section()

    def setup_input_section(self) -> None:
        f_frame = ctk.CTkFrame(self.left_frame, fg_color="transparent")
        f_frame.pack(fill=tk.X, pady=(0, 10), padx=5)

        f_content = ctk.CTkFrame(f_frame)
        f_content.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        f_content.columnconfigure(1, weight=1)

        self._create_label(f_content, text="Wejście:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        entry_in = self._create_entry(f_content, textvariable=self.input_folder)
        entry_in.grid(row=0, column=1, sticky="ew", padx=5)
        self.add_context_menu(entry_in)
        self._create_button(f_content, text="...", var_name="btn_browse_in", width=50, command=self.choose_input_folder_dialog).grid(row=0, column=2, padx=5)

        self._create_label(f_content, text="Wyjście:").grid(row=1, column=0, sticky="w", padx=5, pady=2)
        entry_out = self._create_entry(f_content, textvariable=self.output_folder)
        entry_out.grid(row=1, column=1, sticky="ew", padx=5)
        self.add_context_menu(entry_out)
        self._create_button(f_content, text="...", var_name="btn_browse_out", width=50, command=self.choose_output).grid(row=1, column=2, padx=5)

        ttk.Separator(f_content, orient='horizontal').grid(row=2, column=0, columnspan=3, sticky="ew", pady=5)

        self._create_button(f_content, text="ZAŁADUJ ZDJĘCIA", var_name="load_btn", command=self.load_from_current_input, fg_color="#007bff", hover_color="#0056b3")
        self.load_btn.grid(row=3, column=0, columnspan=3, sticky="ew", padx=5, pady=(0,5))

    def setup_naming_section(self) -> None:
        n_frame = ctk.CTkFrame(self.left_frame, fg_color="transparent")
        n_frame.pack(fill=tk.X, pady=(0, 10), padx=5)

        n_content = ctk.CTkFrame(n_frame)
        n_content.pack(fill=tk.BOTH, expand=True, padx=5, pady=(5, 5))

        label_row = ctk.CTkFrame(n_content, fg_color="transparent")
        label_row.pack(fill=tk.X, padx=5, pady=2)

        self._create_label(label_row, text="NAZWA PIM:").pack(side=tk.LEFT)

        start_num_entry = self._create_entry(label_row, textvariable=self.start_number_var, width=60)
        start_num_entry.pack(side=tk.RIGHT)
        self._create_label(label_row, text="Numer od:").pack(side=tk.RIGHT, padx=(5, 2))

        self.name_entry = self._create_entry(n_content, textvariable=self.clean_name_var)
        self.name_entry.pack(fill=tk.X, padx=5, pady=(0, 5))
        self.add_context_menu(self.name_entry)

        def on_paste(_):
            self.root.after(10, self.process_pasted_text)

        self.name_entry.bind("<<Paste>>", on_paste)

        def on_key_release(_):
            current = self.clean_name_var.get()
            cleaned = slugify_pl(current)
            if cleaned != current and current:
                self.clean_name_var.set(cleaned)

        self.name_entry.bind("<KeyRelease>", on_key_release)

    def setup_params_section(self) -> None:
        p_frame = ctk.CTkFrame(self.left_frame, fg_color="transparent")
        p_frame.pack(fill=tk.X, pady=(0, 10), padx=5)

        p_content = ctk.CTkFrame(p_frame)
        p_content.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        grid_opts = {'padx': 5, 'pady': 2, 'sticky': 'w'}

        self._create_label(p_content, text="Margines (px):").grid(row=0, column=0, **grid_opts)
        self._create_entry(p_content, textvariable=self.margin_var, width=60).grid(row=0, column=1, **grid_opts)
        self._create_checkbox(p_content, variable=self.use_margin_var, text="").grid(row=0, column=2, **grid_opts)

        self._create_label(p_content, text="Max bok (px):").grid(row=1, column=0, **grid_opts)
        self._create_entry(p_content, textvariable=self.max_side_var, width=60).grid(row=1, column=1, **grid_opts)
        self._create_checkbox(p_content, variable=self.use_max_side_var, text="").grid(row=1, column=2, **grid_opts)

        self._create_label(p_content, text="Min rozmiar (px):").grid(row=2, column=0, **grid_opts)
        self._create_entry(p_content, textvariable=self.min_size_var, width=60).grid(row=2, column=1, **grid_opts)
        self._create_checkbox(p_content, variable=self.use_min_size_var, text="").grid(row=2, column=2, **grid_opts)

        self._create_label(p_content, text="Max mb:").grid(row=3, column=0, **grid_opts)
        self._create_entry(p_content, textvariable=self.max_mb_var, width=60).grid(row=3, column=1, **grid_opts)
        self._create_checkbox(p_content, variable=self.use_max_mb_var, text="").grid(row=3, column=2, **grid_opts)

        # --- NOWY ELEMENT: Wybór formatu zapisu ---
        self._create_label(p_content, text="Format:").grid(row=4, column=0, **grid_opts)
        format_dropdown = self._create_option_menu(
            p_content,
            variable=self.output_format_var,
            values=["JPG", "WEBP", "PNG", "AVIF", "TIFF"],
            width=70,
            fg_color="#444444" if self.dark_mode else "#e0e0e0",
            button_color="#555555" if self.dark_mode else "#cccccc",
            button_hover_color="#666666" if self.dark_mode else "#bbbbbb"
        )
        format_dropdown.grid(row=4, column=1, sticky="w", padx=5, pady=2)

        p_content.columnconfigure(3, weight=1)

    def setup_processing_section(self) -> None:
        proc_frame = ctk.CTkFrame(self.left_frame, fg_color="transparent")
        proc_frame.pack(fill=tk.X, pady=(0, 10), padx=5)

        proc_content = ctk.CTkFrame(proc_frame)
        proc_content.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self._create_button(proc_content, text="START", var_name="start_btn", command=self.start_processing, fg_color="#28a745", hover_color="#218838").pack(fill=tk.X, padx=5, pady=5)
        self.progress = ctk.CTkProgressBar(proc_content)
        self.progress.set(0)
        self.progress.pack(fill=tk.X, padx=5, pady=(5,0))
        self.status_lbl = self._create_label(proc_content, text="", anchor="center")
        self.status_lbl.pack(fill=tk.X, padx=5, pady=(0,0))

        action_frame = ctk.CTkFrame(proc_content, fg_color="transparent")
        action_frame.pack(fill=tk.X, padx=5, pady=(2, 0))
        action_frame.columnconfigure(0, weight=1)
        action_frame.columnconfigure(1, weight=1)

        self.btn_delete_input = self._create_button(
            action_frame,
            text="Usuń wejście",
            command=self.delete_processed_input_files,
            fg_color="#dc3545",
            hover_color="#c82333",
            state="disabled"
        )
        self.btn_delete_input.grid(row=0, column=0, sticky="ew", padx=(0, 2), pady=(2, 2))

        self.btn_delete_output = self._create_button(
            action_frame,
            text="Usuń wyjście",
            command=self.delete_processed_output_files,
            fg_color="#dc3545",
            hover_color="#c82333",
            state="disabled"
        )
        self.btn_delete_output.grid(row=0, column=1, sticky="ew", padx=(2, 0), pady=(2, 2))

        self.btn_crop_mode = self._create_button(
            action_frame,
            text="Kadrowanie (K)",
            command=self.toggle_crop_mode,
            fg_color="#6c757d",
            hover_color="#5a6268"
        )
        self.btn_crop_mode.grid(row=1, column=0, sticky="ew", padx=(0, 2), pady=(2, 2))

        self.btn_reset_crop = self._create_button(
            action_frame,
            text="Cofnij",
            command=self.reset_current_crop,
            fg_color="#dc3545",
            hover_color="#c82333",
            state="disabled"
        )
        self.btn_reset_crop.grid(row=1, column=1, sticky="ew", padx=(2, 0), pady=(2, 2))

        self.btn_eraser_mode = self._create_button(
            action_frame,
            text="Gumka (G)",
            command=self.toggle_eraser_mode,
            fg_color="#6c757d",
            hover_color="#5a6268"
        )
        self.btn_eraser_mode.grid(row=2, column=0, sticky="ew", padx=(0, 2), pady=(2, 2))

        self.btn_eraser_undo = self._create_button(
            action_frame,
            text="Cofnij",
            command=self.undo_eraser,
            fg_color="#dc3545", hover_color="#c82333", state="disabled"
        )
        self.btn_eraser_undo.grid(row=2, column=1, sticky="ew", padx=(2, 0), pady=(2, 2))



        appearance_frame = ctk.CTkFrame(proc_content, fg_color="transparent")
        appearance_frame.pack(fill=tk.X, padx=5, pady=(15, 0))

        self.appearance_menubutton = tk.Menubutton(
            appearance_frame,
            text="Wygląd / Ustawienia ▼",
            font=(self.font_family_var.get(), 10),
            relief="flat",
            bd=0,
            padx=10,
            pady=8
        )
        self.appearance_menubutton.pack(fill=tk.X)
        self._create_appearance_dropdown_menu()
        self._update_header_theme()

    def setup_center_panel(self) -> None:
        tree_frame = ctk.CTkFrame(self.center_frame, fg_color="transparent")
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)

        tree_content = ctk.CTkFrame(tree_frame)
        tree_content.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)

        scroll = ttk.Scrollbar(tree_content)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.all_columns = (self.COL_NAME, self.COL_SIZE, self.COL_RESOLUTION, self.COL_NEWNAME)
        self.tree = ttk.Treeview(tree_content, columns=self.all_columns, yscrollcommand=scroll.set, selectmode="extended")
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.config(command=self.on_scrollbar_scroll)

        self.tree.drop_target_register(DND_FILES)
        self.tree.dnd_bind('<<Drop>>', self.on_drop_files)
        self.tree["displaycolumns"] = self.display_columns

        # Najpierw ustaw nagłówki
        self.tree.heading("#0", text="☐ Lifestyle", command=self.on_lifestyle_header_click)
        self.tree.heading(self.COL_NAME, text="Plik źródłowy")
        self.tree.heading(self.COL_SIZE, text="Rozmiar")
        self.tree.heading(self.COL_RESOLUTION, text="Rozdzielczość")
        self.tree.heading(self.COL_NEWNAME, text="Nowa nazwa (2xKlik = Edytuj)")

        # Funkcja pomocnicza do ustawiania szerokości kolumny
        def set_col_width(col, width, **kwargs):
            self.tree.column(col, width=width, **kwargs)

        # Ustaw zapisane szerokości lub domyślne
        saved_widths = self.config_manager.saved_col_widths

        # Kolumna #0 (Lifestyle)
        width_0 = saved_widths.get("#0", 138) if saved_widths else 138
        set_col_width("#0", width_0, minwidth=60, stretch=tk.NO)

        # Kolumna Name
        width_name = saved_widths.get(self.COL_NAME, 150) if saved_widths else 150
        set_col_width(self.COL_NAME, width_name)

        # Kolumna Size
        width_size = saved_widths.get(self.COL_SIZE, 60) if saved_widths else 60
        set_col_width(self.COL_SIZE, width_size, stretch=tk.NO, anchor="e")

        # Kolumna Resolution
        width_res = saved_widths.get(self.COL_RESOLUTION, 100) if saved_widths else 100
        set_col_width(self.COL_RESOLUTION, width_res, stretch=tk.NO, anchor="center")

        # Kolumna NewName
        width_newname = saved_widths.get(self.COL_NEWNAME, 318) if saved_widths else 318
        set_col_width(self.COL_NEWNAME, width_newname)

        # Utwórz DragDropHandler po utworzeniu tree
        self.drag_drop_handler = DragDropHandler(
            tree=self.tree,
            root=self.root,
            logger=logger,
            thumbnails=self.thumbnails,
            valid_ext=self.VALID_EXT,
            get_is_processing_callback=lambda: self.is_processing,
            process_files_callback=self.add_paths_thread,
            show_preview_callback=self.show_preview,
            toggle_lifestyle_callback=self.toggle_lifestyle,
            sort_column_callback=self.sort_by_column,
            swap_columns_callback=self.swap_columns,
            apply_names_callback=self.apply_names,
            set_manual_order_callback=self.set_manual_order_enabled,
            # Callbacki do odczytu zmiennych Tkinter w głównym wątku
            get_margin_callback=lambda: int(self.margin_var.get()) if self.margin_var else 0,
            get_threshold_callback=lambda: int(self.threshold_var.get()) if self.threshold_var else 10,
            get_use_margin_callback=lambda: self.use_margin_var.get() if self.use_margin_var else True
        )

        # Utwórz ThumbnailManager
        self.thumbnail_manager = ThumbnailManager(
            tree=self.tree,
            logger=logger,
            thumb_size_var=self.thumb_size_var,
            dark_mode_var=lambda: self.dark_mode,
            thumbnails=self.thumbnails,
            lifestyle_states=self.lifestyle_states
        )

        self.tree.bind("<ButtonPress-1>", self.on_left_click)
        self.tree.bind("<B1-Motion>", self.on_drag_motion)
        self.tree.bind("<ButtonRelease-1>", self.on_drag_release)
        self.tree.bind("<Double-1>", self.on_double_click)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        
        self.tree.bind("<Delete>", self.delete_selected_items)
        self.tree.bind("<Control-a>", self.select_all)
        self.tree.bind("<space>", self.toggle_selection_lifestyle)
        
        self.tree.bind("<Motion>", self.on_tree_hover)
        self.tree.bind("<Leave>", lambda e: self.hide_tooltip())
        
        self.tree_menu = tk.Menu(self.root, tearoff=0)
        self.tree_menu.add_command(label="Usuń zaznaczone", command=self.delete_selected_items)
        self.tree.bind("<Button-3>", self.show_tree_context_menu)

    def setup_preview_panel(self) -> None:
        self.preview_threshold_scale = None
        self.create_preview_threshold_scale_widget()

        preview_canvas_frame = ctk.CTkFrame(self.preview_frame, fg_color="transparent")
        preview_canvas_frame.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)

        self.preview_canvas = tk.Canvas(
            preview_canvas_frame,
            bg=self.light_preview_bg,
            highlightthickness=0
        )
        self.preview_canvas.pack(fill=tk.BOTH, expand=True)

        # Rotacja obsługiwana klawiszami strzałek (←/→)

        self.preview_canvas.bind("<ButtonPress-1>", self.on_canvas_crop_press, add="+")
        self.preview_canvas.bind("<B1-Motion>", self.on_canvas_crop_drag, add="+")
        self.preview_canvas.bind("<ButtonRelease-1>", self.on_canvas_crop_release, add="+")
        self.preview_canvas.bind("<Motion>", self.on_canvas_eraser_motion, add="+")
        self.preview_canvas.bind("<Double-Button-1>", self.toggle_preview_fullscreen, add="+")


        self.preview_canvas_image_id = self.preview_canvas.create_image(0, 0, anchor="nw")

        self.preview_manager = PreviewManager(
            root=self.root,
            preview_canvas=self.preview_canvas,
            logger=logger,
            get_threshold_callback=lambda: int(self.threshold_var.get())
        )

        self.current_preview_item = None
        self.preview_frame.bind("<Configure>", self.on_preview_panel_resize)

    def setup_event_bindings(self) -> None:
        # Używamy _last_sash_positions z ConfigManager
        self.main_paned.bind("<Button-1>", self.on_sash_motion)
        self.main_paned.bind("<B1-Motion>", self.on_sash_motion)
        self.main_paned.bind("<ButtonRelease-1>", self.on_sash_released)
        self.tree.bind("<ButtonRelease-1>", self.on_column_width_changed, add="+")
        self.root.bind("<f>", self.toggle_preview_fullscreen)
        self.root.bind("<F>", self.toggle_preview_fullscreen)
        self.root.bind("<k>", self.toggle_crop_mode_shortcut)
        self.root.bind("<K>", self.toggle_crop_mode_shortcut)
        self.root.bind("<g>", self.toggle_eraser_shortcut)
        self.root.bind("<G>", self.toggle_eraser_shortcut)
        self.root.bind("<c>", lambda e: self.undo_eraser_shortcut(e))
        self.root.bind("<C>", lambda e: self.undo_eraser_shortcut(e))
        self.root.bind("<plus>", self.increase_eraser)
        self.root.bind("<minus>", self.decrease_eraser)
        self.root.bind("<KP_Add>", self.increase_eraser)
        self.root.bind("<KP_Subtract>", self.decrease_eraser)
        self.root.bind("<F1>", self.show_help)
        self.root.bind("<question>", self.show_help)
        # Rotacja strzałkami (lewo/prawo)
        self.root.bind("<Right>", lambda e: self.rotate_current_image_right())
        self.root.bind("<Left>", lambda e: self.rotate_current_image_left())

    def show_help(self, event=None) -> None:
        lines = [
            u"Skróty klawiszowe",
            u"=" * 40,
            "",
            "F1 / ?        \u2013 Ta pomoc",
            "K             \u2013 Tryb kadrowania (Crop)",
            "G             \u2013 Gumka (Eraser)",
            "C             \u2013 Cofnij gumk\u0119 / kadrowanie",
            "F             \u2013 Pe\u0142ny ekran podgl\u0105du",
            "F11           \u2013 Pe\u0142ny ekran aplikacji",
            u"\u2190 / \u2192         \u2013 Obrót obrazu",
            "+ / \u2212         \u2013 Rozmiar gumki",
            "Spacja        \u2013 Zaznacz / odznacz",
            "Ctrl+A        \u2013 Zaznacz wszystko",
            "Delete        \u2013 Usu\u0144 zaznaczone",
            u"\u2191 / \u2193         \u2013 Nawigacja (pe\u0142ny ekran)",
        ]
        msg = "\n".join(lines)
        messagebox.showinfo(u"Skróty klawiszowe \u2013 FotoPIM", msg)

    def toggle_preview_fullscreen(self, event=None) -> None:
        """Przełącza panel podglądu w osobne okno pełnoekranowe (bez przerysowywania reszty układu)."""
        if event and getattr(event, 'char', '') in ('f', 'F'):
            focus_widget = self.root.focus_get()
            if focus_widget and hasattr(focus_widget, 'winfo_class'):
                w_class = focus_widget.winfo_class()
                if w_class in ('Entry', 'TEntry', 'Text'):
                    return

        if getattr(self, '_fs_toplevel', None) and self._fs_toplevel.winfo_exists():
            self._fs_toplevel.destroy()
            return

        if not self.current_preview_item:
            return

        if getattr(self, "eraser_rect_id", None):
            try:
                self.preview_canvas.delete(self.eraser_rect_id)
            except Exception: pass
            self.eraser_rect_id = None

        # Utworzenie okna nakładki
        self._fs_toplevel = ctk.CTkToplevel(self.root)
        self._fs_toplevel.attributes('-fullscreen', True)
        self._fs_toplevel.attributes('-topmost', True)
        
        # Kolory
        bg_col = self.light_preview_bg
        self._fs_toplevel.configure(fg_color=bg_col)
        
        # Bindy zamknięcia
        self._fs_toplevel.bind("<f>", self.toggle_preview_fullscreen)
        self._fs_toplevel.bind("<F>", self.toggle_preview_fullscreen)
        self._fs_toplevel.bind("<k>", self.toggle_crop_mode_shortcut)
        self._fs_toplevel.bind("<K>", self.toggle_crop_mode_shortcut)
        self._fs_toplevel.bind("<g>", self.toggle_eraser_shortcut)
        self._fs_toplevel.bind("<G>", self.toggle_eraser_shortcut)
        self._fs_toplevel.bind("<c>", lambda e: self.undo_eraser_shortcut(e))
        self._fs_toplevel.bind("<C>", lambda e: self.undo_eraser_shortcut(e))
        self._fs_toplevel.bind("<plus>", self.increase_eraser)
        self._fs_toplevel.bind("<minus>", self.decrease_eraser)
        self._fs_toplevel.bind("<Escape>", self.toggle_preview_fullscreen)
        self._fs_toplevel.bind("<F1>", self.show_help)
        # Rotacja strzałkami (lewo/prawo)
        self._fs_toplevel.bind("<Right>", lambda e: self.rotate_current_image_right())
        self._fs_toplevel.bind("<Left>", lambda e: self.rotate_current_image_left())
        self._fs_toplevel.focus_set()

        def fs_navigate(event, direction):
            if not self.current_preview_item: return
            children = self.tree.get_children('')
            if not children: return
            try:
                idx = children.index(self.current_preview_item)
            except ValueError:
                return
            new_idx = idx + direction
            if 0 <= new_idx < len(children):
                next_item = children[new_idx]
                self.tree.selection_set(next_item)
                self.tree.see(next_item) # Scroll w głównym oknie żeby nadążał
                self.show_preview(next_item)

        self._fs_toplevel.bind("<Up>", lambda e: fs_navigate(e, -1))
        self._fs_toplevel.bind("<Down>", lambda e: fs_navigate(e, 1))
        
        def fs_mouse_wheel(event):
            # event.delta > 0 to scroll up (poprzedni); Windows/Mac
            if hasattr(event, "delta") and event.delta != 0:
                direction = -1 if event.delta > 0 else 1
            # event.num to obśługa scrolla w Linuksie
            elif hasattr(event, "num"):
                direction = -1 if event.num == 4 else 1
            else:
                return
            fs_navigate(event, direction)

        self._fs_toplevel.bind("<MouseWheel>", fs_mouse_wheel)
        self._fs_toplevel.bind("<Button-4>", fs_mouse_wheel)
        self._fs_toplevel.bind("<Button-5>", fs_mouse_wheel)

        # Canvas dla podglądu (tworzony jako dolny)
        fs_canvas = tk.Canvas(self._fs_toplevel, bg=bg_col, highlightthickness=0)
        fs_canvas.pack(fill=tk.BOTH, expand=True)

        # Ustaw kursor na podstawie aktywnego trybu
        if self.crop_mode_active:
            fs_canvas.config(cursor="crosshair")
        elif self.eraser_mode_active:
            fs_canvas.config(cursor="diamond_cross")

        # Rotacja w fullscreen obsługiwana klawiszami strzałek (←/→)

        # Powiąż zdarzenia kadrowania używając wstrzykniętego wskaźnika
        fs_canvas.bind("<ButtonPress-1>", self.on_canvas_crop_press)
        fs_canvas.bind("<B1-Motion>", self.on_canvas_crop_drag)
        fs_canvas.bind("<ButtonRelease-1>", self.on_canvas_crop_release)
        fs_canvas.bind("<Motion>", self.on_canvas_eraser_motion)
        fs_canvas.bind("<Double-Button-1>", self.toggle_preview_fullscreen)

        # Panel kontrolny na samej górze
        ctrl_frame = ctk.CTkFrame(self._fs_toplevel, fg_color="transparent")
        ctrl_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=(10, 10), before=fs_canvas)

        
        text_color = "black" if bg_col == "#d0d0d0" else "white"
        if getattr(self, 'dark_mode', False): text_color = "white"
        # Bez etykiety "Próg bieli:" w fullscreen - tylko suwak

        current_thresh = self.item_thresholds.get(self.current_preview_item, int(self.threshold_var.get()))
        fs_thresh_var = tk.IntVar(value=current_thresh)
        fs_scale = ctk.CTkSlider(ctrl_frame, from_=0, to=255, variable=fs_thresh_var, number_of_steps=255, width=400)
        fs_scale.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=15)

        def on_fs_scale(val):
            val = int(val)
            with self.data_lock:
                self.item_thresholds[self.current_preview_item] = val
            self.perform_threshold_update(val)
        fs_scale.configure(command=on_fs_scale)
        self.make_scale_draggable(fs_scale)
        self._fs_scale = fs_scale
        
        def on_jump_fs_click(ev):
            w = fs_scale.winfo_width()
            if w > 0:
                new_v = max(0, min(255, int((ev.x / w) * 255)))
                fs_scale.set(new_v)
                on_fs_scale(new_v)
        fs_scale.bind("<Button-1>", on_jump_fs_click)

        # Trzeba wyczyścić linie kadrowania NA ORYGINALNYM CANVASIE zanim stracimy jego identyfikatory z self.crop_lines
        self.clear_crop_lines()

        # Przejęcie wskaźnika canvas w obrębie klasy
        self._original_preview_canvas = self.preview_canvas
        self.preview_canvas = fs_canvas
        self._original_preview_image_id = self.preview_canvas_image_id
        self.preview_canvas_image_id = self.preview_canvas.create_image(0, 0, anchor="nw")

        def on_destroy(e):
            if e.widget == self._fs_toplevel:
                # Wyczyść ewentualne przypięte ramki na pełnym ekranie zanim powrócimy
                self.clear_crop_lines()
                if getattr(self, "eraser_rect_id", None):
                    try:
                        self.preview_canvas.delete(self.eraser_rect_id)
                    except Exception: pass
                    self.eraser_rect_id = None

                # Przywrócenie pierwotnego canvasu
                self.preview_canvas = self._original_preview_canvas
                self.preview_canvas_image_id = self._original_preview_image_id
                self._fs_toplevel = None
                
                if self.current_preview_item:
                    new_val = self.item_thresholds.get(self.current_preview_item, int(self.threshold_var.get()))
                    if self.preview_threshold_scale:
                        self.preview_threshold_scale.set(new_val)
                    # Wymuszenie wyrenderowania obrazu w standardowym oknie
                    self.show_preview(self.current_preview_item)

        self._fs_toplevel.protocol("WM_DELETE_WINDOW", self.toggle_preview_fullscreen)
        self._fs_toplevel.bind("<Destroy>", on_destroy)

        # Zaktualizuj i załaduj duży podgląd
        self._fs_toplevel.update_idletasks()
        # Załaduj obraz na pełnoekranowy podgląd (z odpowiednim rozmiarem)
        self.root.after(50, lambda: self.show_preview(self.current_preview_item))

    def toggle_crop_mode_shortcut(self, event=None) -> None:
        """Skrót klawiszowy wywołujący włączenie/wyłączenie kadrowania."""
        if event and getattr(event, 'char', '') in ('k', 'K'):
            focus_widget = self.root.focus_get()
            if focus_widget and hasattr(focus_widget, 'winfo_class'):
                w_class = focus_widget.winfo_class()
                if w_class in ('Entry', 'TEntry', 'Text'):
                    return
        if self.current_preview_item:
            self.toggle_crop_mode()

    def schedule_config_save(self) -> None:
        self.config_manager.schedule_config_save(self.save_config)

    def on_sash_released(self, _) -> None:
        try:
            changed = False
            num_panes = len(self.main_paned.panes())
            for idx in range(num_panes - 1):
                current_pos = self.main_paned.sash_coord(idx)[0]
                if self.config_manager.get_last_sash_position(idx) != current_pos:
                    self.config_manager.set_last_sash_position(idx, current_pos)
                    changed = True
            if changed:
                self.schedule_config_save()
        except tk.TclError as e:
            logger.debug(f"Błąd Tcl: Sprawdzanie pozycji sashów okna przerywane - {e}")

    def on_sash_motion(self, _) -> None:
        try:
            num_panes = len(self.main_paned.panes())
            for idx in range(num_panes - 1):
                current_pos = self.main_paned.sash_coord(idx)[0]
                self.config_manager.set_last_sash_position(idx, current_pos)
        except tk.TclError:
            pass

    def on_column_width_changed(self, event=None) -> None:
        """Sprawdza czy szerokości kolumn się zmieniły i zapisuje jeśli tak."""
        # Uruchom po krótkim czasie, aby upewnić się, że Treeview zakończyło operację
        self.root.after(50, self._check_and_save_column_widths)

    def _check_and_save_column_widths(self) -> None:
        """Wewnętrzna metoda do sprawdzania i zapisu."""
        try:
            current_widths = self.config_manager.capture_column_widths(self.tree, self.all_columns)
            
            # Jeśli szerokości są inne niż ostatnio znane/zapisane
            if current_widths != self.config_manager.saved_col_widths:
                # Zaktualizuj pamięć podręczną
                self.config_manager.saved_col_widths = current_widths
                # Zaplanuj zapis na dysk
                self.schedule_config_save()
        except Exception as e:
            logger.debug(f"Błąd sprawdzania szerokości: {e}")

    def create_preview_threshold_scale_widget(self) -> None:
        if self.preview_threshold_scale:
            self.preview_threshold_scale.destroy()

        scale_frame = ctk.CTkFrame(self.preview_frame, fg_color="transparent")
        scale_frame.pack(fill=tk.X, padx=0, pady=(0, 5), side=tk.TOP)

        self.preview_threshold_scale = ctk.CTkSlider(
            scale_frame,
            from_=0, to=255,
            number_of_steps=255,
            button_color="#007bff",
            button_hover_color="#0056b3"
        )
        self.preview_threshold_scale.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.preview_threshold_scale.set(int(self.threshold_var.get()))
        self.preview_threshold_scale.configure(command=self.on_preview_threshold_change)
        self.make_scale_draggable(self.preview_threshold_scale)

        def jump_to_click(event):
            width = self.preview_threshold_scale.winfo_width()
            if width > 0:
                click_x = event.x
                new_val = int((click_x / width) * 255)
                new_val = max(0, min(255, new_val))
                self.preview_threshold_scale.set(new_val)
                self.on_preview_threshold_change(new_val)

        self.preview_threshold_scale.bind("<Button-1>", jump_to_click)

    def on_preview_threshold_change(self, value) -> None:
        self.perform_threshold_update(value)

    def perform_threshold_update(self, value) -> None:
        if self.current_preview_item:
            new_threshold = int(float(value))
            with self.data_lock:
                self.item_thresholds[self.current_preview_item] = new_threshold
            if self.preview_manager:
                self.preview_manager.clear_cache_for_item(self.current_preview_item)

            # OPTYMALIZACJA: load_preview_async już generuje miniaturkę przez update_thumbnail_from_mem
            # Nie potrzebujemy osobnego update_single_row_image - unikamy podwójnego I/O
            self.show_preview(self.current_preview_item)

    def on_preview_panel_resize(self, event=None):
        # Don't overwrite loaded config values during initialization
        current_winfo = self.preview_frame.winfo_width()
        if self.enable_debug_logging:
            logger.info(f"on_preview_panel_resize START: _is_initializing={self._is_initializing}, winfo_width={current_winfo}, self.preview_panel_width={self.preview_panel_width}")
        if self._is_initializing:
            if self.enable_debug_logging:
                logger.info(f"on_preview_panel_resize: SKIP because _is_initializing=True")
            return

        self.preview_panel_width = current_winfo
        if self.enable_debug_logging:
            logger.info(f"on_preview_panel_resize: UPDATED preview_panel_width to {self.preview_panel_width}")
            
        # Debouncing the resize event to prevent frontend lag
        if hasattr(self, '_resize_timer') and self._resize_timer:
            self.root.after_cancel(self._resize_timer)
            
        def trigger_preview():
            if self.current_preview_item:
                self.show_preview(self.current_preview_item)
                
        self._resize_timer = self.root.after(150, trigger_preview)

    # ===== Obsługa Zewnętrznego Drop =====

    def on_drop_files(self, event) -> None:
        """Deleguje do DragDropHandler."""
        if self.drag_drop_handler:
            self._reset_edit_modes(None)  # Reset trybów przy dodawaniu nowych plików
            self.drag_drop_handler.on_drop_files(event)

    def add_paths_thread(self, paths, margin=None, threshold=None, use_margin=None) -> None:
        # ROZPOCZĘCIJ POMIAR CZASU WCZYTYWANIA ZDJĘĆ
        load_start_time = time.time()
        total_images = len(paths)
        logger.info(f"ROZPOCZĘTO WCZYTYWANIE {total_images} ZDJĘĆ")

        # Odczyt zmiennych Tkinter - bezpieczne jeśli wywołane z głównego wątku
        # Parametry mają pierwszeństwo (gdy przekazane z bezpiecznego wątku)
        if margin is None:
            try: margin = int(self.margin_var.get())
            except ValueError: margin = 0
        if threshold is None:
            try: threshold = int(self.threshold_var.get())
            except ValueError: threshold = 10
        if use_margin is None:
            try: use_margin = self.use_margin_var.get()
            except AttributeError: use_margin = True

        canvas_w = self.preview_canvas.winfo_width()
        canvas_h = self.preview_canvas.winfo_height()
        if canvas_w < 50 or canvas_h < 50:
            self.preview_canvas.update_idletasks()
            canvas_w = self.preview_canvas.winfo_width()
            canvas_h = self.preview_canvas.winfo_height()
        if canvas_w > 50 and canvas_h > 50:
            target_preview_width = max(canvas_w, canvas_h)
        else:
            target_preview_width = max(self.preview_panel_width - 20, 300)

        # Czy używać wysokiej jakości miniaturek? (odczytane bezpiecznie przed wątkami)
        try: use_hq = self.fullscreen_hq_var.get()
        except AttributeError: use_hq = False
        if use_hq:
            # Obliczenie docelowej rozdzielczości z monitora (minus 10%)
            screen_w = self.root.winfo_screenwidth()
            screen_h = self.root.winfo_screenheight()
            target_preview_dim = int(max(screen_w, screen_h) * 0.9)
        else:
            target_preview_dim = target_preview_width

        # Ustalamy rozmiar roboczy dla optymalnej jakości
        LOAD_SIZE = target_preview_dim


        def process_image(path, target_preview_dim=target_preview_dim, LOAD_SIZE=LOAD_SIZE):
            try:
                fname = os.path.basename(path)

                if not HAS_PYVIPS:
                    # Fallback dla Pillow (tylko jeśli pyvips nieobecny w systemie)
                    with Image.open(path) as img_load:
                        img_raw = img_load.convert("RGB")
                    
                    # Trimowanie w fallbacku
                    actual_margin = margin if use_margin else 0
                    trimmed_raw = trim_whitespace(img_raw, margin=actual_margin, threshold=threshold)
                    
                    w, h = trimmed_raw.size
                    size_str = format_size(os.path.getsize(path))
                    res_str = f"{w}x{h}"
                    
                    # Jeden obraz o maksymalnej rozdzielczości podglądu
                    max_dim = max(target_preview_dim, 600)
                    preview_pil = trimmed_raw.copy()
                    preview_pil.thumbnail((max_dim, max_dim), Image.Resampling.LANCZOS)

                    thumb = preview_pil.copy()
                    thumb.thumbnail((ConfigConstants.THUMBNAIL_SIZE, ConfigConstants.THUMBNAIL_SIZE))
                    
                    self.root.after(0, self.add_item_to_tree, fname, size_str, res_str, path, thumb, preview_pil, preview_pil)
                    return


                # --- OPTYMALIZACJA PYVIPS ---

                # 1. Wczytujemy plik z odpowiednimi parametrami dla formatu
                ext = os.path.splitext(path)[1].lower()
                tiff_exts = ['.tif', '.tiff']
                try:
                    if ext in tiff_exts:
                        # W drag & drop robimy tylko miniatury, więc sequential jest bezpieczny
                        try:
                            # Przełączamy z powrotem na access='sequential', żeby duże pliki nie zatkały RAMu!
                            img_full = pyvips.Image.new_from_file(path, access='sequential', tile_height=256, unlimited=True)
                        except pyvips.Error:
                            try:
                                img_full = pyvips.Image.new_from_file(path, access='sequential', unlimited=True)
                            except pyvips.Error:
                                img_full = pyvips.Image.new_from_file(path, access='sequential')
                    else:
                        img_full = pyvips.Image.new_from_file(path, memory=True, access='sequential')
                except pyvips.Error:
                    raise
                
                # 2. Pobieramy wymiary oryginału
                orig_w, orig_h = img_full.width, img_full.height
                size_str = format_size(os.path.getsize(path))

                # 3. Tworzymy mniejszą wersję roboczą
                # Zapisujemy wynik do pamięci RAM. Ponieważ thumbnail_image to stream z wczytywanego
                # sekwencyjnie wielkiego pliku, copy_memory() wymusza przepchnięcie całego pliku raz 
                # i zapisanie go jako LEKKI (scaled) obraz w pamieci, bez przetrzymywania 3GB oryginału!
                img = img_full.thumbnail_image(LOAD_SIZE).copy_memory()

                # 4. Szybki trim na mniejszym obrazku
                actual_margin = margin if use_margin else 0
                trimmed_vips = trim_whitespace(img, margin=actual_margin, threshold=threshold)

                # Obliczamy nową rozdzielczość na podstawie proporcji przycięcia
                # Skalujemy wymiary trimmed_vips z powrotem do skali oryginału
                ratio_w = orig_w / img.width
                ratio_h = orig_h / img.height
                final_w = int(trimmed_vips.width * ratio_w)
                final_h = int(trimmed_vips.height * ratio_h)
                res_str = f"{final_w}x{final_h}"

                # 5. Jeden obraz o maksymalnej rozdzielczości podglądu
                # → używany zarówno do preloaded (panel podglądu) jak i source_images (miniatury)
                max_dim = max(target_preview_dim, 600)
                source_trimmed_vips = trimmed_vips.thumbnail_image(max_dim)
                source_trimmed_pil = vips_to_pil(source_trimmed_vips)

                if not source_trimmed_pil:
                    raise ValueError("Błąd konwersji do PIL")

                preview_img_pil = source_trimmed_pil

                thumb_img = source_trimmed_pil.copy()
                thumb_img.thumbnail((ConfigConstants.THUMBNAIL_SIZE, ConfigConstants.THUMBNAIL_SIZE))

                self.root.after(0, self.add_item_to_tree, fname, size_str, res_str, path, thumb_img, preview_img_pil, source_trimmed_pil)


            except Exception as e:
                # Fallback do Pillow gdy pyvips nie zadziała (np. limit pamięci TIFF)
                logger.warning(f"PyVips nie poradził sobie z {path}, próbuję Pillow: {e}")
                try:
                    fname = os.path.basename(path)

                    # Fallback dla Pillow
                    with Image.open(path) as img_load:
                        img_raw = img_load.convert("RGB")

                    # Trimowanie w fallbacku
                    actual_margin = margin if use_margin else 0
                    trimmed_raw = trim_whitespace(img_raw, margin=actual_margin, threshold=threshold)

                    w, h = trimmed_raw.size
                    size_str = format_size(os.path.getsize(path))
                    res_str = f"{w}x{h}"

                    max_dim = max(target_preview_dim, 600)
                    preview_pil = trimmed_raw.copy()
                    preview_pil.thumbnail((max_dim, max_dim), Image.Resampling.LANCZOS)

                    thumb = preview_pil.copy()
                    thumb.thumbnail((ConfigConstants.THUMBNAIL_SIZE, ConfigConstants.THUMBNAIL_SIZE))

                    self.root.after(0, self.add_item_to_tree, fname, size_str, res_str, path, thumb, preview_pil, preview_pil)
                    logger.info(f"Pomyślnie załadowano przez Pillow: {path}")
                except Exception as e2:
                    logger.error(f"Błąd przy wczytywaniu {path} (również Pillow nie zadziałał): {e2}")

        # Używamy list(), aby wymusić wykonanie iteratora map w wątkach
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as executor:
            list(executor.map(process_image, paths))

        # OBLICZ I WYŚWIETL CZAS WCZYTYWANIA ZDJĘĆ
        load_elapsed_time = time.time() - load_start_time
        minutes = int(load_elapsed_time // 60)
        seconds = int(load_elapsed_time % 60)
        time_str = f"{minutes}m {seconds}s"
        logger.info(f"WCZYTYWANIE UKOŃCZONE: {total_images} plików w czasie: {time_str}")
        self.root.after(0, lambda: self.status_lbl.configure(text=f"Wczytano {total_images} zdjęć (Czas: {time_str})"))

    # ===== Obsługa Checkboxa i Grafiki =====



    # ===== NOWA FUNKCJA: Obsługa kliknięcia nagłówka Lifestyle =====
    def on_lifestyle_header_click(self) -> None:
        # Przełącz stan globalny
        self.all_lifestyle_checked = not self.all_lifestyle_checked
        
        # Zmień wygląd nagłówka
        symbol = "☑" if self.all_lifestyle_checked else "☐"
        self.tree.heading("#0", text=f"{symbol} Lifestyle")
        
        # Pobierz wszystkie elementy
        children = self.tree.get_children()
        if not children:
            return

        # Zaktualizuj stan dla wszystkich elementów
        with self.data_lock:
            for item_id in children:
                self.lifestyle_states[item_id] = self.all_lifestyle_checked
        
        # Zastosuj nazwy i odśwież widok
        self.apply_names()
        self.refresh_thumbnails_display()

    # ===== INLINE EDITING =====

    def on_double_click(self, event) -> None:
        region = self.tree.identify_region(event.x, event.y)
        if region not in ("cell", "tree"): return

        column_id = self.tree.identify_column(event.x)
        item_id = self.tree.identify_row(event.y)
        if not item_id: return

        logical_column = self.tree.column(column_id, option='id')

        if logical_column == self.COL_NEWNAME:
            bbox = self.tree.bbox(item_id, column=column_id)
            if not bbox: return

            current_value = self.tree.set(item_id, logical_column)

            # Używamy standardowego tk.Entry zamiast ctk.CTkEntry dla lepszej kompatybilności z Treeview
            entry = tk.Entry(
                self.tree,
                bg="white" if not self.dark_mode else "#3e3e3e",
                fg="black" if not self.dark_mode else "white",
                insertbackground="black" if not self.dark_mode else "white",  # Kolor kursora
                relief="flat",
                highlightthickness=0
            )
            entry.place(x=bbox[0], y=bbox[1], width=bbox[2], height=bbox[3])
            entry.insert(0, current_value)
            entry.select_range(0, tk.END)
            entry.focus_set()
            entry.icursor(tk.END)

            def save_edit(event=None):
                if entry.winfo_exists():
                    new_text = entry.get()
                    self.tree.set(item_id, logical_column, new_text)
                    self._manually_edited_names.add(item_id)  # Zapisz że ta nazwa była edytowana ręcznie
                    entry.destroy()

            def cancel_edit(event=None):
                if entry.winfo_exists():
                    entry.destroy()

            def on_tree_scroll(event):
                if entry.winfo_exists():
                    save_edit()

            entry.bind("<Return>", save_edit)
            entry.bind("<FocusOut>", save_edit)
            entry.bind("<Escape>", cancel_edit)

            # Nasłuchuj scrollowania tła dla ukrycia lewitującego widgetu tekstowego
            self.tree.bind("<MouseWheel>", on_tree_scroll, add="+")
            self.tree.bind("<Button-4>", on_tree_scroll, add="+")
            self.tree.bind("<Button-5>", on_tree_scroll, add="+")
        else:
            # Dla każdej innej kolumny podwójne kliknięcie odpala pogląd pełnoekranowy
            self.show_preview(item_id)
            if not getattr(self, '_fs_toplevel', None) or not self._fs_toplevel.winfo_exists():
                self.toggle_preview_fullscreen()


    # ===== SORTOWANIE =====

    def parse_size_to_bytes(self, size_str) -> int:
        try:
            parts = size_str.split()
            if len(parts) != 2: return 0
            val = float(parts[0])
            unit = parts[1].upper()
            multipliers = {'B': 1, 'KB': 1024, 'MB': 1024**2, 'GB': 1024**3}
            return int(val * multipliers.get(unit, 1))
        except ValueError: return 0

    def parse_resolution_to_area(self, res_str) -> float:
        try:
            w, h = map(int, res_str.lower().split('x'))
            return float(w * h)
        except ValueError: return 0.0

    def set_manual_order_enabled(self) -> None:
        """Oznacz że ręczna kolejność została ustawiona przez Drag & Drop."""
        self.manual_order_enabled = True

    def sort_by_column(self, col_id) -> None:
        # Jeśli ręczna kolejność była ustawiona, resetujemy flagę przy sortowaniu
        if self.manual_order_enabled:
            self.manual_order_enabled = False

        col_name = self.tree.column(col_id, option='id')
        reverse = self.sort_reverse.get(col_name, False)

        items = self.tree.get_children('')

        def natural_sort_key(s):
            return [int(text) if text.isdigit() else text.lower() for text in re.split(r'(\d+)', str(s))]

        data = []
        for item_id in items:
            val = self.tree.set(item_id, col_name)
            sort_val = val
            if col_name == self.COL_SIZE:
                sort_val = self.parse_size_to_bytes(val)
            elif col_name == self.COL_RESOLUTION:
                sort_val = self.parse_resolution_to_area(val)
            elif col_name == self.COL_NEWNAME:
                if not str(val).strip():
                    val = self.tree.set(item_id, self.COL_NAME)
                sort_val = natural_sort_key(val)
            elif col_name == self.COL_NAME:
                sort_val = natural_sort_key(val)

            data.append((sort_val, item_id))

        data.sort(key=lambda x: x[0], reverse=reverse)

        for index, (_, item_id) in enumerate(data):
            self.tree.move(item_id, '', index)

        self.sort_reverse[col_name] = not reverse

    # ===== SKRÓTY KLAWISZOWE =====

    def select_all(self, event=None) -> str:
        children = self.tree.get_children()
        self.tree.selection_set(children)
        return "break"

    def toggle_selection_lifestyle(self, event=None) -> str:
        selected_items = self.tree.selection()
        if not selected_items:
            return "break"
        
        for item_id in selected_items:
            self.toggle_lifestyle(item_id)
        
        return "break"

    # ===== Obsługa Zdarzeń Myszki =====

    def show_drag_ghost(self, item_id, event) -> None:
        """Deleguje do DragDropHandler."""
        if self.drag_drop_handler:
            self.drag_drop_handler.show_drag_ghost(item_id, event)

    def on_left_click(self, event) -> Optional[str]:
        """Deleguje do DragDropHandler."""
        if self.drag_drop_handler:
            result = self.drag_drop_handler.on_left_click(event)
            if result == "break":
                return "break"

    def on_tree_select(self, event=None) -> None:
        selected = self.tree.selection()

        if selected:
            self.root.after(50, lambda: self.show_preview(selected[0]))
        else:
            self.clear_preview()

    def show_preview(self, item_id) -> None:
        if not item_id:
            self.clear_preview()
            return

        self.current_preview_item = item_id

        # Aktualizacja paska progu bieli przy zmianie zdjęcia
        new_val = self.item_thresholds.get(item_id, int(self.threshold_var.get()))
        if self.preview_threshold_scale:
            self.preview_threshold_scale.set(new_val)
        if getattr(self, '_fs_scale', None) and self._fs_scale.winfo_exists():
            self._fs_scale.set(new_val)

        with self.data_lock:
            current_thresh = self.item_thresholds.get(item_id, int(self.threshold_var.get()))
            path = self.thumbnails.get(f"{item_id}_path")
            rotation = self.item_rotations.get(item_id, 0)
            has_eraser = item_id in self.eraser_strokes and self.eraser_strokes[item_id]

        if not path or not os.path.exists(path):
            self.show_no_preview()
            return
        
        is_fs = getattr(self, '_fs_toplevel', None) is not None
        if is_fs:
            # W trybie pełnoekranowym używamy rozmiaru canvasu (żeby uwzględnić górny pasek narzędzi)
            target_w = self.preview_canvas.winfo_width()
            target_h = self.preview_canvas.winfo_height()
            if target_w < 100 or target_h < 100: # Fallback jeśli jeszcze się nie wyrenderowało
                target_w = self._fs_toplevel.winfo_screenwidth()
                target_h = self._fs_toplevel.winfo_screenheight() - 80
        else:
            target_w = self.preview_canvas.winfo_width() - 4
            target_h = self.preview_canvas.winfo_height() - 4
            if target_w < 50: target_w = 300
            if target_h < 50: target_h = 300

        # Pobierz cache z PreviewManager
        preview_cache = self.preview_manager.get_cache() if self.preview_manager else {}
        preloaded_pil = self.preview_manager.get_preloaded() if self.preview_manager else {}

        # Klucz bufora - podgląd w programie zawsze pokazuje pełne zdjęcie z nakładką crop
        # UWAGA: rotation i has_eraser już odczytane w data_lock (linia 3791-3792) - używamy ich dla spójności
        # has_eraser = item_id in getattr(self, "eraser_strokes", {}) and self.eraser_strokes[item_id]
        cache_key = f"{item_id}_{target_w}x{target_h}_rot{rotation}_eraser{has_eraser}"

        # 1. Sprawdź cache dokładny
        if cache_key in preview_cache:
            photo, img_width, img_height = preview_cache[cache_key]
            self.display_preview_image(photo, img_width, img_height)
            return

        # 2. Sprawdź preloaded i przeskaluj jeśli trzeba
        has_eraser = item_id in getattr(self, "eraser_strokes", {}) and self.eraser_strokes[item_id]

        if item_id in preloaded_pil:
            preloaded_img = preloaded_pil[item_id]
            pw, ph = preloaded_img.size
            avail_w_check = max(1, target_w - (0 if is_fs else 20))
            avail_h_check = max(1, target_h - (0 if is_fs else 20))
            preloaded_big_enough = pw >= avail_w_check or ph >= avail_h_check

            if preloaded_big_enough:
                try:
                    img = preloaded_img

                    rotation = self.item_rotations.get(item_id, 0)
                    if rotation > 0:
                        logger.debug(f"show_preview: Rotacja z preloaded, item_id={item_id}, rotation={rotation}, img_size_before={img.size}")
                        angle = rotation * 90
                        img = img.rotate(angle, expand=True, fillcolor=(255, 255, 255))

                    pass

                    avail_w = avail_w_check
                    avail_h = avail_h_check

                    pw2, ph2 = img.size
                    ratio = min(avail_w / pw2, avail_h / ph2)
                    
                    if abs(ratio - 1.0) > 0.01:
                        img = img.resize((int(pw2 * ratio), int(ph2 * ratio)), Image.Resampling.BILINEAR)
                    else:
                        if has_eraser or rotation > 0 or item_id in self.item_crops:
                            pass
                        else:
                            img = img.copy()

                    if has_eraser:
                        img = self.apply_eraser_to_pil(img, item_id, current_thresh)

                    photo = ImageTk.PhotoImage(img)
                    w, h = img.size
                    preview_cache[cache_key] = (photo, w, h)
                    
                    self.display_preview_image(photo, w, h)
                    return
                except Exception as e:
                    logger.exception(f"Błąd użycia preloaded preview: {e}")

        # 3. Ładowanie
        if self.preview_image_ref is None:
            self.show_loading_indicator()

        if self.preview_manager:
            self.preview_manager.set_loading(True)
            current_req_id = self.preview_manager.new_request_id()
            # Odczytaj zmienne Tkinter w wątku głównym PRZED wątkiem tła (thread-safety)
            threshold_val = int(self.threshold_var.get())
            margin_val = int(self.margin_var.get()) if self.use_margin_var.get() else 0
            # Użyj executora zamiast tworzyć nowy wątek
            self.preview_manager.submit_preview_task(
                self.load_preview_async,
                item_id, cache_key, target_w, target_h, current_req_id,
                threshold_val, margin_val
            )
        else:
            # Fallback do starej metody gdy brak preview_manager
            current_req_id = 0
            # Odczytaj zmienne Tkinter w wątku głównym PRZED wątkiem tła (thread-safety)
            threshold_val = int(self.threshold_var.get())
            margin_val = int(self.margin_var.get()) if self.use_margin_var.get() else 0
            threading.Thread(
                target=self.load_preview_async,
                args=(item_id, cache_key, target_w, target_h, current_req_id, threshold_val, margin_val),
                daemon=True
            ).start()

    def load_preview_async(self, item_id, cache_key, target_panel_w, target_panel_h, req_id, threshold_val, margin_val) -> None:
        preview_cache = self.preview_manager.get_cache() if self.preview_manager else {}
        try:
            path = self.thumbnails.get(f"{item_id}_path")
            if not path or not os.path.exists(path):
                if self.preview_manager:
                    self.preview_manager.set_loading(False)
                self.root.after(0, self.show_no_preview)
                return

            threshold = self.item_thresholds.get(item_id, threshold_val)
            margin = margin_val

            # OPTYMALIZACJA: Sprawdź czy obraz jest już w preloaded zamiast wczytywać z dysku
            trimmed_img = None
            if self.preview_manager and item_id in self.preview_manager.get_preloaded():
                trimmed_img = self.preview_manager.get_preloaded()[item_id]
                logger.debug(f"load_preview_async: Użyto preloaded dla {item_id}")

            if HAS_PYVIPS and trimmed_img is None:
                # Wczytujemy w pyvips z odpowiednimi parametrami
                ext = os.path.splitext(path)[1].lower()
                tiff_exts = ['.tif', '.tiff']
                try:
                    if ext in tiff_exts:
                        try:
                            # Wrócono do sekwencyjnego, by oszczędzać RAM. copy_memory() będzie zastosowane na małej miniaturze
                            vips_img = pyvips.Image.new_from_file(path, access='sequential', tile_height=256, unlimited=True)
                        except pyvips.Error:
                            try:
                                vips_img = pyvips.Image.new_from_file(path, access='sequential', unlimited=True)
                            except pyvips.Error:
                                vips_img = pyvips.Image.new_from_file(path, access='sequential')
                    else:
                        vips_img = pyvips.Image.new_from_file(path, memory=True, access='sequential')
                except pyvips.Error:
                    raise
                
                # Skalujemy na szybko do obszaru roboczego
                max_dim = max(target_panel_w, target_panel_h, 1500)
                # Wymuszamy copy_memory() na ZMNIEJSZONYM obrazie, by reszta operacji trim 
                # na zbuforowanej pamięci działała bezbłędnie i nie wyrzucała 'out of order' read.
                vips_img = vips_img.thumbnail_image(int(max_dim * 1.5)).copy_memory()
                
                vips_trimmed = trim_whitespace(vips_img, margin=margin, threshold=threshold)
                    
                trimmed_img = vips_to_pil(vips_trimmed)
                del vips_img
                del vips_trimmed
            elif trimmed_img is None:
                # Fallback PIL - tylko gdy nie mamy obrazu z preloaded
                with Image.open(path) as img_load:
                    img_raw = img_load.convert("RGB")

                trimmed_img = trim_whitespace(img_raw, margin=margin, threshold=threshold)


            # Kadrowanie (Crop) - w podglądzie nigdy nie tniemy fizycznie, by zachować widok cieniowania
            pass

            # Zastosuj rotację
            rotation = self.item_rotations.get(item_id, 0)
            if rotation > 0:
                angle = rotation * 90
                # expand=True - zmienia wymiary przy rotacji 90/270°
                # fillcolor=(255,255,255) - wypełnia białym zamiast czarnego
                trimmed_img = trimmed_img.rotate(angle, expand=True, fillcolor=(255, 255, 255))

            img_w, img_h = trimmed_img.size
            if img_w <= 0 or img_h <= 0:
                if self.preview_manager:
                    self.preview_manager.set_loading(False)
                return

            is_fs = getattr(self, '_fs_toplevel', None) is not None
            padding_total = 0 if is_fs else 20
            available_w = max(1, target_panel_w - padding_total)
            available_h = max(1, target_panel_h - padding_total)

            scale_w = available_w / img_w
            scale_h = available_h / img_h
            scale = min(scale_w, scale_h)

            target_w = int(img_w * scale)
            target_h = int(img_h * scale)

            # Najpierw zmniejszamy obraz - znacznie przyspiesza gumkę na dużych zdjęciach
            resized = trimmed_img.resize((target_w, target_h), Image.Resampling.BILINEAR)

            # Gumka nakładana na zmniejszonym obrazie (koordynaty są relatywne, więc działa poprawnie)
            has_eraser = hasattr(self, "apply_eraser_to_pil") and item_id in getattr(self, "eraser_strokes", {}) and self.eraser_strokes[item_id]
            if has_eraser:
                resized = self.apply_eraser_to_pil(resized, item_id, threshold)

            # Zapisujemy do preloaded cache (bez gumki i bez rotacji/crop)
            # aby kolejne przejścia (np. do fullscreen) były błyskawiczne
            if self.preview_manager:
                logger.debug(f"load_preview_async: Zapis do preloaded, item_id={item_id}, rotation={rotation}, img_size={trimmed_img.size}")
                self.preview_manager.get_preloaded()[item_id] = trimmed_img

            # Aktualizujemy miniaturkę w tabeli (z gumką) bez nadpisywania source_images
            def _update_tree_thumbnail(iid= item_id, src_img=resized):
                try:
                    thumb = src_img.copy()
                    thumb.thumbnail((150, 150))
                    with self.data_lock:
                        is_checked = self.lifestyle_states.get(iid, False)
                    photo = self.thumbnail_manager.create_composite_thumbnail(thumb, is_checked)
                    with self.data_lock:
                        self.thumbnails[iid] = photo
                    if self.tree.exists(iid):
                        self.tree.item(iid, image=photo)
                except Exception:
                    pass
            self.root.after(0, _update_tree_thumbnail)

            photo = ImageTk.PhotoImage(resized)
            actual_w, actual_h = resized.size
            preview_cache[cache_key] = (photo, actual_w, actual_h)

            current_req_id = self.preview_manager.get_current_request_id() if self.preview_manager else req_id
            if req_id == current_req_id:
                if self.current_preview_item == item_id:
                    self.root.after(0, lambda: self.display_preview_image(photo, actual_w, actual_h))

        except Exception as e:
            logger.exception(f"Błąd ładowania podglądu")
            current_req_id = self.preview_manager.get_current_request_id() if self.preview_manager else req_id
            if req_id == current_req_id:
                self.root.after(0, self.show_no_preview)
        finally:
            current_req_id = self.preview_manager.get_current_request_id() if self.preview_manager else req_id
            if req_id == current_req_id:
                if self.preview_manager:
                    self.preview_manager.set_loading(False)

    def display_preview_image(self, photo, img_width, img_height) -> None:
        if not photo: return

        self.preview_image_ref = photo

        canvas_width = self.preview_canvas.winfo_width()
        canvas_height = self.preview_canvas.winfo_height()

        center_x = canvas_width / 2
        center_y = canvas_height / 2

        img_x = int(center_x - img_width / 2)
        img_y = int(center_y - img_height / 2)

        # W trybie pełnoekranowym przesuń obraz, aby wyrównać z ctrl_frame (padx=10) i dodaj odstęp na dole (3px)
        is_fs = getattr(self, '_fs_toplevel', None) is not None
        if is_fs:
            img_x = img_x + 10  # Przesunięcie o 10px w prawo (padding ctrl_frame)
            img_y = img_y - 3   # Przesunięcie o 3px w górę (odstęp na dole)

        self.preview_canvas.coords(self.preview_canvas_image_id, img_x, img_y)
        self.preview_canvas.itemconfig(self.preview_canvas_image_id, image=photo)

        self.preview_img_x = img_x
        self.preview_img_y = img_y
        self.preview_img_w = img_width
        self.preview_img_h = img_height

        # Zintegrowane odświeżanie nakładki kadrowania (zawsze wywołujemy, by uniknąć wycieku wizualnego z poprzedniego zdjęcia)
        self.root.after(10, self.draw_crop_lines)

    def _create_placeholder_image(self, text: str) -> Image.Image:
        """Tworzy placeholder obrazek z wycentrowanym tekstem."""
        width = max(self.preview_panel_width - 40, 200)
        height = 100
        bg_color = '#444444' if self.dark_mode else '#e0e0e0'
        text_color = 'white' if self.dark_mode else 'black'

        img = Image.new('RGB', (width, height), color=bg_color)
        draw = ImageDraw.Draw(img)
        bbox = draw.textbbox((0, 0), text)
        text_w = bbox[2] - bbox[0]
        text_h = bbox[3] - bbox[1]
        draw.text(((width - text_w) // 2, (height - text_h) // 2), text, fill=text_color)
        return img

    def show_loading_indicator(self) -> None:
        try:
            loading_img = self._create_placeholder_image("Ładowanie...")
            photo = ImageTk.PhotoImage(loading_img)
            self.display_preview_image(photo, loading_img.width, loading_img.height)
        except Exception as e:
            logger.exception(f"Błąd wyświetlania wskaźnika ładowania")

    def show_no_preview(self) -> None:
        try:
            no_preview_img = self._create_placeholder_image("Brak podglądu")
            photo = ImageTk.PhotoImage(no_preview_img)
            self.display_preview_image(photo, no_preview_img.width, no_preview_img.height)
        except Exception as e:
            logger.exception(f"Błąd wyświetlania braku podglądu")
    
    def clear_preview(self) -> None:
        self.preview_canvas.itemconfig(self.preview_canvas_image_id, image='')
        self.preview_image_ref = None
        self.current_preview_item = None
        
        # Czyść wizualizacje kadrowania i gumki
        self.clear_crop_lines()
        if getattr(self, "eraser_rect_id", None):
            try: self.preview_canvas.delete(self.eraser_rect_id)
            except Exception: pass
            self.eraser_rect_id = None
        try: self.preview_canvas.delete("temp_eraser_stroke")
        except Exception: pass

        if self.preview_threshold_scale:
            self.preview_threshold_scale.set(int(self.threshold_var.get()))

    def _reset_edit_modes(self, keep_mode: Optional[str] = None) -> None:
        """Wyłącz wszystkie tryby edycji. Opcjonalnie zachowaj jeden tryb aktywny.

        Args:
            keep_mode: 'crop', 'eraser' lub None - który tryb zachować
        """
        if keep_mode != 'crop':
            self.crop_mode_active = False
            self.crop_dragging = None
            try:
                self.btn_crop_mode.configure(fg_color="#6c757d", hover_color="#5a6268")
            except Exception: pass

        if keep_mode != 'eraser':
            self.eraser_mode_active = False
            try:
                self.btn_eraser_mode.configure(fg_color="#6c757d", hover_color="#5a6268")
            except Exception: pass
            if self.eraser_rect_id:
                self.preview_canvas.delete(self.eraser_rect_id)
                self.eraser_rect_id = None

        # Reset kursora
        cursor = ""
        if keep_mode == 'crop':
            cursor = "crosshair"
        elif keep_mode == 'eraser':
            cursor = "diamond_cross"
        self.preview_canvas.config(cursor=cursor)

        # Czyścimy wizualizacje jeśli całkowicie wychodzimy z trybów edycji
        if keep_mode is None:
            self.clear_crop_lines()
            if getattr(self, "eraser_rect_id", None):
                try: self.preview_canvas.delete(self.eraser_rect_id)
                except Exception: pass
                self.eraser_rect_id = None

    def toggle_crop_mode(self) -> None:
        if self.crop_mode_active:
            # Wyłącz crop
            self._reset_edit_modes(keep_mode=None)
        else:
            # Włącz crop, wyłącz eraser
            self._reset_edit_modes(keep_mode='crop')
            self.crop_mode_active = True
            try:
                self.btn_crop_mode.configure(fg_color="#007bff", hover_color="#0056b3")
            except Exception: pass
            
        # Odśwież podgląd, by zastosować/usunąć fizyczne przycięcie w widoku
        if self.current_preview_item:
            self.show_preview(self.current_preview_item)

    def draw_crop_lines(self) -> None:
        self.clear_crop_lines()
        if not self.current_preview_item:
            return

        img_x = self.preview_img_x
        img_y = self.preview_img_y
        img_w = self.preview_img_w
        img_h = self.preview_img_h

        if img_w < 10 or img_h < 10:
            self._crop_timer_id = self.root.after(50, self.draw_crop_lines)
            return

        crop_data = self.item_crops.get(self.current_preview_item)
        if not crop_data:
            if not self.crop_mode_active:
                return
            crop = (0.0, 0.0, 1.0, 1.0)
        else:
            crop = crop_data

        left_x = int(img_x + crop[0] * img_w)
        top_y = int(img_y + crop[1] * img_h)
        right_x = int(img_x + crop[2] * img_w)
        bottom_y = int(img_y + crop[3] * img_h)

        overlay_color = "#808080"
        overlay_stipple = "gray50"
        line_color = "#ff0000"
        line_width = 2

        self.crop_lines['overlay_left'] = self.preview_canvas.create_rectangle(
            img_x, img_y, left_x, img_y + img_h,
            fill=overlay_color, stipple=overlay_stipple, outline=""
        )
        self.crop_lines['overlay_right'] = self.preview_canvas.create_rectangle(
            right_x, img_y, img_x + img_w, img_y + img_h,
            fill=overlay_color, stipple=overlay_stipple, outline=""
        )
        self.crop_lines['overlay_top'] = self.preview_canvas.create_rectangle(
            left_x, img_y, right_x, top_y,
            fill=overlay_color, stipple=overlay_stipple, outline=""
        )
        self.crop_lines['overlay_bottom'] = self.preview_canvas.create_rectangle(
            left_x, bottom_y, right_x, img_y + img_h,
            fill=overlay_color, stipple=overlay_stipple, outline=""
        )

        # Bezpieczne koordynaty, aby linie nie uległy obcięciu na brzegach (połowa grubości)
        cw = self.preview_canvas.winfo_width()
        ch = self.preview_canvas.winfo_height()
        
        def c_x(v): return max(1, min(int(v), cw - 2)) if cw > 2 else int(v)
        def c_y(v): return max(1, min(int(v), ch - 2)) if ch > 2 else int(v)

        l_x, r_x = c_x(left_x), c_x(right_x)
        t_y, b_y = c_y(top_y), c_y(bottom_y)
        i_x, i_xw = c_x(img_x), c_x(img_x + img_w)
        i_y, i_yh = c_y(img_y), c_y(img_y + img_h)

        self.crop_lines['left'] = self.preview_canvas.create_line(
            l_x, i_y, l_x, i_yh, 
            fill=line_color, width=line_width
        )
        self.crop_lines['top'] = self.preview_canvas.create_line(
            i_x, t_y, i_xw, t_y, 
            fill=line_color, width=line_width
        )
        self.crop_lines['right'] = self.preview_canvas.create_line(
            r_x, i_y, r_x, i_yh, 
            fill=line_color, width=line_width
        )
        self.crop_lines['bottom'] = self.preview_canvas.create_line(
            i_x, b_y, i_xw, b_y, 
            fill=line_color, width=line_width
        )

        self.crop_lines['handle_lt'] = self.preview_canvas.create_oval(
            l_x - 5, t_y - 5, l_x + 5, t_y + 5,
            fill=line_color, outline="white"
        )
        self.crop_lines['handle_rt'] = self.preview_canvas.create_oval(
            r_x - 5, t_y - 5, r_x + 5, t_y + 5,
            fill=line_color, outline="white"
        )
        self.crop_lines['handle_lb'] = self.preview_canvas.create_oval(
            l_x - 5, b_y - 5, l_x + 5, b_y + 5,
            fill=line_color, outline="white"
        )
        self.crop_lines['handle_rb'] = self.preview_canvas.create_oval(
            r_x - 5, b_y - 5, r_x + 5, b_y + 5,
            fill=line_color, outline="white"
        )

    def clear_crop_lines(self) -> None:
        if getattr(self, '_crop_timer_id', None):
            self.root.after_cancel(self._crop_timer_id)
            self._crop_timer_id = None
        for line_id in self.crop_lines.values():
            try:
                self.preview_canvas.delete(line_id)
            except Exception:
                pass
        self.crop_lines.clear()

    def toggle_eraser_shortcut(self, event=None):
        if event and getattr(event, 'char', '') in ('g', 'G'):
            focus_widget = self.root.focus_get()
            if focus_widget and hasattr(focus_widget, 'winfo_class'):
                w_class = focus_widget.winfo_class()
                if w_class in ('Entry', 'TEntry', 'Text'):
                    return
        if self.current_preview_item:
            self.toggle_eraser_mode()

    def undo_eraser_shortcut(self, event=None):
        if event and getattr(event, 'char', '') in ('c', 'C'):
            focus_widget = self.root.focus_get()
            if focus_widget and hasattr(focus_widget, 'winfo_class'):
                w_class = focus_widget.winfo_class()
                if w_class in ('Entry', 'TEntry', 'Text'):
                    return
        self.undo_eraser()
        self.reset_current_crop()

    def toggle_eraser_mode(self):
        if not self.current_preview_item: return
        if self.eraser_mode_active:
            # Wyłącz eraser
            self._reset_edit_modes(keep_mode=None)
        else:
            # Włącz eraser, wyłącz crop
            self._reset_edit_modes(keep_mode='eraser')
            self.eraser_mode_active = True
            try:
                self.btn_eraser_mode.configure(fg_color="#28a745", hover_color="#218838")
            except Exception: pass
            if getattr(self, '_fs_toplevel', None) and self._fs_toplevel.winfo_exists():
                self.preview_canvas.config(cursor="diamond_cross")
        
        # Odśwież podgląd, by zastosować/usunąć fizyczne przycięcie w widoku
        if self.current_preview_item:
            self.show_preview(self.current_preview_item)

        self._update_eraser_shape_buttons()

    def set_eraser_shape(self, shape: str):
        self.eraser_shape = shape
        self._update_eraser_shape_buttons()
        if self.eraser_mode_active and self.current_preview_item:
            self.rebuild_preview_for_eraser()

    # TODO: Zaimplementować aktualizację wizualną przycisków wyboru kształtu gumki (square/circle)
    def _update_eraser_shape_buttons(self):
        pass

    def undo_eraser(self):
        if not self.current_preview_item: return
        item_id = self.current_preview_item
        if item_id in self.eraser_strokes and self.eraser_strokes[item_id]:
            self.eraser_strokes[item_id].pop()
            if not self.eraser_strokes[item_id]:
                del self.eraser_strokes[item_id]
                self.btn_eraser_undo.configure(state="disabled")
            self.rebuild_preview_for_eraser()

    def increase_eraser(self, event=None):
        self.eraser_size += 5
        self.draw_eraser_rect(getattr(event, 'x', -100), getattr(event, 'y', -100))
        
    def decrease_eraser(self, event=None):
        self.eraser_size = max(5, self.eraser_size - 5)
        self.draw_eraser_rect(getattr(event, 'x', -100), getattr(event, 'y', -100))

    def rebuild_preview_for_eraser(self):
        if self.current_preview_item:
            try:
                self.preview_canvas.delete("temp_eraser_stroke")
            except Exception: pass
            if self.preview_manager:
                self.preview_manager.clear_cache_for_item(self.current_preview_item, clear_preloaded=True)
            self.show_preview(self.current_preview_item)
            self.update_single_row_image(self.current_preview_item)

    def draw_eraser_rect(self, x, y):
        if getattr(self, "eraser_mode_active", False):
            if self.eraser_rect_id:
                self.preview_canvas.delete(self.eraser_rect_id)
            r = self.eraser_size / 2.0
            if self.eraser_shape == "circle":
                self.eraser_rect_id = self.preview_canvas.create_oval(x-r, y-r, x+r, y+r, outline="red", width=2)
            else:
                self.eraser_rect_id = self.preview_canvas.create_rectangle(x-r, y-r, x+r, y+r, outline="red", width=2)
            
    def on_canvas_eraser_motion(self, event):
        if getattr(self, "eraser_mode_active", False):
            self.draw_eraser_rect(event.x, event.y)

    def rotate_current_image_right(self):
        """Obraca bieżące zdjęcie o 90° w prawo."""
        focus_widget = self.root.focus_get()
        if focus_widget and hasattr(focus_widget, 'winfo_class'):
            w_class = focus_widget.winfo_class()
            if w_class in ('Entry', 'TEntry', 'Text', 'TSpinbox'):
                return
        if not self.current_preview_item:
            return
        if self.current_preview_item in self.eraser_strokes and self.eraser_strokes.get(self.current_preview_item):
            messagebox.showinfo("Obracanie zablokowane", "Nie można obracać zdjęcia po użyciu gumki.")
            return
        with self.data_lock:
            current_rotation = self.item_rotations.get(self.current_preview_item, 0)
            new_rotation = (current_rotation + 1) % 4
            self.item_rotations[self.current_preview_item] = new_rotation
        self.show_preview(self.current_preview_item)

    def rotate_current_image_left(self):
        """Obraca bieżące zdjęcie o 90° w lewo."""
        focus_widget = self.root.focus_get()
        if focus_widget and hasattr(focus_widget, 'winfo_class'):
            w_class = focus_widget.winfo_class()
            if w_class in ('Entry', 'TEntry', 'Text', 'TSpinbox'):
                return
        if not self.current_preview_item:
            return
        if self.current_preview_item in self.eraser_strokes and self.eraser_strokes.get(self.current_preview_item):
            messagebox.showinfo("Obracanie zablokowane", "Nie można obracać zdjęcia po użyciu gumki.")
            return
        with self.data_lock:
            current_rotation = self.item_rotations.get(self.current_preview_item, 0)
            new_rotation = (current_rotation - 1) % 4
            self.item_rotations[self.current_preview_item] = new_rotation
        self.show_preview(self.current_preview_item)

    def add_eraser_point(self, x, y):
        if not self.current_preview_item: return
        img_x = self.preview_img_x
        img_y = self.preview_img_y
        img_w = self.preview_img_w
        img_h = self.preview_img_h
        
        if img_w < 10 or img_h < 10: return
        
        ax = int(x - img_x)
        ay = int(y - img_y)
        
        points_to_add = [(ax, ay)]
        
        if self.current_eraser_stroke:
            last_ax, last_ay, _, _, _, _ = self.current_eraser_stroke[-1]
            dx = ax - last_ax
            dy = ay - last_ay
            dist = max(abs(dx), abs(dy))
            if dist > 1:
                points_to_add = []
                for i in range(1, dist + 1):
                    px = last_ax + int(dx * i / dist)
                    py = last_ay + int(dy * i / dist)
                    points_to_add.append((px, py))
                    
        r = self.eraser_size / 2.0
        bg_col = self.light_preview_bg if not getattr(self, "dark_mode", False) else "#333333"
        eraser_shape = getattr(self, "eraser_shape", "square")
        
        for px, py in points_to_add:
            self.current_eraser_stroke.append((px, py, self.eraser_size, img_w, img_h, eraser_shape))
            cx = px + img_x
            cy = py + img_y
            if eraser_shape == "circle":
                self.preview_canvas.create_oval(cx-r, cy-r, cx+r, cy+r, fill=bg_col, outline="", tags="temp_eraser_stroke")
            else:
                self.preview_canvas.create_rectangle(cx-r, cy-r, cx+r, cy+r, fill=bg_col, outline="", tags="temp_eraser_stroke")

    def apply_eraser_to_pil(self, img_pil, item_id, threshold: int):
        if item_id in getattr(self, "eraser_strokes", {}) and self.eraser_strokes[item_id]:
            from PIL import ImageDraw
            w, h = img_pil.size
            fill_color = (255, 255, 255)
            if img_pil.mode == "RGBA":
                fill_color = (255, 255, 255, 255)

            trim_threshold = self.item_thresholds.get(item_id, threshold)

            for stroke in self.eraser_strokes[item_id]:
                draw = ImageDraw.Draw(img_pil)
                for px, py, esize, pw, ph, *rest in stroke:
                    eraser_shape = rest[0] if rest else "square"

                    cx = (px / pw) * w
                    cy = (py / ph) * h
                    r = ((esize / pw) * w) / 2.0

                    if eraser_shape == "circle":
                        draw.ellipse([cx-r, cy-r, cx+r, cy+r], fill=fill_color)
                    else:
                        draw.rectangle([cx-r, cy-r, cx+r, cy+r], fill=fill_color)

                img_pil = trim_whitespace_pil(img_pil, threshold=trim_threshold)
                w, h = img_pil.size
            return img_pil
        return img_pil

    def on_canvas_crop_press(self, event) -> None:
        if getattr(self, "eraser_mode_active", False):
            self.current_eraser_stroke = []
            self.add_eraser_point(event.x, event.y)
            return

        if not self.crop_mode_active or not self.current_preview_item:
            return

        threshold = 20
        img_x = self.preview_img_x
        img_y = self.preview_img_y
        img_w = self.preview_img_w
        img_h = self.preview_img_h

        if img_w < 10 or img_h < 10:
            return

        crop = self.item_crops.get(self.current_preview_item, (0.0, 0.0, 1.0, 1.0))
        left_x = img_x + crop[0] * img_w
        top_y = img_y + crop[1] * img_h
        right_x = img_x + crop[2] * img_w
        bottom_y = img_y + crop[3] * img_h

        corner_threshold = 15
        if abs(event.x - left_x) < corner_threshold and abs(event.y - top_y) < corner_threshold:
            self.crop_dragging = 'top-left'
            self.preview_canvas.config(cursor="sizing")
        elif abs(event.x - right_x) < corner_threshold and abs(event.y - top_y) < corner_threshold:
            self.crop_dragging = 'top-right'
            self.preview_canvas.config(cursor="sizing")
        elif abs(event.x - left_x) < corner_threshold and abs(event.y - bottom_y) < corner_threshold:
            self.crop_dragging = 'bottom-left'
            self.preview_canvas.config(cursor="sizing")
        elif abs(event.x - right_x) < corner_threshold and abs(event.y - bottom_y) < corner_threshold:
            self.crop_dragging = 'bottom-right'
            self.preview_canvas.config(cursor="sizing")
        elif abs(event.x - left_x) < threshold and top_y - threshold < event.y < bottom_y + threshold:
            self.crop_dragging = 'left'
            self.preview_canvas.config(cursor="sb_h_double_arrow")
        elif abs(event.x - right_x) < threshold and top_y - threshold < event.y < bottom_y + threshold:
            self.crop_dragging = 'right'
            self.preview_canvas.config(cursor="sb_h_double_arrow")
        elif abs(event.y - top_y) < threshold and left_x - threshold < event.x < right_x + threshold:
            self.crop_dragging = 'top'
            self.preview_canvas.config(cursor="sb_v_double_arrow")
        elif abs(event.y - bottom_y) < threshold and left_x - threshold < event.x < right_x + threshold:
            self.crop_dragging = 'bottom'
            self.preview_canvas.config(cursor="sb_v_double_arrow")

        if self.crop_dragging:
            self.crop_original_coords = {
                'left': crop[0], 'top': crop[1],
                'right': crop[2], 'bottom': crop[3]
            }

    def on_canvas_crop_drag(self, event) -> None:
        if getattr(self, "eraser_mode_active", False):
            self.add_eraser_point(event.x, event.y)
            self.draw_eraser_rect(event.x, event.y)
            return

        if not self.crop_dragging or not self.current_preview_item:
            return

        img_x = self.preview_img_x
        img_y = self.preview_img_y
        img_w = self.preview_img_w
        img_h = self.preview_img_h
        if img_w < 10 or img_h < 10:
            return

        crop = list(self.item_crops.get(self.current_preview_item, (0.0, 0.0, 1.0, 1.0)))

        rel_x = (event.x - img_x) / img_w
        rel_y = (event.y - img_y) / img_h

        if self.crop_dragging == 'left':
            crop[0] = max(0.0, min(rel_x, crop[2] - 0.01))
        elif self.crop_dragging == 'right':
            crop[2] = min(1.0, max(rel_x, crop[0] + 0.01))
        elif self.crop_dragging == 'top':
            crop[1] = max(0.0, min(rel_y, crop[3] - 0.01))
        elif self.crop_dragging == 'bottom':
            crop[3] = min(1.0, max(rel_y, crop[1] + 0.01))
        elif self.crop_dragging == 'top-left':
            crop[0] = max(0.0, min(rel_x, crop[2] - 0.01))
            crop[1] = max(0.0, min(rel_y, crop[3] - 0.01))
        elif self.crop_dragging == 'top-right':
            crop[2] = min(1.0, max(rel_x, crop[0] + 0.01))
            crop[1] = max(0.0, min(rel_y, crop[3] - 0.01))
        elif self.crop_dragging == 'bottom-left':
            crop[0] = max(0.0, min(rel_x, crop[2] - 0.01))
            crop[3] = min(1.0, max(rel_y, crop[1] + 0.01))
        elif self.crop_dragging == 'bottom-right':
            crop[2] = min(1.0, max(rel_x, crop[0] + 0.01))
            crop[3] = min(1.0, max(rel_y, crop[1] + 0.01))

        with self.data_lock:
            self.item_crops[self.current_preview_item] = tuple(crop)
        self.draw_crop_lines()
        self.btn_reset_crop.configure(state="normal")

    def on_canvas_crop_release(self, event) -> None:
        if getattr(self, "eraser_mode_active", False):
            if hasattr(self, "current_eraser_stroke") and getattr(self, "current_eraser_stroke", []) and self.current_preview_item:
                item_id = self.current_preview_item
                if item_id not in self.eraser_strokes: self.eraser_strokes[item_id] = []
                self.eraser_strokes[item_id].append(self.current_eraser_stroke)
                self.current_eraser_stroke = []
                try:
                    self.btn_eraser_undo.configure(state="normal")
                except Exception: pass
                # Clean up temporary visuals before rebuilding
                try:
                    self.preview_canvas.delete("temp_eraser_stroke")
                except Exception: pass
                
                self.rebuild_preview_for_eraser()
            return

        if self.crop_dragging:
            self.crop_dragging = None
            self.preview_canvas.config(cursor="crosshair" if self.crop_mode_active else "")
            # Odśwież miniaturę i rozdzielczość w tabeli po zakończeniu kadrowania
            if self.current_preview_item:
                self.update_single_row_image(self.current_preview_item)


    def reset_current_crop(self) -> None:
        if self.current_preview_item:
            if self.current_preview_item in self.item_crops:
                del self.item_crops[self.current_preview_item]
                # Odśwież tabelę i podgląd po zresetowaniu kadrowania
                self.update_single_row_image(self.current_preview_item)
            self.btn_reset_crop.configure(state="disabled")
            self.show_preview(self.current_preview_item)


    def on_scrollbar_scroll(self, *args) -> None:
        self.tree.yview(*args)

    def on_drag_motion(self, event) -> None:
        """Deleguje do DragDropHandler."""
        if self.drag_drop_handler:
            self.drag_drop_handler.on_drag_motion(event)

    def on_drag_release(self, event) -> None:
        """Deleguje do DragDropHandler."""
        if self.drag_drop_handler:
            self.drag_drop_handler.on_drag_release(event)

    def swap_columns(self, src_col_id, target_col_id) -> None:
        src_name = self.tree.column(src_col_id, option='id')
        target_name = self.tree.column(target_col_id, option='id')
        
        if src_name in self.display_columns and target_name in self.display_columns:
            old_idx = self.display_columns.index(src_name)
            new_idx = self.display_columns.index(target_name)
            
            self.display_columns.pop(old_idx)
            self.display_columns.insert(new_idx, src_name)
            
            self.tree["displaycolumns"] = self.display_columns

    # ===== Reszta logiki =====

    def toggle_lifestyle(self, item_id) -> None:
        with self.data_lock:
            current_state = self.lifestyle_states.get(item_id, False)
            new_state = not current_state
            self.lifestyle_states[item_id] = new_state
        self.update_single_row_image(item_id)
        self.apply_names()

    def update_single_row_image(self, item_id) -> None:
        try:
            margin_actual = int(self.margin_var.get()) if self.use_margin_var.get() else 0
        except ValueError:
            margin_actual = 0
            
        try:
            global_threshold = int(self.threshold_var.get())
        except ValueError:
            global_threshold = 10

        fallback_res_str = ""
        if self.tree.exists(item_id):
            fallback_res_str = self.tree.set(item_id, self.COL_RESOLUTION)

        def process_in_thread():
            try:
                with self.data_lock:
                    path = self.thumbnails.get(f"{item_id}_path")
                    threshold = self.item_thresholds.get(item_id, global_threshold)
                    crop = self.item_crops.get(item_id) if item_id in self.item_crops else None
                    source_img = self.source_images.get(item_id)
                
                trimmed = None
                res_str = ""
                success = False

                if path and os.path.exists(path):
                    margin = margin_actual

                    # OPTYMALIZACJA: Sprawdź czy obraz jest już w preloaded zamiast wczytywać z dysku
                    if self.preview_manager and item_id in self.preview_manager.get_preloaded():
                        preloaded_img = self.preview_manager.get_preloaded()[item_id]
                        if preloaded_img:
                            trimmed = preloaded_img.copy()
                            res_str = fallback_res_str
                            success = True
                            logger.debug(f"update_single_row_image: Użyto preloaded dla {item_id}")

                    # 1. Silnik PyVips - tylko gdy nie mamy obrazu z preloaded
                    if HAS_PYVIPS and not success:
                        try:
                            ext = os.path.splitext(path)[1].lower()
                            tiff_exts = ['.tif', '.tiff']
                            try:
                                if ext in tiff_exts:
                                    try:
                                        vips_full = pyvips.Image.new_from_file(path, access='sequential', tile_height=256, unlimited=True)
                                    except pyvips.Error:
                                        try:
                                            vips_full = pyvips.Image.new_from_file(path, access='sequential', unlimited=True)
                                        except pyvips.Error:
                                            vips_full = pyvips.Image.new_from_file(path, access='sequential')
                                else:
                                    vips_full = pyvips.Image.new_from_file(path, memory=True, access='sequential')
                            except pyvips.Error:
                                raise

                            orig_w, orig_h = vips_full.width, vips_full.height
                            vips_work = vips_full.thumbnail_image(800)
                            vips_trimmed = trim_whitespace(vips_work, margin=margin, threshold=threshold)
                            
                            # Skalowanie przycięcia do wymiarów oryginału
                            rw, rh = orig_w / vips_work.width, orig_h / vips_work.height
                            curr_w, curr_h = int(vips_trimmed.width * rw), int(vips_trimmed.height * rh)
                            
                            trimmed = vips_to_pil(vips_trimmed)
                            res_str = f"{curr_w}x{curr_h}"
                            success = True
                            del vips_full, vips_work, vips_trimmed
                        except Exception as e:
                            logger.warning(f"PyVips nie poradził sobie z miniaturą {item_id}: {e}, próbuję Pillow")
                            trimmed = None

                    # 2. Silnik Pillow (Fallback) - tylko gdy nie udało się uzyskać obrazu z preloaded
                    if not success and trimmed is None:
                        try:
                            with Image.open(path) as img_raw:
                                orig_w, orig_h = img_raw.size
                                img_work = img_raw.copy()
                                img_work.thumbnail((800, 800))
                                v_trimmed = trim_whitespace(img_work, margin=margin, threshold=threshold)
                                
                                rw, rh = orig_w / img_work.width, orig_h / img_work.height
                                curr_w, curr_h = int(v_trimmed.width * rw), int(v_trimmed.height * rh)
                                trimmed = v_trimmed
                                res_str = f"{curr_w}x{curr_h}"
                                success = True
                        except Exception as e:
                            logger.exception(f"Pillow również zawiódł przy miniaturze {item_id}")

                    # Wspólne operacje (GUMKA, CROP, THUMBNAIL)
                    if success and trimmed:
                        # Zastosuj gumkę jeśli istnieje (jak w podglądzie)
                        with self.data_lock:
                            has_eraser = item_id in self.eraser_strokes and self.eraser_strokes[item_id]
                        if has_eraser:
                            trimmed = self.apply_eraser_to_pil(trimmed, item_id, threshold)
                            # Aktualizuj rozdzielczość po gumce (trim zmienia wymiary)
                            w, h = trimmed.size
                            res_str = f"{w}x{h}"

                        if crop:
                            # Przelicz wymiary res_str dla cropa
                            w, h = map(int, res_str.split('x'))
                            curr_w = int(w * (crop[2] - crop[0]))
                            curr_h = int(h * (crop[3] - crop[1]))
                            res_str = f"{curr_w}x{curr_h}"
                            trimmed = apply_crop_to_image(trimmed, crop)
                        
                        trimmed.thumbnail((150, 150))
                else:
                    trimmed = source_img
                    res_str = fallback_res_str
                    # Zastosuj gumkę również dla obrazów z source_images
                    if trimmed:
                        with self.data_lock:
                            has_eraser = item_id in self.eraser_strokes and self.eraser_strokes[item_id]
                        if has_eraser:
                            trimmed = self.apply_eraser_to_pil(trimmed, item_id, threshold)
                            w, h = trimmed.size
                            res_str = f"{w}x{h}"

                if trimmed:
                    self.root.after(0, apply_update, trimmed, res_str)
            except Exception as e:
                logger.exception(f"Błąd krytyczny aktualizacji miniaturek w tle")

        def apply_update(pil_img, new_res_str):
            try:
                with self.data_lock:
                    is_checked = self.lifestyle_states.get(item_id, False)
                photo = self.thumbnail_manager.create_composite_thumbnail(pil_img, is_checked)
                with self.data_lock:
                    self.thumbnails[item_id] = photo
                if self.tree.exists(item_id):
                    self.tree.item(item_id, image=photo)
                    if new_res_str:
                        # Aktualizacja kolumny "Resolution" (indeks 2 w wartościach)
                        vals = list(self.tree.item(item_id, "values"))
                        if len(vals) >= 3:
                            vals[2] = new_res_str
                            self.tree.item(item_id, values=tuple(vals))
            except Exception as e:
                logger.exception(f"Błąd stosowania aktualizacji") 

        self.thumbnail_executor.submit(process_in_thread)


    def update_thumbnail_from_mem(self, item_id, pil_img) -> None:
        try:
            img_copy = pil_img.copy()
            img_copy.thumbnail((150, 150))
            with self.data_lock:
                is_checked = self.lifestyle_states.get(item_id, False)
            photo = self.thumbnail_manager.create_composite_thumbnail(img_copy, is_checked)
            with self.data_lock:
                self.thumbnails[item_id] = photo
            if self.tree.exists(item_id):
                self.tree.item(item_id, image=photo)
        except Exception as e:
            logger.exception(f"Błąd aktualizacji miniatury z pamięci")

    def refresh_thumbnails_display(self) -> None:
        items = self.tree.get_children()
        if items:
            threading.Thread(target=self.regenerate_thumbnails_thread, args=(items,), daemon=True).start()

    def regenerate_thumbnails_thread(self, items) -> None:
        for item_id in items:
            self.root.after(0, self.update_single_row_image, item_id)
            time.sleep(0.005)

    def show_tree_context_menu(self, event) -> None:
        item = self.tree.identify_row(event.y)
        if item:
            if item not in self.tree.selection():
                self.tree.selection_set(item)
        self.tree_menu.tk_popup(event.x_root, event.y_root)

    def delete_selected_items(self, event=None) -> None:
        selected_items = self.tree.selection()
        if not selected_items: return
        with self.data_lock:
            for item_id in selected_items:
                if item_id in self.thumbnails: del self.thumbnails[item_id]
                if item_id in self.source_images: del self.source_images[item_id]
                if item_id in self.lifestyle_states: del self.lifestyle_states[item_id]
                if item_id in self.item_crops: del self.item_crops[item_id]
                if item_id in self.item_rotations: del self.item_rotations[item_id]
                if item_id in self.eraser_strokes: del self.eraser_strokes[item_id]
                if item_id in self.item_thresholds: del self.item_thresholds[item_id]
                path_key = f"{item_id}_path"
                if path_key in self.thumbnails: del self.thumbnails[path_key]

                # Czyść cache przez PreviewManager dla każdego usuniętego pliku (Fix)
                if self.preview_manager:
                    preview_cache = self.preview_manager.get_cache()
                    preloaded = self.preview_manager.get_preloaded()
                    keys_to_delete = [k for k in list(preview_cache.keys()) if k.startswith(f"{item_id}_")]
                    for key in keys_to_delete:
                        del preview_cache[key]
                    if item_id in preloaded:
                        del preloaded[item_id]

        # Operacje na GUI poza domknięciem locka
        for item_id in selected_items:
            try:
                if self.tree.exists(item_id):
                    self.tree.delete(item_id)
                    # Usuń z śledzonych ręcznie edytowanych nazw
                    self._manually_edited_names.discard(item_id)
            except Exception as e:
                logger.exception(f"Błąd usuwania elementu z drzewa GUI")

        # Wyczyszczenie podglądu, jeśli usunięto bieżący (Fix get_children nie jest thread safe)
        if self.current_preview_item and not self.tree.exists(self.current_preview_item):
            self.clear_preview()

    def process_pasted_text(self) -> None:
        """Przetwarza wklejony tekst na slug."""
        current = self.clean_name_var.get()
        cleaned = slugify_pl(current)
        if cleaned != current:
            self.clean_name_var.set(cleaned)

    def apply_names(self) -> None:
        if not self.tree:
            return
        base_name = self.clean_name_var.get().strip('-')
        children = self.tree.get_children()

        start_val_str = self.start_number_var.get()
        # Obsługa prefiksów i wiodących zer (np. X1, 01)
        match = re.search(r'(.*?)(\d+)$', start_val_str)
        if match:
            prefix = match.group(1)
            num_part = match.group(2)
            padding = len(num_part)
            start_num = int(num_part)
        else:
            prefix = start_val_str
            start_num = 1
            padding = 1

        if not base_name:
            for item_id in children:
                # Nie nadpisuj ręcznie edytowanych nazw
                if item_id not in self._manually_edited_names:
                    self.tree.set(item_id, self.COL_NEWNAME, "")
            return

        for i, item_id in enumerate(children):
            # Pomiń ręcznie edytowane nazwy
            if item_id in self._manually_edited_names:
                continue

            is_lifestyle = self.lifestyle_states.get(item_id, False)
            suffix = "-lifestyle" if is_lifestyle else ""

            # Generowanie numeru z zachowaniem formatowania
            current_num = start_num + i
            formatted_num = f"{current_num:0{padding}d}"

            fmt_ext = self.output_format_var.get().lower()
            new_filename = f"{base_name}{suffix}-{prefix}{formatted_num}.{fmt_ext}"
            self.tree.set(item_id, self.COL_NEWNAME, new_filename)

    def choose_input_folder_dialog(self) -> None:
        folder = filedialog.askdirectory()
        if folder: self.input_folder.set(folder)

    def load_from_current_input(self) -> None:
        if self.is_processing:
            logger.warning("Przycisk Załaduj zdjęcia zablokowany - przetwarzanie w toku")
            return

        current_path = self.input_folder.get().strip()
        if current_path and os.path.isdir(current_path):
            self.refresh_list(folder=current_path)
        else:
            folder = filedialog.askdirectory(title="Wybierz folder ze zdjęciami")
            if folder:
                self.input_folder.set(folder)
                self.refresh_list(folder=folder)

    def refresh_list(self, folder=None) -> None:
        self.tree.delete(*self.tree.get_children())
        with self.data_lock:
            self.thumbnails.clear()
            self.source_images.clear()
            self.lifestyle_states.clear()
            self.item_thresholds.clear()
            self.item_crops.clear()
            self.item_rotations.clear()
            self.eraser_strokes.clear()
        # Czyścimy ręcznie edytowane nazwy przy odświeżeniu listy
        self._manually_edited_names.clear()
        # Czyść cache przez PreviewManager
        if self.preview_manager:
            self.preview_manager.get_cache().clear()
            self.preview_manager.get_preloaded().clear()
        self.all_lifestyle_checked = False
        self.tree.heading("#0", text="☐ Lifestyle")
        
        self._reset_edit_modes(None)  # Reset trybów przy odświeżeniu folderu
        self.clear_preview()
        
        try: margin = int(self.margin_var.get())
        except ValueError: margin = 0
        try: threshold = int(self.threshold_var.get())
        except ValueError: threshold = 10
        use_margin = self.use_margin_var.get()
        # Uruchom przetwarzanie w osobnym wątku - zmienne Tkinter już odczytane
        threading.Thread(target=self.load_images_thread, args=(folder, margin, threshold, use_margin), daemon=True).start()

    def load_images_thread(self, folder, margin, threshold, use_margin) -> None:
        if not folder or not os.path.exists(folder): return
        try: names = sorted([f for f in os.listdir(folder) if f.lower().endswith(self.VALID_EXT)])
        except OSError: return
        full_paths = [os.path.join(folder, n) for n in names]
        # Przekazujemy parametry zamiast odczytywać Tkinter w wątku
        self.add_paths_thread(full_paths, margin=margin, threshold=threshold, use_margin=use_margin)

    def add_item_to_tree(self, fname, size_str, res_str, path, thumb_img, preview_img, source_trimmed_img) -> None:
        photo_thumb = self.thumbnail_manager.create_composite_thumbnail(thumb_img, False)
        item_id = self.tree.insert("", "end", text="", image=photo_thumb, values=(fname, size_str, res_str, ""))

        with self.data_lock:
            self.thumbnails[item_id] = photo_thumb
            self.thumbnails[f"{item_id}_path"] = path
            self.source_images[item_id] = source_trimmed_img
            self.lifestyle_states[item_id] = False

        if self.preview_manager:
            self.preview_manager.get_preloaded()[item_id] = preview_img

    def choose_output(self) -> None:
        f = filedialog.askdirectory()
        if f: self.output_folder.set(f)

    def start_processing(self) -> None:
        if self.is_processing:
            self.stop_event.set()
            self.start_btn.configure(text="Zatrzymywanie...", state="disabled")
            return

        # Wyłącz wszystkie tryby edycji przed przetwarzaniem
        self._reset_edit_modes(keep_mode=None)

        out_dir = self.output_folder.get()
        if not out_dir:
            messagebox.showerror("Błąd", "Wybierz folder wyjściowy!")
            return
        items = self.tree.get_children()
        if not items:
            messagebox.showwarning("Pusto", "Brak plików do przetworzenia.")
            return

        # Wyczyść dane z poprzedniej sesji
        self.processed_source_files.clear()
        self.processed_output_files.clear()

        file_tasks = []
        for item_id in items:
            with self.data_lock:
                path = self.thumbnails.get(f"{item_id}_path")
                item_thresh = self.item_thresholds.get(item_id, int(self.threshold_var.get()))
                item_crop = self.item_crops.get(item_id)
                item_rotation = self.item_rotations.get(item_id, 0)
                eraser = self.eraser_strokes.get(item_id, None)

            new_name = self.tree.set(item_id, self.COL_NEWNAME)
            if not new_name: new_name = self.tree.set(item_id, self.COL_NAME)

            # Sprawdzenie wagi
            file_size = os.path.getsize(path) if path and os.path.exists(path) else 0
            is_large = file_size >= 10 * 1024 * 1024

            if path:
                file_tasks.append(FileTask(source_path=path, target_name=new_name, threshold=item_thresh, crop=item_crop, item_id=item_id, is_large=is_large, eraser_strokes=eraser, rotation=item_rotation))
            else:
                logger.warning(f"Pominięto element {item_id} - brak ścieżki pliku.")

        # Logowanie diagnostyczne
        logger.info(f"Przygotowano {len(file_tasks)} zadań z {len(items)} elementów. Brakujące ścieżki: {len(items) - len(file_tasks)}")

        # Sprawdź czy są pliki do przetworzenia
        if not file_tasks:
            messagebox.showwarning("Brak plików", "Nie znaleziono poprawnych ścieżek do plików.\n\nMożliwe że pliki nie zostały wczytane poprawnie lub ścieżki są uszkodzone.\n\nSpróbuj ponownie dodać pliki.")
            return

        # Wyświetl informację o liczbie plików
        logger.info(f"Rozpoczynam przetwarzanie {len(file_tasks)} plików...")

        try:
            params = {
                "file_list": file_tasks,
                "output_folder": out_dir,
                "margin": int(self.margin_var.get()),
                "threshold": int(self.threshold_var.get()),
                "max_side": int(self.max_side_var.get()),
                "min_size": int(self.min_size_var.get()),
                "max_mb": float(self.max_mb_var.get()),
                "output_format": self.output_format_var.get(),
                "use_margin": self.use_margin_var.get(),
                "use_max_side": self.use_max_side_var.get(),
                "use_min_size": self.use_min_size_var.get(),
                "use_max_mb": self.use_max_mb_var.get()
            }
        except ValueError:
            messagebox.showerror("Błąd", "Parametry liczbowe muszą być liczbami całkowitymi.")
            return
        self.toggle_ui_state(False)

        self.stop_event.clear()
        self.start_btn.configure(text="STOP", fg_color="#dc3545", hover_color="#c82333")
        self.status_lbl.configure(text="Przetwarzanie...")
        self.progress.set(0)  # Reset paska postępu na początku
        self.processing_thread = threading.Thread(target=self.run_processing, args=(params,))
        self.processing_thread.daemon = True
        self.processing_thread.start()
        self.check_queue()

    def toggle_ui_state(self, enabled) -> None:
        self.is_processing = not enabled
        state = "normal" if enabled else "disabled"
        logger.info(f"toggle_ui_state: enabled={enabled}, is_processing={self.is_processing}, state={state}")

        if enabled:
            self.start_btn.configure(text="START", fg_color="#28a745", hover_color="#218838", state="normal")
            # Wyłącz przycisk cofania kadrowania po zakończeniu przetwarzania
            if self.btn_reset_crop:
                self.btn_reset_crop.configure(state="disabled")
            # Anuluj ewentualne kadrowanie
            self._reset_edit_modes(None)

        if self.load_btn: self.load_btn.configure(state=state)
        # Nie wyłączamy btn start_btn, zawsze musi być wlączony żeby przerwac
        if self.btn_browse_in: self.btn_browse_in.configure(state=state)
        if self.btn_browse_out: self.btn_browse_out.configure(state=state)

        # Wyłącz przyciski usuwania podczas przetwarzania (gdy enabled jest False)
        # Przywracanie z powrotem jest obsługiwane w check_queue po zakończeniu
        if not enabled:
            if self.btn_delete_input:
                self.btn_delete_input.configure(state="disabled")
            if self.btn_delete_output:
                self.btn_delete_output.configure(state="disabled")

    def run_processing(self, params) -> None:
        cb = lambda p, m: self.processing_queue.put(('progress', p, m))
        file_cb = lambda i, p: self.processing_queue.put(('file_progress', i, p))
        params['file_progress_callback'] = file_cb
        params['stop_event'] = self.stop_event
        try: batch_trim_and_convert_files(**params, progress_callback=cb)
        except Exception as e: self.processing_queue.put(('error', str(e)))

    def check_queue(self) -> None:
        try:
            while not self.processing_queue.empty():
                msg = self.processing_queue.get_nowait()
                if msg[0] == 'progress':
                    if msg[1] is not None: self.progress.set(msg[1] / 100)  # customtkinter uses 0.0-1.0 range
                    if msg[2]:
                        self.status_lbl.configure(text=msg[2])
                        # Sprawdzamy czy komunikat zaczyna się od "Zakończono" lub "Zatrzymano" (może zawierać czas)
                        if msg[2].startswith("Zakończono") or msg[2].startswith("Zatrzymano"):
                            self.toggle_ui_state(True)

                            if msg[2].startswith("Zakończono"):
                                # Czyścimy pozostałe elementy (małe pliki bez progress callback)
                                # Najpierw zatrzymaj animacje spinnerów, aby uniknąć race condition
                                self.active_spinners.clear()
                                self._spinner_frames_cache.clear()
                                remaining = self.tree.get_children()
                                if remaining:
                                    self.tree.delete(*remaining)
                                with self.data_lock:
                                    self.thumbnails.clear()
                                    self.source_images.clear()
                                    self.lifestyle_states.clear()
                                    self.item_thresholds.clear()
                                    self.item_crops.clear()
                                    self.item_rotations.clear()
                                    self.eraser_strokes.clear()

                                # Czyścimy ręcznie edytowane nazwy
                                self._manually_edited_names.clear()

                                # Czyścimy cache podglądu
                                if self.preview_manager:
                                    self.preview_manager.get_cache().clear()
                                    self.preview_manager.get_preloaded().clear()

                                self.clean_name_var.set("")
                                self.clear_preview()
                            
                            self.progress.set(0)  # Reset paska postępu

                            # Komunikat o zakończeniu znikający po 5 sekundach
                            self.show_temp_status(msg[2])

                            # Włącz przyciski usuwania
                            logger.info(f"Proces zakończony. Plików wejściowych do usunięcia: {len(self.processed_source_files)}, wyjściowych: {len(self.processed_output_files)}")
                            if self.processed_source_files:
                                self.btn_delete_input.configure(state="normal")
                            if self.processed_output_files:
                                self.btn_delete_output.configure(state="normal")

                            return  # Nie planujemy kolejnego check_queue
                elif msg[0] == 'error':
                    messagebox.showerror("Błąd", msg[1])
                    self.toggle_ui_state(True)
                    self.progress.set(0)  # Reset paska postępu przy błędzie
                    # Wyczyść listy przetworzonych plików przy błędzie
                    self.processed_source_files.clear()
                    self.processed_output_files.clear()
                    return  # Nie planujemy kolejnego check_queue
                # SPINNER ANIMACJA + USUWANIE PRZETWORZONYCH MINIATUR
                elif msg[0] == 'file_progress':
                    item_id, status = msg[1], msg[2]
                    if status == 'start':
                        self.start_file_spinner(item_id)
                    elif status == 'abort':
                        self.stop_file_spinner(item_id, redraw=True)
                    elif status == 'done':
                        # PRZETWARZANIE ZAKOŃCZONE - zapisz ścieżki do usunięcia
                        # Odtwarzamy wynikową ściężkę
                        file_saved = False
                        if self.tree and self.tree.exists(item_id):
                            new_name = self.tree.set(item_id, self.COL_NEWNAME)
                            if not new_name: new_name = self.tree.set(item_id, self.COL_NAME)
                            out_dir = self.output_folder.get()
                            base, _ = os.path.splitext(new_name)
                            fmt_ext = self.output_format_var.get().lower()
                            output_path = os.path.join(out_dir, base + f".{fmt_ext}")

                            # SPRAWDŹ czy plik faktycznie został zapisany przed usunięciem miniaturki
                            if os.path.exists(output_path):
                                file_saved = True
                                self.processed_output_files.append(output_path)
                            else:
                                logger.error(f"Plik {output_path} nie został zapisany! Nie usuwam miniaturki.")

                        path = self.thumbnails.get(f"{item_id}_path")
                        if path:
                            self.processed_source_files.append(path)

                        # Usuwamy spinner
                        self.stop_file_spinner(item_id, redraw=False)

                        # Usuń przetworzoną miniaturę z drzewa TYLKO jeśli plik został zapisany
                        if file_saved and self.tree and self.tree.exists(item_id):
                            if item_id == self.current_preview_item:
                                self.clear_preview()
                            self.tree.delete(item_id)
                            self._manually_edited_names.discard(item_id)
                        
                        # Wyczyść dane dla tego elementu
                        with self.data_lock:
                            for key in [item_id, f"{item_id}_path"]:
                                self.thumbnails.pop(key, None)
                            self.source_images.pop(item_id, None)
                            self.lifestyle_states.pop(item_id, None)
                            self.item_thresholds.pop(item_id, None)
                            self.item_crops.pop(item_id, None)
                            self.item_rotations.pop(item_id, None)
                            self.eraser_strokes.pop(item_id, None)
        except queue.Empty: pass
        # Planujemy kolejne sprawdzenie tylko jeśli nie zakończono
        self.root.after(100, self.check_queue)

    def _prerender_spinner_frames(self, item_id: str, pil_img, is_checked: bool) -> List[Any]:
        """Pre-renderuje 18 klatek spinnera (360° / 20° na klatkę)."""
        frames = []
        for angle in range(0, 360, 20):
            photo = self.thumbnail_manager.create_composite_thumbnail(
                pil_img, is_checked, spinner_angle=angle
            )
            frames.append(photo)
        return frames

    def start_file_spinner(self, item_id: str) -> None:
        self.active_spinners[item_id] = 0

        # Pre-renderuj klatki spinnera raz na start
        pil_img = self.source_images.get(item_id)
        is_checked = self.lifestyle_states.get(item_id, False)
        if pil_img:
            self._spinner_frames_cache[item_id] = self._prerender_spinner_frames(item_id, pil_img, is_checked)

        if not getattr(self, '_spinner_timer', None):
            self._animate_spinners()

    def stop_file_spinner(self, item_id: str, redraw: bool = True) -> None:
        if item_id in self.active_spinners:
            del self.active_spinners[item_id]

        # Wyczyść cached frames dla tego elementu
        if item_id in self._spinner_frames_cache:
            del self._spinner_frames_cache[item_id]

        if not redraw:
            return

        # Ostatnie przerysowanie, żeby usunąć kółko i przywrócić wygląd checkboxa
        if self.tree and self.tree.exists(item_id):
            pil_img = self.source_images.get(item_id)
            if pil_img:
                is_checked = self.lifestyle_states.get(item_id, False)
                photo = self.thumbnail_manager.create_composite_thumbnail(pil_img, is_checked)
                self.thumbnails[item_id] = photo
                self.tree.item(item_id, image=photo)

    def _animate_spinners(self) -> None:
        if not self.active_spinners:
            self._spinner_timer = None
            return

        for item_id in list(self.active_spinners.keys()):
            if not self.tree or not self.tree.exists(item_id):
                del self.active_spinners[item_id]
                continue

            # Obrót o 20 stopni na klatkę
            self.active_spinners[item_id] = (self.active_spinners[item_id] + 20) % 360
            angle_idx = self.active_spinners[item_id] // 20

            # Użyj pre-renderowanej klatki z cache
            frames = self._spinner_frames_cache.get(item_id)
            if frames and angle_idx < len(frames):
                photo = frames[angle_idx]
                self.thumbnails[item_id] = photo
                self.tree.item(item_id, image=photo)

        # Uruchom kolejną klatkę za 50 ms (ok. 20 FPS)
        self._spinner_timer = self.root.after(50, self._animate_spinners)

    def move_to_recycle_bin(self, file_path) -> bool:
        """Przenosi plik do kosza systemowego (cross-platform)."""
        try:
            send2trash(file_path)
            return True
        except Exception as e:
            logger.exception(f"Błąd przenoszenia do kosza")
            return False

    def show_temp_status(self, message, duration_ms=5000) -> None:
        """Wyświetla tymczasowy komunikat statusu, który znika po określonym czasie."""
        self.status_lbl.configure(text=message)
        # Anuluj poprzedni timer jeśli istnieje
        if self._status_timer:
            self.root.after_cancel(self._status_timer)
        # Ustaw nowy timer do wyczyszczenia statusu
        self._status_timer = self.root.after(duration_ms, lambda: self.status_lbl.configure(text=""))

    def delete_processed_input_files(self) -> None:
        """Usuwa przetworzone pliki z folderu wejściowego."""
        if not self.processed_source_files:
            return

        self.status_lbl.configure(text="Usuwanie plików wejściowych...")
        self.root.update_idletasks()

        # WYMUSZENIE ZWOLNIENIA PLIKÓW
        try:
            if 'pyvips' in sys.modules:
                import pyvips
                pyvips.cache_set_max(0)
                pyvips.cache_set_max_mem(0)
        except Exception:
            pass
        gc.collect()
        time.sleep(0.1) # Krótka przerwa dla systemu plików


        errors = 0
        deleted = 0
        for file_path in self.processed_source_files:
            try:
                # Normalizuj ścieżkę dla Windows
                abs_path = os.path.abspath(file_path)
                if os.path.exists(abs_path):
                    if self.move_to_recycle_bin(abs_path):
                        deleted += 1
                    else:
                        errors += 1
                else:
                    logger.warning(f"Plik wejściowy nie istnieje: {abs_path}")
                    errors += 1
            except Exception as e:
                logger.exception(f"Błąd usuwania pliku wejściowego {file_path}")
                errors += 1

        self.processed_source_files.clear()
        self.btn_delete_input.configure(state="disabled")

        msg = f"Przeniesiono do kosza: {deleted} plików."
        if errors > 0:
            msg += f" Błędy: {errors}."

        self.show_temp_status(msg)

    def delete_processed_output_files(self) -> None:
        """Usuwa przetworzone pliki z folderu wyjściowego."""
        if not self.processed_output_files:
            return

        self.status_lbl.configure(text="Usuwanie plików wyjściowych...")
        self.root.update_idletasks()

        # WYMUSZENIE ZWOLNIENIA PLIKÓW
        try:
            if 'pyvips' in sys.modules:
                import pyvips
                pyvips.cache_set_max(0)
                pyvips.cache_set_max_mem(0)
        except Exception:
            pass
        gc.collect()
        time.sleep(0.1)

        errors = 0
        deleted = 0
        for file_path in self.processed_output_files:
            try:
                # Normalizuj ścieżkę dla Windows
                abs_path = os.path.abspath(file_path)
                if os.path.exists(abs_path):
                    if self.move_to_recycle_bin(abs_path):
                        deleted += 1
                    else:
                        errors += 1
                else:
                    logger.warning(f"Plik wyjściowy nie istnieje: {abs_path}")
                    errors += 1
            except Exception as e:
                logger.exception(f"Błąd usuwania pliku wyjściowego {file_path}")
                errors += 1

        self.processed_output_files.clear()
        self.btn_delete_output.configure(state="disabled")

        msg = f"Przeniesiono do kosza: {deleted} plików."
        if errors > 0:
            msg += f" Błędy: {errors}."

        self.show_temp_status(msg)

    def save_config(self) -> None:
        """Zapisuje konfigurację do pliku."""
        if not self.tree:
            return
        # Pobierz aktualne szerokości kolumn Treeview przez ConfigManager
        col_widths = self.config_manager.capture_column_widths(self.tree, self.all_columns)

        # Pobierz aktualne pozycje sash dla zapisu (ale nie nadpisuj self.*_panel_width)
        saved_left_width = self.left_panel_width
        saved_preview_width = self.preview_panel_width

        try:
            # Używamy sashpos jako źródła prawdy dla PanedWindow
            # winfo_width dla ramek wewnątrz może być niedokładne w momencie zdarzenia
            if self.main_paned.winfo_exists():
                total_w = self.main_paned.winfo_width()
                # Tylko jeśli okno ma sensowny rozmiar
                if total_w > 100:
                    try:
                        # sash_coord(0) = szerokość lewego panelu
                        sash0 = self.main_paned.sash_coord(0)[0]
                        # sash_coord(1) = pozycja drugiego sasha
                        sash1 = self.main_paned.sash_coord(1)[0]

                        # Zapisz aktualne pozycje do zmiennych lokalnych (nie nadpisuj self!)
                        if sash0 > 10:
                            saved_left_width = sash0

                        preview_w = total_w - sash1
                        if preview_w > 10:
                            saved_preview_width = preview_w

                    except tk.TclError:
                        # Fallback do winfo_width jeśli sashes nie są gotowe
                        left_w = self.left_frame.winfo_width()
                        right_w = self.preview_frame.winfo_width()
                        if left_w > 10: saved_left_width = int(left_w)
                        if right_w > 10: saved_preview_width = int(right_w)
            
            # Parametry szerokości są używane bezpośrednio w konstruktorze AppConfig poniżej
                
        except tk.TclError as e:
            logger.debug(f"Błąd Tcl: Pobieranie pozycji sashy przerwane: {e}")

        def safe_int(var_str, default=0):
            try: return int(var_str.get())
            except ValueError: return default
            
        def safe_float(var_str, default=0.0):
            try: return float(var_str.get())
            except ValueError: return default

        config = AppConfig(
            input_folder=self.input_folder.get(),
            output_folder=self.output_folder.get(),
            processing=ProcessingParams(
                margin=safe_int(self.margin_var, 0),
                threshold=safe_int(self.threshold_var, 10),
                max_side=safe_int(self.max_side_var, 3000),
                min_size=safe_int(self.min_size_var, 500),
                max_mb=safe_float(self.max_mb_var, 2.99),
                output_format=self.output_format_var.get(),  # <--- DODANO
                use_margin=self.use_margin_var.get(),
                use_max_side=self.use_max_side_var.get(),
                use_min_size=self.use_min_size_var.get(),
                use_max_mb=self.use_max_mb_var.get()
            ),
            appearance=AppearanceSettings(
                font_size_left_panel=self.font_size_left_panel_var.get(),
                font_size_table_header=self.font_size_table_header_var.get(),
                thumb_size=self.thumb_size_var.get(),
                dark_mode=self.dark_mode,
                light_preview_bg=self.light_preview_bg,
                light_font_color=self.light_font_color,
                dark_font_color=getattr(self, 'dark_font_color', "white"),
                enable_debug_logging=self.debug_logging_var.get(),
                fullscreen_hq=self.fullscreen_hq_var.get(),
                button_colors=self.button_colors,
                button_text_colors=self.button_text_colors,
                font_family=self.font_family_var.get(),
                font_bold=self.font_bold_var.get()
            ),
            column_widths=col_widths,
            display_columns=self.display_columns,
            window_geometry=self.root.geometry(),
            left_panel_width=saved_left_width,
            preview_panel_width=saved_preview_width,
            naming=NamingSettings(
                clean_name="",  # Nie zapisuj - zawsze puste przy starcie
                start_number="1"  # Nie zapisuj - zawsze domyślne przy starcie
            )
        )

        # Zapisz przez ConfigManager
        self.config_manager.save_config(config)

    def load_config(self) -> None:
        """Wczytuje konfigurację z pliku."""
        config = self.config_manager.load_config()
        if config is None:
            return

        try:
            if self.enable_debug_logging:
                logger.info(f"load_config: left_panel_width={config.left_panel_width}, preview_panel_width={config.preview_panel_width}, window_geometry={config.window_geometry}")
            self.input_folder.set(config.input_folder)
            self.output_folder.set(config.output_folder)
            self.margin_var.set(str(config.processing.margin))
            self.threshold_var.set(str(config.processing.threshold))
            self.max_side_var.set(str(config.processing.max_side))
            self.min_size_var.set(str(config.processing.min_size))
            self.max_mb_var.set(str(config.processing.max_mb))
            self.output_format_var.set(config.processing.output_format)  # <--- DODANO

            self.use_margin_var.set(config.processing.use_margin)
            self.use_max_side_var.set(config.processing.use_max_side)
            self.use_min_size_var.set(config.processing.use_min_size)
            self.use_max_mb_var.set(config.processing.use_max_mb)


            self.font_size_left_panel_var.set(config.appearance.font_size_left_panel)
            self.font_size_table_header_var.set(config.appearance.font_size_table_header)
            self.font_family_var.set(config.appearance.font_family)
            self.font_bold_var.set(config.appearance.font_bold)
            self.thumb_size_var.set(config.appearance.thumb_size)
            self.fullscreen_hq_var.set(config.appearance.fullscreen_hq)
            self.dark_mode = config.appearance.dark_mode
            self.light_preview_bg = config.appearance.light_preview_bg
            self.light_font_color = config.appearance.light_font_color
            self.dark_font_color = config.appearance.dark_font_color
            self.debug_logging_var.set(config.appearance.enable_debug_logging)
            self.enable_debug_logging = config.appearance.enable_debug_logging
            self.config_manager.enable_debug_logging = config.appearance.enable_debug_logging
            self.button_colors = config.appearance.button_colors.copy()
            self.button_text_colors = getattr(config.appearance, 'button_text_colors', {}).copy()
            # Włącz/wyłącz logowanie do pliku na podstawie configu
            set_file_logging(self.enable_debug_logging)

            self.display_columns = config.display_columns
            self.root.geometry(config.window_geometry)
            if config.fullscreen:
                self.root.attributes('-fullscreen', True)
            self.left_panel_width = config.left_panel_width
            self.preview_panel_width = config.preview_panel_width

            # Nie wczytuj ustawień nazewnictwa - zawsze puste przy starcie
            self.clean_name_var.set("")
            self.start_number_var.set("1")

        except (IOError, OSError, json.JSONDecodeError, ValueError) as e:
            logger.error(f"Błąd wczytywania konfiguracji: {e}")
            # Upewnij się że is_processing jest False po błędzie ładowania configu
            self.is_processing = False

    def restore_layout_state(self):
        """Przywraca zapisane szerokości paneli po pełnym załadowaniu okna."""
        try:
            if self.enable_debug_logging:
                logger.info(f"restore_layout_state START: _is_initializing={self._is_initializing}, left_panel_width={self.left_panel_width}, preview_panel_width={self.preview_panel_width}")
            self.config_manager.restore_layout_state(
                self.main_paned,
                self.left_panel_width,
                self.preview_panel_width
            )
            # Mark initialization complete
            self._is_initializing = False
            if self.enable_debug_logging:
                logger.info(f"restore_layout_state END: _is_initializing={self._is_initializing}")
        finally:
            # Udostępnij widok okna użytkownikowi ściągając zasłonę tymczasową
            self.root.attributes("-alpha", 1.0)

    def on_closing(self) -> None:
        """Obsługuje zamknięcie aplikacji."""
        try:
            self.stop_event.set()
            self.save_config()
            
            # 1. Brutalne sprzątanie wycieków po plikach tymczasowych (Temp Leak)
            import tempfile
            import shutil
            temp_dir = os.path.join(tempfile.gettempdir(), "fotopim_cache")
            if os.path.exists(temp_dir):
                try:
                    shutil.rmtree(temp_dir, ignore_errors=True)
                except Exception as e:
                    logger.exception(f"Nie udało się wyczyścić plików temp Cache")
                    
            # Anuluj timer statusu
            if self._status_timer:
                self.root.after_cancel(self._status_timer)
            # Zamknij executor podglądu
            if self.preview_manager:
                self.preview_manager.shutdown()
            # Zamknij executor miniaturek
            if self.thumbnail_executor:
                self.thumbnail_executor.shutdown(wait=False)
        except Exception as e:
            logger.exception(f"Błąd podczas zamykania")
        finally:
            # Gwarantowane zamknięcie okna głównego i przerwanie pętli Tcl
            self.root.quit()
            self.root.destroy()

    def _get_selected_items(self) -> List[str]:
        target_items = []
        # 1. Sprawdź zaznaczone na liście (niebieskie podświetlenie)
        selected = self.tree.selection()
        if selected:
            target_items.extend(selected)

        # 2. Sprawdź zaznaczone checkboxem (Lifestyle)
        for item_id, state in self.lifestyle_states.items():
            if state and item_id not in target_items:
                target_items.append(item_id)
                
        # 3. Jeśli wciąż nic, weź aktualny podgląd
        if not target_items and self.current_preview_item and self.current_preview_item not in target_items:
            target_items.append(self.current_preview_item)
            
        return target_items

    def _reload_item_visuals(self, item_id: str, raw_pil_image=None, margin=0, threshold=10, keep_orig=False, fullscreen_hq=False) -> None:
        with self.data_lock:
            path = self.thumbnails.get(f"{item_id}_path")

        if raw_pil_image is None:
            if not path or not os.path.exists(path): return
            with Image.open(path) as img_load:
                raw_pil_image = img_load.convert("RGB")
                
        trimmed_raw = trim_whitespace(raw_pil_image, margin=margin, threshold=threshold)
        w, h = trimmed_raw.size
        res_str = f"{w}x{h}"
        self.root.after(0, lambda iid=item_id, rs=res_str: self.tree.set(iid, self.COL_RESOLUTION, rs))
        
        thumb_size = ConfigConstants.THUMBNAIL_SIZE
        thumb = trimmed_raw.copy()
        thumb.thumbnail((thumb_size, thumb_size))
        
        target_preview_dim = max(self.preview_panel_width - 20, 300)
        if fullscreen_hq:
            target_preview_dim = int(max(self.root.winfo_screenwidth(), self.root.winfo_screenheight()) * 0.9)
            
        preview_pil = trimmed_raw.copy()
        preview_pil.thumbnail((target_preview_dim, target_preview_dim), Image.Resampling.LANCZOS)
        
        with self.data_lock:
            self.source_images[item_id] = preview_pil
            if self.preview_manager:
                self.preview_manager.get_preloaded()[item_id] = preview_pil

        # Aktualizuj wizualizację elementu
        self.root.after(0, lambda iid=item_id: self.update_single_row_image(iid))
            
        if self.preview_manager:
            self.preview_manager.clear_cache_for_item(item_id, keep_orig=keep_orig)
            
        if self.current_preview_item == item_id:
            self.root.after(0, lambda iid=item_id: self.show_preview(iid))

if __name__ == "__main__":
    # === 1. NAPRAWA IKONY NA PASKU ZADAŃ (AppUserModelID) ===
    # Dzięki temu Windows traktuje program jako oddzielną aplikację
    try:
        myappid = 'mojafirma.fotopim.procesor.v1'
        if IS_WINDOWS:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(myappid)
    except Exception:
        pass

    # Load config temporarily to get dark_mode setting before creating root
    temp_dark_mode = False
    if os.path.exists(ConfigManager.CONFIG_FILE):
        try:
            with open(ConfigManager.CONFIG_FILE, encoding='utf-8') as f:
                data = json.load(f)
                temp_dark_mode = data.get("dark_mode", False)
        except (IOError, OSError, json.JSONDecodeError):
            pass

    # Set customtkinter appearance mode
    ctk.set_appearance_mode("Dark" if temp_dark_mode else "Light")

    root = TkinterDnD.Tk()
    root.withdraw()  # Ukryj natychmiast, żeby uniknąć mignięcia białego okienka

    # === USTAWIENIE IKONY OKNA I PASKA ZADAŃ ===
    # Znajdź ścieżkę do ikony osadzonej w exe
    def get_icon_path():
        """Znajdź ścieżkę do ikony (osadzona w exe lub plik lokalny)."""

        if getattr(sys, 'frozen', False):
            base_path = sys._MEIPASS
        else:
            base_path = os.path.dirname(os.path.abspath(__file__))

        icon_file = 'ikona.icns' if IS_MACOS else 'ikona.ico'
        icon_path = os.path.join(base_path, icon_file)
        return icon_path

    _app_icon_photo = None

    try:
        icon_path = get_icon_path()
        if os.path.exists(icon_path):
            if IS_MACOS:
                from PIL import Image as PILImage
                img = PILImage.open(icon_path)
                root._app_icon_photo = ImageTk.PhotoImage(img)
                root.iconphoto(True, root._app_icon_photo)
            else:
                root.iconbitmap(icon_path)
                try:
                    from PIL import Image as PILImage
                    img = PILImage.open(icon_path)
                    root._app_icon_photo = ImageTk.PhotoImage(img)
                    root.iconphoto(True, root._app_icon_photo)
                except Exception as photo_err:
                    logger.debug(f"Nie udało się ustawić iconphoto: {photo_err}")
    except Exception as e:
        logger.debug(f"Nie udało się ustawić ikony: {e}")

    app = ImageProcessorApp(root)
    # Ukryj zawartość okna dopóki panele z Configu nie zakończą się fizycznie porządkować, co zapobiega migotaniu interfejsu
    root.attributes("-alpha", 0.0)
    root.deiconify()
    root.mainloop()