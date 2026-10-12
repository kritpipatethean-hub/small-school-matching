"""โครงสร้างโฟลเดอร์ย่อยภายในโฟลเดอร์รายพื้นที่ใต้ ``02 งานรายพื้นที่/``.

ไฟล์นี้เป็นแหล่งความจริงเดียวของ layout รายพื้นที่ สคริปต์ใน ``04 เครื่องมือ/``
ที่ใช้โฟลเดอร์รายพื้นที่ (``sms_pipeline.py``) ต้อง import จากที่นี่
ห้ามพิมพ์ชื่อโฟลเดอร์ย่อยซ้ำในไฟล์อื่น รายละเอียดกติกาอยู่ใน ``Project Tor.md`` หัวข้อ 4

โครงสร้างของหนึ่งพื้นที่ (ตัดสินร่วมกับผู้ใช้ 4 กันยายน 2569)::

    02 งานรายพื้นที่/<ชื่อพื้นที่>/
      ผลตรวจ_<areacode>.json          ← root: QC และ commit marker ของชุดไฟล์
      แผนที่ผลการจับคู่_<...>.qgz      ← root: จุดยึดของพาธ relative ในโครงการ QGIS
      01 ข้อมูล GIS/                   ← .gpkg ทุกชนิด
      02 แผนที่และ PDF/                ← .png และ .pdf
      03 ตารางและรายงาน/              ← .xlsx, .md และ .docx

โมดูลนี้ใช้เฉพาะ standard library เพื่อให้ import ได้จากทุก interpreter
"""

from __future__ import annotations

from pathlib import PurePath

LAYOUT_VERSION = 2

GIS_DIR = "01 ข้อมูล GIS"
MEDIA_DIR = "02 แผนที่และ PDF"
REPORT_DIR = "03 ตารางและรายงาน"
SUBDIRS: tuple[str, ...] = (GIS_DIR, MEDIA_DIR, REPORT_DIR)

# kind ตาม key ของ output_names()/pilot.files ใน sms_pipeline.py และ areas.json
# ค่า None หมายถึงไฟล์อยู่ที่ root ของโฟลเดอร์พื้นที่
KIND_SUBDIR: dict[str, str | None] = {
    "boundary": GIS_DIR,
    "small": GIS_DIR,
    "magnets": GIS_DIR,
    "roads": GIS_DIR,
    "od": GIS_DIR,
    "status": GIS_DIR,
    "full_od": GIS_DIR,
    "time_od": GIS_DIR,
    "image": MEDIA_DIR,
    "pdf": MEDIA_DIR,
    "size_image": MEDIA_DIR,
    "excel": REPORT_DIR,
    "qc": None,
    "project": None,
}

# นามสกุลที่มีกฎ layout; .json อนุญาตเฉพาะ QC marker ที่ root (ตรวจด้วยชื่อไฟล์ ไม่ใช่นามสกุล)
# และ .qgz อยู่ที่ root เสมอ จึงไม่อยู่ในตารางนี้
EXT_SUBDIR: dict[str, str] = {
    ".gpkg": GIS_DIR,
    ".png": MEDIA_DIR,
    ".pdf": MEDIA_DIR,
    ".xlsx": REPORT_DIR,
    ".md": REPORT_DIR,
    ".docx": REPORT_DIR,
}

SUBDIR_EXTENSIONS: dict[str, frozenset[str]] = {
    sub: frozenset(ext for ext, target in EXT_SUBDIR.items() if target == sub)
    for sub in SUBDIRS
}


def subdir_for_extension(extension: str) -> str | None:
    """คืนชื่อโฟลเดอร์ย่อยตามนามสกุล หรือ None เมื่อไม่มีกฎ (ผู้เรียกต้องตัดสินว่าจะหยุด)"""
    return EXT_SUBDIR.get(extension.lower())


def area_relpath(kind: str, filename: str) -> PurePath:
    """พาธของไฟล์เทียบกับโฟลเดอร์พื้นที่ เช่น ``01 ข้อมูล GIS/ถนน_x.gpkg`` หรือ ``ผลตรวจ_x.json``.

    ``filename`` ต้องเป็นชื่อไฟล์เปล่า (ไม่มีตัวคั่นโฟลเดอร์) ตามสัญญาเดิมของ areas.json และ QC JSON
    kind ที่ไม่รู้จักจะใช้นามสกุลตัดสินแทน หากไม่มีกฎเลยจะ raise เพื่อไม่ให้ไฟล์หลุดไปที่ root โดยเงียบ ๆ
    """
    if not filename or PurePath(filename).name != filename or filename in {".", ".."}:
        raise ValueError(f"ชื่อไฟล์ต้องเป็นชื่อเปล่าไม่มีโฟลเดอร์: {filename!r}")
    if kind in KIND_SUBDIR:
        subdir = KIND_SUBDIR[kind]
    else:
        subdir = subdir_for_extension(PurePath(filename).suffix)
        if subdir is None:
            raise ValueError(f"ไม่มีกฎ layout สำหรับ kind {kind!r} / ไฟล์ {filename!r}")
    return PurePath(subdir, filename) if subdir else PurePath(filename)
