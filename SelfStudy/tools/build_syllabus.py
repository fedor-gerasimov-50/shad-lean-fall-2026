#!/usr/bin/env python3
"""Build the printable syllabus from SelfStudy/Syllabus.md using ReportLab.

Run with a Python environment containing reportlab. The source Markdown remains
the editable content; explicit PAGEBREAK markers define the three desk pages.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path
from xml.sax.saxutils import escape

from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    PageBreak,
    Paragraph,
    SimpleDocTemplate,
    Spacer,
    Table,
    TableStyle,
)


BASE = Path(__file__).resolve().parents[1]
INK = colors.HexColor("#172C42")
MUTED = colors.HexColor("#536476")
PALE = colors.HexColor("#F0F4F7")
RULE = colors.HexColor("#D6DFE7")


def register_fonts() -> None:
    runtime_fonts = (
        Path.home()
        / ".cache/codex-runtimes/codex-primary-runtime/dependencies/native"
        / "libreoffice-headless/libreoffice/LibreOfficeDev.app/Contents"
        / "Resources/fonts/truetype"
    )
    candidates = [
        runtime_fonts,
        Path("/usr/share/fonts/truetype/dejavu"),
        Path("/usr/local/share/fonts"),
    ]
    for family, filename in [
        ("Guide", "DejaVuSans.ttf"),
        ("GuideBold", "DejaVuSans-Bold.ttf"),
        ("GuideItalic", "DejaVuSans-Oblique.ttf"),
        ("GuideMono", "DejaVuSansMono.ttf"),
    ]:
        match = next((p / filename for p in candidates if (p / filename).exists()), None)
        if match is None:
            raise SystemExit(f"Missing font {filename}; install DejaVu Sans or add its directory.")
        pdfmetrics.registerFont(TTFont(family, str(match)))
    pdfmetrics.registerFontFamily(
        "Guide", normal="Guide", bold="GuideBold", italic="GuideItalic", boldItalic="GuideBold"
    )


def inline(text: str) -> str:
    # Printable copies use ASCII hyphens while retaining meaningful symbols.
    text = text.translate(str.maketrans({"\u2010": "-", "\u2011": "-", "\u2012": "-", "\u2013": "-", "\u2014": "-"}))
    text = escape(text)
    text = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r'<link href="\2" color="#245F8A">\1</link>', text)
    text = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", text)
    text = re.sub(r"`([^`]+)`", r'<font name="GuideMono">\1</font>', text)
    return text


def styles() -> dict[str, ParagraphStyle]:
    common = dict(fontName="Guide", textColor=INK, alignment=TA_LEFT)
    return {
        "title": ParagraphStyle("Title", fontSize=18, leading=22, spaceAfter=8, **common),
        "h2": ParagraphStyle("H2", fontSize=12.5, leading=16, spaceBefore=7, spaceAfter=7, keepWithNext=True, **common),
        "h3": ParagraphStyle("H3", fontSize=10, leading=13, spaceBefore=8, spaceAfter=4, keepWithNext=True, **common),
        "body": ParagraphStyle("Body", fontSize=9, leading=12, spaceAfter=7, **common),
        "bullet": ParagraphStyle("Bullet", fontSize=8.8, leading=11.4, spaceAfter=2.5, leftIndent=12, firstLineIndent=0, bulletIndent=0, bulletFontName="Guide", bulletFontSize=9, **common),
        "cell": ParagraphStyle("Cell", fontSize=8.35, leading=11, spaceAfter=0, **common),
        "headcell": ParagraphStyle("HeadCell", fontName="GuideBold", fontSize=8.2, leading=10.5, textColor=colors.white),
    }


def parse_markdown(source: str, sty: dict[str, ParagraphStyle]) -> list:
    lines = source.splitlines()
    story = []
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
        if line == "<!-- PAGEBREAK -->":
            story.append(PageBreak())
            i += 1
            continue
        if line.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].strip().startswith("|"):
                cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
                if not all(re.fullmatch(r":?-+:?", c) for c in cells):
                    rows.append(cells)
                i += 1
            data = [
                [Paragraph(inline(c), sty["headcell" if r == 0 else "cell"]) for c in row]
                for r, row in enumerate(rows)
            ]
            table = Table(data, colWidths=[42, 52, 182, 248], repeatRows=1, hAlign="LEFT")
            table.setStyle(TableStyle([
                ("BACKGROUND", (0, 0), (-1, 0), INK),
                ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, PALE]),
                ("VALIGN", (0, 0), (-1, -1), "TOP"),
                ("LEFTPADDING", (0, 0), (-1, -1), 6),
                ("RIGHTPADDING", (0, 0), (-1, -1), 6),
                ("TOPPADDING", (0, 0), (-1, -1), 5),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
                ("LINEBELOW", (0, 0), (-1, 0), 0.6, INK),
                ("LINEBELOW", (0, -1), (-1, -1), 0.6, RULE),
            ]))
            story.extend([table, Spacer(1, 8)])
            continue
        if line.startswith("### "):
            story.append(Paragraph(inline(line[4:]), sty["h3"]))
            i += 1
            continue
        if line.startswith("## "):
            story.append(Paragraph(inline(line[3:]), sty["h2"]))
            i += 1
            continue
        if line.startswith("# "):
            story.append(Paragraph(inline(line[2:]), sty["title"]))
            i += 1
            continue
        if line.startswith("- "):
            item = line[2:]
            checkbox = item.startswith("[ ] ")
            if checkbox:
                item = item[4:]
            story.append(Paragraph(inline(item), sty["bullet"], bulletText="\u2610" if checkbox else "\u2022"))
            i += 1
            continue
        paragraph = [line]
        i += 1
        while i < len(lines):
            nxt = lines[i].strip()
            if not nxt or nxt.startswith(("#", "- ", "|", "<!--")):
                break
            paragraph.append(nxt)
            i += 1
        story.append(Paragraph(inline(" ".join(paragraph)), sty["body"]))
    return story


def decorate(canvas, doc) -> None:
    canvas.saveState()
    canvas.setStrokeColor(RULE)
    canvas.setLineWidth(0.6)
    canvas.line(44, 756, 568, 756)
    canvas.setFillColor(MUTED)
    canvas.setFont("Guide", 7.3)
    canvas.drawString(44, 765, "SELF STUDY  /  LEAN PROOF VERIFICATION")
    canvas.drawRightString(568, 765, "SHAD + MIL + TPiL")
    canvas.line(44, 35, 568, 35)
    canvas.drawString(44, 23, "Prepared 21 Oct 2026  |  Suggested deadlines  |  Course pins: v4.33.1")
    canvas.drawRightString(568, 23, str(doc.page))
    canvas.restoreState()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=BASE / "Syllabus.md")
    parser.add_argument("--output", type=Path, default=BASE / "output/pdf/Syllabus.pdf")
    args = parser.parse_args()
    register_fonts()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    doc = SimpleDocTemplate(
        str(args.output),
        pagesize=letter,
        leftMargin=44,
        rightMargin=44,
        topMargin=46,
        bottomMargin=45,
        title="Lean proof verification: desk syllabus",
        author="Independent study plan",
    )
    doc.build(parse_markdown(args.source.read_text(), styles()), onFirstPage=decorate, onLaterPages=decorate)
    print(f"Created {args.output}")


if __name__ == "__main__":
    main()
