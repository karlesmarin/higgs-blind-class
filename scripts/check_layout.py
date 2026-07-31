# -*- coding: utf-8 -*-
"""Layout audit: finds pages with a large blank band inside the text area.

A clean LaTeX compile reports overfull boxes but says nothing about half-empty pages caused by float
congestion, which is what a reader notices first. For each page this measures the biggest vertical
gap between consecutive content blocks, ignoring the running head and the page number, and reports
any gap above a threshold as a fraction of the text height.

    python check_layout.py orbit_pair.pdf [threshold_fraction]

Authors: Carles Marin, Claude (AI assistant)."""
import sys
import fitz

path = sys.argv[1] if len(sys.argv) > 1 else "orbit_pair.pdf"
THR = float(sys.argv[2]) if len(sys.argv) > 2 else 0.14

doc = fitz.open(path)
worst = []
for i, page in enumerate(doc):
    H = page.rect.height
    head, foot = 0.10 * H, 0.93 * H          # drop running head and folio
    blocks = []
    for b in page.get_text("blocks"):
        x0, y0, x1, y1 = b[:4]
        text = b[4].strip() if len(b) > 4 else ""
        if not text:
            continue
        if y1 < head or y0 > foot:
            continue
        blocks.append((y0, y1))
    # images and drawings count as content too
    for d in page.get_image_info():
        bb = d.get("bbox")
        if bb and bb[3] > head and bb[1] < foot:
            blocks.append((bb[1], bb[3]))
    if len(blocks) < 2:
        continue
    blocks.sort()
    # merge, then find the largest hole
    merged = [list(blocks[0])]
    for y0, y1 in blocks[1:]:
        if y0 <= merged[-1][1] + 1:
            merged[-1][1] = max(merged[-1][1], y1)
        else:
            merged.append([y0, y1])
    gap, at = 0.0, None
    for a, b in zip(merged, merged[1:]):
        g = b[0] - a[1]
        if g > gap:
            gap, at = g, a[1]
    frac = gap / (foot - head)
    if frac >= THR:
        worst.append((frac, i + 1, gap, at))

worst.sort(reverse=True)
print("%s : %d pages, threshold %.0f%% of the text height" % (path, doc.page_count, THR * 100))
if not worst:
    print("  no page has an internal blank band above the threshold.")
for frac, pg, gap, at in worst:
    print("  page %3d : blank band %.0f%% of the text height (%.0fpt, starting at y=%.0f)"
          % (pg, frac * 100, gap, at))
