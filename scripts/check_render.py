#!/usr/bin/env python3
"""check_render.py - the fourth gate: render the paper and look at it.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

The other three gates read the SOURCE. check_numbers asks whether every printed number is backed by
an archived run, check_structure whether every label is referenced, check_layout where the floats
land. None of them looks at the PAGE, and in one session seven defects got past all three because
they were defects of reading, not of syntax:

  * a stray line inside a tikzpicture, typeset at the origin and printed on top of the root node;
  * a caption telling the reader to look at a grey plane that was drawn at alpha 0.16;
  * three axis labels landing on top of tick marks, annotations or a colour bar;
  * a legend key colliding with a panel title.

The compiler reported none of them. Zero errors, zero warnings, every time.

This gate does the half a machine can do -- find text that overlaps other text -- and then produces
the renders so that the half a machine cannot do is an explicit step with a checklist, rather than
something one remembers to do when suspicious.

VALIDATED, and recorded here because a guard whose ability to fire was never demonstrated is the
error this gate exists to prevent. Two guards failed that way in the same session: check_numbers
matched substrings and passed `1.816` on the strength of `816` inside a JSON blob, and the AHMN
validation demanded the OPPOSITE sign to the published one and therefore passed on the very
discrepancy it was written to catch.

So: the stray-tikz-line defect was deliberately re-introduced into a copy of the source, rebuilt, and
this script run against it. It reports

    page  2  TEXT OVERLAPS TEXT
         parities   <-->  , checkedon
         lie        <-->  , checkedon

against 0 on the clean document. It fires.

Usage:  python check_render.py            audit + render every figure page
        python check_render.py --all      render every page
"""
import os
import sys

import fitz

ES = "--es" in sys.argv
PDF = "ghu_observability_es.pdf" if ES else "ghu_observability.pdf"
OUT = os.path.join("..", "outputs", "render_es" if ES else "render")
CAPTION = "Figura " if ES else "Figure "     # the picker keys on the caption word, which is localised
DPI = 150
OVERLAP = 0.55          # fraction of the smaller span that must be covered to count as a collision
MINLEN = 2              # ignore single glyphs: maths legitimately overlaps them


def spans(page):
    out = []
    for b in page.get_text("dict")["blocks"]:
        for l in b.get("lines", []):
            for s in l.get("spans", []):
                t = s["text"].strip()
                if len(t) >= MINLEN:
                    out.append((fitz.Rect(s["bbox"]), t, b["number"]))
    return out


def overlaps(page):
    hits = []
    sp = spans(page)
    for i in range(len(sp)):
        ri, ti, bi = sp[i]
        for j in range(i + 1, len(sp)):
            rj, tj, bj = sp[j]
            if bi == bj:
                continue                      # same block: normal line packing
            inter = ri & rj
            if inter.is_empty:
                continue
            small = min(abs(ri.get_area()), abs(rj.get_area()))
            if small and abs(inter.get_area()) / small > OVERLAP:
                hits.append((ti, tj))
    return hits


def main():
    every = "--all" in sys.argv
    d = fitz.open(PDF)
    os.makedirs(OUT, exist_ok=True)

    figpages = sorted({i for i in range(d.page_count)
                       if CAPTION in d[i].get_text() and ":" in d[i].get_text()})
    pages = range(d.page_count) if every else figpages
    if not figpages:
        # a picker that silently returns nothing renders no pages and still exits green:
        # exactly the failure mode this gate exists to prevent. Say so.
        print("   WARNING: no page matched the caption word %r -- rendering everything" % CAPTION)
        pages = range(d.page_count)

    print("check_render: %s, %d pages" % (PDF, d.page_count))
    print()
    bad = 0
    for i in range(d.page_count):
        h = overlaps(d[i])
        if h:
            bad += len(h)
            print("   page %2d  TEXT OVERLAPS TEXT" % (i + 1))
            for a, b in h[:4]:
                print("        %-38s  <-->  %s" % (a[:38], b[:38]))
    print("   overlapping text spans: %d" % bad)

    print()
    print("   rendered for looking at (this is the half a machine cannot do):")
    for i in pages:
        p = os.path.join(OUT, "page%02d.png" % (i + 1))
        d[i].get_pixmap(dpi=DPI).save(p)
        print("      %s" % p)
    print()
    print("   CHECKLIST, one line per figure, to be answered by looking:")
    print("      does every caption describe what is actually drawn?")
    print("      is every axis label, legend and annotation clear of everything else?")
    print("      is anything the caption tells the reader to look at actually visible?")
    print("      do the numbers in the figure match the numbers in the text?")
    return bad


if __name__ == "__main__":
    raise SystemExit(1 if main() else 0)
