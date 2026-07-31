#!/usr/bin/env python3
"""check_numbers.py - is every number printed in Part V greppable in an archived run?

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Rewritten for Part V because the inherited version LIED. It stripped the decimal point and matched
substrings, so it passed `1.816` on the strength of `816` appearing inside a Laurent coefficient in
outputs/fibre_eta.json. A gate that cannot fail is not a gate.

This one keeps the decimal point, matches on token boundaries, and puts every non-measurement
(years, equation numbers, arXiv identifiers, quoted experimental values) in an explicit allow-list
so the exceptions are visible in the source instead of silently dropped.
"""
import os
import re

TEXS = ["ghu_observability.tex", "ghu_observability_es.tex"]
OUT = "../outputs"

ALLOW = {
    "2004", "2024", "2018", "1940", "2026", "07", "31", "2016",  # years and dates
    "3.25", "3.11", "4.1", "4.2", "3.20", "4.3", "4.13", "4.11", # equation numbers
    "5.22", "5.28", "5.1", "2.2", "3.4", "2.4", "2.26", "6.7",
    "015022", "0309088", "2312.08608", "2502.08250",             # identifiers
    "2401.09809", "2404.19411", "1509.01636", "1206.1890",
    "1211.2843", "1804.04514", "0.5281", "21438226", "21463000",
    "111", "657", "669", "317", "126", "190", "158", "103",      # volumes / pages
    "105", "275", "734", "483001", "165", "478", "064", "613",
    "999", "055003", "306", "132", "82", "153", "60", "61",
    "141", "234", "265", "033", "063", "98", "76", "78",
    "0.653", "246", "125", "80.4", "303", "48.0",                # quoted from AHMN / PDG
    "0.0645", "0.0796", "0.0109",                                # AHMN eq. (4.2), quoted
}


def tokens(s):
    return set(re.findall(r"(?<![\w.])\d+(?:\.\d+)?(?![\w.])", s))


def audit(tex, have):
    s = open(tex, encoding="utf-8").read()
    # (?<!\\): an ESCAPED percent is content, not a comment. The naive r"%.*" silently swallowed
    # every number to the right of a printed percentage -- they were never checked at all.
    s = re.sub(r"(?<!\\)%.*", "", s)
    s = re.sub(r"\\begin\{thebibliography\}.*", "", s, flags=re.S)
    # layout is not data: tikz coordinates, colour definitions, box widths, column specs
    s = re.sub(r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}", "", s, flags=re.S)
    s = re.sub(r"\\definecolor\{[^}]*\}\{RGB\}\{[^}]*\}", "", s)
    s = re.sub(r"[\d.]+\\textwidth", "", s)
    s = re.sub(r"\\(geometry|includegraphics|usepackage)\[[^\]]*\]", "", s)
    s = re.sub(r"p\{[\d.]+cm\}|\[[\d.]+pt\]|\{[\d.]+cm\}", "", s)
    # a row-height factor and a glue length are typesetting, not measurements of anything
    s = re.sub(r"\\renewcommand\{\\arraystretch\}\{[\d.]+\}", "", s)
    s = re.sub(r"\\setlength\{\\[a-zA-Z]+\}\{[^}]*\}", "", s)

    found, missing, allowed = [], [], []
    for t in sorted(tokens(s), key=lambda x: (-len(x), x)):
        if len(t) < 2:
            continue
        (allowed if t in ALLOW else found if t in have else missing).append(t)

    print("%s: every printed number against %s/*" % (tex, OUT))
    print("  greppable in an archived run : %d" % len(found))
    print("  declared non-measurements    : %d" % len(allowed))
    print("  NOT FOUND                    : %d" % len(missing))
    for t in missing:
        print("     %s   <-- archive its run, or remove it" % t)
    return missing


def main():
    corpus = ""
    for fn in sorted(os.listdir(OUT)):
        p = os.path.join(OUT, fn)
        if os.path.isfile(p):
            corpus += open(p, encoding="utf-8", errors="ignore").read() + "\n"
    have = tokens(corpus)
    # a run that printed 2.73e+00 DID archive 2.73; without this the mantissa is invisible to the
    # token boundary and the gate reports a number it actually holds.
    have |= set(re.findall(r"(?<![\w.])(\d+(?:\.\d+)?)e[+-]?\d+", corpus))
    bad = []
    for tex in TEXS:
        bad += audit(tex, have)
        print()
    return bad


if __name__ == "__main__":
    raise SystemExit(1 if main() else 0)
