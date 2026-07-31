#!/usr/bin/env python3
"""check_structure.py - structural audit of Part V, both editions.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Mechanical checks only, the ones a reading misses: every label referenced, every figure
referenced from the body, the two editions carrying the same sections, equations, figures and
displayed numbers.  Nothing here judges prose.
"""
import re
import sys

EN, ES = "ghu_observability.tex", "ghu_observability_es.tex"
LAB = re.compile(r"\\label\{([^}]*)\}")
REF = re.compile(r"\\(?:eq)?ref\{([^}]*)\}")
FIG = re.compile(r"\\begin\{figure\}(.*?)\\end\{figure\}", re.S)
INC = re.compile(r"includegraphics[^{]*\{([^}]*)\}")
SEC = re.compile(r"\\section\{(.*?)\}\\label\{([^}]*)\}")
EQN = re.compile(r"\\begin\{equation\}\\label\{([^}]*)\}")
NUM = re.compile(r"(?<![\w\\])(\d[\d,]{2,})(?![\w])")


def audit(path):
    s = open(path, encoding="utf-8").read()
    # a comment is not content: without this the parity block reports a difference between the
    # two editions' HEADER NOTES as a difference between the two papers.
    s = re.sub(r"(?<!\\)%.*", "", s)
    labels, refs = set(LAB.findall(s)), set(REF.findall(s))
    print("== %s" % path)
    print("   labels %d, references %d" % (len(labels), len(refs)))
    orphan = sorted(labels - refs)
    dangling = sorted(refs - labels)
    print("   NEVER referenced : %s" % (orphan or "none"))
    print("   referenced but undefined : %s" % (dangling or "none"))
    for i, fg in enumerate(FIG.findall(s), 1):
        lab = LAB.search(fg)
        inc = INC.search(fg)
        name = lab.group(1) if lab else "NO LABEL"
        print("   fig %d  %-16s %-26s referenced_in_body=%s"
              % (i, name, inc.group(1) if inc else "(tikz)",
                 (name in refs) if lab else "-"))
    return dict(labels=labels, refs=refs, s=s,
                secs=[m[1] for m in SEC.findall(s)],
                eqs=EQN.findall(s),
                figs=[LAB.search(f).group(1) for f in FIG.findall(s) if LAB.search(f)],
                nums=sorted(set(NUM.findall(s))))


if __name__ == "__main__":
    a, b = audit(EN), audit(ES)
    print()
    print("== EN vs ES parity")
    differ = False
    for k in ("secs", "eqs", "figs"):
        same = a[k] == b[k]
        differ |= not same
        print("   %-5s EN %d / ES %d  %s"
              % (k, len(a[k]), len(b[k]),
                 "SAME ORDER" if same else "DIFFER: %s" % (set(a[k]) ^ set(b[k]) or "order only")))
    only_en = sorted(set(a["nums"]) - set(b["nums"]))
    only_es = sorted(set(b["nums"]) - set(a["nums"]))
    print("   displayed numbers only in EN : %s" % (only_en or "none"))
    print("   displayed numbers only in ES : %s" % (only_es or "none"))
    print()
    print("== summary")
    fail = False
    for tag, d in (("EN", a), ("ES", b)):
        orphan = sorted(set(d["labels"]) - set(d["refs"]))
        dangling = sorted(set(d["refs"]) - set(d["labels"]))
        unref = [f for f in d["figs"] if f not in d["refs"]]
        fail |= bool(dangling or unref)
        print("   %s  sections %d  equations %d  figures %d"
              % (tag, len(d["secs"]), len(d["eqs"]), len(d["figs"])))
        print("       orphan labels        : %d %s" % (len(orphan), orphan or ""))
        print("       dangling references  : %d %s" % (len(dangling), dangling or ""))
        print("       figures unreferenced : %d %s" % (len(unref), unref or ""))
    raise SystemExit(1 if (fail or differ or only_en or only_es) else 0)
