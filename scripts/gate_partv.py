#!/usr/bin/env python3
"""gate_partv.py - the pre-publication gate for Part V: ONE pass over the whole artifact.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Same rule as `_gate.py` for Parts III/IV, and it exists for the same reason: verifying pieces
serially guarantees churn, and every defect we ever patched had been there since v1. This runs
before anything touches Zenodo.

The distinguishing principle, and the reason this is not just the five gates in a trench coat:
EVERY CHECK COMPARES AGAINST AN INDEPENDENT GROUND TRUTH, never against the code that produced
the number.

  * a quotation from somebody else's paper  -> that paper's own text, in `../../_papers/`
  * a number we attribute to AHMN           -> the string in AHMN's text
  * a Lean theorem we name in the prose     -> the .lean file, and its freedom from `sorry`
  * the headline counts of the blind class  -> recomputed from the BIALTERNANT in exact rational
                                               arithmetic, not read back from our own JSON
  * everything mechanical                   -> the five gates, which must all be green

A quotation is the most dangerous object in a paper of this kind: it is the one place where we
speak in someone else's voice, and a paraphrase that has drifted is indistinguishable from a
quotation until someone opens the source. So every `` '' in the source text must be classified
here -- either as ATTRIBUTED, with the file it must appear in, or as OURS. A new quotation added
later and left unclassified FAILS the gate until a human says which it is.

Exit 0 iff every check is PASS or WARN.
"""
import json
import os
import pathlib
import re
import subprocess
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
PART_V = HERE.parent
ROOT = PART_V.parent
PAPERS = ROOT / "_papers"
LEAN = pathlib.Path("E:/proyectos/godsil-gutman-lean")
EN, ES = HERE / "ghu_observability.tex", HERE / "ghu_observability_es.tex"

results = []


def record(cid, title, status, detail=""):
    results.append((cid, title, status, detail))


def read(p):
    return p.read_text(encoding="utf-8", errors="replace")


def strip_tex(s):
    return re.sub(r"(?<!\\)%.*", "", s)


def norm(s, source=False):
    """whitespace- and TeX-insensitive normalisation, for matching prose against a PDF extract.

    Two differences between a .tex quotation and a PDF text layer bit this gate on its first run
    and produced a FALSE failure, so both are handled here and neither silently:
      * operator spacing -- we write `$q+r$`, the extract reads `q + r`;
      * line-break hyphenation -- the extract reads `degen- eracy` where the page shows one word.
    De-hyphenation is applied ONLY to the source, because a hyphen in our own text is a real one.
    """
    s = re.sub(r"\\[a-zA-Z]+\s*", " ", s)
    s = re.sub(r"[{}$\\~^_]", " ", s)
    s = s.replace("--", "-").replace("''", '"').replace("``", '"')
    s = " ".join(s.split()).lower()
    if source:
        s = re.sub(r"-\s+", "", s)
    s = re.sub(r"\s*([+=/])\s*", r"\1", s)
    # punctuation spacing differs too: they set `[p; q, r; s]` where we write `[p;q,r;s]`, and a
    # stripped `\mathbf` leaves a space before the full stop. Both sides get the same treatment.
    s = re.sub(r"\s+([.,;:])", r"\1", s)
    s = re.sub(r"([,;:])\s+", r"\1", s)
    return s


# ---------------------------------------------------------------- G1: quotations
# Every `` '' in the paper, classified. "file" = the primary source it must appear in;
# None = it is our own sentence in quotation marks (a self-quote or a retracted claim).
QUOTES = [
    ("is a function of $q+r$ only",                       "hhk_0309088.txt"),
    ("does not select unique",                            "hhk_0309088.txt"),
    ("there remains a degeneracy among the theories of the lowest energy density",
                                                          "hhk_0309088.txt"),
    ("which is equivalent with the one of",               "KKKY_2502.08250.txt"),
    ("This holds for any representation",                 "KKKY_2502.08250.txt"),
    ("arrived from physics",                              "../paper/ghu_secondfixed.tex"),
    ("factors into three",                                None),
    ("Twisted trace",                                     None),
    ("the character of $\\bar R$ at $U_6$",               None),
    ("has a coset sector",                                None),
    ("The coset half is the only observable that sees charge conjugation", None),
    ("At the vacuum the coset half carries the whole Higgs curvature",     None),
    ("came from the physics",                             None),
    ("dimension",                                         None),
]


def check_quotes(_text=None):
    """G1 every quotation is classified, and every attributed one is IN its source"""
    s = _text if _text is not None else strip_tex(read(EN))
    found = [" ".join(q.split()) for q in re.findall(r"``(.{3,200}?)''", s, re.S)]
    bad, checked, unclassified = [], 0, []
    for q in found:
        hit = None
        for key, src in QUOTES:
            if norm(key) and norm(key) in norm(q):
                hit = (key, src)
                break
        if hit is None:
            unclassified.append(q[:70])
            continue
        key, src = hit
        if src is None:
            continue
        p = (ROOT / src[3:]) if src.startswith("../") else (PAPERS / src)
        text = norm(read(p), source=not src.endswith(".tex"))
        # An ellipsis is a CLAIM: that the omitted words sat between these fragments, in this
        # order. So the fragments are checked in order, not the quote as one lump.
        pos, ok = 0, True
        for frag in re.split(r"\\l?dots|\\ldots|…", q):
            n = norm(frag)
            if len(n) < 4:
                continue
            i = text.find(n, pos)
            if i < 0:
                bad.append("%r not found in %s (at or after the previous fragment)"
                           % (frag.strip()[:50], os.path.basename(str(p))))
                ok = False
                break
            pos = i + len(n)
        checked += ok
    status = "FAIL" if (bad or unclassified) else "PASS"
    detail = " | ".join(bad + ["UNCLASSIFIED: " + u for u in unclassified]) or \
        "%d quotations, %d attributed and verbatim in their source" % (len(found), checked)
    record("G1", "quotations verbatim in the cited paper", status, detail)


# ---------------------------------------------------------------- G2: AHMN's printed numbers
# Every equation of somebody else's that Part V cites by number, and the paper it must be in.
# `(3.11)` is deliberately ambiguous: AHMN and Haba-Yamashita each have one and Part V cites
# both, so it is satisfied by either -- the gate records the ambiguity instead of hiding it.
EQUATIONS = [
    ("(2.4)",  ["hhk_0309088.txt"]),
    ("(3.20)", ["hhk_0309088.txt"]),
    ("(4.3)",  ["hhk_0309088.txt"]),
    ("(4.13)", ["hhk_0309088.txt"]),
    ("(3.25)", ["AHMN_2312.08608.txt"]),
    ("(4.1)",  ["AHMN_2312.08608.txt"]),
    ("(3.11)", ["AHMN_2312.08608.txt", "hy_0401185.txt"]),
    ("(3.8)",  ["hy_0401185.txt"]),
    ("(3.9)",  ["hy_0401185.txt"]),
    ("(3.10)", ["hy_0401185.txt"]),
    ("(5.22)", ["KKKY_2502.08250.txt"]),
    ("(5.28)", ["KKKY_2502.08250.txt"]),
    ("(2.26)", ["cstar_1509.01636.txt"]),
    ("(6.7)",  ["cstar_1509.01636.txt"]),
]


def check_equations():
    """G2 every equation of theirs that we cite by number exists in their paper"""
    tex = strip_tex(read(EN))
    bad, checked, skipped = [], 0, 0
    for eq, srcs in EQUATIONS:
        if ("eq.~%s" % eq) not in tex and ("eqs.~%s" % eq) not in tex and \
                ("--%s" % eq) not in tex and ("(%s" % eq[1:]) not in tex:
            skipped += 1
            continue
        if not any(eq in read(PAPERS / s) for s in srcs):
            bad.append("%s cited but not in %s" % (eq, " or ".join(srcs)))
        else:
            checked += 1
    record("G2", "equations we cite by number exist in their paper", "FAIL" if bad else "PASS",
           " | ".join(bad) or "%d equation numbers verified in five primary sources (%d not cited)"
           % (checked, skipped))


# ---------------------------------------------------------------- G3: the Lean certificates
LEAN_NAMES = {
    "GHUBlindCount.lean": ["blind_iff_notch", "blind_iff_N_zero", "blind_l1_odd",
                           "card_shellA", "card_shellB", "card_shell"],
    "GHUCosetCensus.lean": ["label_move", "eqv_of_label", "coset_parity",
                            "card_classes", "card_cosetClasses"],
    "NotchCentreCharge.lean": ["V_ne_zero"],
}


def check_lean():
    """G3 every Lean name the prose cites exists, and neither brick contains `sorry`"""
    tex = strip_tex(read(EN)) + strip_tex(read(ES))
    bad, checked = [], 0
    for fn, names in LEAN_NAMES.items():
        p = LEAN / fn
        if not p.exists():
            bad.append("%s missing" % fn)
            continue
        src = read(p)
        if re.search(r"(?<![A-Za-z_])sorry(?![A-Za-z_])", src):
            bad.append("%s contains sorry" % fn)
        for n in names:
            if ("theorem %s" % n) not in src and ("lemma %s" % n) not in src \
                    and ("def %s" % n) not in src:
                bad.append("%s: %s not declared" % (fn, n))
            elif n.replace("_", "\\_") in tex or n in tex:
                checked += 1
    record("G3", "Lean names cited in the prose exist, no sorry", "FAIL" if bad else "PASS",
           " | ".join(bad) or "%d cited names declared; both bricks sorry-free" % checked)


# ---------------------------------------------------------------- G4: independent recomputation
def det(M):
    M = [row[:] for row in M]
    n = len(M)
    d = F(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None:
            return F(0)
        if piv != i:
            M[i], M[piv] = M[piv], M[i]
            d = -d
        d *= M[i][i]
        inv = M[i][i]
        for r in range(i + 1, n):
            if M[r][i] != 0:
                f = M[r][i] / inv
                M[r] = [x - f * y for x, y in zip(M[r], M[i])]
    return d


def schur(lam, xs):
    n = len(xs)
    L = list(lam) + [0] * (n - len(lam))
    mu = [L[i] + n - 1 - i for i in range(n)]
    num = det([[x ** m for m in mu] for x in xs])
    den = det([[x ** (n - 1 - j) for j in range(n)] for x in xs])
    return num / den


def check_blind_count():
    """G4 the blind class, recomputed from the bialternant at several exact points"""
    # D_lambda(t) = s_lambda(1,-1,t,1/t); lambda is blind iff it vanishes identically.
    # Independent of every script in part_v/: this evaluates the DEFINITION.
    pts = [F(2), F(3), F(5, 2), F(7, 3)]
    lam_range = [(l1, l2, l3, 0) for l1 in range(0, 13) for l2 in range(0, l1 + 1)
                 for l3 in range(0, l2 + 1)]
    blind = []
    for lam in lam_range:
        if all(schur(lam, [F(1), F(-1), t, 1 / t]) == 0 for t in pts):
            blind.append(lam)
    tex = strip_tex(read(EN))
    bad = []
    if len(lam_range) != 455:
        bad.append("multiplets in range: %d, paper says 455" % len(lam_range))
    if len(blind) != 47:
        bad.append("blind multiplets: %d, paper says 47" % len(blind))
    if any(l[0] % 2 == 0 for l in blind):
        bad.append("a blind multiplet with even l1 exists -- blind_l1_odd is false")
    # the shell count of Proposition 1, per odd l1
    import math
    for k in range(0, 6):
        want = math.ceil((k + 1) ** 2 / 2)
        got = sum(1 for l in blind if l[0] == 2 * k + 1)
        if want != got:
            bad.append("shell l1=%d: %d blind, Proposition 1 says %d" % (2 * k + 1, got, want))
    record("G4", "blind class recomputed from the bialternant", "FAIL" if bad else "PASS",
           " | ".join(bad) or "455 in range, 47 blind, every l1 odd, shells match ceil((k+1)^2/2)")


def check_census():
    """G5 the census of Proposition 4, recomputed by brute force over [p;q,r;s]"""
    bad = []
    for N in range(2, 11):
        seen = set()
        coset = set()
        for p in range(N + 1):
            for q in range(N + 1 - p):
                for r in range(N + 1 - p - q):
                    s = N - p - q - r
                    lab = (p + q, q + s)
                    seen.add(lab)
                    if (q + r) % 2 == 1:
                        coset.add(lab)
        if len(seen) != (N + 1) ** 2:
            bad.append("N=%d: %d classes, HHK says %d" % (N, len(seen), (N + 1) ** 2))
        if len(coset) != (N + 1) ** 2 // 2:
            bad.append("N=%d: %d with coset sector, Proposition 4 says %d"
                       % (N, len(coset), (N + 1) ** 2 // 2))
        if coset & (seen - coset):
            bad.append("N=%d: a class is both" % N)
    record("G5", "census recomputed by brute force, N=2..10", "FAIL" if bad else "PASS",
           " | ".join(bad) or "(N+1)^2 classes and floor((N+1)^2/2) with a coset sector, all N")


# ---------------------------------------------------------------- G6: the five mechanical gates
def check_five_gates():
    """G6 the five mechanical gates are green on both editions"""
    bad = []
    for script, args in (("check_numbers.py", []), ("check_structure.py", []),
                         ("check_provenance.py", []), ("check_render.py", ["--all"]),
                         ("check_render.py", ["--es", "--all"])):
        r = subprocess.run([sys.executable, str(HERE / script)] + args,
                           cwd=str(HERE), capture_output=True)
        if r.returncode:
            bad.append("%s %s exits %d" % (script, " ".join(args), r.returncode))
    lay = ROOT / "paper" / "check_layout.py"
    for pdf in ("ghu_observability.pdf", "ghu_observability_es.pdf"):
        r = subprocess.run([sys.executable, str(lay), pdf], cwd=str(HERE), capture_output=True)
        out = r.stdout.decode("utf-8", "replace")
        if "no page has an internal blank band" not in out:
            bad.append("check_layout on %s: %s" % (pdf, out.strip().splitlines()[-1:]))
    record("G6", "the five mechanical gates, both editions", "FAIL" if bad else "PASS",
           " | ".join(bad) or "numbers, structure, provenance, render EN+ES, layout EN+ES")


# ---------------------------------------------------------------- G7: nothing unpublished is cited
def check_no_unpublished():
    """G7 no citation to work that is not deposited, and no stale companion reference"""
    bad = []
    for f in (EN, ES):
        s = strip_tex(read(f))
        if "OrbitPair" in s:
            bad.append("%s cites the companion, which is not deposited" % f.name)
        bib = re.search(r"\\begin\{thebibliography\}(.*?)\\end\{thebibliography\}", s, re.S)
        for key, body in re.findall(r"\\bibitem\{([^}]*)\}(.*?)(?=\\bibitem|\Z)",
                                    bib.group(1) if bib else "", re.S):
            if "Mar" in body and "n," in body:                      # our own series
                if not re.search(r"10\.\d{4,9}/|arXiv:", body):
                    bad.append("%s: self-citation %s has no identifier" % (f.name, key))
    record("G7", "no citation to undeposited work", "FAIL" if bad else "PASS",
           " | ".join(bad) or "every self-citation carries a DOI; the companion is absent")


CHECKS = [check_quotes, check_equations, check_lean, check_blind_count, check_census,
          check_five_gates, check_no_unpublished]


def selftest():
    """Demonstrate that G1 can fail. A gate that has only ever passed is not a gate.

    Two mutations of the real text, each the kind of drift that actually happens: a word swapped
    inside a quotation, and a quotation nobody classified. Both must be caught.
    """
    base = strip_tex(read(EN))
    cases = [
        ("a word drifted inside a quotation",
         base.replace("is a function of $q+r$ only", "is a function of $q+r$ alone")),
        ("a new, unclassified quotation",
         base + "\n``a sentence nobody has classified, in quotation marks''\n"),
    ]
    ok = True
    print(" SELF-TEST of G1 -- each mutation must be caught")
    for name, text in cases:
        del results[:]
        check_quotes(text)
        status = results[0][2]
        print("   %-38s -> %s" % (name, status))
        ok &= status == "FAIL"
    del results[:]
    print("   verdict:", "the gate fires" if ok else "*** THE GATE DID NOT FIRE ***")
    print()
    return 0 if ok else 1


def main():
    if "--selftest" in sys.argv:
        return selftest()
    for fn in CHECKS:
        try:
            fn()
        except Exception as e:
            record(fn.__name__, fn.__doc__ or fn.__name__, "ERROR", "%s: %s" % (type(e).__name__, e))
    print("=" * 92)
    print(" PRE-PUBLICATION GATE  --  Part V, one pass against primary sources")
    print("=" * 92)
    nfail = nwarn = 0
    for cid, title, status, detail in results:
        mark = {"PASS": "  ok ", "FAIL": "FAIL ", "WARN": "warn ", "ERROR": "ERR  "}[status]
        nfail += status in ("FAIL", "ERROR")
        nwarn += status == "WARN"
        print(" [%s] %-4s %s" % (mark, cid, title))
        if detail:
            print("            %s" % detail)
    print("=" * 92)
    print(" %d checks | %d FAIL/ERROR | %d WARN" % (len(results), nfail, nwarn))
    print(" VERDICT:", "GREEN - safe to publish" if nfail == 0
          else "RED - do NOT publish, fix the above")
    print("=" * 92)
    return 1 if nfail else 0


if __name__ == "__main__":
    raise SystemExit(main())
