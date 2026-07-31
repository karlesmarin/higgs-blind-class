#!/usr/bin/env python3
"""ahmn_anchor.py - reproduce AHMN's PUBLISHED one-loop potential from the two Schur characters.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Akamatsu, Hirose, Maru, Nago, "Electroweak Symmetry Breaking in Two Higgs Doublet Model from 6D
Gauge-Higgs Unification on T^2/Z_2", arXiv:2312.08608, write their one-loop effective potential as
a winding sum whose coefficients have the form {A + B(-1)^{k_2}}:

  eq (3.25)  fermion, the 35:   charges 2, 3/2, 1, 1/2  ->  {1}, {1+(-1)^k2}, {3+(-1)^k2}, {3+3(-1)^k2}
  eq (3.11)  gauge, antiperiodic:  charge 1/2 -> 2{1+(-1)^k2},  charge 1 -> {1}
  eq (4.1)   total = 3 x (3.25) - (3.11)

Our claim (part_v/HANDOFF.md) is that the winding parity IS the O(4) component label, so the whole
potential is two Schur specialisations of one partition:

  Sigma_lambda(t) = s_lambda(1, 1,t,1/t)   (k_2 even, identity component)
  D_lambda(t)     = s_lambda(1,-1,t,1/t)   (k_2 odd,  reflection coset  = Part IV's object)

which predicts, with no free parameter and nothing fitted,

  A = (Sigma + D)/2      B = (Sigma - D)/2      at each charge = exponent/2.

This script checks that against their printed numbers. The one adjustment used is the one THEY
state in the text: the gauge field carries antiperiodic boundary conditions, which multiply the
winding amplitude by (-1)^{k_2} and therefore exchange A and B.
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fibre import schur, EVEN, ODD

# ---------------------------------------------------------------- what they printed
AHMN_FERMION_35 = {4: (1, 0), 3: (1, 1), 2: (3, 1), 1: (3, 3)}     # exponent -> (A, B)
AHMN_GAUGE_15 = {2: (1, 0), 1: (2, 2)}                              # antiperiodic
TOTAL_41 = {4: (3, 0), 3: (3, 3), 2: (8, 3), 1: (7, 7)}             # eq (4.1)


def halves(lam):
    """(A, B) per exponent, from the two Schur specialisations"""
    S, D = schur(lam, EVEN), schur(lam, ODD)
    out = {}
    for e in sorted({abs(k) for k in list(S) + list(D)}):
        if e == 0:
            continue                      # the alpha-independent term; absent from their sum
        s, d = S.get(e, 0), D.get(e, 0)
        assert (s + d) % 2 == 0 and (s - d) % 2 == 0, "A, B must be integers"
        out[e] = ((s + d) // 2, (s - d) // 2)
    return S, D, out


def dim(S):
    return sum(S.values())


def main():
    ok = True

    def check(name, good, detail=""):
        nonlocal ok
        ok = ok and good
        print(("  PASS " if good else "  FAIL ") + name + ("  --  " + detail if detail else ""))

    print("AHMN arXiv:2312.08608 reproduced from two Schur characters\n")

    # ---- the 35, eq (3.25): the fermion, periodic ---------------------------------
    S, D, AB = halves([4, 0, 0, 0])
    check("the 35 has dimension 35", dim(S) == 35, "Sigma(1) = %d" % dim(S))
    got = {e: AB[e] for e in AHMN_FERMION_35}
    check("eq (3.25), the 35: every (A,B) reproduced", got == AHMN_FERMION_35,
          " ".join("q=%s:%s%s" % (e / 2, got[e], "" if got[e] == AHMN_FERMION_35[e] else "!=")
                   for e in sorted(AHMN_FERMION_35, reverse=True)))

    # ---- the 15, eq (3.11): the gauge field, ANTIPERIODIC -------------------------
    S15, D15, AB15 = halves([2, 1, 1, 0])
    check("the adjoint has dimension 15", dim(S15) == 15, "Sigma(1) = %d" % dim(S15))
    raw = {e: AB15[e] for e in AHMN_GAUGE_15}
    twisted = {e: (b, a) for e, (a, b) in raw.items()}     # antiperiodic: x (-1)^{k_2}
    check("eq (3.11), the adjoint, after the antiperiodic twist THEY state",
          twisted == AHMN_GAUGE_15,
          "raw %s -> twisted %s" % (raw, twisted))

    # ---- eq (4.1): their own total, as an internal consistency check --------------
    tot = {}
    for e in set(list(AHMN_FERMION_35) + list(AHMN_GAUGE_15)):
        fa, fb = AHMN_FERMION_35.get(e, (0, 0))
        ga, gb = AHMN_GAUGE_15.get(e, (0, 0))
        tot[e] = (3 * fa - ga, 3 * fb - gb)               # colour factor 3, gauge enters with -
    check("eq (4.1) = 3 x (3.25) - (3.11), their own arithmetic", tot == TOTAL_41, str(tot))

    print("\n  charge |  Sigma  D  |  A  B (ours) |  A  B (AHMN)")
    for e in sorted(AHMN_FERMION_35, reverse=True):
        print("   %4s  | %5d %3d |   %d  %d       |   %d  %d"
              % (e / 2, schur([4, 0, 0, 0], EVEN).get(e, 0), schur([4, 0, 0, 0], ODD).get(e, 0),
                 AB[e][0], AB[e][1], *AHMN_FERMION_35[e]))

    print("\n" + ("ALL CHECKS PASS -- twelve published numbers, nothing fitted"
                  if ok else "*** SOME CHECK FAILED ***"))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
