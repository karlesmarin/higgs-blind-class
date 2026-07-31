#!/usr/bin/env python3
"""check_provenance.py - the fifth gate: does the paper we cite say what we say it says?

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

The other four gates all read THIS paper. check_numbers asks whether every printed number is backed
by an archived run, check_structure whether every label resolves, check_layout where the floats land,
check_render what the page actually looks like. None of them opens a paper we CITE -- and that is
where Part V was wrong for two sessions and four green gates:

  * the text said "Part IV PROVED a closed form", while the published Part IV states that identity as
    \\begin{observation}[verified, not proved] and repeats it in its own ledger;
  * the promotion to Theorem existed only in an UNPUBLISHED draft, resting on a companion paper;
  * that companion was cited as "Zenodo (2026)" with NO DOI, because it is not deposited at all.

A status word is not prose. "Theorem", "verified" and "open" are the load-bearing vocabulary of this
series, and an attribution that upgrades one of them is a false claim about somebody else's work --
here, about our own earlier work, which is the easiest kind to get wrong and the least excusable.

WHAT THIS GATE CAN AND CANNOT DO. It only checks citations to OUR OWN series, because only for those
do we hold the source .tex and know the conventions. It cannot read a third-party paper. So it is not
a proof of correct attribution; it is the discipline that every proof-attribution to our own work has
been put next to that work's own status word by a human, and that the exceptions are visible in this
file instead of being forgotten.

Three checks:

  1. SELF-CITATION HAS A DOI. A bibliography entry for our own series with no DOI and no arXiv id is
     a citation to something unpublished. That is what "Zenodo (2026)" was hiding.
  2. NO SILENT UPGRADE. If a source declares anything "verified, not proved", then every sentence of
     ours that attributes a proof to that source must be on the ALLOW list, with a reason.
  3. THE PUBLISHED FILE IS THE ONE READ. If an unpublished newer draft of a cited source exists, say
     so out loud: it is the draft's status word one tends to remember.

VALIDATED, and it has to be, because a guard whose ability to fire was never demonstrated is the
error this gate exists to prevent (it has already happened twice here: check_numbers matched
substrings, and check_render's page picker silently selected nothing and exited green). Run

    python check_provenance.py --against HEAD~1

which extracts the pre-fix text from git and audits that instead. Against the English text as it
stood before 2026-07-31 it reports six findings and exits 1:

    FAIL: \\bibitem{OrbitPair} carries no DOI and no arXiv id
    FAIL: attributes a proof to PartIV ... "Part~IV computed $\\Dl$ and proved a closed form for it:"
    FAIL: ... "Part~IV proves $\\Dl=\\zeta\\chi\\chi\\chi$ or $0$;"
    FAIL: ... "it does so because Part~IV proved the coefficients carry one sign."
    FAIL: ... "Everything Part~IV proved is a statement about that function, uniform in it."

(and, at that revision, the Spanish edition was still a stub with no bibliography, which the
empty-work-list guard reports as a failure instead of passing silently). On the current text: 0.
It fires, and it fires on the four sentences that were actually wrong and on none of the many
sentences where OUR proof legitimately USES Part IV's identity.

Usage:  python check_provenance.py                audit both editions as they stand
        python check_provenance.py --against REV  audit the versions in git revision REV
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TEXS = ["ghu_observability.tex", "ghu_observability_es.tex"]

# our own series: bibliography key -> the PUBLISHED source, relative to this directory
SELF = {
    "PartIII":   "../../paper/ghu_notch.tex",
    "PartIV":    "../../paper/ghu_secondfixed.tex",
    "OrbitPair": "../../../orbit-pair/paper/orbit_pair.tex",
}

# unpublished drafts of the same sources: read for nothing, reported so nobody quotes them by memory
DRAFTS = {
    "PartIV": "../../_pending_v5/ghu_secondfixed_V5DRAFT.tex",
}

# how each key is named in running prose, when the sentence does not carry a \cite
PROSE = {
    "PartIII": [r"Part~III", r"Parte~III"],
    "PartIV":  [r"Part~IV", r"Parte~IV"],
}

VERB = r"(?:proves?|proved|proving|demuestra|demostr(?:o|ó|ado|ada|aron|amos))"
# The verb has to be GOVERNED by the source: "Part IV proved X", or "X is proved in [Part IV]".
# A bare "proof" anywhere in the sentence is not an attribution -- most of them are OUR proofs, which
# legitimately USE the cited identity. Getting this wrong in the loose direction is what makes a gate
# get switched off.
def attribution(src_pat):
    return [re.compile(r"%s[^.]{0,40}?\b%s\b" % (src_pat, VERB), re.IGNORECASE),
            re.compile(r"\b%s\b[^.]{0,40}?(?:in|by|en|por)\s+%s" % (VERB, src_pat), re.IGNORECASE)]
UNPROVED = re.compile(r"verified,\s*not\s*proved|verificad[oa],\s*no\s*demostrad[oa]", re.IGNORECASE)
HEDGE = re.compile(r"verified,\s*not\s*proved|verificad[oa],?\s*(y\s*)?no\s*demostrad[oa]"
                   r"|not\s*proved|sin\s*demostrar|no\s*demostrad[oa]", re.IGNORECASE)
IDENT = re.compile(r"10\.\d{4,9}/|arXiv:|hep-ph/|hep-th/|math/|doi:", re.IGNORECASE)
BIBITEM = re.compile(r"\\bibitem\{([^}]*)\}(.*?)(?=\\bibitem\{|\\end\{thebibliography\})", re.S)
STATUS = re.compile(r"\\begin\{(theorem|proposition|observation|conjecture)\}(\[[^\]]*\])?"
                    r"(\\label\{([^}]*)\})?")

# Sentences that DO attribute a proof to a source with an unproved status somewhere, and are correct
# anyway, each with the reason it is correct. Anything not here is a finding.
ALLOW = [
    ("PartIV", "the criterion the identity computes",
     "the criterion is Part III's theorem; Part IV's ledger says so itself"),
    ("PartIII", "proves the classification outright",
     "Part III's vanishing classification is a Theorem there, and Part IV's ledger credits it as such"),
    ("PartIII", "Part~III's theorem in Dynkin labels",
     "same object, same standing, and GHUBlindCount.lean certifies the dictionary"),
]


def read(path, rev=None, gitroot=None):
    if rev is None:
        return open(os.path.join(HERE, path), encoding="utf-8").read()
    rel = os.path.relpath(os.path.join(HERE, path), gitroot).replace(os.sep, "/")
    out = subprocess.run(["git", "show", "%s:%s" % (rev, rel)], cwd=gitroot,
                         capture_output=True)
    if out.returncode:
        return None
    return out.stdout.decode("utf-8", "replace")


def strip(s):
    return re.sub(r"(?<!\\)%.*", "", s)


def sentences(s):
    s = strip(s)
    # environment delimiters are not words: \begin{proof} must not read as the noun "proof"
    s = re.sub(r"\\(begin|end)\{[^}]*\}", " ", s)
    s = re.sub(r"\s+", " ", s)
    return [t.strip() for t in re.split(r"(?<=[.:;])\s+", s) if t.strip()]


def source_status(key, path, rev, gitroot):
    """What status words does the cited paper itself use?"""
    s = read(path, rev, gitroot)
    if s is None:
        return None
    s = strip(s)
    objects = []
    for m in STATUS.finditer(s):
        env, opt, _, lab = m.groups()
        objects.append((env, (opt or "").strip("[]"), lab or ""))
    unproved = [o for o in objects if UNPROVED.search(o[1])]
    return dict(path=path, objects=objects, unproved=unproved,
                says_unproved=bool(unproved) or bool(UNPROVED.search(s)))


def audit(tex, rev, gitroot):
    s = read(tex, rev, gitroot)
    if s is None:
        print("   %s : not in %s" % (tex, rev))
        return 1
    print("== %s" % tex)
    bib = dict((k, v) for k, v in BIBITEM.findall(strip(s)))
    bad = 0

    cited = [k for k in SELF if k in bib]
    print("   self-citations found : %d %s" % (len(cited), cited or ""))
    if not cited:
        # an empty work-list is not a pass. That failure mode has already cost us one gate.
        print("   FAIL: no \\bibitem of our own series resolved -- either the keys in SELF are stale,")
        print("         or this file has no bibliography yet (a stub). Either way nothing was checked.")
        return 1

    for key in cited:
        if not IDENT.search(bib[key]):
            print("   FAIL: \\bibitem{%s} carries no DOI and no arXiv id" % key)
            print("         -> %s" % " ".join(bib[key].split())[:110])
            print("         a self-citation with no identifier is a citation to something unpublished")
            bad += 1

    for key in cited:
        st = source_status(key, SELF[key], rev, gitroot)
        if st is None:
            print("   FAIL: %s cited but its source file is missing (%s)" % (key, SELF[key]))
            bad += 1
            continue
        tag = "declares SOMETHING verified-and-not-proved" if st["says_unproved"] else "all statuses proved"
        print("   %-10s %-46s %s" % (key, os.path.basename(st["path"]), tag))
        for env, opt, lab in st["unproved"]:
            print("              its own words: \\begin{%s}[%s] %s" % (env, opt, lab))
        if key in DRAFTS and os.path.exists(os.path.join(HERE, DRAFTS[key])):
            print("              NOTE: an unpublished draft exists (%s)." % DRAFTS[key])
            print("                    The status above is the PUBLISHED one. Quote that one.")
        if not st["says_unproved"]:
            continue

        pats = []
        for src in [r"\\cite\{[^}]*%s[^}]*\}" % key] + PROSE.get(key, []):
            pats += attribution(src)
        hits = []
        for sent in sentences(s):
            if not any(p.search(sent) for p in pats):
                continue
            if HEDGE.search(sent):
                continue                       # the sentence carries the qualifier itself
            if any(k == key and frag in sent for k, frag, _ in ALLOW):
                continue
            hits.append(sent)
        for h in hits:
            print("   FAIL: attributes a proof to %s, which does not claim one:" % key)
            print("         \"%s\"" % (h[:150] + ("..." if len(h) > 150 else "")))
            bad += 1
        print("              proof-attributing sentences: %d flagged, %d on the ALLOW list"
              % (len(hits), sum(1 for k, _, _ in ALLOW if k == key)))
    return bad


def main():
    rev = None
    if "--against" in sys.argv:
        rev = sys.argv[sys.argv.index("--against") + 1]
    gitroot = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=HERE,
                             capture_output=True).stdout.decode().strip()
    print("check_provenance: the status words of the papers we cite%s"
          % ("" if rev is None else "  [reading revision %s]" % rev))
    print()
    bad = 0
    for tex in TEXS:
        bad += audit(tex, rev, gitroot)
        print()
    print("== summary")
    print("   findings: %d" % bad)
    if not bad:
        print("   every proof attributed to our own series matches that paper's own status word,")
        print("   and every self-citation carries an identifier.")
    return bad


if __name__ == "__main__":
    raise SystemExit(1 if main() else 0)
