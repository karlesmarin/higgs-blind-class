# 🙈 What the Higgs Potential Cannot See

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21727095-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.21727095)
[![License](https://img.shields.io/badge/License-Apache_2.0-B5530F)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean_4-two_bricks,_sorry--free-2C2C2C?logo=lean)](lean/)
[![Gates](https://img.shields.io/badge/gates-6_green-1B6F8C)](scripts/gate_partv.py)
[![Language](https://img.shields.io/badge/paper-EN_%2B_ES-1B6F8C)](paper/)

**Bulk matter that cannot help select a boundary condition.**

**📄 Paper (EN + ES), both Lean certificates and every verification script on Zenodo → https://doi.org/10.5281/zenodo.21727095**

> ### 📚 Part **V** of a series
> - **Part I — *Anomaly- and Tadpole-Compatible Fermion Completion of 6D SU(4) GHU***
>   → [github.com/karlesmarin/ghu-su4-completion](https://github.com/karlesmarin/ghu-su4-completion) · [Zenodo 10.5281/zenodo.21432625](https://doi.org/10.5281/zenodo.21432625)
> - **Part II — *Three Gates to a Quark Generation***
>   → [github.com/karlesmarin/su4-sm-cell-criterion](https://github.com/karlesmarin/su4-sm-cell-criterion) · [Zenodo 10.5281/zenodo.21432627](https://doi.org/10.5281/zenodo.21432627)
> - **Part III — *A Centre-Charge Selection Rule for the Wilson-Line Potential***
>   → [github.com/karlesmarin/centre-parity-selection](https://github.com/karlesmarin/centre-parity-selection) · [Zenodo 10.5281/zenodo.21438226](https://doi.org/10.5281/zenodo.21438226)
> - **Part IV — *Schur Functions at (1,−1,t,t⁻¹)***
>   → [github.com/karlesmarin/schur-nonidentity-o4](https://github.com/karlesmarin/schur-nonidentity-o4) · [Zenodo 10.5281/zenodo.21463000](https://doi.org/10.5281/zenodo.21463000)
> - **Part V — *What the Higgs Potential Cannot See*** (this repo)

The one-loop Wilson-line potential of the 6D SU(4) model is **one operator traced twice** — a
dimension and an index — and the discrete boundary-condition sign multiplies the index alone.
Part III's translation matrix U₆ = P₂P₀⁻¹ has det = −1, so one trip round the compact
direction applies a **reflection**: the even-winding half of the potential is a character on the
identity component of O(4), the odd-winding half a character on the reflection coset.

```
Σ_λ(t) = s_λ(1, 1, t, t⁻¹)        the identity component — a graded dimension
D_λ(t) = s_λ(1,−1, t, t⁻¹)        the reflection coset   — an index
```

Σ_λ is a graded dimension and cannot cancel; D_λ is an index and can. That is
the whole paper.

## 🧭 What is in it

| | |
|---|---|
| **The anchor** | The published one-loop coefficients {A + B(−1)^k₂} of AHMN are exactly (Σ ± D)/2 — twelve printed numbers, nothing fitted. Two further published potentials follow from the same mode counts. |
| **The theorem** | (λ,η) ~ (λ*, η(−1)^λ₁) is an observational identity, and the boundary sign η = η₀η₁ is unobservable **exactly** on Part IV's vanishing class. |
| **The count** | The blind class is ⌈(k+1)²/2⌉ at λ₁ = 2k+1, and **never** for λ₁ even — machine-checked, and chained to the certificate Part III already carried. |
| **The census** | Invisibility has a second, disjoint cause: ⌊(N+1)²/2⌋ of the (N+1)² boundary-condition classes have a coset sector at all — machine-checked for **every** N. |
| **One step past a multiplet** | If the non-blind multiplets of a content share one effective sign, the content is blind iff each of them is: *collective blindness requires sign frustration*. |

## 🔍 Reproducing it

```bash
python scripts/ahmn_anchor.py        # the twelve published numbers, nothing fitted
python scripts/fibre_eta.py          # 910 pairs -> 470 observational classes, 0 unexplained
python scripts/verify_formulas.py    # the box identities, exact integer arithmetic
python scripts/gate_partv.py         # the whole-artifact gate: 7 checks, primary sources
python scripts/gate_partv.py --selftest   # and the proof that the gate can fail
```

Every number printed in the paper is greppable in `outputs/`, and `scripts/check_numbers.py` is the
gate that enforces it.

## 🧰 A reusable tool: `check_provenance.py`

The gate that found the defect this paper had carried for two sessions, and it is not specific to this
series. Four gates read *our* paper; none of them opens a paper we **cite** — which is exactly where a
status word drifts. It checks that no sentence attributes a proof to a source that claims none, that
every self-citation carries a DOI (a missing one is a citation to something undeposited), and it warns
when an unpublished newer draft of a cited source exists, because that is the version one remembers.

```
python scripts/check_provenance.py                  # 0 findings on this paper
python scripts/check_provenance.py --against HEAD~1 # 6 on the text before the fix: it fires
```

Point `SELF` at your own series and it works on any paper that cites its own earlier parts.

## 🔒 The gates

Six, and they are the reason the paper says what it says:

- `check_numbers.py` — every displayed number backed by an archived run;
- `check_structure.py` — labels, references, and **EN/ES structural parity**;
- `check_layout.py` — no page with a blank band;
- `check_render.py` — the rendered page, and text that overlaps text;
- `check_provenance.py` — **the papers we cite**: no proof attributed to a source that claims none, and no self-citation without a DOI;
- `gate_partv.py` — one pass over the whole artifact against primary sources, and it is validated by mutation.

## 📐 Lean 4

Both bricks are `sorry`-free and depend only on `propext`, `Classical.choice`, `Quot.sound`.

- [`lean/GHUBlindCount.lean`](lean/GHUBlindCount.lean) — the blind class in partition coordinates, its dictionary to Part III's Dynkin criterion, and the count.
- [`lean/GHUCosetCensus.lean`](lean/GHUCosetCensus.lean) — the boundary-condition census: the block pair is a **complete** class invariant, hence (N+1)² classes and ⌊(N+1)²/2⌋ with a coset sector.
- [`lean/NotchCentreCharge.lean`](lean/NotchCentreCharge.lean) — Part III's brick, included so the chain compiles on its own.

## ⚖️ Honesty ledger

Part IV states its closed form as **verified and not proved**, and everything here that rests on it
inherits exactly that standing — the paper says so at first use and again in its scope section. What
does *not* depend on it is the criterion that identity computes, which is Part III's theorem: the
blind class, its count and its Lean certificate stand regardless. That the relation above generates
*all* observational collisions is verified over 910 pairs and **not proved**. A claim of an earlier
draft — that the coset half is the only observable that sees charge conjugation — is false, and is
**retracted inside the paper** rather than removed from it.

## 📖 Citation

```bibtex
@misc{marin2026higgsblind,
  author = {Mar\'in Mu\~noz, Carles},
  title  = {What the Higgs Potential Cannot See: Bulk Matter That Cannot Help
            Select a Boundary Condition (Part V)},
  year   = {2026},
  doi    = {10.5281/zenodo.21727095},
  note   = {Part V of the 6D SU(4) gauge-Higgs unification series}
}
```

Apache 2.0. Carles Marín Muñoz, independent researcher — with Claude (Anthropic) as AI research
assistant.
