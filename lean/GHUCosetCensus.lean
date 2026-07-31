/-
  GHUCosetCensus.lean
  Author: Carles Marín <karlesmarin@gmail.com>  (Claude, Anthropic, as AI assistant).

  Machine-checked brick for Part V of the SU(4) 6D gauge-Higgs unification study:
  the OTHER half of the invisibility dichotomy.  `GHUBlindCount.lean` counts the
  matter that cannot see the boundary-condition sign; this file counts the
  boundary conditions that have no place for it to live.

  Setting.  Haba, Hosotani and Kawamura (hep-ph/0309088) classify the boundary
  conditions of `SU(N)` gauge theory on `S^1/Z_2` by the block sizes `[p; q, r; s]`
  of two commuting parity matrices `P_0, P_1`: `p` basis vectors with
  `(P_0,P_1) = (+,+)`, then `q` with `(+,-)`, `r` with `(-,+)`, `s` with `(-,-)`,
  and `p + q + r + s = N`.  Boundary conditions related by a gauge transformation
  that shifts the Wilson line are physically the same theory, and the move that
  generates that equivalence is

      [p; q, r; s]  ~  [p-1; q+1, r+1; s-1].

  Part V needs one number about that classification.  The winding element is
  `U = P_0 P_1`, `det U = (-1)^(q+r)`, so the theory has a reflection-coset sector
  -- the only place where the boundary sign `eta` can act at all -- exactly when
  `q + r` is odd.  The paper stated the census as a sweep over `N = 2..10`.  Here
  it is a theorem for every `N`.

  What is certified.

  * `label`   : the pair `(p+q, q+s)`, that is `(#(P_0 = +1), #(P_1 = -1))`.
  * `label_move`, `rank_move` : the move changes neither the label nor `N`.
  * `eqv_of_label` : the converse, which is the half that has content -- two
    boundary conditions with the same `N` and the same label are joined by a chain
    of moves.  So the label is a COMPLETE invariant, and the classes are exactly
    the pairs `(u,v)` with `u, v <= N`: HHK's `(N+1)^2`, recovered.
  * `coset_parity` : `q + r` and `u + v + N` have the same parity, so "admits a
    coset sector" is a property of the class and not of the representative.
  * `card_cosetClasses` : **the census**.  Of the `(N+1)^2` classes, exactly
    `floor((N+1)^2 / 2)` admit a coset sector -- for every `N`, not for `N <= 10`.

  Sorry-free.  `#print axioms` at the bottom.
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace GHU

open Finset

/-! ### Boundary conditions, the move, and the label -/

/-- A boundary condition in HHK's block form `[p; q, r; s]`. -/
structure BC where
  p : ℕ
  q : ℕ
  r : ℕ
  s : ℕ
deriving DecidableEq, Repr

/-- `N`: the rank of the gauge group, `p + q + r + s`. -/
def rank (x : BC) : ℕ := x.p + x.q + x.r + x.s

/-- The label `(p+q, q+s)` = `(#(P₀ = +1), #(P₁ = -1))`. -/
def label (x : BC) : ℕ × ℕ := (x.p + x.q, x.q + x.s)

/-- Whether the class has a reflection-coset sector: `det U = (-1)^(q+r) = -1`. -/
def hasCoset (x : BC) : Prop := (x.q + x.r) % 2 = 1

instance (x : BC) : Decidable (hasCoset x) := by unfold hasCoset; infer_instance

/-- One class move, `[p; q, r; s] → [p-1; q+1, r+1; s-1]`, stated without
subtraction. -/
inductive Move : BC → BC → Prop
  | intro (p q r s : ℕ) : Move ⟨p + 1, q, r, s + 1⟩ ⟨p, q + 1, r + 1, s⟩

/-- Boundary conditions in the same equivalence class. -/
def Equivalent : BC → BC → Prop := Relation.EqvGen Move

theorem rank_move {x y : BC} (h : Move x y) : rank x = rank y := by
  cases h; simp only [rank]; omega

theorem label_move {x y : BC} (h : Move x y) : label x = label y := by
  cases h; simp only [label, Prod.mk.injEq]; omega

theorem rank_eqv {x y : BC} (h : Equivalent x y) : rank x = rank y := by
  induction h with
  | rel _ _ h => exact rank_move h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem label_eqv {x y : BC} (h : Equivalent x y) : label x = label y := by
  induction h with
  | rel _ _ h => exact label_move h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### The label is a complete invariant

The direction with content.  If `x` and `y` have the same `N` and the same label,
walk `x` towards `y` one move at a time.  The step is legal because the label
forces the room for it: if `x.q < y.q` then `x.p = y.p + (y.q - x.q) ≥ 1` and
`x.s = y.s + (y.q - x.q) ≥ 1`. -/

private theorem eqv_of_label_aux (d : ℕ) :
    ∀ x y : BC, rank x = rank y → label x = label y → y.q = x.q + d → Equivalent x y := by
  induction d with
  | zero =>
    intro x y hr hl hq
    obtain ⟨p, q, r, s⟩ := x
    obtain ⟨p', q', r', s'⟩ := y
    simp only [label, Prod.mk.injEq] at hl
    simp only [rank] at hr
    dsimp only at hq
    have : (⟨p, q, r, s⟩ : BC) = ⟨p', q', r', s'⟩ := by simp only [BC.mk.injEq]; omega
    exact this ▸ Relation.EqvGen.refl _
  | succ d ih =>
    intro x y hr hl hq
    obtain ⟨p, q, r, s⟩ := x
    simp only [label, Prod.mk.injEq] at hl
    simp only [rank] at hr
    dsimp only at hq
    obtain ⟨hp, hs⟩ := hl
    -- the move is legal: the label leaves room for it, `p ≥ 1` and `s ≥ 1`
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
    refine Relation.EqvGen.trans _ ⟨a, q + 1, r + 1, b⟩ _
      (Relation.EqvGen.rel _ _ (Move.intro a q r b)) (ih _ y ?_ ?_ ?_)
    · simp only [rank]; omega
    · simp only [label, Prod.mk.injEq]; omega
    · dsimp only; omega

/-- **The label is complete.**  Same `N`, same label ⟹ joined by moves. -/
theorem eqv_of_label {x y : BC} (hr : rank x = rank y) (hl : label x = label y) :
    Equivalent x y := by
  rcases le_total x.q y.q with h | h
  · exact eqv_of_label_aux (y.q - x.q) x y hr hl (by omega)
  · exact Relation.EqvGen.symm _ _
      (eqv_of_label_aux (x.q - y.q) y x hr.symm hl.symm (by omega))

/-- The label of a rank-`N` boundary condition lies in the `(N+1) × (N+1)` grid. -/
theorem label_le (x : BC) : (label x).1 ≤ rank x ∧ (label x).2 ≤ rank x := by
  simp only [label, rank]; omega

/-- ... and every point of the grid is a label: the explicit representative. -/
def witness (N u v : ℕ) : BC :=
  if u + v ≤ N then ⟨u, 0, N - u - v, v⟩ else ⟨N - v, u + v - N, 0, N - u⟩

theorem witness_rank {N u v : ℕ} (hu : u ≤ N) (hv : v ≤ N) : rank (witness N u v) = N := by
  unfold witness; split <;> simp only [rank] <;> omega

theorem witness_label {N u v : ℕ} (hu : u ≤ N) (hv : v ≤ N) : label (witness N u v) = (u, v) := by
  unfold witness; split <;> simp only [label, Prod.mk.injEq] <;> omega

/-- **`hasCoset` is a class function.**  `q + r` is not invariant under the move,
but its parity is, and the parity is read off the label and `N`. -/
theorem coset_parity (x : BC) :
    (x.q + x.r) % 2 = ((label x).1 + (label x).2 + rank x) % 2 := by
  simp only [label, rank]; omega

theorem hasCoset_iff (x : BC) :
    hasCoset x ↔ ((label x).1 + (label x).2 + rank x) % 2 = 1 := by
  rw [hasCoset, coset_parity]

/-! ### Counting the classes -/

/-- The classes of rank `N`, as their labels: the `(N+1) × (N+1)` grid. -/
def classes (N : ℕ) : Finset (ℕ × ℕ) := (range (N + 1)) ×ˢ (range (N + 1))

/-- The classes that admit a reflection-coset sector. -/
def cosetClasses (N : ℕ) : Finset (ℕ × ℕ) :=
  (classes N).filter (fun c => (c.1 + c.2 + N) % 2 = 1)

/-- HHK's count, recovered from the label. -/
theorem card_classes (N : ℕ) : (classes N).card = (N + 1) ^ 2 := by
  simp only [classes, card_product, card_range]; ring

/-- Every rank-`N` boundary condition has its label in the grid ... -/
theorem label_mem_classes {x : BC} {N : ℕ} (h : rank x = N) : label x ∈ classes N := by
  have := label_le x
  simp only [classes, mem_product, mem_range]
  omega

/-- ... and every point of the grid comes from one.  With `eqv_of_label` (same
label ⟹ same class) this is the bijection: classes of rank `N` ↔ `classes N`. -/
theorem exists_of_mem_classes {N : ℕ} {c : ℕ × ℕ} (h : c ∈ classes N) :
    ∃ x : BC, rank x = N ∧ label x = c := by
  simp only [classes, mem_product, mem_range] at h
  exact ⟨witness N c.1 c.2, witness_rank (by omega) (by omega),
    by rw [witness_label (by omega) (by omega)]⟩

/-- How many numbers below `N+1` have a given residue mod `2`. -/
theorem card_mod_range (N j : ℕ) (hj : j < 2) :
    ((range (N + 1)).filter (fun v => v % 2 = j)).card = (N + 2 - j) / 2 := by
  induction N with
  | zero =>
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> decide
  | succ n ih =>
    rw [range_add_one, filter_insert]
    by_cases h : (n + 1) % 2 = j
    · rw [if_pos h, card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg h]
      omega

/-- ... and the complementary count. -/
theorem card_mod_range_not (N j : ℕ) (hj : j < 2) :
    ((range (N + 1)).filter (fun v => ¬ v % 2 = j)).card = (N + 1) - (N + 2 - j) / 2 := by
  have h := card_filter_add_card_filter_not (s := range (N + 1)) (fun v => v % 2 = j)
  rw [card_mod_range N j hj, card_range] at h
  omega

/-- The census in the form `filter_product_card` wants it. -/
theorem cosetClasses_eq (N : ℕ) :
    cosetClasses N =
      (classes N).filter (fun c => (c.1 % 2 = 0) = (c.2 % 2 = (N + 1) % 2)) := by
  unfold cosetClasses
  refine filter_congr ?_
  intro c _
  simp only [eq_iff_iff]
  omega

/-- **Proposition (Part V), the geometric half of the dichotomy.**  Of the
`(N+1)^2` equivalence classes of boundary conditions, exactly `⌊(N+1)^2/2⌋` admit
a reflection-coset sector -- and in the other `⌈(N+1)^2/2⌉` the boundary sign is
invisible to *every* multiplet, for reasons that have nothing to do with matter. -/
theorem card_cosetClasses (N : ℕ) : (cosetClasses N).card = (N + 1) ^ 2 / 2 := by
  have hsplit := filter_product_card (range (N + 1)) (range (N + 1))
    (fun u : ℕ => u % 2 = 0) (fun v : ℕ => v % 2 = (N + 1) % 2)
  rw [cosetClasses_eq, classes, hsplit]
  have h0 := card_mod_range N 0 (by omega)
  have h0' := card_mod_range_not N 0 (by omega)
  rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
  · -- `N` even: the coset classes are the `(u,v)` with `u + v` odd.
    -- rows: `m+1` even values and `m` odd ones, so `(m+1)·m + m·(m+1) = 2m(m+1)`.
    have hj : (2 * m + 1) % 2 = 1 := by omega
    have h1 := card_mod_range (2 * m) 1 (by omega)
    have h1' := card_mod_range_not (2 * m) 1 (by omega)
    rw [hj, h0, h0', h1, h1']
    have d1 : (2 * m + 2 - 0) / 2 = m + 1 := by omega
    have d2 : (2 * m + 2 - 1) / 2 = m := by omega
    rw [d1, d2]
    have d3 : 2 * m + 1 - (m + 1) = m := by omega
    have d4 : 2 * m + 1 - m = m + 1 := by omega
    rw [d3, d4]
    have e : (m + 1) * m + m * (m + 1) = 2 * (m * m) + 2 * m := by ring
    have e2 : (2 * m + 1) ^ 2 = 4 * (m * m) + 4 * m + 1 := by ring
    rw [e, e2]
    omega
  · -- `N` odd: the coset classes are the `(u,v)` with `u + v` even.
    -- both halves of each row have `m+1` values, so `(m+1)² + (m+1)²`.
    have hj : (2 * m + 1 + 1) % 2 = 0 := by omega
    rw [hj, h0, h0']
    have d1 : (2 * m + 1 + 2 - 0) / 2 = m + 1 := by omega
    rw [d1]
    have d2 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
    rw [d2]
    have e : (m + 1) * (m + 1) + (m + 1) * (m + 1) = 2 * (m * m) + 4 * m + 2 := by ring
    have e2 : (2 * m + 1 + 1) ^ 2 = 4 * (m * m) + 8 * m + 4 := by ring
    rw [e, e2]
    omega

/-! ### Sanity checks against the table printed in Part V (`N = 2..10`)

The first two are the control that matters: they do not touch the theorems above.
They enumerate the actual `[p;q,r;s]` tuples of rank `3`, take their labels, and
compare with the grid -- so if `witness` or `label_le` were wrong, or the label
missed part of the grid, these would fail and the census would still "prove". -/

/-- All boundary conditions of rank `N`, by brute force. -/
def BCs (N : ℕ) : Finset BC :=
  (((range (N + 1)) ×ˢ (range (N + 1)) ×ˢ (range (N + 1)) ×ˢ (range (N + 1))).image
      (fun t => (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : BC))).filter (fun x => rank x = N)

set_option maxRecDepth 8000 in
example : (BCs 3).image label = classes 3 := by decide

set_option maxRecDepth 8000 in
example : ((BCs 3).filter hasCoset).image label = cosetClasses 3 := by decide

/-! And the controls are not vacuous.  A label that looks equally natural --
`(p+q, q+r)`, the two "off-diagonal" sums -- is *not* invariant under the move,
so `label_move` is a real constraint and not bookkeeping: -/
example : ((⟨1, 0, 0, 1⟩ : BC).p + (⟨1, 0, 0, 1⟩ : BC).q,
           (⟨1, 0, 0, 1⟩ : BC).q + (⟨1, 0, 0, 1⟩ : BC).r) ≠
          ((⟨0, 1, 1, 0⟩ : BC).p + (⟨0, 1, 1, 0⟩ : BC).q,
           (⟨0, 1, 1, 0⟩ : BC).q + (⟨0, 1, 1, 0⟩ : BC).r) := by decide

-- ... and the parity is load-bearing: the OTHER parity class has `⌈(N+1)²/2⌉`,
-- which is a different number, so `card_cosetClasses` is not counting everything.
example : ((classes 2).filter (fun c => (c.1 + c.2 + 2) % 2 = 0)).card = 5 := by decide
example : (cosetClasses 2).card ≠ ((classes 2).filter (fun c => (c.1 + c.2 + 2) % 2 = 0)).card := by
  decide

example : (classes 2).card = 9 ∧ (cosetClasses 2).card = 4 := by decide
example : (classes 3).card = 16 ∧ (cosetClasses 3).card = 8 := by decide
example : (classes 4).card = 25 ∧ (cosetClasses 4).card = 12 := by decide
example : (classes 5).card = 36 ∧ (cosetClasses 5).card = 18 := by decide

-- `[1;1,0;0]` for `SU(2)`: `q + r = 1`, a coset sector, and its label is `(2,1)`.
example : hasCoset ⟨1, 1, 0, 0⟩ := by decide
example : label ⟨1, 1, 0, 0⟩ = (2, 1) ∧ rank ⟨1, 1, 0, 0⟩ = 2 := by decide

-- the move changes `q + r` by two, and the class by nothing
example : Move ⟨1, 0, 0, 1⟩ ⟨0, 1, 1, 0⟩ := Move.intro 0 0 0 0
example : label ⟨1, 0, 0, 1⟩ = label ⟨0, 1, 1, 0⟩ := by decide

#print axioms rank_eqv
#print axioms label_eqv
#print axioms eqv_of_label
#print axioms witness_label
#print axioms coset_parity
#print axioms card_classes
#print axioms card_cosetClasses

end GHU
