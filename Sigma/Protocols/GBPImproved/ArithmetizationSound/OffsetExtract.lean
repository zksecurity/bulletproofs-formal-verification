/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.Honest

/-!
# Offset-protocol soundness: the tree, the `r`-quadrants, and the `t̂`-quadratic

The extraction layer for the protocol of record `Sigma.Protocols.GBPImproved.arithRed'`
(the opening `(τ_x, μ, a, b)` is the output witness, decorating the leaves after the binding
challenge `r`; binding offset `z^{q+1}·𝟙` on the mask slot of `f_L`). Tree shape
`(n, q+2, 2c+5, 3)`:

* `q+2` `z`-children — one more than the constraint count, to isolate the offset's fresh
  `z^{q+1}`-degree in the elimination argument;
* `3` `r`-children — the opening is per-`r`, so the `t̂`-identity
  `⟨a_e, b_e⟩ = ⟨a*,β⟩·r_e⁻¹ + C + ⟨α,b*⟩·r_e` needs three points to force the cross terms to zero.

Since the opening may differ across the `r`-children, two children only *interpolate* the split
commitments to four **quadrants** (`aStarF, betaF, alphaF, bStarF`) and the interpolated split
blinders `muLF, muRF`: `P_L` opens as `⟨a*,𝐆⟩ + ⟨β,𝐇'⟩ + muLF·H` and `P_R` as
`⟨α,𝐆⟩ + ⟨b*,𝐇'⟩ + muRF·H` (`node_quad_open`), with the stray blocks `β, α` not yet forced to
zero — that is the offset elimination argument's job (`OffsetEliminate.lean`). The third child either lies on
the interpolated family — openings *and* blinder — (`quad_family01`, `famCand`-vanishing) or
yields a discrete-log relation; `eq1` pins `⟨a_e, b_e⟩` across children (its right-hand side is
fixed before `r`, so a per-child `(t̂, τ_x)`-deviation is a relation on `(g, h)`), and the
scalar three-point lemma `tHat_quad` then forces `⟨a*, β⟩ = 0` and `⟨α, b*⟩ = 0` per node.

This file also provides the three-block `x`-Vandermonde extraction (`coeff_open3`,
`bundle_openL/R`), the `eq1` recoveries at target `c+1`, the candidate witness, and clause 4.
All machinery lives in the namespace `Sigma.Protocols.GBPImproved.Offset`.
-/

namespace Sigma.Protocols.GBPImproved.Offset

open Sigma.Protocols.GBP Sigma.Protocols.GBPImproved
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The arity-annotated move list of the `(n, q+2, 2c+5, 3)`-tree. Stripping the arities
recovers `arithMoves' F G c`. -/
@[reducible] def arithMK' (F G : Type) [Monoid F] (n q c : ℕ) : List MoveK :=
  [ .msg (G × G × G × G × G), .chal Fˣ n, .chal F (q + 2),
    .msg (Fin (2 * c + 5) → G), .chal Fˣ (2 * c + 5), .chal Fˣ 3 ]

/-- The decorated `(n, q+2, 2c+5, 3)`-tree of the improved arithmetization reduction:
conversations over `arithMoves'`, decorated with the (never sent) openings
`(τ_x, μ, a, b)`. -/
abbrev ArithTree' (F G : Type) [Field F] (n q c : ℕ) :=
  TreeK (arithMK' F G n q c) (F × F × (Fin n → F) × (Fin n → F))

section OffsetAccessors

variable {n q c : ℕ}

/-- The root message `(A_L, A_R, A_O, S_L, S_R)`. -/
@[reducible] def rootO (T : ArithTree' F G n q c) : G × G × G × G × G := T.msgVal

/-- The `y`-challenges. -/
@[reducible] def chalYO (T : ArithTree' F G n q c) : Fin n → Fˣ := T.msgSub.chalVal

/-- The `z`-challenges below the `i`-th `y`-branch. -/
@[reducible] def chalZO (T : ArithTree' F G n q c) (i : Fin n) : Fin (q + 2) → F :=
  (T.msgSub.chalSub i).chalVal

/-- The `{T_i}` message below the `(i, j)`-th branch. -/
@[reducible] def tcomO (T : ArithTree' F G n q c) (i : Fin n) (j : Fin (q + 2)) :
    Fin (2 * c + 5) → G :=
  ((T.msgSub.chalSub i).chalSub j).msgVal

/-- The `x`-challenges below the `(i, j)`-th branch, as raw units: the challenge space is
`Fˣ`, since perfect HVZK of the arithmetization requires an invertible `x`. -/
@[reducible] def rawXO (T : ArithTree' F G n q c) (i : Fin n) (j : Fin (q + 2)) :
    Fin (2 * c + 5) → Fˣ :=
  ((T.msgSub.chalSub i).chalSub j).msgSub.chalVal

/-- The `x`-challenges below the `(i, j)`-th branch, coerced to `F`. -/
@[reducible] def chalXO (T : ArithTree' F G n q c) (i : Fin n) (j : Fin (q + 2)) :
    Fin (2 * c + 5) → F :=
  fun l => ((rawXO T i j l : Fˣ) : F)

/-- The binding challenges below the `(i, j, l)`-th branch. -/
@[reducible] def chalRO (T : ArithTree' F G n q c) (i : Fin n) (j : Fin (q + 2))
    (l : Fin (2 * c + 5)) : Fin 3 → Fˣ :=
  (((T.msgSub.chalSub i).chalSub j).msgSub.chalSub l).chalVal

/-- The opening `(τ_x, μ, a, b)` decorating the `(i, j, l, e)`-th leaf. -/
@[reducible] def leafV' (T : ArithTree' F G n q c) (i : Fin n) (j : Fin (q + 2))
    (l : Fin (2 * c + 5)) (e : Fin 3) : F × F × (Fin n → F) × (Fin n → F) :=
  ((((T.msgSub.chalSub i).chalSub j).msgSub.chalSub l).chalSub e).leafVal

/-- The `(i, j, l, e)`-th conversation of the tree. -/
@[reducible] def pathConvO (T : ArithTree' F G n q c) (i : Fin n) (j : Fin (q + 2))
    (l : Fin (2 * c + 5)) (e : Fin 3) : Conversation (arithMoves' F G c) :=
  (rootO T, chalYO T i, chalZO T i j, tcomO T i j, rawXO T i j l,
   chalRO T i j l e, PUnit.unit)

end OffsetAccessors

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `(i, j, l, e)`-th decorated root-to-leaf conversation of an `(n, q+2, 2c+5, 3)`-tree
is one of the tree's `paths`. -/
lemma mem_paths {n q c : ℕ}
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) :
    (pathConvO tree i j l e, leafV' tree i j l e) ∈ tree.paths := by
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((chalYO tree i, chalZO tree i j, tcomO tree i j, rawXO tree i j l,
    chalRO tree i j l e, PUnit.unit), leafV' tree i j l e), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨i, by simp, List.mem_map.2 ⟨((chalZO tree i j, tcomO tree i j,
    rawXO tree i j l, chalRO tree i j l e, PUnit.unit),
    leafV' tree i j l e), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨j, by simp, List.mem_map.2 ⟨((tcomO tree i j, rawXO tree i j l,
    chalRO tree i j l e, PUnit.unit), leafV' tree i j l e), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((rawXO tree i j l, chalRO tree i j l e,
    PUnit.unit), leafV' tree i j l e), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨l, by simp, List.mem_map.2 ⟨((chalRO tree i j l e, PUnit.unit),
    leafV' tree i j l e), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨e, by simp, List.mem_map.2 ⟨(PUnit.unit, leafV' tree i j l e),
    ?_, rfl⟩⟩
  rw [TreeK.paths_eq_leaf]
  exact List.mem_singleton.2 rfl

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `y`-challenges of the root, coerced to `F`, are pairwise distinct. -/
lemma chalY_inj {n q c : ℕ} (tree : ArithTree' F G n q c) :
    Function.Injective (fun i => ((chalYO tree i : Fˣ) : F)) :=
  Units.val_injective.comp tree.msgSub.chalInj

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `z`-challenges below a fixed `y`-branch are pairwise distinct. -/
lemma chalZ_inj {n q c : ℕ} (tree : ArithTree' F G n q c) (i : Fin n) :
    Function.Injective (fun j => (chalZO tree i j)) :=
  (tree.msgSub.chalSub i).chalInj

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The first `q+1` `z`-challenges (the restriction consumed by the `z`-deaggregations built
for `q+1` points) are pairwise distinct. -/
lemma chalZres_inj {n q c : ℕ} (tree : ArithTree' F G n q c) (i : Fin n) :
    Function.Injective (fun j : Fin (q + 1) =>
      (chalZO tree i (Fin.castLE (by omega) j))) :=
  (chalZ_inj tree i).comp (Fin.castLE_injective _)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `x`-challenges below a fixed `(y, z)`-branch are pairwise distinct. -/
lemma chalX_inj {n q c : ℕ} (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) :
    Function.Injective (fun l => (chalXO tree i j l)) := fun _ _ hab =>
  ((tree.msgSub.chalSub i).chalSub j).msgSub.chalInj (Units.val_injective hab)

/-- Every decorated root-to-leaf conversation of an accepting tree is accepting: the
`(i, j, l, e)` opening vectors satisfy both verifier equations at the derived statement. -/
lemma path_verify {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) :
    (relArith' F G n).rel (arithOut' s (rootO tree, chalYO tree i, chalZO tree i j,
      tcomO tree i j, rawXO tree i j l, chalRO tree i j l e,
      PUnit.unit)) (leafV' tree i j l e) = true := by
  obtain ⟨st, hst, hrel⟩ := hacc _ (mem_paths tree i j l e)
  simp only [arithRed'] at hst
  obtain rfl := Option.some.inj hst
  exact hrel

/-! ## The two verifier checks, restated for extraction -/

set_option maxHeartbeats 1600000 in
/-- The verifier's second check (`eq2`), restated through `PL_repackage`/`PR_repackage`: at
binding challenge `r`, the recombination of the two coefficient polynomials (with the binding
offset folded into the `S_L`-slot argument) opens to the *post-`r`* message `(a, b)`. -/
lemma verify_eq2 {n q m c : ℕ} (s : Statement F G n q m c)
    (AL AR AO SL SR : G) (yu : Fˣ) (z : F) (xu ru : Fˣ) (T : Fin (2 * c + 5) → G)
    (τx μ : F) (a b : Fin n → F)
    (h : (relArith' F G n).rel (arithOut' s ((AL, AR, AO, SL, SR), yu, z, T, xu,
        ru, PUnit.unit)) (τx, μ, a, b) = true) :
    (∑ p : Fin (2 * c + 5), (↑xu : F) ^ (p : ℕ)
        • PcoefL' s (↑yu : F) z AL AO
            (SL + msm (fun _ => z ^ (q + 1)) s.gs) p)
      + (↑ru : F) • ∑ ℓ : Fin (2 * c + 5), (↑xu : F) ^ (ℓ : ℕ)
        • PcoefR' s (↑yu : F) z AR SR ℓ
      = msm a s.gs + (↑ru : F) • msm b (vinv (powers (↑yu : F) n) ⊙ s.hs)
        + μ • s.h := by
  simp only [arithOut', Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 := h.2
  rw [msm_smul_gen] at h2
  rw [PL_repackage s (↑yu : F) z (↑xu : F) AL AO
      (SL + msm (fun _ => z ^ (q + 1)) s.gs),
    PR_repackage s (↑yu : F) z (↑xu : F) AR SR] at h2
  exact h2

set_option maxHeartbeats 1600000 in
/-- The verifier's first check (`eq1`), restated as `⟨a,b⟩·g + τₓ·h = ∑ᵣ xʳ·T'ᵣ` with the
special `(c+1)`-coefficient `(δ−w_c)·g − ⟨w_V,V⟩`. The right-hand side is fixed before `r`. -/
lemma verify_eq1 {n q m c : ℕ} (s : Statement F G n q m c)
    (AL AR AO SL SR : G) (yu : Fˣ) (z : F) (xu ru : Fˣ) (T : Fin (2 * c + 5) → G)
    (τx μ : F) (a b : Fin n → F)
    (h : (relArith' F G n).rel (arithOut' s ((AL, AR, AO, SL, SR), yu, z, T, xu,
        ru, PUnit.unit)) (τx, μ, a, b) = true) :
    ip a b • s.g + τx • s.h
      = ∑ r : Fin (2 * c + 5), (↑xu : F) ^ (r : ℕ) • (if (r : ℕ) = c + 1 then
          ((ip (hadamard (vinv (powers (↑yu : F) n)) (z • (powers z q ᵥ* s.WR)))
                (z • (powers z q ᵥ* s.WL))
              - z * ip (powers z q) s.cc) • s.g
            - msm (z • (powers z q ᵥ* s.WV)) s.V)
          else T r) := by
  simp only [arithOut', Bool.and_eq_true, decide_eq_true_eq] at h
  rw [eq1_RHS_repackage' (↑xu : F) (c + 1) (by omega)
      ((ip (hadamard (vinv (powers (↑yu : F) n)) (z • (powers z q ᵥ* s.WR)))
            (z • (powers z q ᵥ* s.WL))
          - z * ip (powers z q) s.cc) • s.g
        - msm (z • (powers z q ᵥ* s.WV)) s.V) T] at h
  exact h.1

/-! ## The two-point quadrant interpolation -/

omit [DecidableEq F] [DecidableEq G] in
/-- **Two-point quadrant interpolation (group level).** The `eq2` identities at two distinct
binding challenges, with *possibly different* openings `(A_e, B_e)` and blinders `μ_e`, pin
the two sides to the interpolated quadrant combinations (the blinders interpolate alongside
the quadrants). -/
lemma quad_open_core {PL PR A0 A1 B0 B1 H : G} {μ0 μ1 r0 r1 : F} (hne : r0 ≠ r1)
    (h0 : PL + r0 • PR = A0 + r0 • B0 + μ0 • H)
    (h1 : PL + r1 • PR = A1 + r1 • B1 + μ1 • H) :
    PL = (r1 - r0)⁻¹ • (r1 • A0 - r0 • A1)
        + (r1 - r0)⁻¹ • ((r0 * r1) • (B0 - B1))
        + ((r1 - r0)⁻¹ * (r1 * μ0 - r0 * μ1)) • H
    ∧ PR = (r1 - r0)⁻¹ • (A1 - A0)
        + (r1 - r0)⁻¹ • (r1 • B1 - r0 • B0)
        + ((r1 - r0)⁻¹ * (μ1 - μ0)) • H := by
  have hr : r1 - r0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  constructor
  · have e : (r1 - r0) • PL
        = (r1 - r0) • ((r1 - r0)⁻¹ • (r1 • A0 - r0 • A1)
            + (r1 - r0)⁻¹ • ((r0 * r1) • (B0 - B1))
            + ((r1 - r0)⁻¹ * (r1 * μ0 - r0 * μ1)) • H) := by
      have hmul : (r1 - r0) * ((r1 - r0)⁻¹ * (r0 * r1)) = r0 * r1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
      have hmulH : (r1 - r0) * ((r1 - r0)⁻¹ * (r1 * μ0 - r0 * μ1)) = r1 * μ0 - r0 * μ1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
      have expand : (r1 - r0) • ((r1 - r0)⁻¹ • (r1 • A0 - r0 • A1)
            + (r1 - r0)⁻¹ • ((r0 * r1) • (B0 - B1))
            + ((r1 - r0)⁻¹ * (r1 * μ0 - r0 * μ1)) • H)
          = ((r1 - r0) * (r1 - r0)⁻¹) • (r1 • A0 - r0 • A1)
            + ((r1 - r0) * ((r1 - r0)⁻¹ * (r0 * r1))) • (B0 - B1)
            + ((r1 - r0) * ((r1 - r0)⁻¹ * (r1 * μ0 - r0 * μ1))) • H := by
        simp only [smul_add, smul_smul]
      rw [expand, mul_inv_cancel₀ hr, hmul, hmulH]
      simp only [one_smul]
      linear_combination (norm := module) r1 • h0 - r0 • h1
    have e2 := congrArg (fun g : G => (r1 - r0)⁻¹ • g) e
    simpa only [inv_smul_smul₀ hr] using e2
  · have e : (r1 - r0) • PR
        = (r1 - r0) • ((r1 - r0)⁻¹ • (A1 - A0)
            + (r1 - r0)⁻¹ • (r1 • B1 - r0 • B0)
            + ((r1 - r0)⁻¹ * (μ1 - μ0)) • H) := by
      have hmulH : (r1 - r0) * ((r1 - r0)⁻¹ * (μ1 - μ0)) = μ1 - μ0 := by
        rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
      have expand : (r1 - r0) • ((r1 - r0)⁻¹ • (A1 - A0)
            + (r1 - r0)⁻¹ • (r1 • B1 - r0 • B0)
            + ((r1 - r0)⁻¹ * (μ1 - μ0)) • H)
          = ((r1 - r0) * (r1 - r0)⁻¹) • (A1 - A0)
            + ((r1 - r0) * (r1 - r0)⁻¹) • (r1 • B1 - r0 • B0)
            + ((r1 - r0) * ((r1 - r0)⁻¹ * (μ1 - μ0))) • H := by
        simp only [smul_add, smul_smul]
      rw [expand, mul_inv_cancel₀ hr, hmulH]
      simp only [one_smul]
      linear_combination (norm := module) h1 - h0
    have e2 := congrArg (fun g : G => (r1 - r0)⁻¹ • g) e
    simpa only [inv_smul_smul₀ hr] using e2

/-! ## The quadrant vectors -/

section Quadrants

variable {n q c : ℕ}

/-- The first two `r`-challenges of the `(i,j,l)` node, as field elements. -/
def rch (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) : F :=
  ((chalRO tree i j l e : Fˣ) : F)

/-- The opening `(τ_x, μ, a, b)` decorating the `e`-th `r`-child of the `(i,j,l)` node: the
`τ_x`-component. -/
def leafTau (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) : F :=
  (leafV' tree i j l e).1

@[inherit_doc leafTau]
def leafMu (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) : F :=
  (leafV' tree i j l e).2.1

@[inherit_doc leafTau]
def leafA (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) : Fin n → F :=
  (leafV' tree i j l e).2.2.1

@[inherit_doc leafTau]
def leafB (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) : Fin n → F :=
  (leafV' tree i j l e).2.2.2

/-- The `𝐆`-quadrant of `P_L`: the interpolation `(r₁−r₀)⁻¹·(r₁·a₀ − r₀·a₁)`. -/
def aStarF (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) : Fin n → F :=
  (rch tree i j l 1 - rch tree i j l 0)⁻¹
    • (rch tree i j l 1 • leafA tree i j l 0 - rch tree i j l 0 • leafA tree i j l 1)

/-- The `𝐇'`-quadrant (stray mass) of `P_L`: `(r₁−r₀)⁻¹·r₀r₁·(b₀ − b₁)`. -/
def betaF (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) : Fin n → F :=
  (rch tree i j l 1 - rch tree i j l 0)⁻¹
    • ((rch tree i j l 0 * rch tree i j l 1) • (leafB tree i j l 0 - leafB tree i j l 1))

/-- The `𝐆`-quadrant (stray mass) of `P_R`: `(r₁−r₀)⁻¹·(a₁ − a₀)`. -/
def alphaF (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) : Fin n → F :=
  (rch tree i j l 1 - rch tree i j l 0)⁻¹
    • (leafA tree i j l 1 - leafA tree i j l 0)

/-- The `𝐇'`-quadrant of `P_R`: `(r₁−r₀)⁻¹·(r₁·b₁ − r₀·b₀)`. -/
def bStarF (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) : Fin n → F :=
  (rch tree i j l 1 - rch tree i j l 0)⁻¹
    • (rch tree i j l 1 • leafB tree i j l 1 - rch tree i j l 0 • leafB tree i j l 0)

/-- The interpolated `𝐆`-side blinder of `P_L`: `(r₁−r₀)⁻¹·(r₁·μ₀ − r₀·μ₁)`. -/
def muLF (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) : F :=
  (rch tree i j l 1 - rch tree i j l 0)⁻¹
    * (rch tree i j l 1 * leafMu tree i j l 0 - rch tree i j l 0 * leafMu tree i j l 1)

/-- The interpolated `𝐇`-side blinder of `P_R`: `(r₁−r₀)⁻¹·(μ₁ − μ₀)`. -/
def muRF (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) : F :=
  (rch tree i j l 1 - rch tree i j l 0)⁻¹
    * (leafMu tree i j l 1 - leafMu tree i j l 0)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `r`-challenges of a node are pairwise distinct as field elements. -/
lemma rch_inj (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) {e e' : Fin 3} (hcc : e ≠ e') :
    rch tree i j l e ≠ rch tree i j l e' := fun hcontra =>
  absurd ((((tree.msgSub.chalSub i).chalSub j).msgSub.chalSub l).chalInj (Units.ext hcontra)) hcc

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `r`-challenges are nonzero (they are units). -/
lemma rch_ne_zero (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) :
    rch tree i j l e ≠ 0 :=
  Units.ne_zero _

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The first two children lie on the quadrant family by construction**: `a_e = a* + r_e·α`
and `r_e·b_e = β + r_e·b*` for `c = 0, 1`. -/
lemma quad_family01 (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 2) :
    leafA tree i j l ⟨(e : ℕ), by omega⟩
        = aStarF tree i j l + rch tree i j l ⟨(e : ℕ), by omega⟩ • alphaF tree i j l
      ∧ rch tree i j l ⟨(e : ℕ), by omega⟩ • leafB tree i j l ⟨(e : ℕ), by omega⟩
        = betaF tree i j l
          + rch tree i j l ⟨(e : ℕ), by omega⟩ • bStarF tree i j l := by
  have hne : rch tree i j l 0 ≠ rch tree i j l 1 := rch_inj tree i j l (by decide)
  have hr : rch tree i j l 1 - rch tree i j l 0 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hne)
  have hι : (rch tree i j l 1 - rch tree i j l 0)⁻¹
      * (rch tree i j l 1 - rch tree i j l 0) = 1 := inv_mul_cancel₀ hr
  have hc2 : (e : ℕ) = 0 ∨ (e : ℕ) = 1 := by omega
  rcases hc2 with hc | hc
  · have hci : (⟨(e : ℕ), by omega⟩ : Fin 3) = 0 := by
      apply Fin.ext; simpa using hc
    rw [hci]
    constructor
    · funext t
      simp only [aStarF, alphaF, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination (-(leafA tree i j l 0 t)) * hι
    · funext t
      simp only [betaF, bStarF, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination (-(rch tree i j l 0 * leafB tree i j l 0 t)) * hι
  · have hci : (⟨(e : ℕ), by omega⟩ : Fin 3) = 1 := by
      apply Fin.ext; simpa using hc
    rw [hci]
    constructor
    · funext t
      simp only [aStarF, alphaF, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination (-(leafA tree i j l 1 t)) * hι
    · funext t
      simp only [betaF, bStarF, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination (-(rch tree i j l 1 * leafB tree i j l 1 t)) * hι

end Quadrants

/-! ## Per-node quadrant openings -/

omit [DecidableEq F] [DecidableEq G] in
/-- Folding the quadrant scalar combination through `msm` (two `smul`s and a `sub`). -/
lemma msm_quad_fold {nn : ℕ} (c d e : F) (u v : Fin nn → F) (gs : Fin nn → G) :
    msm (c • (d • u - e • v)) gs = c • (d • msm u gs - e • msm v gs) := by
  rw [msm_smul_left, msm_sub_left, msm_smul_left, msm_smul_left]

omit [DecidableEq F] [DecidableEq G] in
/-- Folding the quadrant scalar combination through `msm` (plain difference). -/
lemma msm_quad_fold' {nn : ℕ} (c : F) (u v : Fin nn → F) (gs : Fin nn → G) :
    msm (c • (u - v)) gs = c • (msm u gs - msm v gs) := by
  rw [msm_smul_left, msm_sub_left]

omit [DecidableEq F] [DecidableEq G] in
/-- Folding the `β`-quadrant combination through `msm` (inner `smul` of a difference). -/
lemma msm_quad_fold'' {nn : ℕ} (c d : F) (u v : Fin nn → F) (gs : Fin nn → G) :
    msm (c • (d • (u - v))) gs = c • (d • (msm u gs - msm v gs)) := by
  rw [msm_smul_left, msm_smul_left, msm_sub_left]

/-- **Per-node quadrant openings.** At every `(y, z, x)` node of an accepting tree, the first
two `r`-children interpolate the two coefficient polynomials to the quadrant openings:
`P_L(x) = ⟨a*,𝐆⟩ + ⟨β,𝐇'⟩ + muLF·H` and `P_R(x) = ⟨α,𝐆⟩ + ⟨b*,𝐇'⟩ + muRF·H`. -/
lemma node_quad_open {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) :
    (∑ p : Fin (2 * c + 5), (chalXO tree i j l) ^ (p : ℕ)
        • PcoefL' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
            (rootO tree).1 (rootO tree).2.2.1
            ((rootO tree).2.2.2.1
              + msm (fun _ => (chalZO tree i j) ^ (q + 1)) s.gs) p)
      = msm (aStarF tree i j l) s.gs
        + msm (betaF tree i j l) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
        + muLF tree i j l • s.h
    ∧ (∑ ℓ : Fin (2 * c + 5), (chalXO tree i j l) ^ (ℓ : ℕ)
        • PcoefR' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
            (rootO tree).2.1 (rootO tree).2.2.2.2 ℓ)
      = msm (alphaF tree i j l) s.gs
        + msm (bStarF tree i j l) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
        + muRF tree i j l • s.h := by
  have h0 := verify_eq2 s (rootO tree).1 (rootO tree).2.1 (rootO tree).2.2.1
    (rootO tree).2.2.2.1 (rootO tree).2.2.2.2 (chalYO tree i) (chalZO tree i j)
    (rawXO tree i j l)
    (chalRO tree i j l 0)
    (tcomO tree i j) _ _ _ _ (path_verify s tree hacc i j l 0)
  have h1 := verify_eq2 s (rootO tree).1 (rootO tree).2.1 (rootO tree).2.2.1
    (rootO tree).2.2.2.1 (rootO tree).2.2.2.2 (chalYO tree i) (chalZO tree i j)
    (rawXO tree i j l)
    (chalRO tree i j l 1)
    (tcomO tree i j) _ _ _ _ (path_verify s tree hacc i j l 1)
  have hne : rch tree i j l 0 ≠ rch tree i j l 1 := rch_inj tree i j l (by decide)
  have hquad := quad_open_core (H := s.h) (μ0 := leafMu tree i j l 0)
    (μ1 := leafMu tree i j l 1) hne h0 h1
  constructor
  · rw [hquad.1]
    rw [show msm (aStarF tree i j l) s.gs
        = (rch tree i j l 1 - rch tree i j l 0)⁻¹
          • (rch tree i j l 1 • msm (leafA tree i j l 0) s.gs
            - rch tree i j l 0 • msm (leafA tree i j l 1) s.gs) from
      msm_quad_fold _ _ _ _ _ _]
    rw [show msm (betaF tree i j l) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
        = (rch tree i j l 1 - rch tree i j l 0)⁻¹
          • ((rch tree i j l 0 * rch tree i j l 1)
            • (msm (leafB tree i j l 0) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
              - msm (leafB tree i j l 1) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs))) from
      msm_quad_fold'' _ _ _ _ _]
    rfl
  · rw [hquad.2]
    rw [show msm (alphaF tree i j l) s.gs
        = (rch tree i j l 1 - rch tree i j l 0)⁻¹
          • (msm (leafA tree i j l 1) s.gs - msm (leafA tree i j l 0) s.gs) from
      msm_quad_fold' _ _ _ _]
    rw [show msm (bStarF tree i j l) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
        = (rch tree i j l 1 - rch tree i j l 0)⁻¹
          • (rch tree i j l 1
              • msm (leafB tree i j l 1) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
            - rch tree i j l 0
              • msm (leafB tree i j l 0) (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)) from
      msm_quad_fold _ _ _ _ _ _]
    rfl

/-! ## The scalar three-point lemma -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The `t̂`-quadratic.** A function `r ↦ A·r⁻¹ + C + B·r` constant (`= t`) at three distinct
nonzero points has `A = B = 0` and value `C = t`. -/
lemma tHat_quad {r0 r1 r2 A B C t : F} (h01 : r0 ≠ r1) (h02 : r0 ≠ r2) (h12 : r1 ≠ r2)
    (hn0 : r0 ≠ 0) (hn1 : r1 ≠ 0) (hn2 : r2 ≠ 0)
    (e0 : A * r0⁻¹ + C + B * r0 = t)
    (e1 : A * r1⁻¹ + C + B * r1 = t)
    (e2 : A * r2⁻¹ + C + B * r2 = t) :
    A = 0 ∧ B = 0 ∧ C = t := by
  have hi0 : r0⁻¹ * r0 = 1 := inv_mul_cancel₀ hn0
  have hi1 : r1⁻¹ * r1 = 1 := inv_mul_cancel₀ hn1
  have hi2 : r2⁻¹ * r2 = 1 := inv_mul_cancel₀ hn2
  have m0 : A + C * r0 + B * (r0 * r0) = t * r0 := by
    linear_combination r0 * e0 - A * hi0
  have m1 : A + C * r1 + B * (r1 * r1) = t * r1 := by
    linear_combination r1 * e1 - A * hi1
  have m2 : A + C * r2 + B * (r2 * r2) = t * r2 := by
    linear_combination r2 * e2 - A * hi2
  have d01 : C + B * (r0 + r1) - t = 0 := by
    have e : (r0 - r1) * (C + B * (r0 + r1) - t) = 0 := by linear_combination m0 - m1
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr h01)
  have d02 : C + B * (r0 + r2) - t = 0 := by
    have e : (r0 - r2) * (C + B * (r0 + r2) - t) = 0 := by linear_combination m0 - m2
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr h02)
  have hB : B = 0 := by
    have e : (r1 - r2) * B = 0 := by linear_combination d01 - d02
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr h12)
  have hC : C = t := by linear_combination d01 - (r0 + r1) * hB
  have hA : A = 0 := by linear_combination m0 - r0 * hC - (r0 * r0) * hB
  exact ⟨hA, hB, hC⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The inner product of two on-family openings, as the quadratic form in `r`:
`⟨a* + r·α, r⁻¹·β + b*⟩ = ⟨a*,β⟩·r⁻¹ + (⟨a*,b*⟩ + ⟨α,β⟩) + ⟨α,b*⟩·r`. -/
lemma ip_quad {n : ℕ} {r : F} (hr : r ≠ 0) (aS α β bS : Fin n → F) :
    ip (aS + r • α) (r⁻¹ • β + bS)
      = ip aS β * r⁻¹ + (ip aS bS + ip α β) + ip α bS * r := by
  have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  rw [ip_add_left, ip_add_right, ip_add_right, ip_smul_left, ip_smul_left, ip_smul_right,
    ip_smul_right]
  linear_combination (ip α β) * hi

/-! ## The three-block `x`-Vandermonde extraction -/

omit [DecidableEq F] [DecidableEq G] in
/-- **`x`-level extraction (three-block form).** From `N` accepting openings
`∑ₚ xₗᵖ • Pc p = ⟨v l, gs⟩ + ⟨w l, hs'⟩ + μ l · hG` at distinct `xₗ`, each coefficient `Pc p`
opens with the inverse-Vandermonde combinations of the `(v, w, μ)` data. -/
lemma coeff_open3 {N nn : ℕ} (gs hs' : Fin nn → G) (hG : G) (Pc : Fin N → G)
    (x : Fin N → F) (hx : Function.Injective x)
    (v w : Fin N → (Fin nn → F)) (μ : Fin N → F)
    (heq : ∀ l, (∑ p : Fin N, x l ^ (p : ℕ) • Pc p)
      = msm (v l) gs + msm (w l) hs' + μ l • hG)
    (p : Fin N) :
    Pc p = msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • v l) gs
      + msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • w l) hs'
      + (∑ l, (Matrix.vandermonde x)⁻¹ p l • μ l) • hG := by
  refine congrFun (vandermonde_coeff_unique x hx Pc
    (fun p => msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • v l) gs
      + msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • w l) hs'
      + (∑ l, (Matrix.vandermonde x)⁻¹ p l • μ l) • hG) ?_) p
  intro l
  rw [heq l]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · rw [show (∑ ℓ : Fin N, x l ^ (ℓ : ℕ)
            • msm (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • v l') gs)
          = msm (∑ ℓ : Fin N, x l ^ (ℓ : ℕ)
            • (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • v l')) gs from by
        rw [msm_sum_left]; exact Finset.sum_congr rfl fun ℓ _ => (msm_smul_left _ _ _).symm]
      rw [← vandermonde_recover x hx v l]
    · rw [show (∑ ℓ : Fin N, x l ^ (ℓ : ℕ)
            • msm (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • w l') hs')
          = msm (∑ ℓ : Fin N, x l ^ (ℓ : ℕ)
            • (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • w l')) hs' from by
        rw [msm_sum_left]; exact Finset.sum_congr rfl fun ℓ _ => (msm_smul_left _ _ _).symm]
      rw [← vandermonde_recover x hx w l]
  · simp only [← smul_assoc, ← Finset.sum_smul]
    rw [← vandermonde_recover x hx μ l]

end Sigma.Protocols.GBPImproved.Offset
