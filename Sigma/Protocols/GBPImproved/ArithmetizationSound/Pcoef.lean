/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBPImproved.ArithmetizationPreR
import Sigma.Protocols.GBPImproved.ArithmetizationComplete
import Sigma.Protocols.GBP.ArithmetizationSound.ReadOff

/-!
# Improved-arithmetization soundness: split verifier coefficients and the binding interpolation

The improved arithmetization (`Sigma.Protocols.GBPImproved.arithRedPreR`) evaluates the
`𝐆`-side commitment `P_L` and the `𝐇`-side commitment `P_R` separately, and recombines them with
the binding challenge `r` drawn *after* the prover's opening `(τ_x, μ_L, μ_R, f_L(x), f_R(x))`.
This file provides the coefficient-level layer of its soundness proof:

* the split verifier-coefficient families `PcoefL'`/`PcoefR'` with their per-degree pinning
  lemmas (`PcoefL'_AL/AO/AC/SL`, `PcoefR'_Wtk/WtO/AR/SR`, `*_high_zero`) and the repackaging of
  the verifier's `P_L`/`P_R` as polynomial evaluations (`PL_repackage`/`PR_repackage`);
* the two verifier checks restated for extraction (`arithVerifyPreR_eq1`/`arithVerifyPreR_eq2`);
* the **binding interpolation** `r_interpolate`: the `eq2` identity is *affine* in `r`, and the
  prover's opening is fixed *before* `r`, so the two `r`-children of a node pin `P_L` to a pure
  `(𝐆, H)`-opening and `P_R` to a pure `(𝐲⁻¹⊙𝐇, H)`-opening — with **no** stray cross-component.
  This is the step that makes the tighter relation `R_GBP'` (no `aux`) extractable;
* the `x`-level Vandermonde extraction `coeff_open` (two-block form, shared by both sides), and
  the `eq1` special-coefficient extraction `eq1_special_extract'` (generic special index, used at
  the improved target degree `c+1`).

The `gens`/`gvec`/`vandInv` infrastructure is shared with the base proof
(`Sigma.Protocols.GBP.ArithmetizationSound`); the `Statement` type is the same.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## The split verifier-coefficient families -/

/-- The `x`-power coefficient family of the verifier's `𝐆`-side commitment `P_L` (one group
element per degree `0 … 2c+4`): `A_L + W̃_R` at `0`, `A_O` at `1`, `A_C⁽ʲ⁾` at `j+2`, `S_L` at
`c+2`, and `0` elsewhere (in particular at every degree above `c+2`). -/
def PcoefL' {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AL AO SL : G)
    (p : Fin (2 * c + 5)) : G :=
  (if (p : ℕ) = 0 then
      AL + msm (hadamard (vinv (powers y n)) (z • (powers z q ᵥ* s.WR))) s.gs else 0)
  + (if (p : ℕ) = 1 then AO else 0)
  + (∑ j : Fin c, if (p : ℕ) = (j : ℕ) + 2 then s.AC j else 0)
  + (if (p : ℕ) = c + 2 then SL else 0)

/-- The `x`-power coefficient family of the verifier's `𝐇`-side commitment `P_R`: the public
`W̃_C⁽ʲ⁾` at `c−j−1`, the public `W̃_O` at `c`, `A_R + W̃_L` at `c+1`, `S_R` at `c+2`, and `0`
elsewhere. -/
def PcoefR' {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AR SR : G)
    (ℓ : Fin (2 * c + 5)) : G :=
  (∑ j : Fin c, if (ℓ : ℕ) = c - (j : ℕ) - 1 then
      msm (z • (powers z q ᵥ* s.WC j)) (vinv (powers y n) ⊙ s.hs) else 0)
  + (if (ℓ : ℕ) = c then
      msm (z • (powers z q ᵥ* s.WO) - powers y n) (vinv (powers y n) ⊙ s.hs) else 0)
  + (if (ℓ : ℕ) = c + 1 then
      AR + msm (z • (powers z q ᵥ* s.WL)) (vinv (powers y n) ⊙ s.hs) else 0)
  + (if (ℓ : ℕ) = c + 2 then SR else 0)

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier's `𝐆`-side commitment `P_L` is the polynomial `∑ₚ xᵖ · PcoefL' p` evaluated at
the challenge `x` (a repackaging of the `arithVerifyPreR` definition of `P_L`). -/
lemma PL_repackage {n q m c : ℕ} (s : Statement F G n q m c) (y z x : F) (AL AO SL : G) :
    AL + msm (hadamard (vinv (powers y n)) (z • (powers z q ᵥ* s.WR))) s.gs + x • AO
        + (∑ j : Fin c, x ^ ((j : ℕ) + 2) • s.AC j) + x ^ (c + 2) • SL
      = ∑ p : Fin (2 * c + 5), x ^ (p : ℕ) • PcoefL' s y z AL AO SL p := by
  simp only [PcoefL', smul_add, Finset.sum_add_distrib]
  rw [sum_pow_smul_ite x 0 (by omega), sum_pow_smul_ite x 1 (by omega),
    sum_pow_smul_sum_ite x (fun j => (j : ℕ) + 2) (fun j => by have := j.isLt; dsimp only; omega),
    sum_pow_smul_ite x (c + 2) (by omega)]
  simp only [pow_zero, one_smul, pow_one]

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier's `𝐇`-side commitment `P_R` is the polynomial `∑ᵩ x^ℓ · PcoefR' ℓ` evaluated at
the challenge `x`. -/
lemma PR_repackage {n q m c : ℕ} (s : Statement F G n q m c) (y z x : F) (AR SR : G) :
    (∑ j : Fin c, x ^ (c - (j : ℕ) - 1)
        • msm (z • (powers z q ᵥ* s.WC j)) (vinv (powers y n) ⊙ s.hs))
      + x ^ c • msm (z • (powers z q ᵥ* s.WO) - powers y n) (vinv (powers y n) ⊙ s.hs)
      + x ^ (c + 1) • (AR + msm (z • (powers z q ᵥ* s.WL)) (vinv (powers y n) ⊙ s.hs))
      + x ^ (c + 2) • SR
      = ∑ ℓ : Fin (2 * c + 5), x ^ (ℓ : ℕ) • PcoefR' s y z AR SR ℓ := by
  simp only [PcoefR', smul_add, Finset.sum_add_distrib]
  rw [sum_pow_smul_sum_ite x (fun j => c - (j : ℕ) - 1) (fun j => by dsimp only; omega),
    sum_pow_smul_ite x c (by omega), sum_pow_smul_ite x (c + 1) (by omega),
    sum_pow_smul_ite x (c + 2) (by omega)]
  simp only [smul_add]

/-! ## Per-degree pinning of the coefficient families -/

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐆`-side coefficient at degree `0` is `A_L` plus the public `W̃_R` (a pure `𝐆`-part). -/
lemma PcoefL'_AL {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AL AO SL : G) :
    PcoefL' s y z AL AO SL ⟨0, by omega⟩
      = AL + msm (hadamard (vinv (powers y n)) (z • (powers z q ᵥ* s.WR))) s.gs := by
  have hac : ∀ j : Fin c, ((0 : ℕ) = (j : ℕ) + 2) = False := fun j => eq_false (by omega)
  simp only [PcoefL', if_true,
    show ((0 : ℕ) = 1) = False from eq_false (by omega),
    show ((0 : ℕ) = c + 2) = False from eq_false (by omega),
    hac, if_false, Finset.sum_const_zero, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐆`-side coefficient at degree `1` is the output commitment `A_O`. -/
lemma PcoefL'_AO {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AL AO SL : G) :
    PcoefL' s y z AL AO SL ⟨1, by omega⟩ = AO := by
  have hac : ∀ j : Fin c, ((1 : ℕ) = (j : ℕ) + 2) = False := fun j => eq_false (by omega)
  simp only [PcoefL', if_true,
    show ((1 : ℕ) = 0) = False from eq_false (by omega),
    show ((1 : ℕ) = c + 2) = False from eq_false (by omega),
    hac, if_false, Finset.sum_const_zero, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐆`-side coefficient at degree `k+2` is exactly the vector commitment `A_C⁽ᵏ⁾`. -/
lemma PcoefL'_AC {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AL AO SL : G) (k : Fin c) :
    PcoefL' s y z AL AO SL ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩ = s.AC k := by
  have hk := k.isLt
  have hac : ∀ j : Fin c, ((k : ℕ) + 2 = (j : ℕ) + 2) = (j = k) := fun j => by
    rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  simp only [PcoefL',
    show ((k : ℕ) + 2 = 0) = False from eq_false (by omega),
    show ((k : ℕ) + 2 = 1) = False from eq_false (by omega),
    show ((k : ℕ) + 2 = c + 2) = False from eq_false (by omega),
    hac, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐆`-side coefficient at degree `c+2` is the masking commitment `S_L`. -/
lemma PcoefL'_SL {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AL AO SL : G) :
    PcoefL' s y z AL AO SL ⟨c + 2, by omega⟩ = SL := by
  have hac : ∀ j : Fin c, (c + 2 = (j : ℕ) + 2) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [PcoefL', if_true,
    show (c + 2 = 0) = False from eq_false (by omega),
    show (c + 2 = 1) = False from eq_false (by omega),
    hac, if_false, Finset.sum_const_zero, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐆`-side coefficient family vanishes above degree `c+2`. -/
lemma PcoefL'_high_zero {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AL AO SL : G)
    (p : Fin (2 * c + 5)) (hp : c + 3 ≤ (p : ℕ)) :
    PcoefL' s y z AL AO SL p = 0 := by
  have hac : ∀ j : Fin c, ((p : ℕ) = (j : ℕ) + 2) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [PcoefL',
    show ((p : ℕ) = 0) = False from eq_false (by omega),
    show ((p : ℕ) = 1) = False from eq_false (by omega),
    show ((p : ℕ) = c + 2) = False from eq_false (by omega),
    hac, if_false, Finset.sum_const_zero, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐇`-side coefficient at degree `c−k−1` is the public `W̃_C⁽ᵏ⁾` (a pure `𝐡'`-part). -/
lemma PcoefR'_Wtk {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AR SR : G) (k : Fin c) :
    PcoefR' s y z AR SR ⟨c - (k : ℕ) - 1, by have := k.isLt; omega⟩
      = msm (z • (powers z q ᵥ* s.WC k)) (vinv (powers y n) ⊙ s.hs) := by
  have hk := k.isLt
  have hwc : ∀ j : Fin c, (c - (k : ℕ) - 1 = c - (j : ℕ) - 1) = (j = k) := fun j => by
    have := j.isLt
    rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  simp only [PcoefR',
    show (c - (k : ℕ) - 1 = c) = False from eq_false (by omega),
    show (c - (k : ℕ) - 1 = c + 1) = False from eq_false (by omega),
    show (c - (k : ℕ) - 1 = c + 2) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐇`-side coefficient at degree `c` is the public `W̃_O` (a pure `𝐡'`-part). -/
lemma PcoefR'_WtO {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AR SR : G) :
    PcoefR' s y z AR SR ⟨c, by omega⟩
      = msm (z • (powers z q ᵥ* s.WO) - powers y n) (vinv (powers y n) ⊙ s.hs) := by
  have hwc : ∀ j : Fin c, ((c : ℕ) = c - (j : ℕ) - 1) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [PcoefR', if_true,
    show ((c : ℕ) = c + 1) = False from eq_false (by omega),
    show ((c : ℕ) = c + 2) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_const_zero, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐇`-side coefficient at degree `c+1` is `A_R + W̃_L`. -/
lemma PcoefR'_AR {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AR SR : G) :
    PcoefR' s y z AR SR ⟨c + 1, by omega⟩
      = AR + msm (z • (powers z q ᵥ* s.WL)) (vinv (powers y n) ⊙ s.hs) := by
  have hwc : ∀ j : Fin c, (c + 1 = c - (j : ℕ) - 1) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [PcoefR', if_true,
    show (c + 1 = c) = False from eq_false (by omega),
    show (c + 1 = c + 2) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_const_zero, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐇`-side coefficient at degree `c+2` is the masking commitment `S_R`. -/
lemma PcoefR'_SR {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AR SR : G) :
    PcoefR' s y z AR SR ⟨c + 2, by omega⟩ = SR := by
  have hwc : ∀ j : Fin c, (c + 2 = c - (j : ℕ) - 1) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [PcoefR', if_true,
    show (c + 2 = c) = False from eq_false (by omega),
    show (c + 2 = c + 1) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_const_zero, zero_add]

omit [DecidableEq F] [DecidableEq G] in
/-- The `𝐇`-side coefficient family vanishes above degree `c+2`. -/
lemma PcoefR'_high_zero {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AR SR : G)
    (ℓ : Fin (2 * c + 5)) (hq : c + 3 ≤ (ℓ : ℕ)) :
    PcoefR' s y z AR SR ℓ = 0 := by
  have hwc : ∀ j : Fin c, ((ℓ : ℕ) = c - (j : ℕ) - 1) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [PcoefR',
    show ((ℓ : ℕ) = c) = False from eq_false (by omega),
    show ((ℓ : ℕ) = c + 1) = False from eq_false (by omega),
    show ((ℓ : ℕ) = c + 2) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_const_zero, add_zero]

/-! ## The two verifier checks, restated for extraction -/

set_option maxHeartbeats 1600000 in
omit [DecidableEq F] in
/-- The verifier's second check (`eq2`), restated: at binding challenge `r`, the recombination
`∑ₚ xᵖ·PcoefL' p + r · ∑ᵩ x^ℓ·PcoefR' ℓ` opens to the prover's *pre-`r`* message
`(a, b, μ_L, μ_R)` as `⟨a,𝐆⟩ + r·⟨b,𝐲⁻¹⊙𝐇⟩ + (μ_L + r·μ_R)·H` (transcript given in destructured
form to keep projections cheap). -/
lemma arithVerifyPreR_eq2 {n q m c : ℕ} (s : Statement F G n q m c)
    (AL AR AO SL SR : G) (yu zu xu ru : Fˣ) (T : Fin (2 * c + 5) → G)
    (τx μL μR : F) (a b : Fin n → F)
    (h : arithVerifyPreR s ((AL, AR, AO, SL, SR), yu, zu, T, xu,
        (τx, μL, μR, a, b), ru, PUnit.unit) = true) :
    (∑ p : Fin (2 * c + 5), (↑xu : F) ^ (p : ℕ)
        • PcoefL' s (↑yu : F) (↑zu : F) AL AO SL p)
      + (↑ru : F) • ∑ ℓ : Fin (2 * c + 5), (↑xu : F) ^ (ℓ : ℕ)
        • PcoefR' s (↑yu : F) (↑zu : F) AR SR ℓ
      = msm a s.gs + (↑ru : F) • msm b (vinv (powers (↑yu : F) n) ⊙ s.hs)
        + (μL + (↑ru : F) * μR) • s.h := by
  simp only [arithVerifyPreR, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 := h.2
  rw [msm_smul_gen] at h2
  rw [PL_repackage s (↑yu : F) (↑zu : F) (↑xu : F) AL AO SL,
    PR_repackage s (↑yu : F) (↑zu : F) (↑xu : F) AR SR] at h2
  exact h2

omit [DecidableEq F] [DecidableEq G] in
/-- Splitting off the excluded index `c` from a guarded sum (the base `eq1_RHS_repackage` at an
arbitrary special index). -/
lemma eq1_RHS_repackage' {N : ℕ} (x : F) (c : ℕ) (hc : c < N) (special : G) (T : Fin N → G) :
    x ^ c • special + (∑ i : Fin N, if (i : ℕ) = c then (0 : G) else x ^ (i : ℕ) • T i)
      = ∑ r : Fin N, x ^ (r : ℕ) • (if (r : ℕ) = c then special else T r) := by
  rw [← sum_pow_smul_ite x c hc special, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) = c <;> simp [hi, smul_zero]

set_option maxHeartbeats 1600000 in
omit [DecidableEq F] in
/-- The verifier's first check (`eq1`), restated as `⟨a,b⟩·g + τₓ·h = ∑ᵣ xʳ·T'ᵣ` with the special
`(c+1)`-coefficient `(δ−w_c)·g − ⟨w_V,V⟩`. -/
lemma arithVerifyPreR_eq1 {n q m c : ℕ} (s : Statement F G n q m c)
    (AL AR AO SL SR : G) (yu zu xu ru : Fˣ) (T : Fin (2 * c + 5) → G)
    (τx μL μR : F) (a b : Fin n → F)
    (h : arithVerifyPreR s ((AL, AR, AO, SL, SR), yu, zu, T, xu,
        (τx, μL, μR, a, b), ru, PUnit.unit) = true) :
    ip a b • s.g + τx • s.h
      = ∑ r : Fin (2 * c + 5), (↑xu : F) ^ (r : ℕ) • (if (r : ℕ) = c + 1 then
          ((ip (hadamard (vinv (powers (↑yu : F) n)) ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WR)))
                ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WL))
              - (↑zu : F) * ip (powers (↑zu : F) q) s.cc) • s.g
            - msm ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WV)) s.V)
          else T r) := by
  simp only [arithVerifyPreR, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [eq1_RHS_repackage' (↑xu : F) (c + 1) (by omega)
      ((ip (hadamard (vinv (powers (↑yu : F) n)) ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WR)))
            ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WL))
          - (↑zu : F) * ip (powers (↑zu : F) q) s.cc) • s.g
        - msm ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WV)) s.V) T] at h
  exact h.1

/-! ## The binding interpolation in `r` -/

omit [DecidableEq F] [DecidableEq G] in
/-- **The binding interpolation.** The improved `eq2` identity is *affine* in the binding
challenge `r`, and the prover's opening `(a, b, μ_L, μ_R)` is sent **before** `r`: from the same
node's two `r`-children, pure linear algebra pins the `𝐆`-side `P_L = A + μ_L·H` and the
`𝐇`-side `P_R = B + μ_R·H` *exactly* — no binding assumption, no honesty assumption, and no
stray cross-component. (This is the reason the extracted witness needs no `aux` slot: the
`𝐇`-mass of every `P_L`-coefficient is forced to `0`.) -/
lemma r_interpolate {PL PR A B H : G} {μL μR r₁ r₂ : F} (hne : r₁ ≠ r₂)
    (h₁ : PL + r₁ • PR = A + r₁ • B + (μL + r₁ * μR) • H)
    (h₂ : PL + r₂ • PR = A + r₂ • B + (μL + r₂ * μR) • H) :
    PL = A + μL • H ∧ PR = B + μR • H := by
  have hr : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr hne
  have hsub : (r₁ - r₂) • PR = (r₁ - r₂) • (B + μR • H) := by
    have e : (r₁ - r₂) • PR = (r₁ - r₂) • B + ((r₁ - r₂) * μR) • H := by
      linear_combination (norm := module) h₁ - h₂
    rw [e, smul_add, smul_smul]
  have hPR : PR = B + μR • H := by
    have e := congrArg (fun g : G => (r₁ - r₂)⁻¹ • g) hsub
    simpa only [inv_smul_smul₀ hr] using e
  refine ⟨?_, hPR⟩
  rw [hPR] at h₁
  linear_combination (norm := module) h₁

/-! ## `x`-level Vandermonde extraction -/

omit [DecidableEq F] [DecidableEq G] in
/-- **`x`-level extraction (two-block form).** From `N` accepting openings
`∑ₚ xₗᵖ • Pc p = ⟨v l, gs⟩ + μ l · hG` at distinct `xₗ`, each coefficient `Pc p` opens with the
inverse-Vandermonde combinations of the `(v, μ)` data. Used once with `gs := 𝐆` (the `P_L`
side) and once with `gs := 𝐲⁻¹⊙𝐇` (the `P_R` side). -/
lemma coeff_open {N nn : ℕ} (gs : Fin nn → G) (hG : G) (Pc : Fin N → G)
    (x : Fin N → F) (hx : Function.Injective x)
    (v : Fin N → (Fin nn → F)) (μ : Fin N → F)
    (heq : ∀ l, (∑ p : Fin N, x l ^ (p : ℕ) • Pc p) = msm (v l) gs + μ l • hG)
    (p : Fin N) :
    Pc p = msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • v l) gs
      + (∑ l, (Matrix.vandermonde x)⁻¹ p l • μ l) • hG := by
  refine congrFun (vandermonde_coeff_unique x hx Pc
    (fun p => msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • v l) gs
      + (∑ l, (Matrix.vandermonde x)⁻¹ p l • μ l) • hG) ?_) p
  intro l
  rw [heq l]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ ℓ : Fin N, x l ^ (ℓ : ℕ)
          • msm (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • v l') gs)
        = msm (∑ ℓ : Fin N, x l ^ (ℓ : ℕ)
          • (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • v l')) gs from by
      rw [msm_sum_left]; exact Finset.sum_congr rfl fun ℓ _ => (msm_smul_left _ _ _).symm]
    rw [← vandermonde_recover x hx v l]
  · simp only [← smul_assoc, ← Finset.sum_smul]
    rw [← vandermonde_recover x hx μ l]

/-! ## `eq1` special-coefficient extraction -/

omit [DecidableEq F] [DecidableEq G] in
/-- **eq1 special coefficient (generic index).** From the `eq1` family at `N` distinct `x`, the
group element `V'` appearing in the special `c`-coefficient `D·g − V'` is a `(g, h)`-combination
of the recovered data. (The base `eq1_special_extract` with the special index decoupled from the
statement dimensions; instantiated at `c := c+1`, `N := 2c+5`, `V' := ⟨w_V, V⟩`.) -/
lemma eq1_special_extract' {N c : ℕ} (hc : c < N) (g h V' : G) (D : F)
    (x : Fin N → F) (hx : Function.Injective x)
    (tHat τx : Fin N → F) (T : Fin N → G)
    (heq : ∀ l, tHat l • g + τx l • h
        = ∑ r : Fin N, x l ^ (r : ℕ) • (if (r : ℕ) = c then (D • g - V') else T r)) :
    V' = (D - ∑ l, (Matrix.vandermonde x)⁻¹ ⟨c, hc⟩ l * tHat l) • g
        + (-∑ l, (Matrix.vandermonde x)⁻¹ ⟨c, hc⟩ l * τx l) • h := by
  have hco := vandermonde_coeff x hx _ _ (fun l => (heq l).symm) ⟨c, hc⟩
  rw [if_pos rfl] at hco
  simp only [smul_add, Finset.sum_add_distrib, smul_smul, ← Finset.sum_smul] at hco
  have h2 : V' = D • g - ((∑ l, (Matrix.vandermonde x)⁻¹ ⟨c, hc⟩ l * tHat l) • g
      + (∑ l, (Matrix.vandermonde x)⁻¹ ⟨c, hc⟩ l * τx l) • h) := by
    rw [← hco]; abel
  rw [h2]; module

end Sigma.Protocols.GBPImproved
