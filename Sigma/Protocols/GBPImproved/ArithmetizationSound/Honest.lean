/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.Pcoef

/-!
# Improved-arithmetization soundness: honest coefficient families and the `(★)` assembly

The honest sparse `f_L`/`f_R` coefficient families of the improved layout (`honestFL'` and
`honestFR'`, degree index `Fin (c+3)`, **no `aux` slot**), their per-slot evaluations
(`honestFL'_at_*`, `honestFR'_at_*`), the slot decompositions (`q_slot_casesL/R`), and the
**constraint-free `t`-polynomial expansion** `tcoeff_expandI` at the improved target degree
`c+1`: the `(c+1)`-convolution coefficient of `⟨f_L, f_R⟩` expands into
`δ + ⟨R1CS linear terms⟩ + ∑ᵢ yⁱ(aLᵢ·aRᵢ − aOᵢ)`, keeping the Hadamard term explicit so the
`(★)` deaggregation can recover the constraints.

`star_at_bundle'` assembles the per-bundle relation `(★)` from the leaf-data consistency
(`Hla`/`Hlb`) and the `eq1` `(c+1)`-coefficient identity (`Heq`), via the degree-`c+1`
specializations `tcoeff_recover'`/`sum_truncate'` of the base Vandermonde machinery and the
reused `star_from_combine`. Unlike the base proof, **every** convolution-relevant slot of both
families is pinned, so no `conv_eq` escape hatch is needed.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## The honest sparse coefficient families (no `aux`) -/

/-- The honest sparse `f_L` coefficient family of the improved layout (degree index
`p : Fin (c+3)`), built from the extracted wires `aL, aO, aC` and mask `sL`:
`X⁰ ↦ a_L + w_R∘y⁻¹`, `X¹ ↦ a_O`, `X^{j+2} ↦ a_C⁽ʲ⁾`, `X^{c+2} ↦ s_L`. -/
def honestFL' {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) (p : Fin (c + 3)) : Fin n → F :=
  (((if (p : ℕ) = 0 then
        fun t => aL t + (z • powers z q ᵥ* s.WR) t * vinv (powers (↑yu) n) t
      else 0) +
      if (p : ℕ) = 1 then aO else 0) +
    ∑ j : Fin c, if (p : ℕ) = (j : ℕ) + 2 then aC j else 0) +
  if (p : ℕ) = c + 2 then sL else 0

/-- The honest sparse `f_R` coefficient family of the improved layout (degree index
`ℓ : Fin (c+3)`), built from the extracted wires `aR` and mask `sR` (**no `aux` slots**):
`X^{c−j−1} ↦ w_C⁽ʲ⁾`, `X^c ↦ w_O − y`, `X^{c+1} ↦ y∘a_R + w_L`, `X^{c+2} ↦ y∘s_R`. -/
def honestFR' {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aR sR : Fin n → F) (ℓ : Fin (c + 3)) : Fin n → F :=
  (((∑ j : Fin c, if (ℓ : ℕ) = c - (j : ℕ) - 1 then
        z • powers z q ᵥ* s.WC j else 0) +
      if (ℓ : ℕ) = c then
        (fun t => (z • powers z q ᵥ* s.WO) t - powers (↑yu) n t) else 0) +
    if (ℓ : ℕ) = c + 1 then
      (fun t => powers (↑yu) n t * aR t + (z • powers z q ᵥ* s.WL) t) else 0) +
  if (ℓ : ℕ) = c + 2 then (fun t => powers (↑yu) n t * sR t) else 0

/-! ## Per-slot evaluations -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL'` at degree `0` (the `A_L` slot). -/
lemma honestFL'_at_AL {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) :
    honestFL' s yu z aL aO sL aC ⟨0, by omega⟩
      = fun t => aL t + (z • powers z q ᵥ* s.WR) t * vinv (powers (↑yu) n) t := by
  simp only [honestFL', if_true,
    show ((0 : ℕ) = 1) = False from eq_false (by omega),
    show ((0 : ℕ) = c + 2) = False from eq_false (by omega),
    Finset.sum_eq_zero (fun (j : Fin c) _ => if_neg (show ¬((0 : ℕ) = (j : ℕ) + 2) by omega)),
    if_false, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL'` at degree `1` (the `A_O` slot). -/
lemma honestFL'_at_AO {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) :
    honestFL' s yu z aL aO sL aC ⟨1, by omega⟩ = aO := by
  simp only [honestFL', if_true,
    show ((1 : ℕ) = 0) = False from eq_false (by omega),
    show ((1 : ℕ) = c + 2) = False from eq_false (by omega),
    Finset.sum_eq_zero (fun (j : Fin c) _ => if_neg (show ¬((1 : ℕ) = (j : ℕ) + 2) by omega)),
    if_false, add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL'` at degree `k+2` (the `A_C⁽ᵏ⁾` slot). -/
lemma honestFL'_at_AC {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) (k : Fin c) :
    honestFL' s yu z aL aO sL aC ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩ = aC k := by
  have hk := k.isLt
  have hac : ∀ j : Fin c, ((k : ℕ) + 2 = (j : ℕ) + 2) = (j = k) := fun j => by
    rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  simp only [honestFL',
    show ((k : ℕ) + 2 = 0) = False from eq_false (by omega),
    show ((k : ℕ) + 2 = 1) = False from eq_false (by omega),
    show ((k : ℕ) + 2 = c + 2) = False from eq_false (by omega),
    hac, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL'` at degree `c+2` (the `S_L` slot). -/
lemma honestFL'_at_SL {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) :
    honestFL' s yu z aL aO sL aC ⟨c + 2, by omega⟩ = sL := by
  have hac : ∀ j : Fin c, (c + 2 = (j : ℕ) + 2) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [honestFL', if_true,
    show (c + 2 = 0) = False from eq_false (by omega),
    show (c + 2 = 1) = False from eq_false (by omega),
    hac, if_false, Finset.sum_const_zero, add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR'` at degree `c−k−1` (the public `W̃_C⁽ᵏ⁾` slot). -/
lemma honestFR'_at_WtC {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aR sR : Fin n → F) (k : Fin c) :
    honestFR' s yu z aR sR ⟨c - (k : ℕ) - 1, by have := k.isLt; omega⟩
      = z • powers z q ᵥ* s.WC k := by
  have hk := k.isLt
  have hwc : ∀ j : Fin c, (c - (k : ℕ) - 1 = c - (j : ℕ) - 1) = (j = k) := fun j => by
    have := j.isLt
    rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  simp only [honestFR',
    show (c - (k : ℕ) - 1 = c) = False from eq_false (by omega),
    show (c - (k : ℕ) - 1 = c + 1) = False from eq_false (by omega),
    show (c - (k : ℕ) - 1 = c + 2) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR'` at degree `c` (the public `W̃_O` slot). -/
lemma honestFR'_at_WtO {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aR sR : Fin n → F) :
    honestFR' s yu z aR sR ⟨c, by omega⟩
      = fun t => (z • powers z q ᵥ* s.WO) t - powers (↑yu) n t := by
  have hwc : ∀ j : Fin c, ((c : ℕ) = c - (j : ℕ) - 1) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [honestFR', if_true,
    show ((c : ℕ) = c + 1) = False from eq_false (by omega),
    show ((c : ℕ) = c + 2) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_const_zero, zero_add, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR'` at degree `c+1` (the `A_R + W̃_L` slot). -/
lemma honestFR'_at_AR {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aR sR : Fin n → F) :
    honestFR' s yu z aR sR ⟨c + 1, by omega⟩
      = fun t => powers (↑yu) n t * aR t + (z • powers z q ᵥ* s.WL) t := by
  have hwc : ∀ j : Fin c, (c + 1 = c - (j : ℕ) - 1) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [honestFR', if_true,
    show (c + 1 = c) = False from eq_false (by omega),
    show (c + 1 = c + 2) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_const_zero, zero_add, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR'` at degree `c+2` (the `S_R` slot). -/
lemma honestFR'_at_SR {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aR sR : Fin n → F) :
    honestFR' s yu z aR sR ⟨c + 2, by omega⟩ = fun t => powers (↑yu) n t * sR t := by
  have hwc : ∀ j : Fin c, (c + 2 = c - (j : ℕ) - 1) = False := fun j =>
    eq_false (by have := j.isLt; omega)
  simp only [honestFR', if_true,
    show (c + 2 = c) = False from eq_false (by omega),
    show (c + 2 = c + 1) = False from eq_false (by omega),
    hwc, if_false, Finset.sum_const_zero, zero_add]

/-! ## Slot decompositions -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Every degree `ℓ : Fin (c+3)` lands in exactly one `f_L` slot: `A_L` at `0`, `A_O` at `1`,
`A_C⁽ᵏ⁾` at `k+2`, or `S_L` at `c+2`. (The improved layout is dense: no zero slots.) -/
lemma q_slot_casesL {c : ℕ} (ℓ : Fin (c + 3)) :
    (ℓ : ℕ) = 0 ∨ (ℓ : ℕ) = 1 ∨ (∃ k : Fin c, (ℓ : ℕ) = (k : ℕ) + 2) ∨ (ℓ : ℕ) = c + 2 := by
  have hq := ℓ.isLt
  by_cases h0 : (ℓ : ℕ) = 0
  · exact Or.inl h0
  by_cases h1 : (ℓ : ℕ) = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : (ℓ : ℕ) = c + 2
  · exact Or.inr (Or.inr (Or.inr h2))
  · exact Or.inr (Or.inr (Or.inl ⟨⟨(ℓ : ℕ) - 2, by omega⟩, by simp only; omega⟩))

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Every degree `ℓ : Fin (c+3)` lands in exactly one `f_R` slot: `W̃_C⁽ᵏ⁾` at `c−k−1`, `W̃_O`
at `c`, `A_R` at `c+1`, or `S_R` at `c+2`. -/
lemma q_slot_casesR {c : ℕ} (ℓ : Fin (c + 3)) :
    (∃ k : Fin c, (ℓ : ℕ) = c - (k : ℕ) - 1) ∨ (ℓ : ℕ) = c ∨ (ℓ : ℕ) = c + 1
      ∨ (ℓ : ℕ) = c + 2 := by
  have hq := ℓ.isLt
  by_cases hlt : (ℓ : ℕ) < c
  · exact Or.inl ⟨⟨c - (ℓ : ℕ) - 1, by omega⟩, by simp only; omega⟩
  by_cases h0 : (ℓ : ℕ) = c
  · exact Or.inr (Or.inl h0)
  by_cases h1 : (ℓ : ℕ) = c + 1
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-! ## The constraint-free `t`-polynomial expansion at target `c+1` -/

set_option maxHeartbeats 1600000 in
omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The constraint-free `t`-polynomial expansion** (the soundness counterpart of the
completeness key lemma `tcoeff'_eq`): the `(c+1)`-coefficient of `⟨f_L, f_R⟩` — the honest
sparse improved-layout polynomials built from extracted wires — expands, *without using any
R1CS/Hadamard constraint*, into `δ + ⟨linear R1CS terms⟩ + ∑ᵢ yⁱ(aLᵢ·aRᵢ − aOᵢ)`. Only the
pairs `(0,c+1)`, `(1,c)`, `(j+2, c−j−1)` survive the guard `p+ℓ = c+1`. -/
lemma tcoeff_expandI {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aL aR aO sL sR : Fin n → F) (aC : Fin c → Fin n → F) :
    (∑ p : Fin (c + 3), ∑ ℓ : Fin (c + 3),
        if (p : ℕ) + (ℓ : ℕ) = c + 1 then
          ip (honestFL' s yu z aL aO sL aC p) (honestFR' s yu z aR sR ℓ) else 0)
      = ip (hadamard (vinv (powers (↑yu) n)) (z • powers z q ᵥ* s.WR))
            (z • powers z q ᵥ* s.WL)
          + ip aL (z • powers z q ᵥ* s.WL)
          + ip aR (z • powers z q ᵥ* s.WR)
          + ip aO (z • powers z q ᵥ* s.WO)
          + (∑ k, ip (aC k) (z • powers z q ᵥ* s.WC k))
          + ∑ t, powers (↑yu) n t * (aL t * aR t - aO t) := by
  simp only [honestFL', honestFR']
  simp only [ip_add_left, ip_sum_left, ip_ite_left, ite_zero_add, ite_zero_sum,
    ite_ite_zero, Finset.sum_add_distrib]
  rw [double_sum_collapse 0 (c + 1) (by omega) (by omega) (by omega),
    double_sum_collapse 1 (c + 1) (by omega) (by omega) (by omega),
    double_sum_zero (c + 2) (c + 1) (by omega),
    family_collapse (fun j => (j : ℕ) + 2) (c + 1)
      (fun j => by have := j.isLt; dsimp only; omega)
      (fun j => by have := j.isLt; dsimp only; omega)
      (fun j => by have := j.isLt; dsimp only; omega)]
  have hidx0 : c + 1 - 0 = c + 1 := by omega
  have hidx1 : c + 1 - 1 = c := by omega
  have hidxj : ∀ j : Fin c, c + 1 - ((j : ℕ) + 2) = c - (j : ℕ) - 1 := fun j => by
    have := j.isLt; omega
  simp only [hidx0, hidx1, hidxj, ip_add_right, ip_sum_right, ip_ite_right]
  have f1 : ∀ j : Fin c, (c + 1 = c - (j : ℕ) - 1) = False := fun j => eq_false (by omega)
  have f2 : (c + 1 = c) = False := eq_false (by omega)
  have f3 : (c + 1 = c + 2) = False := eq_false (by omega)
  have f4 : ∀ j : Fin c, (c = c - (j : ℕ) - 1) = False :=
    fun j => eq_false (by have := j.isLt; omega)
  have f5 : (c = c + 1) = False := eq_false (by omega)
  have f6 : (c = c + 2) = False := eq_false (by omega)
  have eMm1 : ∀ j : Fin c, (c - (j : ℕ) - 1 = c) = False :=
    fun j => eq_false (by have := j.isLt; omega)
  have eMm2 : ∀ j : Fin c, (c - (j : ℕ) - 1 = c + 1) = False :=
    fun j => eq_false (by have := j.isLt; omega)
  have eMm3 : ∀ j : Fin c, (c - (j : ℕ) - 1 = c + 2) = False :=
    fun j => eq_false (by have := j.isLt; omega)
  have eMmj : ∀ j j' : Fin c, (c - (j : ℕ) - 1 = c - (j' : ℕ) - 1) = (j' = j) := fun j j' => by
    have hj := j.isLt; have hj' := j'.isLt
    rw [eq_iff_iff]
    exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  simp only [f1, f2, f3, f4, f5, f6, eMm1, eMm2, eMm3, eMmj, if_true, if_false,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, add_zero, zero_add]
  have hvyinv := powers_mul_vinv yu n
  have hI : ip (fun t => aL t + (z • powers z q ᵥ* s.WR) t * vinv (powers (↑yu) n) t)
          (fun t => powers (↑yu) n t * aR t + (z • powers z q ᵥ* s.WL) t)
        + ip aO (fun t => (z • powers z q ᵥ* s.WO) t - powers (↑yu) n t)
      = ip (hadamard (vinv (powers (↑yu) n)) (z • powers z q ᵥ* s.WR))
            (z • powers z q ᵥ* s.WL)
        + ip aL (z • powers z q ᵥ* s.WL)
        + ip aR (z • powers z q ᵥ* s.WR)
        + ip aO (z • powers z q ᵥ* s.WO)
        + ∑ t, powers (↑yu) n t * (aL t * aR t - aO t) := by
    simp only [ip, hadamard]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    linear_combination ((z • powers z q ᵥ* s.WR) t * aR t) * (hvyinv t)
  linear_combination hI

/-! ## Degree-`c+1` specializations of the Vandermonde machinery -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The coupling at target `c+1`** (the base `tcoeff_recover` at `np := c+1`): the
`(c+1)`-Vandermonde coefficient of the leaf inner products equals the `(c+1)`-convolution
coefficient of the two coefficient families. -/
lemma tcoeff_recover' {n c : ℕ} (x : Fin (2 * c + 5) → F) (hx : Function.Injective x)
    (fL fR : Fin (c + 3) → (Fin n → F)) :
    (∑ l : Fin (2 * c + 5), (Matrix.vandermonde x)⁻¹ ⟨c + 1, by omega⟩ l
        • ip (fun t => ∑ p : Fin (c + 3), x l ^ (p : ℕ) * fL p t)
             (fun t => ∑ ℓ : Fin (c + 3), x l ^ (ℓ : ℕ) * fR ℓ t))
      = ∑ p : Fin (c + 3), ∑ ℓ : Fin (c + 3),
          if (p : ℕ) + (ℓ : ℕ) = c + 1 then ip (fL p) (fR ℓ) else 0 :=
  tcoeff_recover (np := c + 1) x hx fL fR (by omega)

omit [DecidableEq F] in
/-- **Degree truncation at target `c+1`** (the base `sum_truncate` at `np := c+1`): a
`2c+5`-coefficient family agreeing with a `(c+3)`-family below `c+3` and vanishing above
collapses to the lower-degree sum. -/
lemma sum_truncate' {M : Type*} [AddCommMonoid M] [Module F M] {c : ℕ} (x : F)
    (cf : Fin (2 * c + 5) → M) (d : Fin (c + 3) → M)
    (H1 : ∀ ℓ : Fin (c + 3), cf ⟨(ℓ : ℕ), by omega⟩ = d ℓ)
    (H2 : ∀ p : Fin (2 * c + 5), c + 3 ≤ (p : ℕ) → cf p = 0) :
    (∑ p : Fin (2 * c + 5), x ^ (p : ℕ) • cf p) = ∑ ℓ : Fin (c + 3), x ^ (ℓ : ℕ) • d ℓ :=
  sum_truncate (np := c + 1) x cf d H1 H2

/-! ## The per-bundle relation `(★)` -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The per-bundle relation `(★)`** for the improved layout. From the consistency that the
leaf data are the honest polynomials (`Hla`/`Hlb`) and the `eq1` `(c+1)`-coefficient identity
(`Heq`: `= δ − w_c − ⟨w_V, v⟩`), the tcoeff side (`tcoeff_recover'` + `tcoeff_expandI`) gives
`δ + R1CS_lin + Had`; equating and cancelling `δ` yields
`Had + ∑_q z^{ℓ+1}·(R1CS row ℓ) = 0` (`star_from_combine`, reused from the base proof). -/
lemma star_at_bundle' {n q m c : ℕ} (s : Statement F G n q m c) (yu : Fˣ) (z : F)
    (aL aR aO sL sR : Fin n → F) (aC : Fin c → Fin n → F) (v : Fin m → F)
    (x : Fin (2 * c + 5) → F) (hx : Function.Injective x)
    (la lb : Fin (2 * c + 5) → (Fin n → F))
    (Hla : ∀ l, la l = fun t => ∑ p : Fin (c + 3),
      (x l) ^ (p : ℕ) * honestFL' s yu z aL aO sL aC p t)
    (Hlb : ∀ l, lb l = fun t => ∑ ℓ : Fin (c + 3),
      (x l) ^ (ℓ : ℕ) * honestFR' s yu z aR sR ℓ t)
    (Heq : (∑ l, (Matrix.vandermonde x)⁻¹ ⟨c + 1, by omega⟩ l • ip (la l) (lb l))
      = (ip (hadamard (vinv (powers (↑yu : F) n)) (z • powers z q ᵥ* s.WR))
            (z • powers z q ᵥ* s.WL)
          - z * ip (powers z q) s.cc)
        - ip (z • (powers z q ᵥ* s.WV)) v) :
    (∑ t, powers (↑yu : F) n t * (aL t * aR t - aO t))
      + ∑ ℓ : Fin q, z ^ ((ℓ : ℕ) + 1)
          * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k)
              + s.WV *ᵥ v + s.cc) ℓ = 0 := by
  have htc : (∑ l, (Matrix.vandermonde x)⁻¹ ⟨c + 1, by omega⟩ l • ip (la l) (lb l))
      = ip (hadamard (vinv (powers (↑yu) n)) (z • powers z q ᵥ* s.WR))
            (z • powers z q ᵥ* s.WL)
          + ip aL (z • powers z q ᵥ* s.WL)
          + ip aR (z • powers z q ᵥ* s.WR)
          + ip aO (z • powers z q ᵥ* s.WO)
          + (∑ k, ip (aC k) (z • powers z q ᵥ* s.WC k))
          + ∑ t, powers (↑yu) n t * (aL t * aR t - aO t) := by
    rw [show (∑ l, (Matrix.vandermonde x)⁻¹ ⟨c + 1, by omega⟩ l • ip (la l) (lb l))
        = ∑ l, (Matrix.vandermonde x)⁻¹ ⟨c + 1, by omega⟩ l
            • ip (fun t => ∑ p : Fin (c + 3),
                  (x l) ^ (p : ℕ) * honestFL' s yu z aL aO sL aC p t)
                 (fun t => ∑ ℓ : Fin (c + 3), (x l) ^ (ℓ : ℕ) * honestFR' s yu z aR sR ℓ t)
        from by simp only [Hla, Hlb]]
    rw [tcoeff_recover' x hx (honestFL' s yu z aL aO sL aC) (honestFR' s yu z aR sR)]
    exact tcoeff_expandI s yu z aL aR aO sL sR aC
  exact star_from_combine s aL aR aO aC v z
    (∑ t, powers (↑yu : F) n t * (aL t * aR t - aO t))
    (by linear_combination htc.symm.trans Heq)

end Sigma.Protocols.GBPImproved
