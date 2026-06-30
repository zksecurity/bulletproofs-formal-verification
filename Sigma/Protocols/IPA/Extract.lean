/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.IPA.Fold

/-!
# Single-round witness extraction for the inner-product argument

The algebraic core of computational special soundness, following Bulletproofs 2017/1066,
Protocol 2. One folding round reduces a length-`2m` instance with generators `(𝐠,𝐡)` and
commitment `P`, cross-terms `(L,R)`, to a length-`m` instance per challenge `ξ`. Given **four**
challenges with pairwise distinct squares and a witness for each folded instance, we recover a
witness for the parent instance, *or* a non-trivial discrete-log relation among the generators.

This file is self-contained algebra over `msm`/`ip`; it is wired into the per-node
extractor in `Sigma.Protocols.IPA.NodeExtract`.
-/

namespace Sigma.Protocols.IPA

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## `msm` linearity in the coefficient vector -/

/-- `msm` scales by a constant pulled out of the coefficient vector. -/
lemma msm_smul_coeff {ι : Type*} [Fintype ι] (c : F) (v : ι → F) (gs : ι → G) :
    msm (fun i => c * v i) gs = c • msm v gs := by
  simp only [msm, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]

/-- `msm` is additive in the coefficient vector. -/
lemma msm_add_coeff {ι : Type*} [Fintype ι] (v w : ι → F) (gs : ι → G) :
    msm (fun i => v i + w i) gs = msm v gs + msm w gs := by
  simp only [msm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [add_smul]

/-- `msm` against the folded `𝐠` generators splits along the fold weights. -/
lemma msm_foldG {m : ℕ} (v : Fin m → F) (ξ : F) (gL gR : Fin m → G) :
    msm v (foldG ξ gL gR) = ξ⁻¹ • msm v gL + ξ • msm v gR := by
  simp only [msm, foldG, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, smul_smul, mul_comm]

/-- `msm` against the folded `𝐡` generators splits along the fold weights. -/
lemma msm_foldH {m : ℕ} (v : Fin m → F) (ξ : F) (hL hR : Fin m → G) :
    msm v (foldH ξ hL hR) = ξ • msm v hL + ξ⁻¹ • msm v hR := by
  simp only [msm, foldH, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, smul_smul, mul_comm]

/-- `msm` commutes with a finite sum of coefficient vectors. -/
lemma msm_sum_coeff {ι κ : Type*} [Fintype ι] [Fintype κ] (c : κ → ι → F) (gs : ι → G) :
    msm (fun i => ∑ k, c k i) gs = ∑ k, msm (c k) gs := by
  simp only [msm, Finset.sum_smul]
  rw [Finset.sum_comm]

/-! ## Bilinearity of the scalar inner product `ip` -/

private lemma ip_add_left {ι : Type*} [Fintype ι] (a a' b : ι → F) :
    ip (fun i => a i + a' i) b = ip a b + ip a' b := by
  simp only [ip, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring

private lemma ip_smul_left {ι : Type*} [Fintype ι] (c : F) (a b : ι → F) :
    ip (fun i => c * a i) b = c * ip a b := by
  simp only [ip, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

private lemma ip_add_right {ι : Type*} [Fintype ι] (a b b' : ι → F) :
    ip a (fun i => b i + b' i) = ip a b + ip a b' := by
  simp only [ip, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring

private lemma ip_smul_right {ι : Type*} [Fintype ι] (c : F) (a b : ι → F) :
    ip a (fun i => c * b i) = c * ip a b := by
  simp only [ip, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Polynomial vanishing at distinct points (Vandermonde) -/

/-- A polynomial of degree `< n` (given by coefficients `c : Fin n → F`) vanishing at `n`
distinct points `y` is the zero polynomial: all its coefficients vanish. Proved via
invertibility of the Vandermonde matrix. -/
lemma poly_vanish {n : ℕ} {y : Fin n → F} (hy : Function.Injective y) {c : Fin n → F}
    (h : ∀ j, ∑ i, c i * (y j) ^ (i : ℕ) = 0) : c = 0 := by
  have hdet : (Matrix.vandermonde y).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff).mpr hy
  have hunit : IsUnit (Matrix.vandermonde y).det := isUnit_iff_ne_zero.mpr hdet
  have hmv : (Matrix.vandermonde y).mulVec c = 0 := by
    funext j
    simp only [Matrix.mulVec, Matrix.vandermonde_apply, dotProduct, Pi.zero_apply]
    rw [← h j]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : (Matrix.vandermonde y)⁻¹.mulVec ((Matrix.vandermonde y).mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  rw [hmv, Matrix.mulVec_zero] at key
  exact key.symm

/-- A `±x`-symmetric Laurent polynomial with monomials `x³, x, x⁻¹, x⁻³` vanishing at four
points with pairwise distinct squares has all coefficients zero. (After `×x³` it is a cubic in
`x²`, with four distinct roots `x²`.) -/
lemma laurent_cubic_vanish {ξ : Fin 4 → F} (hξ : ∀ j, ξ j ≠ 0)
    (hsq : Function.Injective (fun j => (ξ j) ^ 2)) {c3 c1 cm1 cm3 : F}
    (h : ∀ j, c3 * (ξ j) ^ 3 + c1 * (ξ j) + cm1 * (ξ j)⁻¹ + cm3 * (ξ j)⁻¹ ^ 3 = 0) :
    c3 = 0 ∧ c1 = 0 ∧ cm1 = 0 ∧ cm3 = 0 := by
  set y : Fin 4 → F := fun j => (ξ j) ^ 2 with hy
  have hc : (![cm3, cm1, c1, c3] : Fin 4 → F) = 0 := by
    refine poly_vanish hsq (fun j => ?_)
    have hxj : ξ j ≠ 0 := hξ j
    have hreduce : (∑ i, (![cm3, cm1, c1, c3] : Fin 4 → F) i * (y j) ^ (i : ℕ))
        = (ξ j) ^ 3 * (c3 * (ξ j) ^ 3 + c1 * (ξ j) + cm1 * (ξ j)⁻¹ + cm3 * (ξ j)⁻¹ ^ 3) := by
      rw [Fin.sum_univ_four]
      have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
      simp only [hy, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
        Fin.val_two, e3]
      field_simp
      ring
    rw [hreduce, h j, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrFun hc 3; simpa using this
  · have := congrFun hc 2; simpa using this
  · have := congrFun hc 1; simpa using this
  · have := congrFun hc 0; simpa using this

/-- A `±x`-symmetric Laurent polynomial with monomials `x², 1, x⁻²` vanishing at three points
with pairwise distinct squares has all coefficients zero. (After `×x²` it is a quadratic in
`x²`, with three distinct roots `x²`.) -/
lemma laurent_quad_vanish {ξ : Fin 3 → F} (hξ : ∀ j, ξ j ≠ 0)
    (hsq : Function.Injective (fun j => (ξ j) ^ 2)) {c2 c0 cm2 : F}
    (h : ∀ j, c2 * (ξ j) ^ 2 + c0 + cm2 * (ξ j)⁻¹ ^ 2 = 0) :
    c2 = 0 ∧ c0 = 0 ∧ cm2 = 0 := by
  set y : Fin 3 → F := fun j => (ξ j) ^ 2 with hy
  have hc : (![cm2, c0, c2] : Fin 3 → F) = 0 := by
    refine poly_vanish hsq (fun j => ?_)
    have hxj : ξ j ≠ 0 := hξ j
    have hreduce : (∑ i, (![cm2, c0, c2] : Fin 3 → F) i * (y j) ^ (i : ℕ))
        = (ξ j) ^ 2 * (c2 * (ξ j) ^ 2 + c0 + cm2 * (ξ j)⁻¹ ^ 2) := by
      rw [Fin.sum_univ_three]
      simp only [hy, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two]
      field_simp
      ring
    rw [hreduce, h j, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun hc 2; simpa using this
  · have := congrFun hc 1; simpa using this
  · have := congrFun hc 0; simpa using this

/-- The coefficient matrix of the `(ξ², 1, ξ⁻²)` reconstruction system at three challenges. -/
def vmat (ζ : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  fun j r => ![(ζ j) ^ 2, 1, ((ζ j)⁻¹) ^ 2] r

/-- The coefficient matrix is invertible when the three challenges have distinct (nonzero)
squares; this follows from `laurent_quad_vanish`. -/
lemma vmat_det_ne_zero {ζ : Fin 3 → F} (hζ : ∀ j, ζ j ≠ 0)
    (hsq : Function.Injective (fun j => (ζ j) ^ 2)) : (vmat ζ).det ≠ 0 := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv, hmv⟩
  apply hv
  have hcoord : ∀ j, v 0 * (ζ j) ^ 2 + v 1 + v 2 * ((ζ j)⁻¹) ^ 2 = 0 := by
    intro j
    have := congrFun hmv j
    simp only [Matrix.mulVec, dotProduct, vmat, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Pi.zero_apply] at this
    linear_combination this
  obtain ⟨h0, h1, h2⟩ := laurent_quad_vanish hζ hsq hcoord
  funext j; fin_cases j <;> simp_all

/-- **Explicit, computable reconstruction coefficients `ν`** of the 1066 extractor: the
Cramer/adjugate solution of the `3×3` system `(ξ², 1, ξ⁻²)·ν = target`. This is a genuine
field-arithmetic algorithm (determinant + adjugate over `Fin 3`), not a `Classical.choice`. -/
def nuVec (ζ target : Fin 3 → F) : Fin 3 → F :=
  (vmat ζ).transpose.det⁻¹ • (vmat ζ).transpose.adjugate.mulVec target

/-- `nuVec` solves the `(ξ², 1, ξ⁻²)` system: it satisfies the three defining equations whenever
the challenges have distinct (nonzero) squares. -/
lemma nuVec_spec {ζ : Fin 3 → F} (hζ : ∀ j, ζ j ≠ 0)
    (hsq : Function.Injective (fun j => (ζ j) ^ 2)) (target : Fin 3 → F) :
    (∑ j, nuVec ζ target j * (ζ j) ^ 2 = target 0) ∧
    (∑ j, nuVec ζ target j = target 1) ∧
    (∑ j, nuVec ζ target j * ((ζ j)⁻¹) ^ 2 = target 2) := by
  have hBdet : (vmat ζ).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact vmat_det_ne_zero hζ hsq
  -- `nuVec` solves the transposed system `Nᵀ · ν = target`.
  have hsolve : (vmat ζ).transpose.mulVec (nuVec ζ target) = target := by
    unfold nuVec
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hBdet, one_smul]
  -- Each row `r` of `Nᵀ · ν` is exactly the `r`-th equation.
  have hrow : ∀ (ν : Fin 3 → F),
      ((vmat ζ).transpose.mulVec ν) 0 = ∑ j, ν j * (ζ j) ^ 2 ∧
      ((vmat ζ).transpose.mulVec ν) 1 = ∑ j, ν j ∧
      ((vmat ζ).transpose.mulVec ν) 2 = ∑ j, ν j * ((ζ j)⁻¹) ^ 2 := by
    intro ν
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, vmat, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      exact Finset.sum_congr rfl fun j _ => by ring
  exact ⟨by rw [← (hrow (nuVec ζ target)).1, hsolve],
    by rw [← (hrow (nuVec ζ target)).2.1, hsolve],
    by rw [← (hrow (nuVec ζ target)).2.2, hsolve]⟩

/-! ## Recovering a folded vector from two reconstructed openings -/

/-- One side (`a`/`gen` or `b`/`gen'`) of the 1066 consistency argument. From the two
`(ξ², 1, ξ⁻²)` reconstructions matching the folded vector `s j` (scaled by `ξ⁻¹` and `ξ`
respectively), the cubic-in-`ξ²` consistency (over four distinct squares) forces
`s j = ξ·AP + ξ⁻¹·AP'`: the folded vector is the genuine fold of the `P`-opening halves. -/
lemma recover_side {m : ℕ} {ξ : Fin 4 → F} (hξ : ∀ j, ξ j ≠ 0)
    (hsq : Function.Injective fun j => (ξ j) ^ 2)
    (AL AP AR AL' AP' AR' : Fin m → F) (s : Fin 4 → Fin m → F)
    (h1 : ∀ j x, (ξ j) ^ 2 * AL x + AP x + ((ξ j)⁻¹) ^ 2 * AR x = (ξ j)⁻¹ * s j x)
    (h2 : ∀ j x, (ξ j) ^ 2 * AL' x + AP' x + ((ξ j)⁻¹) ^ 2 * AR' x = (ξ j) * s j x) :
    ∀ j, s j = fun x => (ξ j) * AP x + (ξ j)⁻¹ * AP' x := by
  -- `j`-independent component identities, coordinate by coordinate via `laurent_cubic_vanish`.
  have hx : ∀ x, AL x = 0 ∧ (AP x - AL' x) = 0 ∧ (AR x - AP' x) = 0 ∧ AR' x = 0 := by
    intro x
    have hcub : ∀ j, (AL x) * (ξ j) ^ 3 + (AP x - AL' x) * (ξ j) + (AR x - AP' x) * (ξ j)⁻¹
        + (-(AR' x)) * (ξ j)⁻¹ ^ 3 = 0 := by
      intro j
      have hxj := hξ j
      have e1 := h1 j x; have e2 := h2 j x
      have expand : ((AL x) * (ξ j) ^ 3 + (AP x - AL' x) * (ξ j) + (AR x - AP' x) * (ξ j)⁻¹
            + (-(AR' x)) * (ξ j)⁻¹ ^ 3) * (ξ j) ^ 3
          = ((ξ j) ^ 2 * AL x + AP x + ((ξ j)⁻¹) ^ 2 * AR x) * (ξ j) ^ 4
            - ((ξ j) ^ 2 * AL' x + AP' x + ((ξ j)⁻¹) ^ 2 * AR' x) * (ξ j) ^ 2 := by
        field_simp; ring
      rw [e1, e2] at expand
      have rhs0 : ((ξ j)⁻¹ * s j x) * (ξ j) ^ 4 - ((ξ j) * s j x) * (ξ j) ^ 2 = 0 := by
        field_simp; ring
      rw [rhs0] at expand
      rcases mul_eq_zero.mp expand with h | h
      · exact h
      · exact absurd h (pow_ne_zero 3 hxj)
    obtain ⟨g3, g1, gm1, gm3⟩ := laurent_cubic_vanish hξ hsq hcub
    exact ⟨g3, g1, gm1, by simpa using gm3⟩
  have hAL : AL = 0 := funext fun x => (hx x).1
  have hARAP' : ∀ x, AR x = AP' x := fun x => by have := (hx x).2.2.1; linear_combination this
  intro j
  funext x
  have hxj := hξ j
  have e1 := h1 j x
  rw [congrFun hAL x, hARAP' x] at e1
  simp only [Pi.zero_apply, mul_zero, zero_add] at e1
  have hmul : ξ j * s j x = AP x * (ξ j) ^ 2 + AP' x := by field_simp at e1; exact e1.symm
  calc s j x = (ξ j)⁻¹ * (ξ j * s j x) := by rw [← mul_assoc, inv_mul_cancel₀ hxj, one_mul]
    _ = (ξ j)⁻¹ * (AP x * (ξ j) ^ 2 + AP' x) := by rw [hmul]
    _ = ξ j * AP x + (ξ j)⁻¹ * AP' x := by field_simp

/-! ## Reconstructing the openings of `L`, `P`, `R` -/

/-- The 1066 reconstruction: a linear combination (with coefficients `ν`) of the folded child
relations produces an opening of `(∑ν)·P + (∑νξ²)·L + (∑νξ⁻²)·R` in terms of the parent
generators. Picking `ν` to hit `(0,1,0)`/`(1,0,0)`/`(0,0,1)` yields openings of `P`/`L`/`R`. -/
lemma recon_open {m : ℕ} (gL gR hL hR : Fin m → G) (u P L R : G) (ζ : Fin 3 → F)
    (A B : Fin 3 → Fin m → F)
    (hC : ∀ j, P + (ζ j) ^ 2 • L + ((ζ j)⁻¹) ^ 2 • R
      = msm (A j) (foldG (ζ j) gL gR) + msm (B j) (foldH (ζ j) hL hR) + ip (A j) (B j) • u)
    (ν : Fin 3 → F) :
    msm (fun x => ∑ j, ν j * (ζ j)⁻¹ * A j x) gL
      + msm (fun x => ∑ j, ν j * ζ j * A j x) gR
      + msm (fun x => ∑ j, ν j * ζ j * B j x) hL
      + msm (fun x => ∑ j, ν j * (ζ j)⁻¹ * B j x) hR
      + (∑ j, ν j * ip (A j) (B j)) • u
    = (∑ j, ν j) • P + (∑ j, ν j * (ζ j) ^ 2) • L + (∑ j, ν j * ((ζ j)⁻¹) ^ 2) • R := by
  have hsummand : ∀ j,
      (ν j * (ζ j)⁻¹) • msm (A j) gL + (ν j * ζ j) • msm (A j) gR
        + (ν j * ζ j) • msm (B j) hL + (ν j * (ζ j)⁻¹) • msm (B j) hR
        + (ν j * ip (A j) (B j)) • u
      = ν j • (P + (ζ j) ^ 2 • L + ((ζ j)⁻¹) ^ 2 • R) := by
    intro j; rw [hC j, msm_foldG, msm_foldH]; module
  -- Expand each `msm` of a coefficient sum, pull the `u`-sum out, and merge the five sums.
  simp only [msm_sum_coeff, msm_smul_coeff, Finset.sum_smul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => hsummand j)]
  simp only [smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]

/-! ## The single-round extraction: witness or discrete-log relation -/

/-- The witness-or-relation decision: if the five opening families are all consistent (every
difference `(dgL j, dgR j, dhL j, dhR j, du j)` vanishes) return the reconstructed `P`-opening as a
witness; otherwise return the first non-vanishing difference tuple as a discrete-log relation. The
search is a decidable `List.find?` over the four challenges. -/
def decideStep [DecidableEq F] {m : ℕ} (gLoP gHiP hLoP hHiP : Fin m → F)
    (dgL dgR dhL dhR : Fin 4 → Fin m → F) (du : Fin 4 → F) :
    ((Fin m → F) × (Fin m → F) × (Fin m → F) × (Fin m → F)) ⊕
      ((Fin m → F) × (Fin m → F) × (Fin m → F) × (Fin m → F) × F) :=
  match (List.finRange 4).find?
      (fun j => decide ¬ (dgL j = 0 ∧ dgR j = 0 ∧ dhL j = 0 ∧ dhR j = 0 ∧ du j = 0)) with
  | some j => Sum.inr (dgL j, dgR j, dhL j, dhR j, du j)
  | none => Sum.inl (gLoP, gHiP, hLoP, hHiP)

/-- **Correctness of `decideStep`.** Given that every difference tuple is a discrete-log relation
(`hbreak`) and that consistency forces the reconstructed `P`-opening to be a genuine witness
(`hwit`), every `Sum.inl` output is a valid witness and every `Sum.inr` output a non-trivial
relation. -/
lemma decideStep_valid [DecidableEq F] {m : ℕ} (gL gR hL hR : Fin m → G) (u P : G)
    {gLoP gHiP hLoP hHiP : Fin m → F} {dgL dgR dhL dhR : Fin 4 → Fin m → F} {du : Fin 4 → F}
    (hbreak : ∀ j, msm (dgL j) gL + msm (dgR j) gR + msm (dhL j) hL + msm (dhR j) hR + du j • u = 0)
    (hwit : (∀ j, dgL j = 0 ∧ dgR j = 0 ∧ dhL j = 0 ∧ dhR j = 0 ∧ du j = 0) →
        P = msm gLoP gL + msm gHiP gR + msm hLoP hL + msm hHiP hR + (ip gLoP hLoP + ip gHiP hHiP) • u) :
    (∀ aLo aHi bLo bHi,
        decideStep gLoP gHiP hLoP hHiP dgL dgR dhL dhR du = Sum.inl (aLo, aHi, bLo, bHi) →
        P = msm aLo gL + msm aHi gR + msm bLo hL + msm bHi hR + (ip aLo bLo + ip aHi bHi) • u) ∧
    (∀ vgL vgR vhL vhR vu,
        decideStep gLoP gHiP hLoP hHiP dgL dgR dhL dhR du = Sum.inr (vgL, vgR, vhL, vhR, vu) →
        ¬ (vgL = 0 ∧ vgR = 0 ∧ vhL = 0 ∧ vhR = 0 ∧ vu = 0) ∧
        msm vgL gL + msm vgR gR + msm vhL hL + msm vhR hR + vu • u = 0) := by
  refine ⟨fun aLo aHi bLo bHi hw => ?_, fun vgL vgR vhL vhR vu hv => ?_⟩
  · unfold decideStep at hw
    split at hw
    · exact absurd hw (by simp)
    · -- All families consistent: the reconstructed `P`-opening is a witness.
      rename_i heq
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hw
      refine hwit (fun j => ?_)
      have h := List.find?_eq_none.mp heq j (List.mem_finRange j)
      simpa using h
  · unfold decideStep at hv
    split at hv
    · -- The first inconsistent family yields a non-trivial relation.
      rename_i j heq
      simp only [Sum.inr.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hv
      refine ⟨?_, hbreak j⟩
      have h := List.find?_some heq
      exact of_decide_eq_true h
    · exact absurd hv (by simp)

/-- **Step 1 (single-round reconstruction core, computable).** From the four child witnesses
`(a' i, b' i)` for the folded instances, reconstruct — by pure field arithmetic on the challenges
and the child scalars — either a witness for the parent instance (`Sum.inl`) or a non-trivial
discrete-log relation among the parent generators `𝐠ᴸ,𝐠ᴿ,𝐡ᴸ,𝐡ᴿ,u` (`Sum.inr`). Solving the
`(ξ², 1, ξ⁻²)` system (`nuVec`) yields openings of `L, P, R`; the witness/relation split is the
decidable check of whether the five opening families are mutually consistent. No group elements and
no `Classical.choice`. -/
def extractStepData [DecidableEq F] {m : ℕ} (ξ : Fin 4 → F) (a' b' : Fin 4 → Fin m → F) :
    ((Fin m → F) × (Fin m → F) × (Fin m → F) × (Fin m → F)) ⊕
      ((Fin m → F) × (Fin m → F) × (Fin m → F) × (Fin m → F) × F) :=
  let ζ : Fin 3 → F := fun j => ξ j.castSucc
  let A : Fin 3 → Fin m → F := fun j => a' j.castSucc
  let B : Fin 3 → Fin m → F := fun j => b' j.castSucc
  let νP := nuVec ζ ![0, 1, 0]
  let νL := nuVec ζ ![1, 0, 0]
  let νR := nuVec ζ ![0, 0, 1]
  let gLo_P : Fin m → F := fun x => ∑ j, νP j * (ζ j)⁻¹ * A j x
  let gHi_P : Fin m → F := fun x => ∑ j, νP j * ζ j * A j x
  let hLo_P : Fin m → F := fun x => ∑ j, νP j * ζ j * B j x
  let hHi_P : Fin m → F := fun x => ∑ j, νP j * (ζ j)⁻¹ * B j x
  let c_P : F := ∑ j, νP j * ip (A j) (B j)
  let gLo_L : Fin m → F := fun x => ∑ j, νL j * (ζ j)⁻¹ * A j x
  let gHi_L : Fin m → F := fun x => ∑ j, νL j * ζ j * A j x
  let hLo_L : Fin m → F := fun x => ∑ j, νL j * ζ j * B j x
  let hHi_L : Fin m → F := fun x => ∑ j, νL j * (ζ j)⁻¹ * B j x
  let c_L : F := ∑ j, νL j * ip (A j) (B j)
  let gLo_R : Fin m → F := fun x => ∑ j, νR j * (ζ j)⁻¹ * A j x
  let gHi_R : Fin m → F := fun x => ∑ j, νR j * ζ j * A j x
  let hLo_R : Fin m → F := fun x => ∑ j, νR j * ζ j * B j x
  let hHi_R : Fin m → F := fun x => ∑ j, νR j * (ζ j)⁻¹ * B j x
  let c_R : F := ∑ j, νR j * ip (A j) (B j)
  let dgL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gLo_L x + gLo_P x + ((ξ j)⁻¹) ^ 2 * gLo_R x) - (fun x => (ξ j)⁻¹ * a' j x)
  let dgR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gHi_L x + gHi_P x + ((ξ j)⁻¹) ^ 2 * gHi_R x) - (fun x => (ξ j) * a' j x)
  let dhL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hLo_L x + hLo_P x + ((ξ j)⁻¹) ^ 2 * hLo_R x) - (fun x => (ξ j) * b' j x)
  let dhR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hHi_L x + hHi_P x + ((ξ j)⁻¹) ^ 2 * hHi_R x) - (fun x => (ξ j)⁻¹ * b' j x)
  let du : Fin 4 → F := fun j =>
    (ξ j) ^ 2 * c_L + c_P + ((ξ j)⁻¹) ^ 2 * c_R - ip (a' j) (b' j)
  decideStep gLo_P gHi_P hLo_P hHi_P dgL dgR dhL dhR du

/-- **Step 1 (correctness of `extractStepData`).** Given the four folded-instance relations (with
pairwise distinct challenge squares), every `Sum.inl` output is a valid parent witness, and every
`Sum.inr` output is a non-trivial discrete-log relation among the parent generators. -/
lemma extractStepData_valid [DecidableEq F] {m : ℕ} (gL gR hL hR : Fin m → G) (u P L R : G)
    {ξ : Fin 4 → F} (hξ : ∀ i, ξ i ≠ 0) (hsq : Function.Injective fun i => (ξ i) ^ 2)
    {a' b' : Fin 4 → Fin m → F}
    (hC : ∀ i, P + (ξ i) ^ 2 • L + ((ξ i)⁻¹) ^ 2 • R
      = msm (a' i) (foldG (ξ i) gL gR) + msm (b' i) (foldH (ξ i) hL hR) + ip (a' i) (b' i) • u) :
    (∀ aLo aHi bLo bHi, extractStepData ξ a' b' = Sum.inl (aLo, aHi, bLo, bHi) →
        P = msm aLo gL + msm aHi gR + msm bLo hL + msm bHi hR + (ip aLo bLo + ip aHi bHi) • u) ∧
    (∀ vgL vgR vhL vhR vu, extractStepData ξ a' b' = Sum.inr (vgL, vgR, vhL, vhR, vu) →
        ¬ (vgL = 0 ∧ vgR = 0 ∧ vhL = 0 ∧ vhR = 0 ∧ vu = 0) ∧
        msm vgL gL + msm vgR gR + msm vhL hL + msm vhR hR + vu • u = 0) := by
  -- abbreviations mirroring `extractStepData` (defeq to its `let` bindings).
  set ζ : Fin 3 → F := fun j => ξ j.castSucc with hζdef
  set A : Fin 3 → Fin m → F := fun j => a' j.castSucc with hAdef
  set B : Fin 3 → Fin m → F := fun j => b' j.castSucc with hBdef
  set νP : Fin 3 → F := nuVec ζ ![0, 1, 0] with hνPdef
  set νL : Fin 3 → F := nuVec ζ ![1, 0, 0] with hνLdef
  set νR : Fin 3 → F := nuVec ζ ![0, 0, 1] with hνRdef
  set gLo_P : Fin m → F := fun x => ∑ j, νP j * (ζ j)⁻¹ * A j x with hgLoP
  set gHi_P : Fin m → F := fun x => ∑ j, νP j * ζ j * A j x with hgHiP
  set hLo_P : Fin m → F := fun x => ∑ j, νP j * ζ j * B j x with hhLoP
  set hHi_P : Fin m → F := fun x => ∑ j, νP j * (ζ j)⁻¹ * B j x with hhHiP
  set c_P : F := ∑ j, νP j * ip (A j) (B j) with hcP
  set gLo_L : Fin m → F := fun x => ∑ j, νL j * (ζ j)⁻¹ * A j x with hgLoL
  set gHi_L : Fin m → F := fun x => ∑ j, νL j * ζ j * A j x with hgHiL
  set hLo_L : Fin m → F := fun x => ∑ j, νL j * ζ j * B j x with hhLoL
  set hHi_L : Fin m → F := fun x => ∑ j, νL j * (ζ j)⁻¹ * B j x with hhHiL
  set c_L : F := ∑ j, νL j * ip (A j) (B j) with hcL
  set gLo_R : Fin m → F := fun x => ∑ j, νR j * (ζ j)⁻¹ * A j x with hgLoR
  set gHi_R : Fin m → F := fun x => ∑ j, νR j * ζ j * A j x with hgHiR
  set hLo_R : Fin m → F := fun x => ∑ j, νR j * ζ j * B j x with hhLoR
  set hHi_R : Fin m → F := fun x => ∑ j, νR j * (ζ j)⁻¹ * B j x with hhHiR
  set c_R : F := ∑ j, νR j * ip (A j) (B j) with hcR
  set dgL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gLo_L x + gLo_P x + ((ξ j)⁻¹) ^ 2 * gLo_R x) -
      (fun x => (ξ j)⁻¹ * a' j x) with hdgL
  set dgR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gHi_L x + gHi_P x + ((ξ j)⁻¹) ^ 2 * gHi_R x) -
      (fun x => (ξ j) * a' j x) with hdgR
  set dhL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hLo_L x + hLo_P x + ((ξ j)⁻¹) ^ 2 * hLo_R x) -
      (fun x => (ξ j) * b' j x) with hdhL
  set dhR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hHi_L x + hHi_P x + ((ξ j)⁻¹) ^ 2 * hHi_R x) -
      (fun x => (ξ j)⁻¹ * b' j x) with hdhR
  set du : Fin 4 → F := fun j =>
    (ξ j) ^ 2 * c_L + c_P + ((ξ j)⁻¹) ^ 2 * c_R - ip (a' j) (b' j) with hdu
  -- common reconstruction facts.
  have hζj : ∀ j, ζ j = ξ j.castSucc := fun _ => rfl
  have hζ0 : ∀ j, ζ j ≠ 0 := fun j => hξ _
  have hζsq : Function.Injective fun j : Fin 3 => (ζ j) ^ 2 := fun a b hab =>
    Fin.castSucc_injective 3 (hsq hab)
  have hCζ : ∀ j : Fin 3, P + (ζ j) ^ 2 • L + ((ζ j)⁻¹) ^ 2 • R
      = msm (A j) (foldG (ζ j) gL gR) + msm (B j) (foldH (ζ j) hL hR) + ip (A j) (B j) • u :=
    fun j => hC j.castSucc
  obtain ⟨hνP1, hνP2, hνP3⟩ := nuVec_spec hζ0 hζsq ![0, 1, 0]
  obtain ⟨hνL1, hνL2, hνL3⟩ := nuVec_spec hζ0 hζsq ![1, 0, 0]
  obtain ⟨hνR1, hνR2, hνR3⟩ := nuVec_spec hζ0 hζsq ![0, 0, 1]
  have hreconP : P = msm gLo_P gL + msm gHi_P gR + msm hLo_P hL + msm hHi_P hR + c_P • u := by
    have h := recon_open gL gR hL hR u P L R ζ A B hCζ νP
    rw [hνP2, hνP1, hνP3] at h
    simpa using h.symm
  have hreconL : L = msm gLo_L gL + msm gHi_L gR + msm hLo_L hL + msm hHi_L hR + c_L • u := by
    have h := recon_open gL gR hL hR u P L R ζ A B hCζ νL
    rw [hνL2, hνL1, hνL3] at h
    simpa using h.symm
  have hreconR : R = msm gLo_R gL + msm gHi_R gR + msm hLo_R hL + msm hHi_R hR + c_R • u := by
    have h := recon_open gL gR hL hR u P L R ζ A B hCζ νR
    rw [hνR2, hνR1, hνR3] at h
    simpa using h.symm
  refine decideStep_valid (gLoP := gLo_P) (gHiP := gHi_P) (hLoP := hLo_P) (hHiP := hHi_P)
    (dgL := dgL) (dgR := dgR) (dhL := dhL) (dhR := dhR) (du := du) gL gR hL hR u P ?_ ?_
  · -- Every difference tuple is a discrete-log relation.
    intro j
    have hRecon : msm (fun x => (ξ j) ^ 2 * gLo_L x + gLo_P x + ((ξ j)⁻¹) ^ 2 * gLo_R x) gL
        + msm (fun x => (ξ j) ^ 2 * gHi_L x + gHi_P x + ((ξ j)⁻¹) ^ 2 * gHi_R x) gR
        + msm (fun x => (ξ j) ^ 2 * hLo_L x + hLo_P x + ((ξ j)⁻¹) ^ 2 * hLo_R x) hL
        + msm (fun x => (ξ j) ^ 2 * hHi_L x + hHi_P x + ((ξ j)⁻¹) ^ 2 * hHi_R x) hR
        + ((ξ j) ^ 2 * c_L + c_P + ((ξ j)⁻¹) ^ 2 * c_R) • u
        = (ξ j) ^ 2 • L + P + ((ξ j)⁻¹) ^ 2 • R := by
      simp only [msm_add_coeff, msm_smul_coeff]
      rw [hreconL, hreconP, hreconR]; module
    have hAct : msm (fun x => (ξ j)⁻¹ * a' j x) gL + msm (fun x => (ξ j) * a' j x) gR
        + msm (fun x => (ξ j) * b' j x) hL + msm (fun x => (ξ j)⁻¹ * b' j x) hR
        + ip (a' j) (b' j) • u = (ξ j) ^ 2 • L + P + ((ξ j)⁻¹) ^ 2 • R := by
      have hh := hC j
      rw [msm_foldG, msm_foldH] at hh
      simp only [msm_smul_coeff]
      rw [show (ξ j) ^ 2 • L + P + ((ξ j)⁻¹) ^ 2 • R
          = P + (ξ j) ^ 2 • L + ((ξ j)⁻¹) ^ 2 • R from by abel, hh]
      abel
    rw [hdgL, hdgR, hdhL, hdhR, hdu]
    simp only [msm_sub, sub_smul]
    rw [show ∀ a b c d e f g h i k : G,
        (a - b) + (c - d) + (e - f) + (g - h) + (i - k)
          = (a + c + e + g + i) - (b + d + f + h + k) from fun _ _ _ _ _ _ _ _ _ _ => by abel,
      hRecon, hAct, sub_self]
  · -- Consistency forces the reconstructed `P`-opening to be a genuine witness.
    intro hcons
    have cGLo : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * gLo_L x + gLo_P x + ((ξ j)⁻¹) ^ 2 * gLo_R x
        = (ξ j)⁻¹ * a' j x := by
      intro j x
      have h := congrFun (hcons j).1 x
      simp only [hdgL, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cGHi : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * gHi_L x + gHi_P x + ((ξ j)⁻¹) ^ 2 * gHi_R x
        = (ξ j) * a' j x := by
      intro j x
      have h := congrFun (hcons j).2.1 x
      simp only [hdgR, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cHLo : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * hLo_L x + hLo_P x + ((ξ j)⁻¹) ^ 2 * hLo_R x
        = (ξ j) * b' j x := by
      intro j x
      have h := congrFun (hcons j).2.2.1 x
      simp only [hdhL, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cHHi : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * hHi_L x + hHi_P x + ((ξ j)⁻¹) ^ 2 * hHi_R x
        = (ξ j)⁻¹ * b' j x := by
      intro j x
      have h := congrFun (hcons j).2.2.2.1 x
      simp only [hdhR, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cU : ∀ j : Fin 4, (ξ j) ^ 2 * c_L + c_P + ((ξ j)⁻¹) ^ 2 * c_R = ip (a' j) (b' j) := by
      intro j
      have h := (hcons j).2.2.2.2
      simp only [hdu, sub_eq_zero] at h
      exact h
    have ha' : ∀ j, a' j = fun x => (ξ j) * gLo_P x + (ξ j)⁻¹ * gHi_P x :=
      recover_side hξ hsq gLo_L gLo_P gLo_R gHi_L gHi_P gHi_R a' cGLo cGHi
    have hb' : ∀ j, b' j = fun x => (ξ j) * hHi_P x + (ξ j)⁻¹ * hLo_P x :=
      recover_side hξ hsq hHi_L hHi_P hHi_R hLo_L hLo_P hLo_R b' cHHi cHLo
    have hip : ∀ j, ip (a' j) (b' j)
        = (ξ j) ^ 2 * ip gLo_P hHi_P + (ip gLo_P hLo_P + ip gHi_P hHi_P)
          + ((ξ j)⁻¹) ^ 2 * ip gHi_P hLo_P := by
      intro j
      have hxj := hξ j
      rw [ha' j, hb' j]
      simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right]
      field_simp; ring
    have hquad : ∀ j : Fin 3,
        (c_L - ip gLo_P hHi_P) * (ζ j) ^ 2 + (c_P - (ip gLo_P hLo_P + ip gHi_P hHi_P))
          + (c_R - ip gHi_P hLo_P) * ((ζ j)⁻¹) ^ 2 = 0 := by
      intro j
      have hu := cU j.castSucc
      rw [hip j.castSucc, ← hζj j] at hu
      linear_combination hu
    obtain ⟨_, h0, _⟩ := laurent_quad_vanish hζ0 hζsq hquad
    have hcPeq : c_P = ip gLo_P hLo_P + ip gHi_P hHi_P := by linear_combination h0
    rw [hreconP, hcPeq]

end Sigma.Protocols.IPA
