/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib

/-!
# Module-valued matrix inversion: Vandermonde interpolation and left-inverse recovery

The special-soundness extractor recovers **group-valued** coefficients (commitments `T_i`,
combinations `U_q`) from evaluations at distinct challenges. Mathlib's polynomial/Vandermonde
machinery is scalar-valued (`Matrix.mulVec` needs vector and entries in the same semiring), so
this file provides the module-valued facts we need, over an arbitrary `F`-module `G`.

Everything rests on one computation, `Sigma.matrix_one_smul_recover`: if `M * N = 1` then applying
`M` to the `N`-combinations of a module-vector `D` recovers `D`. From it:

* `Sigma.vandermonde_kernel` / `Sigma.vandermonde_coeff_unique` — a `d`-point Vandermonde system over
  a module has a unique solution (distinct evaluation points pin the coefficients).
* `Sigma.leftInverse_recover` — `M * W = 1` and `U_q = ∑_k W ℓ k • V_k` give `V_k = ∑_q M k ℓ • U_q`.

The file also provides the **efficient** Vandermonde inverse the extractors compute with:
`Matrix.det`/`Matrix.adjugate` are Leibniz sums over all `d!` permutations, so `det⁻¹ • adjugate`
— while a genuine `def` — is no algorithm. `Sigma.vandInv` is the classical `O(d²)`-per-entry
closed form (column `l` holds the coefficients of the `l`-th Lagrange basis polynomial, expanded
by `Sigma.stepRoot`), and `Sigma.vandInv_eq` identifies it with `(Matrix.vandermonde x)⁻¹` at
injective nodes — extractors interpolate in polynomial time, proofs reason about the Mathlib
inverse.
-/

namespace Sigma

open scoped Matrix

variable {F : Type*} [Field F] {G : Type*} [AddCommGroup G] [Module F G]

/-- The module-valued analogue of `(M * N) *ᵥ D = D`: if `M * N = 1` (matrices over `F`), then
for any module-valued vector `D`, applying `M` to the `N`-combinations recovers `D i`. -/
theorem matrix_one_smul_recover {a b : ℕ} (M : Matrix (Fin a) (Fin b) F)
    (N : Matrix (Fin b) (Fin a) F) (h : M * N = 1) (D : Fin a → G) (i : Fin a) :
    ∑ j : Fin b, M i j • (∑ k : Fin a, N j k • D k) = D i := by
  classical
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul,
    zero_smul]
  simp [Finset.sum_ite_eq]

/-- A `d`-point Vandermonde system over a module has at most one solution: if the module-valued
coefficient family `D` evaluates to `0` at `d` distinct points `x j` (`∑ i, (x j)^i • D i = 0`),
then `D = 0`. -/
theorem vandermonde_kernel {d : ℕ} (x : Fin d → F) (hx : Function.Injective x)
    (D : Fin d → G) (h : ∀ j, ∑ i : Fin d, (x j) ^ (i : ℕ) • D i = 0) : D = 0 := by
  classical
  have hu : IsUnit (Matrix.vandermonde x).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hx)
  have hinv : (Matrix.vandermonde x)⁻¹ * Matrix.vandermonde x = 1 :=
    Matrix.nonsing_inv_mul _ hu
  -- the hypothesis is exactly "`vandermonde x` sends `D` to `0`"
  have hVD : ∀ j, ∑ k : Fin d, (Matrix.vandermonde x) j k • D k = 0 := by
    intro j; simp_rw [Matrix.vandermonde_apply]; exact h j
  funext i
  have key := matrix_one_smul_recover (Matrix.vandermonde x)⁻¹ (Matrix.vandermonde x) hinv D i
  rw [← key]
  simp_rw [hVD, smul_zero, Finset.sum_const_zero]
  rfl

/-- Two module-valued coefficient families that agree on their evaluations at `d` distinct
points are equal. -/
theorem vandermonde_coeff_unique {d : ℕ} (x : Fin d → F) (hx : Function.Injective x)
    (T T' : Fin d → G)
    (h : ∀ j, ∑ i : Fin d, (x j) ^ (i : ℕ) • T i = ∑ i : Fin d, (x j) ^ (i : ℕ) • T' i) :
    T = T' := by
  have hD : (fun i => T i - T' i) = 0 := by
    apply vandermonde_kernel x hx
    intro j
    simp_rw [smul_sub, Finset.sum_sub_distrib]
    rw [h j, sub_self]
  funext i
  have := congrFun hD i
  simpa [sub_eq_zero] using this

/-- Interpolation reconstructs the samples: with `d` distinct points `x`, the module-valued
samples `R l` are recovered by evaluating their inverse-Vandermonde coefficients. (`V * V⁻¹ = 1`.) -/
theorem vandermonde_recover {d : ℕ} (x : Fin d → F) (hx : Function.Injective x) (R : Fin d → G)
    (l : Fin d) :
    R l = ∑ p : Fin d, (x l) ^ (p : ℕ) •
        (∑ l' : Fin d, (Matrix.vandermonde x)⁻¹ p l' • R l') := by
  have hu : IsUnit (Matrix.vandermonde x).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hx)
  have key := matrix_one_smul_recover (Matrix.vandermonde x) (Matrix.vandermonde x)⁻¹
    (Matrix.mul_nonsing_inv _ hu) R l
  rw [← key]
  exact Finset.sum_congr rfl fun p _ => by rw [Matrix.vandermonde_apply]

/-- The `r`-th coefficient of a module-valued polynomial known by its values at `d` distinct
points is the corresponding inverse-Vandermonde combination of those values. -/
theorem vandermonde_coeff {d : ℕ} (x : Fin d → F) (hx : Function.Injective x)
    (C samples : Fin d → G) (heq : ∀ l, (∑ r : Fin d, (x l) ^ (r : ℕ) • C r) = samples l)
    (r : Fin d) :
    C r = ∑ l : Fin d, (Matrix.vandermonde x)⁻¹ r l • samples l := by
  refine congrFun (vandermonde_coeff_unique x hx C
    (fun r => ∑ l, (Matrix.vandermonde x)⁻¹ r l • samples l) ?_) r
  intro l
  rw [heq l]
  exact vandermonde_recover x hx samples l

/-- Recover the `V_k` from their `W`-combinations using a left inverse `M` of `W`: if
`M * W = 1` and `U_q = ∑_k W ℓ k • V_k`, then `V_k = ∑_q M k ℓ • U_q`. -/
theorem leftInverse_recover {q m : ℕ} (W : Matrix (Fin q) (Fin m) F)
    (M : Matrix (Fin m) (Fin q) F) (hM : M * W = 1)
    (V : Fin m → G) (U : Fin q → G) (hU : ∀ ℓ, U ℓ = ∑ k, W ℓ k • V k) :
    ∀ k, V k = ∑ ℓ, M k ℓ • U ℓ := by
  intro k
  have key := matrix_one_smul_recover M W hM V k
  rw [← key]
  simp_rw [hU]

/-! ## The efficient Vandermonde inverse

Polynomials are ascending coefficient lists; `stepRoot` multiplies by a linear factor in one
`O(length)` pass, so `rootsPoly` expands `∏ (X − rᵢ)` in quadratic time, and `vandInv` assembles
the Lagrange-basis coefficients into the inverse matrix. -/

/-- Multiply a polynomial, given by its ascending coefficient list, by `X − r`: synthetic
multiplication, carrying the coefficient one degree down (`prev`). -/
def stepRootAux (r : F) (prev : F) : List F → List F
  | [] => [prev]
  | a :: c => (prev - r * a) :: stepRootAux r a c

/-- The ascending coefficient list of `(X − r) · c(X)`. -/
def stepRoot (r : F) : List F → List F
  | [] => []
  | a :: c => (-(r * a)) :: stepRootAux r a c

/-- The ascending coefficient list of `∏_{r ∈ rs} (X − r)`. -/
def rootsPoly : List F → List F
  | [] => [1]
  | r :: rs => stepRoot r (rootsPoly rs)

/-- Horner evaluation of an ascending coefficient list. -/
def evalAsc (t : F) : List F → F
  | [] => 0
  | a :: c => a + t * evalAsc t c

/-- Horner evaluation through one synthetic-multiplication step (the carried coefficient
contributes at the current degree). -/
lemma evalAsc_stepRootAux (t r prev : F) (c : List F) :
    evalAsc t (stepRootAux r prev c) = prev + (t - r) * evalAsc t c := by
  induction c generalizing prev with
  | nil => simp [stepRootAux, evalAsc]
  | cons a c ih => simp only [stepRootAux, evalAsc, ih a]; ring

/-- Multiplying the coefficient list by `X − r` multiplies the evaluation by `t − r`. -/
lemma evalAsc_stepRoot (t r : F) (c : List F) :
    evalAsc t (stepRoot r c) = (t - r) * evalAsc t c := by
  cases c with
  | nil => simp [stepRoot, evalAsc]
  | cons a c => simp only [stepRoot, evalAsc, evalAsc_stepRootAux]; ring

/-- Expanding `∏ (X − rᵢ)` and evaluating is evaluating the product. -/
lemma evalAsc_rootsPoly (t : F) (rs : List F) :
    evalAsc t (rootsPoly rs) = (rs.map (fun r => t - r)).prod := by
  induction rs with
  | nil => simp [rootsPoly, evalAsc]
  | cons r rs ih => rw [rootsPoly, evalAsc_stepRoot, ih, List.map_cons, List.prod_cons]

/-- Each synthetic-multiplication step grows the coefficient list by one. -/
lemma length_stepRootAux (r prev : F) (c : List F) :
    (stepRootAux r prev c).length = c.length + 1 := by
  induction c generalizing prev with
  | nil => rfl
  | cons a c ih => simp [stepRootAux, ih]

/-- `∏_{r ∈ rs} (X − r)` has degree `rs.length`, i.e. `rs.length + 1` coefficients. -/
lemma length_rootsPoly (rs : List F) : (rootsPoly rs).length = rs.length + 1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rcases hr : rootsPoly rs with _ | ⟨a, c⟩
      · rw [hr] at ih; simp at ih
      · rw [rootsPoly, hr, stepRoot, List.length_cons, length_stepRootAux]
        rw [hr] at ih
        simp only [List.length_cons] at ih ⊢
        omega

/-- A `Fin`-indexed power sum of an ascending coefficient list (entries past the length are
zero) is its Horner evaluation. -/
lemma sum_getD_mul_pow (t : F) : ∀ (c : List F) (k : ℕ), c.length ≤ k →
    ∑ p : Fin k, c.getD p 0 * t ^ (p : ℕ) = evalAsc t c
  | [], _, _ => by simp [evalAsc]
  | a :: c, 0, h => by simp at h
  | a :: c, k + 1, h => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getD_cons_zero, pow_zero, mul_one, Fin.val_succ,
        List.getD_cons_succ, evalAsc]
      rw [← sum_getD_mul_pow t c k (by simpa using h), Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun p _ => by rw [pow_succ]; ring

/-- The inverse of a Vandermonde matrix, computed in polynomial time by Lagrange interpolation:
entry `(p, l)` is the `X^p`-coefficient of the `l`-th Lagrange basis polynomial
`m_l(X) = ∏_{j ≠ l} (X − x j) / ∏_{j ≠ l} (x l − x j)`. Agrees with
`(Matrix.vandermonde x)⁻¹` at injective nodes (`vandInv_eq`); unlike `det⁻¹ • adjugate`, this
is an actual algorithm. -/
def vandInv {d : ℕ} (x : Fin d → F) : Matrix (Fin d) (Fin d) F :=
  Matrix.of fun p l =>
    ((((List.finRange d).filter (fun j => j ≠ l)).map (fun j => x l - x j)).prod)⁻¹
      * (rootsPoly (((List.finRange d).filter (fun j => j ≠ l)).map x)).getD p 0

/-- `vandInv` is a right inverse: row `i` of the Vandermonde against column `l` of `vandInv`
evaluates the `l`-th Lagrange basis polynomial at `x i`, which is `1` at `i = l` (numerator =
denominator) and `0` otherwise (the factor `x i − x i` appears). -/
lemma vandermonde_mul_vandInv {d : ℕ} {x : Fin d → F} (hx : Function.Injective x) :
    Matrix.vandermonde x * vandInv x = 1 := by
  ext i l
  set L : List (Fin d) := (List.finRange d).filter (fun j => j ≠ l) with hL
  have hlen : (rootsPoly (L.map x)).length ≤ d := by
    rw [length_rootsPoly, List.length_map]
    have hlt : L.length < (List.finRange d).length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨l, List.mem_finRange l, by simp⟩
    rw [List.length_finRange] at hlt
    omega
  rw [Matrix.mul_apply,
    Finset.sum_congr rfl fun p _ => show Matrix.vandermonde x i p * vandInv x p l
        = ((L.map (fun j => x l - x j)).prod)⁻¹
            * ((rootsPoly (L.map x)).getD p 0 * x i ^ (p : ℕ)) by
      rw [Matrix.vandermonde_apply, vandInv, Matrix.of_apply]; ring,
    ← Finset.mul_sum, sum_getD_mul_pow (x i) _ d hlen, evalAsc_rootsPoly, List.map_map]
  by_cases hil : i = l
  · subst hil
    rw [Matrix.one_apply_eq]
    have hcomp : (fun r => x i - r) ∘ x = fun j => x i - x j := rfl
    rw [hcomp]
    refine inv_mul_cancel₀ (fun h0 => ?_)
    obtain ⟨j, hjL, hj0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    have hji : i = j := hx (sub_eq_zero.mp hj0)
    rw [hL, List.mem_filter] at hjL
    exact absurd hji.symm (by simpa using hjL.2)
  · have h0 : (0 : F) ∈ L.map ((fun r => x i - r) ∘ x) :=
      List.mem_map.mpr ⟨i,
        by rw [hL, List.mem_filter]; exact ⟨List.mem_finRange i, by simpa using hil⟩,
        by simp⟩
    rw [Matrix.one_apply_ne hil, List.prod_eq_zero h0, mul_zero]

/-- **The computable Lagrange form is the Mathlib inverse** at injective nodes. Proofs rewrite
with this once and then reason about `(Matrix.vandermonde x)⁻¹`. -/
lemma vandInv_eq {d : ℕ} {x : Fin d → F} (hx : Function.Injective x) :
    vandInv x = (Matrix.vandermonde x)⁻¹ :=
  (Matrix.inv_eq_right_inv (vandermonde_mul_vandInv hx)).symm

end Sigma
