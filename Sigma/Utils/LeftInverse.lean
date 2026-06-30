/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib

/-!
# A computable, polynomial-time left inverse, by Gaussian elimination

`Sigma.gaussLeftInv` computes a left inverse `M` (`M * W = 1`) of any full-column-rank
`W : Matrix (Fin q) (Fin m) F`. The point is *efficiency*, not mere computability: the
soundness extractors must invert the public `W_V`, and the two textbook "computable" routes
are exponential (searching the `q^m` row selections for an invertible minor) or factorial
(`det⁻¹ • adjugate`, a Leibniz sum over all permutations). Gaussian elimination is `m`
levels of `O(q·m)` field operations, with every level tabulated (`memoM`) so closure
re-evaluation cannot compound across the recursion.

One level works on the first column and recurses on the rest:

* `Sigma.elimStep` pivots on a nonzero entry `W ℓ₀ 0` of the first column (one exists when
  the kernel is trivial: a zero column annihilates the first unit vector, `exists_pivot`) and
  subtracts from every later column the multiple of column `0` that zeroes its `ℓ₀`-entry.
* The reduced matrix again has trivial kernel (`Sigma.elimStep_ker`): a kernel vector
  extends, by the eliminated coefficients, to a kernel vector of `W`.
* `Sigma.assemble` extends a left inverse `M'` of the reduced matrix to one of `W`: row
  `j+1` is row `j` of `M'` corrected by a multiple of the `ℓ₀`-indicator to be orthogonal
  to column `0` (`Sigma.corrRow`), and row `0` dualizes the pivot row against the corrected
  rows.

Correctness (`Sigma.gaussLeftInv_mul`) is proved by recursion from the trivial-kernel
precondition; `Sigma.gaussLeftInv_correct` derives that from the invertible-minor form of
full column rank (`∃ r, (W.submatrix r id).det ≠ 0` — the `hWV` field of the GBP
statement).
-/

namespace Sigma

open scoped Matrix

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Matrix memoization -/

/-- Memoizing identity on matrices: tabulate all entries into a concrete (array-backed)
vector of vectors once, then read entries back in `O(1)`. Propositionally `memoM M = M`
(`memoM_eq`), so proofs strip it; operationally it keeps each elimination level's entries
from being recomputed through the recursion's closures. -/
def memoM {a b : ℕ} {α : Type*} (M : Matrix (Fin a) (Fin b) α) : Matrix (Fin a) (Fin b) α :=
  let tab := Vector.ofFn fun i => Vector.ofFn (M i)
  Matrix.of fun i j => (tab.get i).get j

@[simp] lemma memoM_eq {a b : ℕ} {α : Type*} (M : Matrix (Fin a) (Fin b) α) : memoM M = M := by
  ext i j
  simp [memoM, Vector.get_ofFn]

/-! ## One elimination level -/

/-- One column-elimination step at pivot row `ℓ₀`: from every later column subtract the
multiple of column `0` that zeroes its `ℓ₀`-entry (so row `ℓ₀` of the result is `0`). -/
def elimStep {q m : ℕ} (W : Matrix (Fin q) (Fin (m + 1)) F) (ℓ₀ : Fin q) :
    Matrix (Fin q) (Fin m) F :=
  Matrix.of fun ℓ j => W ℓ j.succ - W ℓ₀ j.succ / W ℓ₀ 0 * W ℓ 0

/-- Row `j` of the recursive left inverse, corrected by a multiple of the `ℓ₀`-indicator to
be orthogonal to column `0` of `W` (`corrRow_col_zero`). -/
def corrRow {q m : ℕ} (W : Matrix (Fin q) (Fin (m + 1)) F) (ℓ₀ : Fin q)
    (M' : Matrix (Fin m) (Fin q) F) (j : Fin m) (ℓ : Fin q) : F :=
  M' j ℓ - (∑ ℓ', M' j ℓ' * W ℓ' 0) / W ℓ₀ 0 * (if ℓ = ℓ₀ then 1 else 0)

/-- Extend a left inverse `M'` of `elimStep W ℓ₀` to one of `W`: rows `j+1` are the
corrected rows, and row `0` dualizes the pivot row against them. -/
def assemble {q m : ℕ} (W : Matrix (Fin q) (Fin (m + 1)) F) (ℓ₀ : Fin q)
    (M' : Matrix (Fin m) (Fin q) F) : Matrix (Fin (m + 1)) (Fin q) F :=
  Matrix.of (Fin.cases
    (fun ℓ => ((if ℓ = ℓ₀ then 1 else 0) - ∑ k, W ℓ₀ k.succ * corrRow W ℓ₀ M' k ℓ) / W ℓ₀ 0)
    (corrRow W ℓ₀ M'))

/-- **The left inverse of a full-column-rank matrix, by Gaussian elimination** (column
recursion, pivoting in the first column, every level tabulated). Total — returns `0` when no
pivot exists, which the trivial-kernel precondition of `gaussLeftInv_mul` rules out. -/
def gaussLeftInv : {m q : ℕ} → Matrix (Fin q) (Fin m) F → Matrix (Fin m) (Fin q) F
  | 0, _, _ => 0
  | _ + 1, q, W =>
    match (List.finRange q).find? (fun ℓ => decide (W ℓ 0 ≠ 0)) with
    | none => 0
    | some ℓ₀ => memoM (assemble W ℓ₀ (gaussLeftInv (memoM (elimStep W ℓ₀))))

/-! ## Kernel facts -/

/-- **A pivot exists**: a matrix with trivial kernel has no zero first column (a zero
column annihilates the first unit vector). -/
lemma exists_pivot {q m : ℕ} {W : Matrix (Fin q) (Fin (m + 1)) F}
    (hker : ∀ v : Fin (m + 1) → F, W *ᵥ v = 0 → v = 0) : ∃ ℓ, W ℓ 0 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : W *ᵥ (fun k => if k = 0 then 1 else 0) = 0 := by
    funext ℓ
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero, Pi.zero_apply,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hcon ℓ
  have h1 := congrFun (hker _ h0) 0
  simp at h1

omit [DecidableEq F] in
/-- **Elimination preserves a trivial kernel**: a kernel vector of the reduced matrix
extends, by the eliminated coefficient `−∑ⱼ cⱼ·v'ⱼ` at index `0`, to a kernel vector
of `W`. -/
lemma elimStep_ker {q m : ℕ} {W : Matrix (Fin q) (Fin (m + 1)) F} {ℓ₀ : Fin q}
    (hker : ∀ v : Fin (m + 1) → F, W *ᵥ v = 0 → v = 0)
    (v' : Fin m → F) (hv' : elimStep W ℓ₀ *ᵥ v' = 0) : v' = 0 := by
  have hWv : W *ᵥ (Fin.cases (-∑ j, W ℓ₀ j.succ / W ℓ₀ 0 * v' j) v' : Fin (m + 1) → F)
      = 0 := by
    funext ℓ
    have hq := congrFun hv' ℓ
    simp only [Matrix.mulVec, dotProduct, elimStep, Matrix.of_apply, Pi.zero_apply] at hq
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    have e1 : ∀ j : Fin m, (W ℓ j.succ - W ℓ₀ j.succ / W ℓ₀ 0 * W ℓ 0) * v' j
        = W ℓ j.succ * v' j - W ℓ 0 * (W ℓ₀ j.succ / W ℓ₀ 0 * v' j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_sub_distrib, ← Finset.mul_sum] at hq
    rw [mul_neg, ← hq]
    ring
  have hv := hker _ hWv
  funext j
  have := congrFun hv j.succ
  simpa using this

/-! ## Correctness of the assembly -/

omit [DecidableEq F] in
/-- **The corrected rows are orthogonal to column `0`**: the `ℓ₀`-indicator correction is
chosen to cancel `⟨M'ⱼ, w₀⟩` exactly. -/
lemma corrRow_col_zero {q m : ℕ} (W : Matrix (Fin q) (Fin (m + 1)) F) (ℓ₀ : Fin q)
    (hq₀ : W ℓ₀ 0 ≠ 0) (M' : Matrix (Fin m) (Fin q) F) (j : Fin m) :
    ∑ ℓ, corrRow W ℓ₀ M' j ℓ * W ℓ 0 = 0 := by
  simp only [corrRow, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [div_mul_cancel₀ _ hq₀, sub_self]

omit [DecidableEq F] in
/-- **The corrected rows are dual to the later columns**: against `w_{j'+1}` the correction
shifts the `M' * elimStep W ℓ₀ = 1` identity from the reduced columns back to those of `W`,
giving exactly `δ_{j j'}`. -/
lemma corrRow_col_succ {q m : ℕ} (W : Matrix (Fin q) (Fin (m + 1)) F) (ℓ₀ : Fin q)
    (M' : Matrix (Fin m) (Fin q) F) (hM' : M' * elimStep W ℓ₀ = 1) (j j' : Fin m) :
    ∑ ℓ, corrRow W ℓ₀ M' j ℓ * W ℓ j'.succ = if j = j' then 1 else 0 := by
  have hMjj' := congrFun (congrFun hM' j) j'
  simp only [Matrix.mul_apply, elimStep, Matrix.of_apply, Matrix.one_apply] at hMjj'
  have e1 : ∀ ℓ, M' j ℓ * (W ℓ j'.succ - W ℓ₀ j'.succ / W ℓ₀ 0 * W ℓ 0)
      = M' j ℓ * W ℓ j'.succ - W ℓ₀ j'.succ / W ℓ₀ 0 * (M' j ℓ * W ℓ 0) := fun ℓ => by ring
  rw [Finset.sum_congr rfl fun ℓ _ => e1 ℓ, Finset.sum_sub_distrib, ← Finset.mul_sum] at hMjj'
  simp only [corrRow, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← hMjj']
  ring

omit [DecidableEq F] in
/-- **Row `0` dualizes the pivot row**: against any column `j'` of `W`, the assembled row
`0` evaluates to `δ_{0 j'}` — the indicator part contributes `W ℓ₀ j'`, and the corrected
rows subtract it back off (column `0` contributes nothing by `corrRow_col_zero`; column
`j''+1` contributes exactly `W ℓ₀ (j''+1)` by `corrRow_col_succ`). -/
lemma row_zero_dual {q m : ℕ} (W : Matrix (Fin q) (Fin (m + 1)) F) (ℓ₀ : Fin q)
    (hq₀ : W ℓ₀ 0 ≠ 0) (M' : Matrix (Fin m) (Fin q) F)
    (hM' : M' * elimStep W ℓ₀ = 1) (j' : Fin (m + 1)) :
    ∑ ℓ, (((if ℓ = ℓ₀ then 1 else 0) - ∑ k, W ℓ₀ k.succ * corrRow W ℓ₀ M' k ℓ) / W ℓ₀ 0)
        * W ℓ j' = if (0 : Fin (m + 1)) = j' then 1 else 0 := by
  have hswap : ∑ ℓ, (∑ k, W ℓ₀ k.succ * corrRow W ℓ₀ M' k ℓ) * W ℓ j'
      = ∑ k, W ℓ₀ k.succ * ∑ ℓ, corrRow W ℓ₀ M' k ℓ * W ℓ j' := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, sub_mul, Finset.sum_sub_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hswap]
  induction j' using Fin.cases with
  | zero =>
      rw [Finset.sum_congr rfl fun k _ => by
        rw [corrRow_col_zero W ℓ₀ hq₀ M' k, mul_zero]]
      simp [div_self hq₀]
  | succ j'' =>
      rw [Finset.sum_congr rfl fun k _ => by rw [corrRow_col_succ W ℓ₀ M' hM' k j'']]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [sub_self, zero_div]
      exact (if_neg (Fin.succ_ne_zero j'').symm).symm

omit [DecidableEq F] in
/-- **The assembly is a left inverse**: at a genuine pivot, extending a left inverse of the
eliminated matrix by `assemble` yields a left inverse of `W` (row `0` by `row_zero_dual`,
rows `j+1` by `corrRow_col_zero`/`corrRow_col_succ`). -/
lemma assemble_mul {q m : ℕ} (W : Matrix (Fin q) (Fin (m + 1)) F) (ℓ₀ : Fin q)
    (hq₀ : W ℓ₀ 0 ≠ 0) (M' : Matrix (Fin m) (Fin q) F)
    (hM' : M' * elimStep W ℓ₀ = 1) :
    assemble W ℓ₀ M' * W = 1 := by
  ext j j'
  rw [Matrix.mul_apply, Matrix.one_apply]
  induction j using Fin.cases with
  | zero =>
      simp only [assemble, Matrix.of_apply, Fin.cases_zero]
      exact row_zero_dual W ℓ₀ hq₀ M' hM' j'
  | succ j =>
      simp only [assemble, Matrix.of_apply, Fin.cases_succ]
      induction j' using Fin.cases with
      | zero =>
          rw [corrRow_col_zero W ℓ₀ hq₀ M' j]
          exact (if_neg (Fin.succ_ne_zero j)).symm
      | succ j'' =>
          rw [corrRow_col_succ W ℓ₀ M' hM' j j'']
          simp [Fin.succ_inj]

/-! ## The main theorems -/

/-- **Gaussian elimination computes a left inverse**, trivial-kernel form: if
`W *ᵥ v = 0` forces `v = 0` then `gaussLeftInv W * W = 1`. Recursion on the columns: a
pivot exists (`exists_pivot`), elimination preserves the precondition (`elimStep_ker`),
and the assembly extends the recursive inverse (`assemble_mul`). -/
theorem gaussLeftInv_mul : ∀ {m q : ℕ} (W : Matrix (Fin q) (Fin m) F),
    (∀ v : Fin m → F, W *ᵥ v = 0 → v = 0) → gaussLeftInv W * W = 1
  | 0, _, _, _ => by ext j j'; exact j.elim0
  | m + 1, q, W, hker => by
      rw [gaussLeftInv]
      cases hf : (List.finRange q).find? (fun ℓ => decide (W ℓ 0 ≠ 0)) with
      | none =>
          obtain ⟨ℓ, hq⟩ := exists_pivot hker
          rw [List.find?_eq_none] at hf
          have h := hf ℓ (List.mem_finRange ℓ)
          simp only [decide_eq_true_eq] at h
          exact absurd hq h
      | some ℓ₀ =>
          have hfq := List.find?_some hf
          have hq₀ : W ℓ₀ 0 ≠ 0 := of_decide_eq_true hfq
          simp only [memoM_eq]
          exact assemble_mul W ℓ₀ hq₀ _
            (gaussLeftInv_mul (elimStep W ℓ₀) (fun v' hv' => elimStep_ker hker v' hv'))

omit [DecidableEq F] in
/-- A matrix with an invertible `m × m` minor has trivial kernel: restrict the kernel
equation to the minor's rows and invert. -/
lemma ker_eq_zero_of_submatrix_det {q m : ℕ} (W : Matrix (Fin q) (Fin m) F)
    (h : ∃ r : Fin m → Fin q, (W.submatrix r id).det ≠ 0)
    (v : Fin m → F) (hv : W *ᵥ v = 0) : v = 0 := by
  obtain ⟨r, hdet⟩ := h
  have hsub : W.submatrix r id *ᵥ v = 0 := by
    funext k
    have h1 := congrFun hv (r k)
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using h1
  have hu : IsUnit (W.submatrix r id).det := isUnit_iff_ne_zero.mpr hdet
  calc v = 1 *ᵥ v := (Matrix.one_mulVec v).symm
    _ = ((W.submatrix r id)⁻¹ * W.submatrix r id) *ᵥ v := by
        rw [Matrix.nonsing_inv_mul _ hu]
    _ = (W.submatrix r id)⁻¹ *ᵥ (W.submatrix r id *ᵥ v) := Matrix.mulVec_mulVec _ _ _ |>.symm
    _ = 0 := by rw [hsub, Matrix.mulVec_zero]

/-- **Correctness of the computable left inverse** under the invertible-minor form of full
column rank: `gaussLeftInv W * W = 1`. -/
theorem gaussLeftInv_correct {q m : ℕ} (W : Matrix (Fin q) (Fin m) F)
    (h : ∃ r : Fin m → Fin q, (W.submatrix r id).det ≠ 0) :
    gaussLeftInv W * W = 1 :=
  gaussLeftInv_mul W (ker_eq_zero_of_submatrix_det W h)

end Sigma
