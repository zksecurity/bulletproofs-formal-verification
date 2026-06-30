/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.IPAImproved.Fold
import Sigma.Protocols.IPA.Extract

/-!
# Single-round witness extraction for the improved inner-product argument

The algebraic core of computational special soundness. One folding round reduces a
length-`2m` instance with generators `(𝐠,𝐡)` and commitment `P`, cross-terms `(L,R)`, to a
length-`m` instance per challenge `ξ`, with the *polynomial* round relation
`ξ²·L + ξ·P + R = ⟨a',𝐠'⟩ + ⟨b',𝐡'⟩ + ⟨a',b'⟩·u`. Given **four pairwise-distinct**
challenges and a witness for each folded instance, we recover a witness for the parent
instance, *or* a non-trivial discrete-log relation among the generators.

Because the round relation is polynomial in `ξ` (monomials `1, ξ, ξ²`; in the style of the
Attema–Cramer compression, eprint 2020/152) — not Laurent as in Bulletproofs 2017/1066
(`Sigma.Protocols.IPA.Extract`) — plain distinctness of the challenges suffices: the
reconstruction system is an honest Vandermonde in `ξ`, and the consistency identities are
ordinary polynomials of degree `≤ 3` killed by four distinct evaluation points. No challenge
needs distinct squares, and no challenge needs to be invertible.

The generic ingredients — `msm` linearity in the coefficient vector, the Vandermonde
vanishing lemma `poly_vanish`, and the witness-or-relation decision `decideStep` — are reused
from `Sigma.Protocols.IPA.Extract`. This file is self-contained algebra over `msm`/`ip`; it
is wired into the per-node extractor in `Sigma.Protocols.IPAImproved.NodeExtract`.

Proof outline — this file is the reconstruction core of the per-round soundness (packaged
per node in `Sigma.Protocols.IPAImproved.NodeExtract`); each substep is discharged by the
named lemma:

* *Reconstruction* (`vmat`/`nuVec`/`recon_open`): expanding the folds, the `j`-th accepted
  challenge opens `ξⱼ²·L + ξⱼ·P + R` over the five parent generators `(𝐠ᴸ, 𝐠ᴿ, 𝐡ᴸ, 𝐡ᴿ, u)`
  with coefficients `(a'ⱼ, ξⱼ·a'ⱼ, ξⱼ·b'ⱼ, b'ⱼ, ⟨a'ⱼ,b'ⱼ⟩)`. Inverting the `3×3` Vandermonde
  system in the monomials `(ξ², ξ, 1)` at the first three challenges `ζ` — the explicit
  Cramer/adjugate solution `nuVec`, computable — yields `ν`-combinations hitting `P`, `L`, `R`
  separately, i.e. openings of each over the parent generators.
* *Decision* (`decideStep`, reused): for each of the four challenges, the
  `(ξⱼ², ξⱼ, 1)`-combination of the reconstructed `L/P/R`-openings and the `j`-th actual
  opening both open `ξⱼ²·L + ξⱼ·P + R`, so their difference is a discrete-log relation among
  the parent generators; if some difference is non-vanishing, return it (`Sum.inr`).
* *Consistency* (`recover_side`, via `cubic_vanish`): if all four differences vanish, comparing
  the plain and `ξ`-scaled reconstructions coordinatewise gives an ordinary cubic in `ξ`
  vanishing at the four distinct challenges (Vandermonde in `ξ`; this is what forces arity 4),
  so `a'ⱼ = ξⱼ·aᴸ + aᴿ` and `b'ⱼ = bᴸ + ξⱼ·bᴿ` for the recovered `P`-opening halves: the
  child witnesses are genuine folds.
* *The value coefficient* (`quad_vanish`): `⟨a'ⱼ, b'ⱼ⟩` is then a quadratic in `ξⱼ` agreeing
  with the reconstructed `u`-coefficient `ξⱼ²·c_L + ξⱼ·c_P + c_R` at the three distinct `ζ`,
  which pins `c_P = ⟨aᴸ,bᴸ⟩ + ⟨aᴿ,bᴿ⟩` — the recovered `P`-opening is a genuine `relIP`
  witness (`extractStepData_valid`).
-/

namespace Sigma.Protocols.IPAImproved

open Sigma.Protocols.IPA (msm_smul_coeff msm_add_coeff msm_sum_coeff poly_vanish
  decideStep decideStep_valid)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## `msm` against the polynomially folded generators -/

/-- `msm` against the folded `𝐠` generators splits along the fold weights. -/
lemma msm_foldG {m : ℕ} (v : Fin m → F) (ξ : F) (gL gR : Fin m → G) :
    msm v (foldG ξ gL gR) = msm v gL + ξ • msm v gR := by
  simp only [msm, foldG, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, smul_smul, mul_comm]

/-- `msm` against the folded `𝐡` generators splits along the fold weights. -/
lemma msm_foldH {m : ℕ} (v : Fin m → F) (ξ : F) (hL hR : Fin m → G) :
    msm v (foldH ξ hL hR) = ξ • msm v hL + msm v hR := by
  simp only [msm, foldH, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, smul_smul, mul_comm]

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

/-! ## Polynomial vanishing at distinct points -/

/-- A quadratic polynomial (monomials `ξ², ξ, 1`) vanishing at three distinct points has all
coefficients zero — a Vandermonde inversion in `ξ` at arity 3 (`poly_vanish`). -/
lemma quad_vanish {ξ : Fin 3 → F} (hξ : Function.Injective ξ) {c2 c1 c0 : F}
    (h : ∀ j, c2 * (ξ j) ^ 2 + c1 * (ξ j) + c0 = 0) :
    c2 = 0 ∧ c1 = 0 ∧ c0 = 0 := by
  have hc : (![c0, c1, c2] : Fin 3 → F) = 0 := by
    refine poly_vanish hξ (fun j => ?_)
    have hreduce : (∑ i, (![c0, c1, c2] : Fin 3 → F) i * (ξ j) ^ (i : ℕ))
        = c2 * (ξ j) ^ 2 + c1 * (ξ j) + c0 := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two]
      ring
    rw [hreduce, h j]
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun hc 2; simpa using this
  · have := congrFun hc 1; simpa using this
  · have := congrFun hc 0; simpa using this

/-- A cubic polynomial (monomials `ξ³, ξ², ξ, 1`) vanishing at four distinct points has all
coefficients zero — a Vandermonde inversion in `ξ` at arity 4 (`poly_vanish`); this is the
inversion that forces the per-round arity to be 4 rather than 3. -/
lemma cubic_vanish {ξ : Fin 4 → F} (hξ : Function.Injective ξ) {c3 c2 c1 c0 : F}
    (h : ∀ j, c3 * (ξ j) ^ 3 + c2 * (ξ j) ^ 2 + c1 * (ξ j) + c0 = 0) :
    c3 = 0 ∧ c2 = 0 ∧ c1 = 0 ∧ c0 = 0 := by
  have hc : (![c0, c1, c2, c3] : Fin 4 → F) = 0 := by
    refine poly_vanish hξ (fun j => ?_)
    have hreduce : (∑ i, (![c0, c1, c2, c3] : Fin 4 → F) i * (ξ j) ^ (i : ℕ))
        = c3 * (ξ j) ^ 3 + c2 * (ξ j) ^ 2 + c1 * (ξ j) + c0 := by
      rw [Fin.sum_univ_four]
      have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
        Fin.val_two, e3]
      ring
    rw [hreduce, h j]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrFun hc 3; simpa using this
  · have := congrFun hc 2; simpa using this
  · have := congrFun hc 1; simpa using this
  · have := congrFun hc 0; simpa using this

/-- The coefficient matrix of the `(ξ², ξ, 1)` reconstruction system at three challenges. -/
def vmat (ζ : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  fun j r => ![(ζ j) ^ 2, ζ j, 1] r

/-- The coefficient matrix is invertible when the three challenges are pairwise distinct;
this follows from `quad_vanish`. -/
lemma vmat_det_ne_zero {ζ : Fin 3 → F} (hζ : Function.Injective ζ) : (vmat ζ).det ≠ 0 := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv, hmv⟩
  apply hv
  have hcoord : ∀ j, v 0 * (ζ j) ^ 2 + v 1 * (ζ j) + v 2 = 0 := by
    intro j
    have := congrFun hmv j
    simp only [Matrix.mulVec, dotProduct, vmat, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Pi.zero_apply] at this
    linear_combination this
  obtain ⟨h0, h1, h2⟩ := quad_vanish hζ hcoord
  funext j; fin_cases j <;> simp_all

/-- **Explicit, computable reconstruction coefficients `ν`** of the extractor: the
Cramer/adjugate solution of the `3×3` system `(ξ², ξ, 1)·ν = target`. This is a genuine
field-arithmetic algorithm (determinant + adjugate over `Fin 3`), not a `Classical.choice`. -/
def nuVec (ζ target : Fin 3 → F) : Fin 3 → F :=
  (vmat ζ).transpose.det⁻¹ • (vmat ζ).transpose.adjugate.mulVec target

/-- `nuVec` solves the `(ξ², ξ, 1)` system: it satisfies the three defining equations whenever
the challenges are pairwise distinct. -/
lemma nuVec_spec {ζ : Fin 3 → F} (hζ : Function.Injective ζ) (target : Fin 3 → F) :
    (∑ j, nuVec ζ target j * (ζ j) ^ 2 = target 0) ∧
    (∑ j, nuVec ζ target j * ζ j = target 1) ∧
    (∑ j, nuVec ζ target j = target 2) := by
  have hBdet : (vmat ζ).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact vmat_det_ne_zero hζ
  -- `nuVec` solves the transposed system `Nᵀ · ν = target`.
  have hsolve : (vmat ζ).transpose.mulVec (nuVec ζ target) = target := by
    unfold nuVec
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hBdet, one_smul]
  -- Each row `r` of `Nᵀ · ν` is exactly the `r`-th equation.
  have hrow : ∀ (ν : Fin 3 → F),
      ((vmat ζ).transpose.mulVec ν) 0 = ∑ j, ν j * (ζ j) ^ 2 ∧
      ((vmat ζ).transpose.mulVec ν) 1 = ∑ j, ν j * ζ j ∧
      ((vmat ζ).transpose.mulVec ν) 2 = ∑ j, ν j := by
    intro ν
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, vmat, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      exact Finset.sum_congr rfl fun j _ => by ring
  exact ⟨by rw [← (hrow (nuVec ζ target)).1, hsolve],
    by rw [← (hrow (nuVec ζ target)).2.1, hsolve],
    by rw [← (hrow (nuVec ζ target)).2.2, hsolve]⟩

/-! ## Recovering a folded vector from two reconstructed openings -/

/-- One side (`a`/`gen` or `b`/`gen'`) of the consistency argument. From the two `(ξ², ξ, 1)`
reconstructions matching the folded vector `s j` (plain and scaled by `ξ` respectively), the
cubic consistency (over four distinct challenges) forces `s j = ξ·AP + AP'`: the folded
vector is the genuine fold of the `P`-opening halves `AP` and `AP'`. -/
lemma recover_side {m : ℕ} {ξ : Fin 4 → F} (hξ : Function.Injective ξ)
    (AL AP AR AL' AP' AR' : Fin m → F) (s : Fin 4 → Fin m → F)
    (h1 : ∀ j x, (ξ j) ^ 2 * AL x + (ξ j) * AP x + AR x = s j x)
    (h2 : ∀ j x, (ξ j) ^ 2 * AL' x + (ξ j) * AP' x + AR' x = (ξ j) * s j x) :
    ∀ j, s j = fun x => (ξ j) * AP x + AP' x := by
  -- `j`-independent component identities, coordinate by coordinate via `cubic_vanish`.
  have hx : ∀ x, AL x = 0 ∧ (AP x - AL' x) = 0 ∧ (AR x - AP' x) = 0 ∧ AR' x = 0 := by
    intro x
    have hcub : ∀ j, (AL x) * (ξ j) ^ 3 + (AP x - AL' x) * (ξ j) ^ 2 + (AR x - AP' x) * (ξ j)
        + (-(AR' x)) = 0 := by
      intro j
      have e1 := h1 j x
      have e2 := h2 j x
      linear_combination (ξ j) * e1 - e2
    obtain ⟨g3, g2, g1, g0⟩ := cubic_vanish hξ hcub
    exact ⟨g3, g2, g1, by simpa using neg_eq_zero.mp g0⟩
  intro j
  funext x
  have e1 := h1 j x
  have hAL : AL x = 0 := (hx x).1
  have hARAP' : AR x = AP' x := sub_eq_zero.mp (hx x).2.2.1
  rw [hAL, mul_zero, zero_add, hARAP'] at e1
  exact e1.symm

/-! ## Reconstructing the openings of `L`, `P`, `R` -/

/-- The reconstruction: a linear combination (with coefficients `ν`) of the folded child
relations produces an opening of `(∑νξ²)·L + (∑νξ)·P + (∑ν)·R` in terms of the parent
generators. Picking `ν` to hit `(0,1,0)`/`(1,0,0)`/`(0,0,1)` yields openings of `P`/`L`/`R`. -/
lemma recon_open {m : ℕ} (gL gR hL hR : Fin m → G) (u P L R : G) (ζ : Fin 3 → F)
    (A B : Fin 3 → Fin m → F)
    (hC : ∀ j, (ζ j) ^ 2 • L + (ζ j) • P + R
      = msm (A j) (foldG (ζ j) gL gR) + msm (B j) (foldH (ζ j) hL hR) + ip (A j) (B j) • u)
    (ν : Fin 3 → F) :
    msm (fun x => ∑ j, ν j * A j x) gL
      + msm (fun x => ∑ j, ν j * ζ j * A j x) gR
      + msm (fun x => ∑ j, ν j * ζ j * B j x) hL
      + msm (fun x => ∑ j, ν j * B j x) hR
      + (∑ j, ν j * ip (A j) (B j)) • u
    = (∑ j, ν j * (ζ j) ^ 2) • L + (∑ j, ν j * ζ j) • P + (∑ j, ν j) • R := by
  have hsummand : ∀ j,
      (ν j) • msm (A j) gL + (ν j * ζ j) • msm (A j) gR
        + (ν j * ζ j) • msm (B j) hL + (ν j) • msm (B j) hR
        + (ν j * ip (A j) (B j)) • u
      = ν j • ((ζ j) ^ 2 • L + (ζ j) • P + R) := by
    intro j; rw [hC j, msm_foldG, msm_foldH]; module
  -- Expand each `msm` of a coefficient sum, pull the `u`-sum out, and merge the five sums.
  simp only [msm_sum_coeff, msm_smul_coeff, Finset.sum_smul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => hsummand j)]
  simp only [smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]

/-! ## The single-round extraction: witness or discrete-log relation

The witness-or-relation decision `decideStep` (and its correctness `decideStep_valid`) is
reused verbatim from `Sigma.Protocols.IPA.Extract`: it is generic in the five opening
families and the difference tuples. -/

/-- **Step 1 (single-round reconstruction core, computable).** From the four child witnesses
`(a' i, b' i)` for the folded instances, reconstruct — by pure field arithmetic on the challenges
and the child scalars — either a witness for the parent instance (`Sum.inl`) or a non-trivial
discrete-log relation among the parent generators `𝐠ᴸ,𝐠ᴿ,𝐡ᴸ,𝐡ᴿ,u` (`Sum.inr`). Uses no group
elements and no `Classical.choice`: the reconstruction coefficients come from `nuVec` (the
`(ξ², ξ, 1)`-Vandermonde inversion at the first three challenges), and the witness/relation
split is the decidable check `decideStep` of whether all five opening families are consistent. -/
def extractStepData [DecidableEq F] {m : ℕ} (ξ : Fin 4 → F) (a' b' : Fin 4 → Fin m → F) :
    ((Fin m → F) × (Fin m → F) × (Fin m → F) × (Fin m → F)) ⊕
      ((Fin m → F) × (Fin m → F) × (Fin m → F) × (Fin m → F) × F) :=
  let ζ : Fin 3 → F := fun j => ξ j.castSucc
  let A : Fin 3 → Fin m → F := fun j => a' j.castSucc
  let B : Fin 3 → Fin m → F := fun j => b' j.castSucc
  let νP := nuVec ζ ![0, 1, 0]
  let νL := nuVec ζ ![1, 0, 0]
  let νR := nuVec ζ ![0, 0, 1]
  let gLo_P : Fin m → F := fun x => ∑ j, νP j * A j x
  let gHi_P : Fin m → F := fun x => ∑ j, νP j * ζ j * A j x
  let hLo_P : Fin m → F := fun x => ∑ j, νP j * ζ j * B j x
  let hHi_P : Fin m → F := fun x => ∑ j, νP j * B j x
  let c_P : F := ∑ j, νP j * ip (A j) (B j)
  let gLo_L : Fin m → F := fun x => ∑ j, νL j * A j x
  let gHi_L : Fin m → F := fun x => ∑ j, νL j * ζ j * A j x
  let hLo_L : Fin m → F := fun x => ∑ j, νL j * ζ j * B j x
  let hHi_L : Fin m → F := fun x => ∑ j, νL j * B j x
  let c_L : F := ∑ j, νL j * ip (A j) (B j)
  let gLo_R : Fin m → F := fun x => ∑ j, νR j * A j x
  let gHi_R : Fin m → F := fun x => ∑ j, νR j * ζ j * A j x
  let hLo_R : Fin m → F := fun x => ∑ j, νR j * ζ j * B j x
  let hHi_R : Fin m → F := fun x => ∑ j, νR j * B j x
  let c_R : F := ∑ j, νR j * ip (A j) (B j)
  let dgL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gLo_L x + (ξ j) * gLo_P x + gLo_R x) - a' j
  let dgR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gHi_L x + (ξ j) * gHi_P x + gHi_R x) - (fun x => (ξ j) * a' j x)
  let dhL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hLo_L x + (ξ j) * hLo_P x + hLo_R x) - (fun x => (ξ j) * b' j x)
  let dhR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hHi_L x + (ξ j) * hHi_P x + hHi_R x) - b' j
  let du : Fin 4 → F := fun j =>
    (ξ j) ^ 2 * c_L + (ξ j) * c_P + c_R - ip (a' j) (b' j)
  decideStep gLo_P gHi_P hLo_P hHi_P dgL dgR dhL dhR du

/-- **Step 1 (correctness of `extractStepData`).** Given the four folded-instance relations (at
pairwise distinct challenges), every `Sum.inl` output is a valid parent witness, and every
`Sum.inr` output is a non-trivial discrete-log relation among the parent generators. The two
obligations handed to `decideStep_valid` are: every difference tuple opens `0` (both sides open
`ξⱼ²·L + ξⱼ·P + R`, by `recon_open` and the round relation), and full consistency forces the
reconstructed `P`-opening to be a genuine witness (`recover_side`, then `quad_vanish` for the
`u`-coefficient). -/
lemma extractStepData_valid [DecidableEq F] {m : ℕ} (gL gR hL hR : Fin m → G) (u P L R : G)
    {ξ : Fin 4 → F} (hξ : Function.Injective ξ)
    {a' b' : Fin 4 → Fin m → F}
    (hC : ∀ i, (ξ i) ^ 2 • L + (ξ i) • P + R
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
  set gLo_P : Fin m → F := fun x => ∑ j, νP j * A j x with hgLoP
  set gHi_P : Fin m → F := fun x => ∑ j, νP j * ζ j * A j x with hgHiP
  set hLo_P : Fin m → F := fun x => ∑ j, νP j * ζ j * B j x with hhLoP
  set hHi_P : Fin m → F := fun x => ∑ j, νP j * B j x with hhHiP
  set c_P : F := ∑ j, νP j * ip (A j) (B j) with hcP
  set gLo_L : Fin m → F := fun x => ∑ j, νL j * A j x with hgLoL
  set gHi_L : Fin m → F := fun x => ∑ j, νL j * ζ j * A j x with hgHiL
  set hLo_L : Fin m → F := fun x => ∑ j, νL j * ζ j * B j x with hhLoL
  set hHi_L : Fin m → F := fun x => ∑ j, νL j * B j x with hhHiL
  set c_L : F := ∑ j, νL j * ip (A j) (B j) with hcL
  set gLo_R : Fin m → F := fun x => ∑ j, νR j * A j x with hgLoR
  set gHi_R : Fin m → F := fun x => ∑ j, νR j * ζ j * A j x with hgHiR
  set hLo_R : Fin m → F := fun x => ∑ j, νR j * ζ j * B j x with hhLoR
  set hHi_R : Fin m → F := fun x => ∑ j, νR j * B j x with hhHiR
  set c_R : F := ∑ j, νR j * ip (A j) (B j) with hcR
  set dgL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gLo_L x + (ξ j) * gLo_P x + gLo_R x) - a' j with hdgL
  set dgR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * gHi_L x + (ξ j) * gHi_P x + gHi_R x) -
      (fun x => (ξ j) * a' j x) with hdgR
  set dhL : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hLo_L x + (ξ j) * hLo_P x + hLo_R x) -
      (fun x => (ξ j) * b' j x) with hdhL
  set dhR : Fin 4 → Fin m → F := fun j =>
    (fun x => (ξ j) ^ 2 * hHi_L x + (ξ j) * hHi_P x + hHi_R x) - b' j with hdhR
  set du : Fin 4 → F := fun j =>
    (ξ j) ^ 2 * c_L + (ξ j) * c_P + c_R - ip (a' j) (b' j) with hdu
  -- common reconstruction facts.
  have hζj : ∀ j, ζ j = ξ j.castSucc := fun _ => rfl
  have hζinj : Function.Injective ζ := fun a b hab =>
    Fin.castSucc_injective 3 (hξ hab)
  have hCζ : ∀ j : Fin 3, (ζ j) ^ 2 • L + (ζ j) • P + R
      = msm (A j) (foldG (ζ j) gL gR) + msm (B j) (foldH (ζ j) hL hR) + ip (A j) (B j) • u :=
    fun j => hC j.castSucc
  obtain ⟨hνP1, hνP2, hνP3⟩ := nuVec_spec hζinj ![0, 1, 0]
  obtain ⟨hνL1, hνL2, hνL3⟩ := nuVec_spec hζinj ![1, 0, 0]
  obtain ⟨hνR1, hνR2, hνR3⟩ := nuVec_spec hζinj ![0, 0, 1]
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
    have hRecon : msm (fun x => (ξ j) ^ 2 * gLo_L x + (ξ j) * gLo_P x + gLo_R x) gL
        + msm (fun x => (ξ j) ^ 2 * gHi_L x + (ξ j) * gHi_P x + gHi_R x) gR
        + msm (fun x => (ξ j) ^ 2 * hLo_L x + (ξ j) * hLo_P x + hLo_R x) hL
        + msm (fun x => (ξ j) ^ 2 * hHi_L x + (ξ j) * hHi_P x + hHi_R x) hR
        + ((ξ j) ^ 2 * c_L + (ξ j) * c_P + c_R) • u
        = (ξ j) ^ 2 • L + (ξ j) • P + R := by
      simp only [msm_add_coeff, msm_smul_coeff]
      rw [hreconL, hreconP, hreconR]; module
    have hAct : msm (a' j) gL + msm (fun x => (ξ j) * a' j x) gR
        + msm (fun x => (ξ j) * b' j x) hL + msm (b' j) hR
        + ip (a' j) (b' j) • u = (ξ j) ^ 2 • L + (ξ j) • P + R := by
      have hh := hC j
      rw [msm_foldG, msm_foldH] at hh
      simp only [msm_smul_coeff]
      rw [hh]; abel
    rw [hdgL, hdgR, hdhL, hdhR, hdu]
    simp only [msm_sub, sub_smul]
    rw [show ∀ a b c d e f g h i k : G,
        (a - b) + (c - d) + (e - f) + (g - h) + (i - k)
          = (a + c + e + g + i) - (b + d + f + h + k) from fun _ _ _ _ _ _ _ _ _ _ => by abel,
      hRecon, hAct, sub_self]
  · -- Consistency forces the reconstructed `P`-opening to be a genuine witness.
    intro hcons
    have cGLo : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * gLo_L x + (ξ j) * gLo_P x + gLo_R x
        = a' j x := by
      intro j x
      have h := congrFun (hcons j).1 x
      simp only [hdgL, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cGHi : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * gHi_L x + (ξ j) * gHi_P x + gHi_R x
        = (ξ j) * a' j x := by
      intro j x
      have h := congrFun (hcons j).2.1 x
      simp only [hdgR, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cHLo : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * hLo_L x + (ξ j) * hLo_P x + hLo_R x
        = (ξ j) * b' j x := by
      intro j x
      have h := congrFun (hcons j).2.2.1 x
      simp only [hdhL, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cHHi : ∀ (j : Fin 4) (x : Fin m), (ξ j) ^ 2 * hHi_L x + (ξ j) * hHi_P x + hHi_R x
        = b' j x := by
      intro j x
      have h := congrFun (hcons j).2.2.2.1 x
      simp only [hdhR, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h
    have cU : ∀ j : Fin 4, (ξ j) ^ 2 * c_L + (ξ j) * c_P + c_R = ip (a' j) (b' j) := by
      intro j
      have h := (hcons j).2.2.2.2
      simp only [hdu, sub_eq_zero] at h
      exact h
    -- The folded scalars are genuine folds of the `P`-opening halves.
    have ha' : ∀ j, a' j = fun x => (ξ j) * gLo_P x + gHi_P x :=
      recover_side hξ gLo_L gLo_P gLo_R gHi_L gHi_P gHi_R a' cGLo cGHi
    have hb' : ∀ j, b' j = fun x => (ξ j) * hHi_P x + hLo_P x :=
      recover_side hξ hHi_L hHi_P hHi_R hLo_L hLo_P hLo_R b' cHHi cHLo
    have hip : ∀ j, ip (a' j) (b' j)
        = (ξ j) ^ 2 * ip gLo_P hHi_P + (ξ j) * (ip gLo_P hLo_P + ip gHi_P hHi_P)
          + ip gHi_P hLo_P := by
      intro j
      rw [ha' j, hb' j]
      simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right]
      ring
    have hquad : ∀ j : Fin 3,
        (c_L - ip gLo_P hHi_P) * (ζ j) ^ 2 + (c_P - (ip gLo_P hLo_P + ip gHi_P hHi_P)) * (ζ j)
          + (c_R - ip gHi_P hLo_P) = 0 := by
      intro j
      have hu := cU j.castSucc
      rw [hip j.castSucc, ← hζj j] at hu
      linear_combination hu
    obtain ⟨_, h0, _⟩ := quad_vanish hζinj hquad
    have hcPeq : c_P = ip gLo_P hLo_P + ip gHi_P hHi_P := by linear_combination h0
    rw [hreconP, hcPeq]

end Sigma.Protocols.IPAImproved
