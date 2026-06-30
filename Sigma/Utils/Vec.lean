/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib

/-!
# Vector helpers for the Generalized Bulletproofs specification

Thin wrappers over Mathlib so the protocol specification reads like the report
(`report-tool/content/generalized-bulletproofs`). Vectors are modelled as functions
`ι → F` / `ι → G` (usually `ι = Fin n`), with `F` a field acting on a module `G`.
-/

namespace Sigma

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- Inner product (dot product) of two scalar vectors, `⟨a, b⟩ = ∑ᵢ aᵢ bᵢ`. -/
def ip {ι : Type*} [Fintype ι] (a b : ι → F) : F := ∑ i, a i * b i

/-- Multi-scalar multiplication / "inner product" of a scalar vector with a generator
vector, `⟨a, 𝐠⟩ = ∑ᵢ aᵢ • gᵢ ∈ G`. -/
def msm {ι : Type*} [Fintype ι] (a : ι → F) (gs : ι → G) : G := ∑ i, a i • gs i

/-- Multi-scalar multiplication splits over `Fin.append`: `⟨a ⧺ b, 𝐠 ⧺ 𝐡⟩ = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩`. -/
lemma msm_append {p q : ℕ} (a : Fin p → F) (b : Fin q → F) (gp : Fin p → G) (gq : Fin q → G) :
    msm (Fin.append a b) (Fin.append gp gq) = msm a gp + msm b gq := by
  simp only [msm]
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left, Fin.append_left]
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right, Fin.append_right]

/-- Hadamard (pointwise) product of two scalar vectors, `(a ∘ b)ᵢ = aᵢ bᵢ`. -/
def hadamard {ι : Type*} (a b : ι → F) : ι → F := fun i => a i * b i

/-- Pointwise inverse of a scalar vector, `(a⁻¹)ᵢ = (aᵢ)⁻¹`. -/
def vinv {ι : Type*} (a : ι → F) : ι → F := fun i => (a i)⁻¹

/-- The powers vector `(1, y, y², …, yⁿ⁻¹) ∈ Fⁿ`. -/
def powers (y : F) (n : ℕ) : Fin n → F := fun i => y ^ (i : ℕ)

/-- Pointwise scaling of a generator vector by a scalar vector, `(s ⊙ 𝐠)ᵢ = sᵢ • gᵢ`.
Used e.g. for the change of basis `𝐇' = 𝐲⁻¹ ⊙ 𝐇`. -/
def vsmul {ι : Type*} (s : ι → F) (gs : ι → G) : ι → G := fun i => s i • gs i

@[inherit_doc] infixr:73 " ⊙ " => vsmul

/-! ## Linearity of `msm` -/

/-- `msm` distributes over a pointwise sum of generator vectors. -/
lemma msm_add {ι : Type*} [Fintype ι] (a : ι → F) (Γ Δ : ι → G) :
    msm a (Γ + Δ) = msm a Γ + msm a Δ := by
  simp only [msm, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- `msm` distributes over a pointwise difference of coefficient vectors. -/
lemma msm_sub {ι : Type*} [Fintype ι] (a b : ι → F) (Γ : ι → G) :
    msm (a - b) Γ = msm a Γ - msm b Γ := by
  simp only [msm, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- The multi-scalar multiplication of `v` against the affine generator vector
`Γᵢ = rᵢ • g + dᵢ • p` collapses to a relation in the two generators `g` and `p`,
with coefficients `⟨v, r⟩` and `⟨v, d⟩`. -/
lemma msm_smul_add_smul {ι : Type*} [Fintype ι] (v r d : ι → F) (g p : G) :
    msm v (fun i => r i • g + d i • p) = ip v r • g + ip v d • p := by
  simp only [msm, ip, smul_add, smul_smul, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, ← Finset.sum_smul]

end Sigma
