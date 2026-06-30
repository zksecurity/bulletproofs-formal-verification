/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Utils.Vec

/-!
# Generic `ip` / `msm` / sum algebra

Protocol-agnostic linearity and sum-manipulation lemmas for the vector helpers in
`Sigma.Utils.Vec` (`ip`, `msm`, `powers`, `vinv`, `hadamard`), shared by the completeness
proofs of the Generalized Bulletproofs arithmetizations (base and improved).
-/

namespace Sigma

open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## Linearity of `ip` and `msm` -/

lemma ip_eq_dotProduct {ι : Type*} [Fintype ι] (a b : ι → F) : ip a b = a ⬝ᵥ b := rfl

lemma ip_comm {ι : Type*} [Fintype ι] (a b : ι → F) : ip a b = ip b a := by
  simp only [ip_eq_dotProduct, dotProduct_comm]

lemma ip_add_left {ι : Type*} [Fintype ι] (a b c : ι → F) :
    ip (a + b) c = ip a c + ip b c := by
  simp only [ip_eq_dotProduct, add_dotProduct]

lemma ip_add_right {ι : Type*} [Fintype ι] (a b c : ι → F) :
    ip a (b + c) = ip a b + ip a c := by
  simp only [ip_eq_dotProduct, dotProduct_add]

lemma ip_zero_left {ι : Type*} [Fintype ι] (c : ι → F) : ip (0 : ι → F) c = 0 := by
  simp only [ip_eq_dotProduct, zero_dotProduct]

lemma ip_zero_right {ι : Type*} [Fintype ι] (c : ι → F) : ip c (0 : ι → F) = 0 := by
  simp only [ip_eq_dotProduct, dotProduct_zero]

lemma ip_sum_left {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → F) (c : ι → F) :
    ip (∑ k ∈ s, f k) c = ∑ k ∈ s, ip (f k) c := by
  simp only [ip, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ip_sum_right {ι κ : Type*} [Fintype ι] (s : Finset κ) (c : ι → F) (f : κ → ι → F) :
    ip c (∑ k ∈ s, f k) = ∑ k ∈ s, ip c (f k) := by
  simp only [ip, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The matrix transpose identity: `⟨a, 𝐳·W⟩ = ⟨𝐳, W·a⟩` (after scaling by `z`). -/
lemma ip_smul_vecMul {n q : ℕ} (z : F) (a : Fin n → F) (vz : Fin q → F)
    (W : Matrix (Fin q) (Fin n) F) :
    ip a (z • (vz ᵥ* W)) = z * ip vz (W *ᵥ a) := by
  rw [ip_eq_dotProduct, ip_eq_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm a (vz ᵥ* W), ← Matrix.dotProduct_mulVec]

lemma msm_add_left {ι : Type*} [Fintype ι] (a b : ι → F) (gs : ι → G) :
    msm (a + b) gs = msm a gs + msm b gs := by
  simp only [msm, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma msm_sub_left {ι : Type*} [Fintype ι] (a b : ι → F) (gs : ι → G) :
    msm (a - b) gs = msm a gs - msm b gs := by
  simp only [msm, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma msm_zero_left {ι : Type*} [Fintype ι] (gs : ι → G) : msm (0 : ι → F) gs = 0 := by
  simp only [msm, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

lemma msm_sum_left {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → F) (gs : ι → G) :
    msm (∑ k ∈ s, f k) gs = ∑ k ∈ s, msm (f k) gs := by
  simp only [msm, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

lemma msm_smul_left {ι : Type*} [Fintype ι] (c : F) (a : ι → F) (gs : ι → G) :
    msm (c • a) gs = c • msm a gs := by
  simp only [msm, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- `msm` distributes over a pointwise sum written as a lambda. -/
lemma msm_add' {ι : Type*} [Fintype ι] (f g : ι → F) (gs : ι → G) :
    msm (fun i => f i + g i) gs = msm f gs + msm g gs := by
  simp only [msm, add_smul, Finset.sum_add_distrib]

/-- `msm` distributes over a pointwise difference written as a lambda. -/
lemma msm_sub' {ι : Type*} [Fintype ι] (f g : ι → F) (gs : ι → G) :
    msm (fun i => f i - g i) gs = msm f gs - msm g gs := by
  simp only [msm, sub_smul, Finset.sum_sub_distrib]

lemma ip_smul_left {ι : Type*} [Fintype ι] (c : F) (a b : ι → F) :
    ip (c • a) b = c * ip a b := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma ip_add_left' {ι : Type*} [Fintype ι] (f g c : ι → F) :
    ip (fun i => f i + g i) c = ip f c + ip g c := by
  simp only [ip, add_mul, Finset.sum_add_distrib]

lemma ip_add_right' {ι : Type*} [Fintype ι] (a f g : ι → F) :
    ip a (fun i => f i + g i) = ip a f + ip a g := by
  simp only [ip, mul_add, Finset.sum_add_distrib]

lemma ip_sub_right' {ι : Type*} [Fintype ι] (a f g : ι → F) :
    ip a (fun i => f i - g i) = ip a f - ip a g := by
  simp only [ip, mul_sub, Finset.sum_sub_distrib]

lemma ip_smul_right {ι : Type*} [Fintype ι] (c : F) (a b : ι → F) :
    ip a (c • b) = c * ip a b := by
  rw [ip_comm, ip_smul_left, ip_comm a b]

/-- `msm` of an `x`-power polynomial of coefficient vectors distributes over the powers. -/
lemma msm_lincomb {ι κ : Type*} [Fintype ι] (s : Finset κ) (c : κ → F) (f : κ → ι → F)
    (gs : ι → G) :
    msm (fun i => ∑ p ∈ s, c p * f p i) gs = ∑ p ∈ s, c p • msm (f p) gs := by
  have hfun : (fun i => ∑ p ∈ s, c p * f p i) = ∑ p ∈ s, c p • f p := by
    funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, msm_sum_left]
  exact Finset.sum_congr rfl fun p _ => msm_smul_left (c p) (f p) gs

/-- The powers vector and its pointwise inverse cancel: `yⁱ · (yⁱ)⁻¹ = 1` (for `y ≠ 0`). -/
lemma powers_mul_vinv (yu : Fˣ) (N : ℕ) (i : Fin N) :
    powers (↑yu : F) N i * vinv (powers (↑yu : F) N) i = 1 :=
  mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero yu))

/-- The change-of-basis cancellation `⟨𝐯𝐲 ∘ w, 𝐲⁻¹ ⊙ 𝐡⟩ = ⟨w, 𝐡⟩` when `𝐯𝐲 ∘ 𝐲⁻¹ = 1`. -/
lemma msm_vy_yinv_cancel {ι : Type*} [Fintype ι] (vy yinv w : ι → F) (hs : ι → G)
    (hvy : ∀ i, vy i * yinv i = 1) :
    msm (fun i => vy i * w i) (yinv ⊙ hs) = msm w hs := by
  simp only [msm, vsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  rw [mul_comm (vy i) (w i), mul_assoc, hvy i, mul_one]

lemma ip_ite_left {ι : Type*} [Fintype ι] (c : Prop) [Decidable c] (a b : ι → F) :
    ip (if c then a else 0) b = if c then ip a b else 0 := by
  split <;> simp [ip_zero_left]

lemma ip_ite_right {ι : Type*} [Fintype ι] (c : Prop) [Decidable c] (a b : ι → F) :
    ip a (if c then b else 0) = if c then ip a b else 0 := by
  split <;> simp [ip_zero_right]

/-- Collapse a double `Fin K`-sum guarded by `p = a ∧ p + ℓ = b`: it picks out `p = a`, `ℓ = b−a`. -/
lemma double_sum_collapse {K : ℕ} {A : Type*} [AddCommMonoid A] (a b : ℕ)
    (ha : a < K) (hab : a ≤ b) (hb : b - a < K) (F : Fin K → Fin K → A) :
    (∑ p : Fin K, ∑ ℓ : Fin K, if (p : ℕ) = a ∧ (p : ℕ) + (ℓ : ℕ) = b then F p ℓ else 0)
      = F ⟨a, ha⟩ ⟨b - a, hb⟩ := by
  rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin K)]
  · rw [Finset.sum_eq_single (⟨b - a, hb⟩ : Fin K)]
    · simp; omega
    · intro ℓ _ hq
      rw [if_neg]; rintro ⟨_, h2⟩; exact hq (Fin.ext (by simp at h2 ⊢; omega))
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    refine Finset.sum_eq_zero fun ℓ _ => ?_
    rw [if_neg]; rintro ⟨h1, _⟩; exact hp (Fin.ext h1)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Distribute a guarded sum over `+`. -/
lemma ite_zero_add {A : Type*} [AddCommMonoid A] (c : Prop) [Decidable c] (a b : A) :
    (if c then a + b else 0) = (if c then a else 0) + (if c then b else 0) := by
  split <;> simp

/-- Distribute a guarded sum over a `Finset.sum`. -/
lemma ite_zero_sum {A K : Type*} [AddCommMonoid A] (c : Prop) [Decidable c] (s : Finset K)
    (f : K → A) : (if c then ∑ k ∈ s, f k else 0) = ∑ k ∈ s, if c then f k else 0 := by
  split <;> simp

/-- Combine nested guards into a conjunction. -/
lemma ite_ite_zero {A : Type*} [Zero A] (c1 c2 : Prop) [Decidable c1] [Decidable c2] (x : A) :
    (if c1 then (if c2 then x else 0) else 0) = if c2 ∧ c1 then x else 0 := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp [h1, h2]

/-- A double `Fin K`-sum guarded by `p = a ∧ p + ℓ = b` with `b < a` is empty. -/
lemma double_sum_zero {K : ℕ} {A : Type*} [AddCommMonoid A] (a b : ℕ) (hgt : b < a)
    (F : Fin K → Fin K → A) :
    (∑ p : Fin K, ∑ ℓ : Fin K, if (p : ℕ) = a ∧ (p : ℕ) + (ℓ : ℕ) = b then F p ℓ else 0) = 0 := by
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun ℓ _ => ?_
  rw [if_neg]; rintro ⟨h1, h2⟩; omega

/-- A `Fin mm`-indexed family double-sum guarded by `p = c k ∧ p + ℓ = b` collapses to one
term per `k`. -/
lemma family_collapse {K mm : ℕ} {A : Type*} [AddCommMonoid A] (c : Fin mm → ℕ) (b : ℕ)
    (hc : ∀ k, c k < K) (hcb : ∀ k, c k ≤ b) (hb : ∀ k, b - c k < K) (F : Fin mm → Fin K → A) :
    (∑ p : Fin K, ∑ ℓ : Fin K, ∑ k : Fin mm,
        if (p : ℕ) = c k ∧ (p : ℕ) + (ℓ : ℕ) = b then F k ℓ else 0)
      = ∑ k : Fin mm, F k ⟨b - c k, hb k⟩ := by
  rw [Finset.sum_congr rfl fun (p : Fin K) _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ =>
    double_sum_collapse (c k) b (hc k) (hcb k) (hb k) (fun _ ℓ => F k ℓ)

/-! ## Collapsing the `x`-power polynomials -/

lemma msm_ite {ι : Type*} [Fintype ι] (c : Prop) [Decidable c] (v : ι → F) (gs : ι → G) :
    msm (if c then v else 0) gs = if c then msm v gs else 0 := by
  split <;> simp [msm_zero_left]

/-- A single monomial of an `x`-power polynomial picks out one power. -/
lemma sum_pow_smul_ite {N : ℕ} (xu : F) (c : ℕ) (hc : c < N) (g : G) :
    (∑ p : Fin N, xu ^ (p : ℕ) • (if (p : ℕ) = c then g else 0)) = xu ^ c • g := by
  rw [Finset.sum_eq_single (⟨c, hc⟩ : Fin N)]
  · simp
  · intro p _ hp
    rw [if_neg (fun h => hp (Fin.ext h)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A `Fin m`-indexed family of monomials picks out one power each. -/
lemma sum_pow_smul_sum_ite {N m : ℕ} (xu : F) (c : Fin m → ℕ) (hc : ∀ k, c k < N)
    (g : Fin m → G) :
    (∑ p : Fin N, xu ^ (p : ℕ) • (∑ k : Fin m, if (p : ℕ) = c k then g k else 0))
      = ∑ k : Fin m, xu ^ (c k) • g k := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => sum_pow_smul_ite xu (c k) (hc k) (g k)

/-- The Cauchy product: the inner product of two evaluated `x`-polynomials equals the sum of
the convolution coefficients times the corresponding power. -/
lemma ip_xpoly_conv {n N M : ℕ} (xu : F) (fL fR : Fin N → Fin n → F)
    (hM : ∀ p ℓ : Fin N, (p : ℕ) + (ℓ : ℕ) < M) :
    ip (fun i => ∑ p : Fin N, xu ^ (p : ℕ) * fL p i)
       (fun i => ∑ ℓ : Fin N, xu ^ (ℓ : ℕ) * fR ℓ i)
      = ∑ d : Fin M, xu ^ (d : ℕ) *
          (∑ p : Fin N, ∑ ℓ : Fin N,
            if (p : ℕ) + (ℓ : ℕ) = (d : ℕ) then ip (fL p) (fR ℓ) else 0) := by
  have hfunL : (fun i => ∑ p : Fin N, xu ^ (p : ℕ) * fL p i) = ∑ p : Fin N, xu ^ (p : ℕ) • fL p := by
    funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hfunR : (fun i => ∑ ℓ : Fin N, xu ^ (ℓ : ℕ) * fR ℓ i) = ∑ ℓ : Fin N, xu ^ (ℓ : ℕ) • fR ℓ := by
    funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hL : ip (fun i => ∑ p : Fin N, xu ^ (p : ℕ) * fL p i)
       (fun i => ∑ ℓ : Fin N, xu ^ (ℓ : ℕ) * fR ℓ i)
      = ∑ p : Fin N, ∑ ℓ : Fin N, xu ^ ((p : ℕ) + (ℓ : ℕ)) * ip (fL p) (fR ℓ) := by
    rw [hfunL, hfunR, ip_sum_left]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ip_smul_left, ip_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [ip_smul_right, pow_add]; ring
  rw [hL]
  symm
  calc ∑ d : Fin M, xu ^ (d : ℕ) *
          (∑ p : Fin N, ∑ ℓ : Fin N,
            if (p : ℕ) + (ℓ : ℕ) = (d : ℕ) then ip (fL p) (fR ℓ) else 0)
      = ∑ d : Fin M, ∑ p : Fin N, ∑ ℓ : Fin N,
          (if (p : ℕ) + (ℓ : ℕ) = (d : ℕ) then xu ^ (d : ℕ) * ip (fL p) (fR ℓ) else 0) := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ p : Fin N, ∑ ℓ : Fin N, ∑ d : Fin M,
          (if (p : ℕ) + (ℓ : ℕ) = (d : ℕ) then xu ^ (d : ℕ) * ip (fL p) (fR ℓ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p : Fin N, ∑ ℓ : Fin N, xu ^ ((p : ℕ) + (ℓ : ℕ)) * ip (fL p) (fR ℓ) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.sum_eq_single (⟨(p : ℕ) + (ℓ : ℕ), hM p ℓ⟩ : Fin M)]
        · simp
        · intro d _ hd; rw [if_neg (fun h => hd (Fin.ext h.symm))]
        · intro h; exact absurd (Finset.mem_univ _) h

/-- Splitting off the excluded index `c` from a guarded sum. -/
lemma sum_ite_zero_eq {M : ℕ} {A : Type*} [AddCommGroup A] (F : Fin M → A) (c : ℕ) (hc : c < M) :
    (∑ x : Fin M, if (x : ℕ) = c then (0 : A) else F x) = (∑ x : Fin M, F x) - F ⟨c, hc⟩ := by
  have hsplit : ∀ x : Fin M,
      F x = (if (x : ℕ) = c then F x else 0) + (if (x : ℕ) = c then 0 else F x) := by
    intro x; split <;> simp
  have hpick : (∑ x : Fin M, if (x : ℕ) = c then F x else 0) = F ⟨c, hc⟩ := by
    rw [Finset.sum_eq_single (⟨c, hc⟩ : Fin M)]
    · simp
    · intro x _ hx; rw [if_neg (fun h => hx (Fin.ext h))]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [eq_sub_iff_add_eq, add_comm]
  conv_rhs => rw [Finset.sum_congr rfl (fun x _ => hsplit x)]
  rw [Finset.sum_add_distrib, hpick]

end Sigma
