/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBP.Arithmetization
import Sigma.Utils.Algebra

/-!
# Completeness of the Generalized Bulletproofs arithmetization

This file proves *perfect completeness* of the arithmetization reduction
`Sigma.Protocols.GBP.arithRed`: every (conversation, opening) pair produced by the honest
prover `arithRedHonest` on a witness satisfying `rel` is accepting — the carried opening
`(τ_x, μ, f_L(x), f_R(x))` satisfies both equations of `Sigma.Protocols.GBP.relArith` at
the derived statement.

The spec in `Sigma.Protocols.GBP.Arithmetization` is not modified; everything here is additive.
-/

namespace Sigma.Protocols.GBP

open OracleComp OracleSpec
open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## Reindexing onto the transmitted degrees -/

/-- **Reindexing a full-degree sum onto the transmitted degrees.** If the coefficients vanish
below degree `c+1`, the sum over all degrees `0 … 2n'+2` is the special term at `n'` plus the
sum over the dense enumeration `tIdx` of `{c+1, …, 2n'+2} \ {n'}`: by `tIdx_inj` the image sum
is the sum over the image, `tIdx_ne` keeps the special degree out of it, and by `tIdx_surj`
everything outside `{n'} ∪ im tIdx` is below `c+1`, where `f` vanishes. -/
lemma sum_split_tIdx {M : Type*} [AddCommMonoid M] {c : ℕ} (f : ℕ → M)
    (hlow : ∀ d, d < c + 1 → f d = 0) :
    (∑ d : Fin (2 * nPrime c + 3), f (d : ℕ))
      = f (nPrime c) + ∑ i : Fin (3 * c + 5), f (tIdx i : ℕ) := by
  have hnp : nPrime c < 2 * nPrime c + 3 := by omega
  have hmem : (⟨nPrime c, hnp⟩ : Fin (2 * nPrime c + 3)) ∉ Finset.univ.image (tIdx (c := c)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i hi => tIdx_ne i (congrArg Fin.val hi)
  have himg : (∑ d ∈ Finset.univ.image (tIdx (c := c)), f (d : ℕ))
      = ∑ i : Fin (3 * c + 5), f (tIdx i : ℕ) :=
    Finset.sum_image fun a _ b _ h => tIdx_inj h
  have hzero : ∀ d ∈ (Finset.univ : Finset (Fin (2 * nPrime c + 3))),
      d ∉ insert (⟨nPrime c, hnp⟩ : Fin (2 * nPrime c + 3)) (Finset.univ.image tIdx) →
        f (d : ℕ) = 0 := by
    intro d _ hd
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists] at hd
    refine hlow _ ?_
    by_contra hge
    obtain ⟨i, hi⟩ := tIdx_surj d (by omega) (fun h => hd.1 (Fin.ext h))
    exact hd.2 i hi
  rw [← himg, ← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_insert hmem]

/-! ## The key coefficient identity -/

omit [AddCommGroup G] [Module F G] in
/-- The "constant-term" identity at the special degree `n' = 2c+2`:

  `tcoeff(n') = δ − w_c − ⟨w_V, v⟩`,

where `tcoeff(n') = Σ_{p+ℓ=n'} ⟨f_L,p, f_R,ℓ⟩`. Expanding `f_L`, `f_R` (each a sparse sum of
indicator vectors) by bilinearity, only the `(p,ℓ)` pairs with `p+ℓ = n'` contribute
`⟨a_L+w_R∘y⁻¹, y∘a_R+w_L⟩ + Σ_k⟨a_C⁽ᵏ⁾,w_C⁽ᵏ⁾⟩ + ⟨a_O, w_O−y⟩`; the Hadamard constraint
`hR2` (`a_L∘a_R = a_O`) and the R1CS row `hR1` then reduce this to `δ − w_c − ⟨w_V, v⟩`. -/
private lemma tcoeff_eq {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    (yu zu : Fˣ) (sL sR : Fin n → F)
    (hR1 : s.WL *ᵥ w.aL + s.WR *ᵥ w.aR + s.WO *ᵥ w.aO + (∑ i, s.WC i *ᵥ w.aC i)
        + s.WV *ᵥ w.v + s.cc = 0)
    (hR2 : hadamard w.aL w.aR - w.aO = 0) :
    (∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
        if (p : ℕ) + (ℓ : ℕ) = nPrime c then
          ip ((((if (p : ℕ) = c + 1 then
                    fun i => w.aL i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i
                  else 0) +
                  ∑ k : Fin c, if (p : ℕ) = nPrime c - ((k : ℕ) + 1) then w.aC k else 0) +
                if (p : ℕ) = nPrime c then w.aO else 0) +
              if (p : ℕ) = nPrime c + 1 then sL else 0)
            (((((if (ℓ : ℕ) = 0 then
                      fun i => ((↑zu : F) • powers (↑zu) q ᵥ* s.WO) i - powers (↑yu) n i else 0) +
                    ∑ x : Fin c, if (ℓ : ℕ) = (x : ℕ) + 1 then (↑zu : F) • powers (↑zu) q ᵥ* s.WC x else 0) +
                  if (ℓ : ℕ) = c + 1 then
                    fun i => powers (↑yu) n i * w.aR i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WL) i else 0) +
                ∑ k : Fin c, if (ℓ : ℕ) = nPrime c - ((k : ℕ) + 1) then
                  fun i => powers (↑yu) n i * w.aux k i else 0) +
              if (ℓ : ℕ) = nPrime c + 1 then fun i => powers (↑yu) n i * sR i else 0)
        else 0)
      = ip (hadamard (vinv (powers (↑yu) n)) ((↑zu : F) • powers (↑zu) q ᵥ* s.WR))
            ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
          - (↑zu : F) * ip (powers (↑zu) q) s.cc
          - ip ((↑zu : F) • powers (↑zu) q ᵥ* s.WV) w.v := by
  -- Expand `ip (f_L p) (f_R ℓ)` over `f_L`; the guard `p+ℓ = n'` pins `ℓ`; collapse each of the
  -- four `f_L`-terms (`double_sum_collapse`/`double_sum_zero`/`family_collapse`), evaluate `f_R`
  -- at the pinned indices (impossible powers vanish by `omega`, the matching `w_C` survives), then
  -- close with the field algebra (`hR2`, `hR1`).
  simp only [ip_add_left, ip_sum_left, ip_ite_left, ite_zero_add, ite_zero_sum,
    ite_ite_zero, Finset.sum_add_distrib]
  rw [double_sum_collapse (c + 1) (nPrime c) (by simp only [nPrime]; omega)
        (by simp only [nPrime]; omega) (by omega),
    double_sum_collapse (nPrime c) (nPrime c) (by omega) (le_refl _) (by omega),
    double_sum_zero (nPrime c + 1) (nPrime c) (by omega),
    family_collapse (fun k => nPrime c - ((k : ℕ) + 1)) (nPrime c)
      (fun k => by dsimp only; omega) (fun k => by dsimp only; omega)
      (fun k => by dsimp only; omega)]
  have hidx1 : nPrime c - (c + 1) = c + 1 := by simp only [nPrime]; omega
  have hidx3 : nPrime c - nPrime c = 0 := by omega
  have hidx2 : ∀ k : Fin c, nPrime c - (nPrime c - ((k : ℕ) + 1)) = (k : ℕ) + 1 :=
    fun k => by have := k.isLt; simp only [nPrime]; omega
  simp only [hidx1, hidx3, hidx2, ip_add_right, ip_sum_right, ip_ite_right]
  simp only [if_true]
  rw [if_neg (show ¬(c + 1 = 0) by omega),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬(c + 1 = (x : ℕ) + 1) by
      have := x.isLt; omega)),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬(c + 1 = nPrime c - ((x : ℕ) + 1)) by
      have := x.isLt; simp only [nPrime]; omega)),
    if_neg (show ¬(c + 1 = nPrime c + 1) by simp only [nPrime]; omega),
    if_neg (show ¬((0 : ℕ) = c + 1) by omega),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬((0 : ℕ) = (x : ℕ) + 1) by omega)),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬((0 : ℕ) = nPrime c - ((x : ℕ) + 1)) by
      have := x.isLt; simp only [nPrime]; omega)),
    if_neg (show ¬((0 : ℕ) = nPrime c + 1) by simp only [nPrime]; omega)]
  have e0 : ∀ x : Fin c, ((x : ℕ) + 1 = 0) = False := fun x => eq_false (by omega)
  have eM : ∀ x : Fin c, ((x : ℕ) + 1 = c + 1) = False := fun x => eq_false (by have := x.isLt; omega)
  have eN : ∀ x : Fin c, ((x : ℕ) + 1 = nPrime c + 1) = False :=
    fun x => eq_false (by simp only [nPrime]; omega)
  have eH : ∀ x x_1 : Fin c, ((x : ℕ) + 1 = nPrime c - ((x_1 : ℕ) + 1)) = False :=
    fun x x_1 => eq_false (by have := x.isLt; have := x_1.isLt; simp only [nPrime]; omega)
  have eD : ∀ x x_1 : Fin c, ((x : ℕ) + 1 = (x_1 : ℕ) + 1) = (x_1 = x) :=
    fun x x_1 => by rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  simp only [e0, eM, eN, eH, eD, if_false, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, add_zero, zero_add]
  -- final field algebra: the three contributions, using `hR2` (Hadamard) and `hR1` (R1CS row)
  have hvyinv := powers_mul_vinv yu n
  have hR2' : ∀ i, w.aL i * w.aR i = w.aO i := fun i => by
    have h := congrFun hR2 i
    simp only [hadamard, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
    exact h
  have hI : ip (fun i => w.aL i + (↑zu • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i)
          (fun i => powers (↑yu) n i * w.aR i + (↑zu • powers (↑zu) q ᵥ* s.WL) i)
        + ip w.aO (fun i => (↑zu • powers (↑zu) q ᵥ* s.WO) i - powers (↑yu) n i)
      = ip (hadamard (vinv (powers (↑yu) n)) (↑zu • powers (↑zu) q ᵥ* s.WR))
            (↑zu • powers (↑zu) q ᵥ* s.WL)
        + ip w.aL ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
        + ip w.aR ((↑zu : F) • powers (↑zu) q ᵥ* s.WR)
        + ip w.aO ((↑zu : F) • powers (↑zu) q ᵥ* s.WO) := by
    simp only [ip, hadamard]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (powers (↑yu) n i) * (hR2' i)
      + ((↑zu • powers (↑zu) q ᵥ* s.WR) i * w.aR i) * (hvyinv i)
  have hWV : ip ((↑zu : F) • powers (↑zu) q ᵥ* s.WV) w.v
      = (↑zu : F) * ip (powers (↑zu) q) (s.WV *ᵥ w.v) := by
    rw [ip_comm, ip_smul_vecMul]
  have hmat : s.WL *ᵥ w.aL + s.WR *ᵥ w.aR + s.WO *ᵥ w.aO + (∑ x, s.WC x *ᵥ w.aC x)
      = -(s.WV *ᵥ w.v) - s.cc := by
    linear_combination hR1
  have hII' : ip w.aL ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
        + ip w.aR ((↑zu : F) • powers (↑zu) q ᵥ* s.WR)
        + ip w.aO ((↑zu : F) • powers (↑zu) q ᵥ* s.WO)
        + ∑ x, ip (w.aC x) ((↑zu : F) • powers (↑zu) q ᵥ* s.WC x)
      = -((↑zu : F) * ip (powers (↑zu) q) s.cc) - ip ((↑zu : F) • powers (↑zu) q ᵥ* s.WV) w.v := by
    simp only [ip_smul_vecMul, hWV]
    rw [← Finset.mul_sum, ← ip_sum_right, ← mul_add, ← mul_add, ← mul_add,
      ← ip_add_right, ← ip_add_right, ← ip_add_right, hmat]
    simp only [ip_eq_dotProduct, dotProduct_sub, dotProduct_neg]
    ring
  linear_combination hI + hII'

omit [AddCommGroup G] [Module F G] in
/-- The honest `t`-polynomial has no coefficient below degree `c+1` (the lowest `f_L` slot):
for `d < c+1`, every summand of the convolution `Σ_{p+ℓ=d} ⟨f_L,p, f_R,ℓ⟩` has `p ≤ d < c+1`,
where all four `f_L`-indicators are off — so each inner product is `⟨0, f_R,ℓ⟩ = 0`. (Stated
with the `x^d`-weight, and against the literal `f_L`/`f_R` expansions so that it feeds
`sum_split_tIdx` and `rw`-matches the goal.) -/
private lemma tcoeff_low {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    (yu zu xu : Fˣ) (sL sR : Fin n → F) {d : ℕ} (hd : d < c + 1) :
    (↑xu : F) ^ d * (∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
        if (p : ℕ) + (ℓ : ℕ) = d then
          ip ((((if (p : ℕ) = c + 1 then
                    fun i => w.aL i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i
                  else 0) +
                  ∑ k : Fin c, if (p : ℕ) = nPrime c - ((k : ℕ) + 1) then w.aC k else 0) +
                if (p : ℕ) = nPrime c then w.aO else 0) +
              if (p : ℕ) = nPrime c + 1 then sL else 0)
            (((((if (ℓ : ℕ) = 0 then
                      fun i => ((↑zu : F) • powers (↑zu) q ᵥ* s.WO) i - powers (↑yu) n i else 0) +
                    ∑ x : Fin c, if (ℓ : ℕ) = (x : ℕ) + 1 then (↑zu : F) • powers (↑zu) q ᵥ* s.WC x else 0) +
                  if (ℓ : ℕ) = c + 1 then
                    fun i => powers (↑yu) n i * w.aR i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WL) i else 0) +
                ∑ k : Fin c, if (ℓ : ℕ) = nPrime c - ((k : ℕ) + 1) then
                  fun i => powers (↑yu) n i * w.aux k i else 0) +
              if (ℓ : ℕ) = nPrime c + 1 then fun i => powers (↑yu) n i * sR i else 0)
        else 0)
      = 0 := by
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun ℓ _ => ?_)
  by_cases hpq : (p : ℕ) + (ℓ : ℕ) = d
  · rw [if_pos hpq,
      if_neg (show ¬((p : ℕ) = c + 1) by omega),
      Finset.sum_eq_zero (fun (k : Fin c) _ => if_neg
        (show ¬((p : ℕ) = nPrime c - ((k : ℕ) + 1)) by
          have := k.isLt; simp only [nPrime]; omega)),
      if_neg (show ¬((p : ℕ) = nPrime c) by simp only [nPrime]; omega),
      if_neg (show ¬((p : ℕ) = nPrime c + 1) by simp only [nPrime]; omega)]
    simp only [add_zero]
    exact ip_zero_left _
  · exact if_neg hpq

/-! ## Completeness -/

variable [DecidableEq F] [DecidableEq G] [SampleableType F] [SampleableType Fˣ]

theorem arithRed_complete {n q m c : ℕ} :
    (arithRed (F := F) (G := G) n q m c).Complete arithRedHonest := by
  intro s w hrel p hp
  simp only [arithRed, relGBP, rel, Bool.and_eq_true, decide_eq_true_eq] at hrel
  obtain ⟨⟨⟨hR1, hR2⟩, hR3⟩, hR4⟩ := hrel
  simp only [arithRedHonest, support_bind, support_uniformSample, support_pure, Set.mem_iUnion,
    Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hp
  obtain ⟨α, β, ρ, sL, sR, yu, zu, τ, xu, rfl⟩ := hp
  refine ⟨_, rfl, ?_⟩
  simp only [arithAssemble, arithRed, relArith, arithOut, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · -- eq1: the t-polynomial identity `t̂·g + τₓ·h = xⁿ'·((δ−w_c)·g − ⟨w_V,V⟩) + Σᵢ x^{tIdx i}·Tᵢ`.
    --
    -- The full reduction is:
    --  • `msm w_V V = ⟨w_V,v⟩·g + ⟨w_V,γ⟩·h`  (from `hR4`, the scalar-commitment openings);
    --  • `t̂ = ⟨f_L(x), f_R(x)⟩ = Σ_d xᵈ·tcoeff d`  (the Cauchy product `ip_xpoly_conv`);
    --  • the full-degree sum collapses to the special `n'`-term plus the transmitted degrees
    --    (`sum_split_tIdx`, fed the low-degree vanishing `tcoeff_low`); pulling `g`/`h` out,
    --    the `g`/`h` coefficients match iff the single field identity
    --        `tcoeff n' = δ − w_c − ⟨w_V, v⟩`
    --    holds, where `tcoeff n' = Σ_{p+ℓ=n'} ⟨f_L,p, f_R,ℓ⟩`.
    --
    -- That coefficient identity is central to the soundness/completeness of the arithmetization:
    -- expanding `f_L`, `f_R` (each a sparse sum of indicator vectors) by bilinearity, the only
    -- (p,ℓ) pairs with p+ℓ = n' = 2c+2 contribute
    --     ⟨a_L + w_R∘y⁻¹, y∘a_R + w_L⟩ + Σ_k ⟨a_C⁽ᵏ⁾, w_C⁽ᵏ⁾⟩ + ⟨a_O, w_O − y⟩
    --   = δ + ⟨a_L,w_L⟩ + ⟨w_R,a_R⟩ + ⟨a_O,w_O⟩ + Σ_k⟨a_C⁽ᵏ⁾,w_C⁽ᵏ⁾⟩      (using a_L∘a_R = a_O, i.e. `hR2`)
    --   = δ + z·⟨v_z, W_L a_L + W_R a_R + W_O a_O + Σ_k W_C⁽ᵏ⁾ a_C⁽ᵏ⁾⟩
    --   = δ − z·⟨v_z, W_V v + c⟩                                         (using the R1CS row `hR1`)
    --   = δ − w_c − ⟨w_V, v⟩.
    -- The convolution, the support-split, `msm`/`ip` linearity, and the matrix-transpose identity
    -- `ip_smul_vecMul` are all proven above and assembled below.
    have hmsmV : msm ((↑zu : F) • powers (↑zu) q ᵥ* s.WV) s.V
        = ip ((↑zu : F) • powers (↑zu) q ᵥ* s.WV) w.v • s.g
          + ip ((↑zu : F) • powers (↑zu) q ᵥ* s.WV) w.γ • s.h := by
      simp only [msm, hR4, smul_add, smul_smul]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
      rfl
    rw [hmsmV, ip_xpoly_conv (M := 2 * nPrime c + 3) (↑xu : F) _ _ (fun p ℓ => by omega)]
    rw [sum_split_tIdx _ (fun d hd => tcoeff_low s w yu zu xu sL sR hd)]
    simp only [smul_sub, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hK := tcoeff_eq s w yu zu sL sR hR1 hR2
    rw [show (∑ i : Fin (3 * c + 5), τ i * (↑xu : F) ^ (tIdx i : ℕ))
          = ∑ i : Fin (3 * c + 5), (↑xu : F) ^ (tIdx i : ℕ) * τ i from
        Finset.sum_congr rfl fun i _ => mul_comm _ _]
    rw [hK]
    module
  · -- eq2: commitment opening
    simp only [hR3]
    rw [msm_lincomb, msm_lincomb]
    simp only [msm_add_left, msm_sum_left, msm_ite, smul_add, Finset.sum_add_distrib]
    have hyy := powers_mul_vinv (F := F) yu n
    have hcancel : ∀ w : Fin n → F,
        msm (fun i => powers (↑yu : F) n i * w i) (vinv (powers (↑yu : F) n) ⊙ s.hs) = msm w s.hs :=
      fun w => msm_vy_yinv_cancel _ _ w s.hs hyy
    have hb1 : c + 1 < nPrime c + 2 := by simp only [nPrime]; omega
    have hb2 : nPrime c < nPrime c + 2 := by omega
    have hb3 : nPrime c + 1 < nPrime c + 2 := by omega
    have hb4 : (0 : ℕ) < nPrime c + 2 := by omega
    have hb5 : ∀ k : Fin c, nPrime c - ((k : ℕ) + 1) < nPrime c + 2 := fun k => by omega
    have hb6 : ∀ k : Fin c, (k : ℕ) + 1 < nPrime c + 2 := fun k => by
      have := k.isLt; simp only [nPrime]; omega
    rw [sum_pow_smul_ite (↑xu : F) (c + 1) hb1,
      sum_pow_smul_sum_ite (↑xu : F) (fun k => nPrime c - ((k : ℕ) + 1)) hb5,
      sum_pow_smul_ite (↑xu : F) (nPrime c) hb2,
      sum_pow_smul_ite (↑xu : F) (nPrime c + 1) hb3,
      sum_pow_smul_ite (↑xu : F) 0 hb4,
      sum_pow_smul_sum_ite (↑xu : F) (fun k => (k : ℕ) + 1) hb6,
      sum_pow_smul_ite (↑xu : F) (c + 1) hb1,
      sum_pow_smul_sum_ite (↑xu : F) (fun k => nPrime c - ((k : ℕ) + 1)) hb5,
      sum_pow_smul_ite (↑xu : F) (nPrime c + 1) hb3]
    simp only [msm_add', msm_sub', hcancel, msm_sub_left, pow_zero, one_smul]
    unfold hadamard
    rw [show (fun i => ((↑zu : F) • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i)
          = (fun i => vinv (powers (↑yu) n) i * ((↑zu : F) • powers (↑zu) q ᵥ* s.WR) i) from
        funext fun i => mul_comm _ _]
    simp only [add_smul, Finset.sum_smul, smul_smul]
    rw [show (∑ x : Fin c, ((↑xu : F) ^ (nPrime c - ((x : ℕ) + 1)) * w.γC x) • s.h)
          = ∑ x : Fin c, (w.γC x * (↑xu : F) ^ (nPrime c - ((x : ℕ) + 1))) • s.h from
        Finset.sum_congr rfl (fun x _ => by rw [mul_comm])]
    module

end Sigma.Protocols.GBP
