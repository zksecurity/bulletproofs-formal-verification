/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBPImproved.Arithmetization
import Sigma.Protocols.GBP.ArithmetizationComplete

/-!
# Completeness of the improved Generalized Bulletproofs arithmetization

This file proves *perfect completeness* of `Sigma.Protocols.GBPImproved.arithRed'`: every
(conversation, output-witness) pair the honest prover `arithHonest'` produces on a witness
satisfying the improved relation `Sigma.Protocols.GBPImproved.rel` is accepting.

The proof mirrors `Sigma.Protocols.GBP.arithmetization_complete` and reuses its (public)
`ip`/`msm` linearity, Cauchy-product (`ip_xpoly_conv`), guarded-sum collapse
(`double_sum_collapse`, `family_collapse`, `sum_ite_zero_eq`, `sum_pow_smul_ite`), and
change-of-basis (`msm_vy_yinv_cancel`) helpers. Differences from the base proof:

* the improved layout has **no `𝐲 ∘ aux` term** in `f_R`, so the target-coefficient identity
  `tcoeff'_eq` (the coefficient of `X^{c+1}` equals `δ − w_c − ⟨w_V, v⟩`) is shorter;
* the verifier evaluates the `𝐆`-side and `𝐇`-side separately and recombines them with the
  binding challenge `r` (the conversation's last move; the virtual final message
  `(τ_x, μ = μ_L + r·μ_R, f_L(x), f_R(x))` is the output witness), so the commitment check
  `eq2` is proved as a `𝐆`-side opening `P_L` plus an `r`-scaled `𝐇`-side opening `P_R`;
* the mask slot `X^{c+2}` of `f_L` carries the **binding offset** `z^{q+1}·𝟙`. The slot has no
  partner at the target degree `c+1`, so `tcoeff'_eq` applies *unchanged* (its mask-slot
  argument is generic) — the offset only shows up in `eq2`, where it cancels against the
  verifier's public `⟨z^{q+1}·𝟙, 𝐆⟩` term.

The spec in `Sigma.Protocols.GBPImproved.Arithmetization` is not modified; everything here is
additive.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP

open OracleComp OracleSpec
open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- Pulling a scalar out of the *generator* vector of a multi-scalar multiplication:
`⟨v, c • 𝐠⟩ = c · ⟨v, 𝐠⟩` (the binding-challenge recombination of the `𝐇`-side). -/
lemma msm_smul_gen {ι : Type*} [Fintype ι] (c : F) (v : ι → F) (g : ι → G) :
    msm v (fun i => c • g i) = c • msm v g := by
  simp only [msm, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

/-! ## The key coefficient identity (no `aux`) -/

omit [AddCommGroup G] [Module F G] in
/-- The target-coefficient identity at the improved target degree `c+1`:

  `tcoeff(c+1) = δ − w_c − ⟨w_V, v⟩`,

where `tcoeff(c+1) = Σ_{p+ℓ=c+1} ⟨f_L,p, f_R,ℓ⟩`. Expanding `f_L`, `f_R` (each a sparse sum of
indicator vectors, with **no `𝐲∘aux` term**), only the `(p,ℓ)` pairs with `p+ℓ = c+1` survive —
`(0,c+1)`, `(1,c)`, and `(j+2, c−j−1)` for each vector commitment `j` — contributing
`⟨a_L+w_R∘y⁻¹, y∘a_R+w_L⟩ + ⟨a_O, w_O−y⟩ + Σ_j ⟨a_C⁽ʲ⁾, w_C⁽ʲ⁾⟩`; the Hadamard constraint `hR2`
(`a_L∘a_R = a_O`) and the R1CS row `hR1` then reduce this to `δ − w_c − ⟨w_V, v⟩`. The mask
slots (`sL` at `X^{c+2}` of `f_L` — in the protocol instantiated as `s_L + z^{q+1}·𝟙`, the mask
plus the binding offset — and the `X^{c+2}` slot of `f_R`) have no partner at the target degree
and drop out, so the lemma is generic in them. -/
private lemma tcoeff'_eq {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    (yu : Fˣ) (z : F) (sL sR : Fin n → F)
    (hR1 : s.WL *ᵥ w.aL + s.WR *ᵥ w.aR + s.WO *ᵥ w.aO + (∑ i, s.WC i *ᵥ w.aC i)
        + s.WV *ᵥ w.v + s.cc = 0)
    (hR2 : hadamard w.aL w.aR - w.aO = 0) :
    (∑ p : Fin (c + 3), ∑ ℓ : Fin (c + 3),
        if (p : ℕ) + (ℓ : ℕ) = c + 1 then
          ip ((((if (p : ℕ) = 0 then
                    fun i => w.aL i + (z • powers z q ᵥ* s.WR) i * vinv (powers (↑yu) n) i
                  else 0) +
                  if (p : ℕ) = 1 then w.aO else 0) +
                  ∑ j : Fin c, if (p : ℕ) = (j : ℕ) + 2 then w.aC j else 0) +
                if (p : ℕ) = c + 2 then sL else 0)
            (((((∑ j : Fin c, if (ℓ : ℕ) = c - (j : ℕ) - 1 then
                      z • powers z q ᵥ* s.WC j else 0) +
                    if (ℓ : ℕ) = c then
                      fun i => (z • powers z q ᵥ* s.WO) i - powers (↑yu) n i else 0) +
                  if (ℓ : ℕ) = c + 1 then
                    fun i => powers (↑yu) n i * w.aR i + (z • powers z q ᵥ* s.WL) i else 0) +
                if (ℓ : ℕ) = c + 2 then fun i => powers (↑yu) n i * sR i else 0))
        else 0)
      = ip (hadamard (vinv (powers (↑yu) n)) (z • powers z q ᵥ* s.WR))
            (z • powers z q ᵥ* s.WL)
          - z * ip (powers z q) s.cc
          - ip (z • powers z q ᵥ* s.WV) w.v := by
  -- Expand `ip (f_L p) (f_R ℓ)` over `f_L`; the guard `p+ℓ = c+1` pins `ℓ`; collapse each of the
  -- `f_L`-terms (`double_sum_collapse`/`double_sum_zero`/`family_collapse`), evaluate `f_R` at the
  -- pinned indices (impossible powers vanish by `omega`, the matching `w_C` survives), then close
  -- with the field algebra (`hR2`, `hR1`).
  simp only [ip_add_left, ip_sum_left, ip_ite_left, ite_zero_add, ite_zero_sum,
    ite_ite_zero, Finset.sum_add_distrib]
  rw [double_sum_collapse 0 (c + 1) (by omega) (by omega) (by omega),
    double_sum_collapse 1 (c + 1) (by omega) (by omega) (by omega),
    double_sum_zero (c + 2) (c + 1) (by omega),
    family_collapse (fun j => (j : ℕ) + 2) (c + 1)
      (fun j => by have := j.isLt; dsimp only; omega)
      (fun j => by have := j.isLt; dsimp only; omega)
      (fun j => by have := j.isLt; dsimp only; omega)]
  -- the pinned `ℓ`-indices: `c+1−0 = c+1`, `c+1−1 = c`, `c+1−(j+2) = c−j−1`
  have hidx0 : c + 1 - 0 = c + 1 := by omega
  have hidx1 : c + 1 - 1 = c := by omega
  have hidxj : ∀ j : Fin c, c + 1 - ((j : ℕ) + 2) = c - (j : ℕ) - 1 := fun j => by
    have := j.isLt; omega
  simp only [hidx0, hidx1, hidxj, ip_add_right, ip_sum_right, ip_ite_right]
  -- evaluate `f_R` at each pinned index; only the matching term survives
  have f1 : ∀ j : Fin c, (c + 1 = c - (j : ℕ) - 1) = False := fun j => eq_false (by omega)
  have f2 : (c + 1 = c) = False := eq_false (by omega)
  have f3 : (c + 1 = c + 2) = False := eq_false (by omega)
  have f4 : ∀ j : Fin c, (c = c - (j : ℕ) - 1) = False := fun j => eq_false (by omega)
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
  -- final field algebra: the three surviving contributions, using `hR2` (Hadamard) and `hR1` (R1CS)
  have hvyinv := powers_mul_vinv yu n
  have hR2' : ∀ i, w.aL i * w.aR i = w.aO i := fun i => by
    have h := congrFun hR2 i
    simp only [hadamard, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
    exact h
  have hI : ip (fun i => w.aL i + (z • powers z q ᵥ* s.WR) i * vinv (powers (↑yu) n) i)
          (fun i => powers (↑yu) n i * w.aR i + (z • powers z q ᵥ* s.WL) i)
        + ip w.aO (fun i => (z • powers z q ᵥ* s.WO) i - powers (↑yu) n i)
      = ip (hadamard (vinv (powers (↑yu) n)) (z • powers z q ᵥ* s.WR))
            (z • powers z q ᵥ* s.WL)
        + ip w.aL (z • powers z q ᵥ* s.WL)
        + ip w.aR (z • powers z q ᵥ* s.WR)
        + ip w.aO (z • powers z q ᵥ* s.WO) := by
    simp only [ip, hadamard]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (powers (↑yu) n i) * (hR2' i)
      + ((z • powers z q ᵥ* s.WR) i * w.aR i) * (hvyinv i)
  have hWV : ip (z • powers z q ᵥ* s.WV) w.v
      = z * ip (powers z q) (s.WV *ᵥ w.v) := by
    rw [ip_comm, ip_smul_vecMul]
  have hmat : s.WL *ᵥ w.aL + s.WR *ᵥ w.aR + s.WO *ᵥ w.aO + (∑ x, s.WC x *ᵥ w.aC x)
      = -(s.WV *ᵥ w.v) - s.cc := by
    linear_combination hR1
  have hII' : ip w.aL (z • powers z q ᵥ* s.WL)
        + ip w.aR (z • powers z q ᵥ* s.WR)
        + ip w.aO (z • powers z q ᵥ* s.WO)
        + ∑ x, ip (w.aC x) (z • powers z q ᵥ* s.WC x)
      = -(z * ip (powers z q) s.cc) - ip (z • powers z q ᵥ* s.WV) w.v := by
    simp only [ip_smul_vecMul, hWV]
    rw [← Finset.mul_sum, ← ip_sum_right, ← mul_add, ← mul_add, ← mul_add,
      ← ip_add_right, ← ip_add_right, ← ip_add_right, hmat]
    simp only [ip_eq_dotProduct, dotProduct_sub, dotProduct_neg]
    ring
  linear_combination hI + hII'

/-! ## Completeness -/

variable [DecidableEq F] [DecidableEq G] [SampleableType F] [SampleableType Fˣ]

/-- **Perfect completeness of the improved arithmetization.** Every (conversation, witness)
pair the honest prover `arithHonest'` produces on a witness satisfying the improved relation
`rel` is accepting. The `eq1` (t-polynomial) check is identical in shape to the base protocol
(the binding offset's slot has no partner at the target degree); the `eq2` (commitment) check splits
into the `𝐆`-side opening `P_L` — including the public offset, which appears identically on
both sides — and the `r`-scaled `𝐇`-side opening `P_R`, and holds for every binding challenge
`r`. -/
theorem arithRed'_complete {n q m c : ℕ} :
    (arithRed' (F := F) (G := G) n q m c).Complete arithHonest' := by
  intro s w hrel p hp
  simp only [arithRed', relGBP', rel, Bool.and_eq_true, decide_eq_true_eq] at hrel
  obtain ⟨⟨⟨hR1, hR2⟩, hR3⟩, hR4⟩ := hrel
  simp only [arithHonest', support_bind, support_uniformSample, support_pure, Set.mem_iUnion,
    Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hp
  obtain ⟨αL, αR, β, ρL, ρR, sL, sR, yu, z, τ, xu, ru, rfl⟩ := hp
  refine ⟨_, rfl, ?_⟩
  simp only [arithAssemble', arithRed', relArith', arithOut', Bool.and_eq_true, decide_eq_true_eq]
  set x : F := (↑xu : F) with hx_def
  refine ⟨?_, ?_⟩
  · -- eq1: the t-polynomial identity (independent of the binding challenge `r`).
    -- `t̂ = ⟨f_L(x),f_R(x)⟩ = Σ_d xᵈ·tcoeff d` (Cauchy product); splitting off the `d = c+1` term and
    -- matching `g`/`h` coefficients reduces to `tcoeff(c+1) = δ − w_c − ⟨w_V, v⟩` (`tcoeff'_eq`,
    -- applied with the offset-shifted mask `s_L + z^{q+1}·𝟙` in the partnerless slot).
    have hmsmV : msm (z • powers z q ᵥ* s.WV) s.V
        = ip (z • powers z q ᵥ* s.WV) w.v • s.g
          + ip (z • powers z q ᵥ* s.WV) w.γ • s.h := by
      simp only [msm, hR4, smul_add, smul_smul]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
      rfl
    rw [hmsmV, ip_xpoly_conv (M := 2 * c + 5) x _ _ (fun p ℓ => by omega)]
    rw [sum_ite_zero_eq _ (c + 1) (show c + 1 < 2 * c + 5 by omega)]
    rw [sum_ite_zero_eq _ (c + 1) (show c + 1 < 2 * c + 5 by omega)]
    simp only [smul_sub, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hK := tcoeff'_eq s w yu z (fun i => sL i + z ^ (q + 1)) sR hR1 hR2
    rw [show (∑ i : Fin (2 * c + 5), τ i * x ^ (i : ℕ))
          = ∑ i : Fin (2 * c + 5), x ^ (i : ℕ) * τ i from
        Finset.sum_congr rfl fun i _ => mul_comm _ _]
    rw [hK]
    module
  · -- eq2: commitment opening, split `𝐆`-side / `𝐇`-side and recombined by `r`. The binding
    -- offset enters the `𝐆`-side identically on both sides (the verifier's public
    -- `⟨z^{q+1}·𝟙, 𝐆⟩` term vs. the `s_L + z^{q+1}·𝟙` coefficient of the sent `f_L(x)`).
    simp only [hR3, msm_smul_gen]
    rw [msm_lincomb, msm_lincomb]
    simp only [msm_add_left, msm_sum_left, msm_ite, smul_add, Finset.sum_add_distrib]
    have hyy := powers_mul_vinv (F := F) yu n
    have hcancel : ∀ v : Fin n → F,
        msm (fun i => powers (↑yu : F) n i * v i) (vinv (powers (↑yu : F) n) ⊙ s.hs) = msm v s.hs :=
      fun v => msm_vy_yinv_cancel _ _ v s.hs hyy
    have hb0 : (0 : ℕ) < c + 3 := by omega
    have hb1 : (1 : ℕ) < c + 3 := by omega
    have hbM : c < c + 3 := by omega
    have hbM1 : c + 1 < c + 3 := by omega
    have hbM2 : c + 2 < c + 3 := by omega
    have hbj1 : ∀ j : Fin c, (j : ℕ) + 2 < c + 3 := fun j => by have := j.isLt; omega
    have hbj2 : ∀ j : Fin c, c - (j : ℕ) - 1 < c + 3 := fun j => by omega
    rw [sum_pow_smul_ite x 0 hb0,
      sum_pow_smul_ite x 1 hb1,
      sum_pow_smul_sum_ite x (fun j => (j : ℕ) + 2) hbj1,
      sum_pow_smul_ite x (c + 2) hbM2,
      sum_pow_smul_sum_ite x (fun j => c - (j : ℕ) - 1) hbj2,
      sum_pow_smul_ite x c hbM,
      sum_pow_smul_ite x (c + 1) hbM1,
      sum_pow_smul_ite x (c + 2) hbM2]
    have hoffsplit : msm (fun i => sL i + z ^ (q + 1)) s.gs
        = msm sL s.gs + msm (fun _ => z ^ (q + 1)) s.gs :=
      msm_add' sL (fun _ => z ^ (q + 1)) s.gs
    simp only [hoffsplit, msm_add', msm_sub', hcancel, msm_sub_left, pow_zero, one_smul]
    unfold hadamard
    rw [show (fun i => (z • powers z q ᵥ* s.WR) i * vinv (powers (↑yu) n) i)
          = (fun i => vinv (powers (↑yu) n) i * (z • powers z q ᵥ* s.WR) i) from
        funext fun i => mul_comm _ _]
    simp only [add_smul, Finset.sum_smul, smul_smul]
    rw [show (∑ j : Fin c, (x ^ ((j : ℕ) + 2) * w.γC j) • s.h)
          = ∑ j : Fin c, (w.γC j * x ^ ((j : ℕ) + 2)) • s.h from
        Finset.sum_congr rfl (fun j _ => by rw [mul_comm])]
    module

end Sigma.Protocols.GBPImproved
