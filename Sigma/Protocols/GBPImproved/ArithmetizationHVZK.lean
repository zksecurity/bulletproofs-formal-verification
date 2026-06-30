/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBPImproved.Arithmetization
import Sigma.Protocols.GBPImproved.ArithmetizationComplete
import Sigma.Utils.Algebra
import Sigma.Utils.ProbDist

/-!
# Perfect honest-verifier zero-knowledge of the improved Generalized Bulletproofs arithmetization

The improved arithmetization `Sigma.Protocols.GBPImproved.arithRed'` is perfectly HVZK: a
witness-free simulator reproduces the honest prover's joint distribution over the conversation
and the output opening `(τ_x, μ, f_L(x), f_R(x))`.

As in the base protocol, the simulator samples the openings and the "free" commitments
uniformly and **solves the two verifier equations** (`Sigma.Protocols.GBPImproved.arithOut'`)
for the remaining messages. Here the split commitment `A_L` enters the recombined commitment
`P = P_L + r·P_R` with coefficient `1`, and the pivot coefficient commitment `T₀` enters the
`t`-target with coefficient `x⁰ = 1`; both solves are unconditional (no division by a possibly
zero `x`). Under the perfectly hiding base assumption (`· • h` bijective) every honest
commitment is uniform, so the simulator matches the honest distribution exactly.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open OracleComp OracleSpec
open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [Fintype F] [Fintype G]
  [SampleableType F] [SampleableType Fˣ] [SampleableType G]

/-- The pivot coefficient-commitment slot the simulator solves from the `t`-polynomial
equation. Slot `0` always exists and is distinct from the special slot `c+1`. -/
def simPivot' (c : ℕ) : Fin (2 * c + 5) := ⟨0, by omega⟩

/-- The fields of the honest assembly `arithAssemble'` that the HVZK proof forwards to the
simulator. Giving them names lets the proof match on the assembly once and refer to the
fields by name, rather than indexing the raw `Conversation × Wit` tuple positionally. -/
structure ArithView' (F G : Type) (n c : ℕ) where
  AR : G
  AO : G
  SL : G
  SR : G
  T : Fin (2 * c + 5) → G
  τx : F
  μ : F
  fLx : Fin n → F
  fRx : Fin n → F

/-- Project the forwarded fields out of the honest assembly, matching the tuple once. -/
def arithView' {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    (αL αR β ρL ρR : F) (sL sR : Fin n → F) (yu : Fˣ) (z : F) (τ : Fin (2 * c + 5) → F)
    (xu ru : Fˣ) : ArithView' F G n c :=
  let ⟨⟨⟨_, AR, AO, SL, SR⟩, _, _, T, _, _, _⟩, τx, μ, fLx, fRx⟩ :=
    arithAssemble' s w αL αR β ρL ρR sL sR yu z τ xu ru
  ⟨AR, AO, SL, SR, T, τx, μ, fLx, fRx⟩

omit [Fintype F] [Fintype G] [SampleableType F] [SampleableType Fˣ] [SampleableType G] in
/-- The honest `f_L(x)` opening determines the mask `s_L` (leading degree-`c+2` coefficient,
weighted by the unit `x^{c+2}`; the binding offset `z^{q+1}` cancels). -/
lemma sL'_inj_of_fLx' {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    {αL αR β ρL ρR : F} {sL sR : Fin n → F} {yu : Fˣ} {z : F} {τ : Fin (2 * c + 5) → F}
    {xu ru : Fˣ} {αL' αR' β' ρL' ρR' : F} {sL' sR' : Fin n → F} {τ' : Fin (2 * c + 5) → F}
    (h : (arithView' s w αL αR β ρL ρR sL sR yu z τ xu ru).fLx
       = (arithView' s w αL' αR' β' ρL' ρR' sL' sR' yu z τ' xu ru).fLx) : sL = sL' := by
  funext i
  have hi := congrFun h i
  simp only [arithView', arithAssemble'] at hi
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single_of_mem (⟨c + 2, by omega⟩ : Fin (c + 3)) (Finset.mem_univ _)
      (fun p _ hp => by
        have hne : (p : ℕ) ≠ c + 2 := fun hc => hp (Fin.ext (by simpa using hc))
        simp only [if_neg hne, Pi.add_apply, Pi.zero_apply, add_zero, sub_self])] at hi
  simp only [if_neg (show ¬(c + 2 = 0) by omega), if_neg (show ¬(c + 2 = 1) by omega),
    Finset.sum_eq_zero (fun (j : Fin c) (_ : j ∈ Finset.univ) => if_neg
      (show ¬(c + 2 = j.val + 2) by have := j.isLt; omega)),
    if_true, Pi.add_apply, Pi.zero_apply, zero_add, add_zero] at hi
  rw [← mul_sub] at hi
  linear_combination (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ (Units.ne_zero xu))

omit [Fintype F] [Fintype G] [SampleableType F] [SampleableType Fˣ] [SampleableType G] in
/-- The honest `f_R(x)` opening determines the mask `s_R` (leading degree-`c+2` coefficient,
weighted by the units `x^{c+2}` and `y^i`). -/
lemma sR'_inj_of_fRx' {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    {αL αR β ρL ρR : F} {sL sR : Fin n → F} {yu : Fˣ} {z : F} {τ : Fin (2 * c + 5) → F}
    {xu ru : Fˣ} {αL' αR' β' ρL' ρR' : F} {sL' sR' : Fin n → F} {τ' : Fin (2 * c + 5) → F}
    (h : (arithView' s w αL αR β ρL ρR sL sR yu z τ xu ru).fRx
       = (arithView' s w αL' αR' β' ρL' ρR' sL' sR' yu z τ' xu ru).fRx) : sR = sR' := by
  funext i
  have hi := congrFun h i
  simp only [arithView', arithAssemble'] at hi
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single_of_mem (⟨c + 2, by omega⟩ : Fin (c + 3)) (Finset.mem_univ _)
      (fun p _ hp => by
        have hne : (p : ℕ) ≠ c + 2 := fun hc => hp (Fin.ext (by simpa using hc))
        simp only [if_neg hne, Pi.add_apply, Pi.zero_apply, add_zero, sub_self])] at hi
  simp only [
    Finset.sum_eq_zero (fun (j : Fin c) (_ : j ∈ Finset.univ) => if_neg
      (show ¬(c + 2 = c - j.val - 1) by omega)),
    if_neg (show ¬(c + 2 = c) by omega), if_neg (show ¬(c + 2 = c + 1) by omega),
    if_true, Pi.add_apply, Pi.zero_apply, zero_add, add_zero] at hi
  rw [← mul_sub, ← mul_sub] at hi
  have hvy : (powers (↑yu : F) n) i ≠ 0 := by
    simp only [powers]; exact pow_ne_zero _ (Units.ne_zero _)
  have h1 := (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ (Units.ne_zero xu))
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hvy)

/-- **The simulator's deterministic output assembly.** From the sampled challenges, opening
`(τ_x, μ, f_L(x), f_R(x))` and free commitments `(A_R, A_O, S_L, S_R, {T_i})`, solve the
commitment equation for `A_L` and the `t`-polynomial equation for the pivot `T₀`, and package
the conversation and opening. No witness is read. -/
def simAssemble' {n q m c : ℕ} (s : Statement F G n q m c)
    (yu : Fˣ) (z : F) (xu ru : Fˣ) (fLx fRx : Fin n → F) (τx μ : F)
    (AR AO SL SR : G) (Trest : Fin (2 * c + 5) → G) :
    Conversation (arithRed' (F := F) (G := G) n q m c).moves
      × (arithRed' (F := F) (G := G) n q m c).Out.Wit :=
  let x : F := ↑xu
  let y : F := ↑yu
  let r : F := ↑ru
  let vy := powers y n
  let yinv := vinv vy
  let vz := powers z q
  let wL := z • (vz ᵥ* s.WL)
  let wR := z • (vz ᵥ* s.WR)
  let wO := z • (vz ᵥ* s.WO)
  let wC := fun j => z • (vz ᵥ* s.WC j)
  let wV := z • (vz ᵥ* s.WV)
  let wc := z * ip vz s.cc
  let δ := ip (hadamard yinv wR) wL
  let h' := yinv ⊙ s.hs
  let h'' : Fin n → G := fun i => r • h' i
  let offL : Fin n → F := fun _ => z ^ (q + 1)
  let WtL := msm wL h'
  let WtR := msm (hadamard yinv wR) s.gs
  let WtO := msm (wO - vy) h'
  let Wtk := fun j => msm (wC j) h'
  let i₀ := simPivot' c
  let PR : G := (∑ j : Fin c, x ^ (c - j.val - 1) • Wtk j) + x ^ c • WtO
              + x ^ (c + 1) • (AR + WtL) + x ^ (c + 2) • SR
  -- Solve the `t`-polynomial equation for the pivot coefficient commitment (coefficient `x⁰=1`).
  let Tsolve : G := ip fLx fRx • s.g + τx • s.h
      - x ^ (c + 1) • ((δ - wc) • s.g - msm wV s.V)
      - (∑ i ∈ Finset.univ.erase i₀, if i.val = c + 1 then (0 : G) else x ^ i.val • Trest i)
  let T : Fin (2 * c + 5) → G := Function.update Trest i₀ Tsolve
  -- Solve the commitment equation for `A_L` (coefficient `1`).
  let AL : G := msm fLx s.gs + msm fRx h'' + μ • s.h - r • PR
      - WtR - x • AO - (∑ j : Fin c, x ^ (j.val + 2) • s.AC j)
      - x ^ (c + 2) • (SL + msm offL s.gs)
  (((AL, AR, AO, SL, SR), yu, z, T, xu, ru, PUnit.unit), (τx, μ, fLx, fRx))

/-- **The witness-free simulator for the improved arithmetization.** Sample the challenges,
opening and free commitments uniformly, then assemble via `simAssemble'` (solving the two
verifier equations for `A_L` and the pivot `T₀`). No witness is read. -/
def arithSim' {n q m c : ℕ} (s : Statement F G n q m c) :
    ProbComp (Conversation (arithRed' (F := F) (G := G) n q m c).moves
      × (arithRed' (F := F) (G := G) n q m c).Out.Wit) := do
  let yu ← uniformSample Fˣ
  let z ← uniformSample F
  let xu ← uniformSample Fˣ
  let ru ← uniformSample Fˣ
  let fLx ← uniformSample (Fin n → F)
  let fRx ← uniformSample (Fin n → F)
  let τx ← uniformSample F
  let μ ← uniformSample F
  let AR ← uniformSample G
  let AO ← uniformSample G
  let SL ← uniformSample G
  let SR ← uniformSample G
  let Trest ← uniformSample (Fin (2 * c + 5) → G)
  pure (simAssemble' s yu z xu ru fLx fRx τx μ AR AO SL SR Trest)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 16384 in
/-- **Perfect HVZK of the improved arithmetization**, assuming each statement's blinding base
`h` is perfectly hiding (`· • h` bijective, e.g. a prime-order group). -/
theorem arithRed'_hvzk {n q m c : ℕ}
    (hHide : ∀ x : (arithRed' (F := F) (G := G) n q m c).In.Stmt,
      Function.Bijective (· • x.h : F → G)) :
    (arithRed' (F := F) (G := G) n q m c).PerfectHVZK arithHonest' arithSim' := by
  intro s w hrel
  haveI : Inhabited F := ⟨0⟩
  haveI : Inhabited G := ⟨0⟩
  haveI : Inhabited Fˣ := ⟨1⟩
  haveI : Inhabited (Fin n → F) := ⟨0⟩
  haveI : Inhabited (Fin (2 * c + 5) → F) := ⟨0⟩
  haveI : Inhabited (Fin (2 * c + 5) → G) := ⟨0⟩
  -- Prepend a dummy unused `G` sample to the prover so both sides have equal-dimension
  -- sample spaces (the simulator's pivot slot `T₀` is overwritten, hence unused).
  rw [show 𝒟[arithHonest' (G := G) s w]
        = 𝒟[($ᵗ G) >>= fun _ => arithHonest' (G := G) s w] from
      (evalDist_bind_const' _ _ (probFailure_uniformSample G)).symm]
  -- Fold both prover and simulator into a single uniform sample over the product of all
  -- their randomness, the form `evalDist_uniform_pure_cross` consumes.
  simp only [arithHonest', arithSim', evalDist_bind_uniform_pair]
  -- The bijection `f` sends the honest randomness
  -- `(dummy,αL,αR,β,ρL,ρR,sL,sR,yu,z,τ,xu,ru)` to the simulator randomness by *projecting*
  -- the honest assembly `r := arithAssemble' …`: challenges pass through, the opening
  -- `(fLx,fRx,τx,μ)` and the free commitments `(A_R,A_O,S_L,S_R)` and non-pivot `T` come
  -- straight from `r`, and the overwritten pivot slot carries the dummy `G` sample.
  refine evalDist_uniform_pure_cross
    (fun p : ((((((((((((G × F) × F) × F) × F) × F) × (Fin n → F)) × (Fin n → F)) × Fˣ) × F)
                × (Fin (2 * c + 5) → F)) × Fˣ) × Fˣ) =>
      let ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨d, αL⟩, αR⟩, β⟩, ρL⟩, ρR⟩, sL⟩, sR⟩, yu⟩, z⟩, τ⟩, xu⟩, ru⟩ := p
      let v := arithView' s w αL αR β ρL ρR sL sR yu z τ xu ru
      ((((((((((((yu, z), xu), ru), v.fLx), v.fRx), v.τx), v.μ),
        v.AR), v.AO), v.SL), v.SR),
        Function.update v.T (simPivot' c) d))
    ?_ ?_
  · -- bijectivity of `f`: injective + equal cardinality (|F| = |G| via the hiding base)
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · -- injective: the simulator coordinates pin down each honest sample
      intro p p' hpp
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨d, αL⟩, αR⟩, β⟩, ρL⟩, ρR⟩, sL⟩, sR⟩, yu⟩, z⟩, τ⟩, xu⟩, ru⟩ := p
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨d', αL'⟩, αR'⟩, β'⟩, ρL'⟩, ρR'⟩, sL'⟩, sR'⟩, yu'⟩, z'⟩, τ'⟩, xu'⟩, ru'⟩ := p'
      simp only [Prod.mk.injEq] at hpp
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hyu, hz⟩, hxu⟩, hru⟩, hfLx⟩, hfRx⟩, hτx⟩, hμ⟩, hAR⟩, hAO⟩, hSL⟩, hSR⟩,
        hTrest⟩ := hpp
      subst hyu; subst hz; subst hxu; subst hru
      obtain rfl : sL = sL' := sL'_inj_of_fLx' s w hfLx
      obtain rfl : sR = sR' := sR'_inj_of_fRx' s w hfRx
      have hbij := (hHide s).injective
      obtain rfl : β = β' := by
        simp only [arithView', arithAssemble'] at hAO; exact hbij (add_left_cancel hAO)
      obtain rfl : ρL = ρL' := by
        simp only [arithView', arithAssemble'] at hSL; exact hbij (add_left_cancel hSL)
      obtain rfl : ρR = ρR' := by
        simp only [arithView', arithAssemble'] at hSR; exact hbij (add_left_cancel hSR)
      obtain rfl : αR = αR' := by
        simp only [arithView', arithAssemble'] at hAR; exact hbij (add_left_cancel hAR)
      obtain rfl : αL = αL' := by
        simp only [arithView', arithAssemble'] at hμ; linear_combination hμ
      obtain rfl : d = d' := by
        have h := congrFun hTrest (simPivot' c)
        rwa [Function.update_self, Function.update_self] at h
      obtain rfl : τ = τ' := by
        have hτne : ∀ j, j ≠ simPivot' c → τ j = τ' j := fun j hj => by
          have h := congrFun hTrest j
          rw [Function.update_of_ne hj, Function.update_of_ne hj] at h
          simp only [arithView', arithAssemble'] at h
          exact hbij (add_left_cancel h)
        funext j
        by_cases hj : j = simPivot' c
        · subst hj
          simp only [arithView', arithAssemble'] at hτx
          have hs : ∑ i : Fin (2 * c + 5),
              ((if i.val = c + 1 then (0 : F) else τ i * (↑xu : F) ^ i.val)
                - (if i.val = c + 1 then (0 : F) else τ' i * (↑xu : F) ^ i.val)) = 0 := by
            rw [Finset.sum_sub_distrib]; linear_combination hτx
          rw [Finset.sum_eq_single_of_mem (simPivot' c) (Finset.mem_univ _)
            (fun k _ hk => by
              by_cases hc : k.val = c + 1
              · rw [if_pos hc, if_pos hc, sub_self]
              · rw [if_neg hc, if_neg hc, hτne k hk, sub_self])] at hs
          rw [if_neg (show ¬((simPivot' c).val = c + 1) by simp only [simPivot']; omega)] at hs
          simp only [simPivot', Fin.val_mk, pow_zero, mul_one] at hs
          exact sub_eq_zero.mp hs
        · exact hτne j hj
      rfl
    · have hFG : Fintype.card F = Fintype.card G :=
        Fintype.card_eq.mpr ⟨Equiv.ofBijective _ (hHide s)⟩
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      rw [hFG]; ring
  · intro p
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, αL⟩, αR⟩, β⟩, ρL⟩, ρR⟩, sL⟩, sR⟩, yu⟩, z⟩, τ⟩, xu⟩, ru⟩ := p
    have hmem : (arithAssemble' s w αL αR β ρL ρR sL sR yu z τ xu ru)
        ∈ support (arithHonest' s w) := by
      simp only [arithHonest', support_bind, support_uniformSample, support_pure,
        Set.mem_iUnion, Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and]
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    obtain ⟨st, hst, hacc⟩ := arithRed'_complete s w hrel _ hmem
    simp only [arithRed'] at hst
    obtain rfl : arithOut' s _ = st := Option.some.inj hst
    simp only [arithRed', relArith', Bool.and_eq_true, decide_eq_true_eq] at hacc
    obtain ⟨heq1, heq2⟩ := hacc
    simp only [simAssemble']
    refine Prod.ext (Prod.ext (Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl rfl))))
      (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl rfl)))))) rfl
    · -- A_L: solved from the commitment equation `heq2` (coefficient `1`, no inversion)
      simp only [arithOut', arithView', arithAssemble'] at heq2 ⊢
      linear_combination (norm := module) heq2
    · -- pivot T: solved from the t-polynomial equation `heq1` (coefficient `x⁰ = 1`)
      -- unfold both sides to the raw `T` so the honest field and the simulator's `v.T` agree
      simp only [arithOut', arithView', arithAssemble'] at heq1 ⊢
      rw [Function.update_idem, eq_comm, Function.update_eq_self_iff]
      -- the non-pivot `T` slots of the simulator's `Trest` carry the honest coefficients
      rw [Finset.sum_congr (rfl : Finset.univ.erase (simPivot' c) = _)
        fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
      -- split the `t`-target sum (on the equation's RHS) off the pivot slot `i₀`
      conv at heq1 => rhs; rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (simPivot' c))]
      rw [if_neg (show ¬((simPivot' c).val = c + 1) by simp only [simPivot']; omega)] at heq1
      rw [show ((simPivot' c : Fin (2 * c + 5)) : ℕ) = 0 from rfl] at heq1 ⊢
      rw [pow_zero, one_smul] at heq1
      linear_combination (norm := module) heq1

end Sigma.Protocols.GBPImproved
