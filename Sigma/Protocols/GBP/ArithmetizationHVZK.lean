/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBP.Arithmetization
import Sigma.Protocols.GBP.ArithmetizationComplete
import Sigma.Utils.Algebra
import Sigma.Utils.ProbDist

/-!
# Perfect honest-verifier zero-knowledge of the Generalized Bulletproofs arithmetization

The arithmetization `Sigma.Protocols.GBP.arithRed` is perfectly HVZK: a witness-free
simulator reproduces the honest prover's joint distribution over the conversation and the
output opening `(τ_x, μ, f_L(x), f_R(x))`.

The simulator samples the openings and the "free" commitments uniformly and **solves the two
verifier equations** (`Sigma.Protocols.GBP.arithOut`) in closed form for the remaining
messages: `A_I` is pinned by the commitment equation (its `x^{c+1}` coefficient is
invertible), and one coefficient commitment `T_{i₀}` is pinned by the `t`-polynomial equation
(its `x^{tIdx i₀}` coefficient is invertible). Under the standard *perfectly hiding* base
assumption — `α • h` is uniform over `G`, i.e. `· • h` is bijective (a prime-order group) —
every honest commitment is uniform, so this matches the honest distribution exactly.
-/

namespace Sigma.Protocols.GBP

open OracleComp OracleSpec
open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [Fintype F] [Fintype G]
  [SampleableType F] [SampleableType Fˣ] [SampleableType G]

/-- The pivot coefficient-commitment slot the simulator solves from the `t`-polynomial
equation. Slot `0` always exists (`3c+5 > 0`). -/
def simPivot (c : ℕ) : Fin (3 * c + 5) := ⟨0, by omega⟩

/-- The fields of the honest assembly `arithAssemble` that the HVZK proof forwards to the
simulator. Giving them names lets the proof match on the assembly once and refer to the
fields by name, rather than indexing the raw `Conversation × Wit` tuple positionally. -/
structure ArithView (F G : Type) (n c : ℕ) where
  AO : G
  Scom : G
  T : Fin (3 * c + 5) → G
  τx : F
  μ : F
  fLx : Fin n → F
  fRx : Fin n → F

/-- Project the forwarded fields out of the honest assembly, matching the tuple once. -/
def arithView {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    (α β ρ : F) (sL sR : Fin n → F) (yu zu : Fˣ) (τ : Fin (3 * c + 5) → F) (xu : Fˣ) :
    ArithView F G n c :=
  let ⟨⟨⟨_, AO, Scom⟩, _, _, T, _, _⟩, τx, μ, fLx, fRx⟩ :=
    arithAssemble s w α β ρ sL sR yu zu τ xu
  ⟨AO, Scom, T, τx, μ, fLx, fRx⟩

omit [Fintype F] [Fintype G] [SampleableType F] [SampleableType Fˣ] [SampleableType G] in
/-- The honest `f_L(x)` opening determines the mask `s_L`: it is the leading (degree `n'+1`)
coefficient, whose weight `x^{n'+1}` is a unit. Used for injectivity of the HVZK bijection. -/
lemma sL_inj_of_fLx {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    {α β ρ : F} {sL sR : Fin n → F} {yu zu : Fˣ} {τ : Fin (3 * c + 5) → F} {xu : Fˣ}
    {α' β' ρ' : F} {sL' sR' : Fin n → F} {τ' : Fin (3 * c + 5) → F}
    (h : (arithView s w α β ρ sL sR yu zu τ xu).fLx
       = (arithView s w α' β' ρ' sL' sR' yu zu τ' xu).fLx) : sL = sL' := by
  funext i
  have hi := congrFun h i
  simp only [arithView, arithAssemble] at hi
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single_of_mem (⟨nPrime c + 1, by simp only [nPrime]; omega⟩ : Fin (nPrime c + 2))
      (Finset.mem_univ _)
      (fun p _ hp => by
        have hne : (p : ℕ) ≠ nPrime c + 1 := fun hc => hp (Fin.ext (by simpa using hc))
        simp only [if_neg hne, Pi.add_apply, Pi.zero_apply, add_zero, sub_self])] at hi
  simp only [Fin.val_mk,
    if_neg (show ¬(nPrime c + 1 = c + 1) by simp only [nPrime]; omega),
    if_neg (show ¬(nPrime c + 1 = nPrime c) by omega),
    Finset.sum_eq_zero (fun (k : Fin c) (_ : k ∈ Finset.univ) => if_neg
      (show ¬(nPrime c + 1 = nPrime c - (k.val + 1)) by have := k.isLt; simp only [nPrime]; omega)),
    if_pos (rfl : nPrime c + 1 = nPrime c + 1),
    Pi.add_apply, Pi.zero_apply, zero_add, add_zero] at hi
  rw [← mul_sub] at hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ (Units.ne_zero xu)))

omit [Fintype F] [Fintype G] [SampleableType F] [SampleableType Fˣ] [SampleableType G] in
/-- The honest `f_R(x)` opening determines the mask `s_R`: its leading (degree `n'+1`)
coefficient is `x^{n'+1}·(y⁻¹-free) · (y ⊙ s_R)`, with `x^{n'+1}` and `y^i` units. -/
lemma sR_inj_of_fRx {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    {α β ρ : F} {sL sR : Fin n → F} {yu zu : Fˣ} {τ : Fin (3 * c + 5) → F} {xu : Fˣ}
    {α' β' ρ' : F} {sL' sR' : Fin n → F} {τ' : Fin (3 * c + 5) → F}
    (h : (arithView s w α β ρ sL sR yu zu τ xu).fRx
       = (arithView s w α' β' ρ' sL' sR' yu zu τ' xu).fRx) : sR = sR' := by
  funext i
  have hi := congrFun h i
  simp only [arithView, arithAssemble] at hi
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single_of_mem (⟨nPrime c + 1, by simp only [nPrime]; omega⟩ : Fin (nPrime c + 2))
      (Finset.mem_univ _)
      (fun p _ hp => by
        have hne : (p : ℕ) ≠ nPrime c + 1 := fun hc => hp (Fin.ext (by simpa using hc))
        simp only [if_neg hne, Pi.add_apply, Pi.zero_apply, add_zero, sub_self])] at hi
  simp only [Fin.val_mk,
    if_neg (show ¬(nPrime c + 1 = 0) by simp only [nPrime]; omega),
    if_neg (show ¬(nPrime c + 1 = c + 1) by simp only [nPrime]; omega),
    Finset.sum_eq_zero (fun (k : Fin c) (_ : k ∈ Finset.univ) => if_neg
      (show ¬(nPrime c + 1 = k.val + 1) by have := k.isLt; simp only [nPrime]; omega)),
    Finset.sum_eq_zero (fun (k : Fin c) (_ : k ∈ Finset.univ) => if_neg
      (show ¬(nPrime c + 1 = nPrime c - (k.val + 1)) by have := k.isLt; simp only [nPrime]; omega)),
    eq_self_iff_true, if_true,
    Pi.add_apply, Pi.zero_apply, zero_add, add_zero] at hi
  rw [← mul_sub, ← mul_sub] at hi
  have hvy : (powers (↑yu : F) n) i ≠ 0 := by
    simp only [powers]; exact pow_ne_zero _ (Units.ne_zero _)
  have h1 := (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ (Units.ne_zero xu))
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hvy)

/-- **The simulator's deterministic output assembly.** From the sampled challenges, opening
`(τ_x, μ, f_L(x), f_R(x))` and free commitments `(A_O, S, {T_i})`, solve the commitment
equation for `A_I` and the `t`-polynomial equation for the pivot `T_{i₀}`, and package the
conversation and opening. No witness is read. -/
def simAssemble {n q m c : ℕ} (s : Statement F G n q m c)
    (yu zu xu : Fˣ) (fLx fRx : Fin n → F) (τx μ : F) (AO Scom : G)
    (Trest : Fin (3 * c + 5) → G) :
    Conversation (arithRed (F := F) (G := G) n q m c).moves
      × (arithRed (F := F) (G := G) n q m c).Out.Wit :=
  let y : F := ↑yu
  let z : F := ↑zu
  let x : F := ↑xu
  let np := nPrime c
  let vy := powers y n
  let yinv := vinv vy
  let vz := powers z q
  let wL := z • (vz ᵥ* s.WL)
  let wR := z • (vz ᵥ* s.WR)
  let wO := z • (vz ᵥ* s.WO)
  let wC := fun k => z • (vz ᵥ* s.WC k)
  let wV := z • (vz ᵥ* s.WV)
  let wc := z * ip vz s.cc
  let δ := ip (hadamard yinv wR) wL
  let h' := yinv ⊙ s.hs
  let WtL := msm wL h'
  let WtR := msm (hadamard yinv wR) s.gs
  let WtO := msm (wO - vy) h'
  let Wtk := fun k => msm (wC k) h'
  let i₀ := simPivot c
  -- Solve the `t`-polynomial equation for the pivot coefficient commitment.
  let Tsolve : G := (x ^ (tIdx i₀ : ℕ))⁻¹ • (ip fLx fRx • s.g + τx • s.h
      - x ^ np • ((δ - wc) • s.g - msm wV s.V)
      - (∑ i ∈ Finset.univ.erase i₀, x ^ (tIdx i : ℕ) • Trest i))
  let T : Fin (3 * c + 5) → G := Function.update Trest i₀ Tsolve
  -- Solve the commitment equation for `A_I`.
  let AI : G := (x ^ (c + 1))⁻¹ • (msm fLx s.gs + msm fRx h' + μ • s.h
        - WtO - (∑ k : Fin c, x ^ (k.val + 1) • Wtk k)
        - (∑ k : Fin c, x ^ (np - (k.val + 1)) • s.AC k)
        - x ^ np • AO - x ^ (np + 1) • Scom) - WtL - WtR
  (((AI, AO, Scom), yu, zu, T, xu, PUnit.unit), (τx, μ, fLx, fRx))

/-- **The witness-free simulator for the arithmetization.** Sample the challenges, the output
opening `(τ_x, μ, f_L(x), f_R(x))`, and the free commitments `(A_O, S, {T_i})` uniformly, then
assemble via `simAssemble` (solving the two verifier equations for `A_I` and the pivot `T_{i₀}`).
No witness is read. -/
def arithSim {n q m c : ℕ} (s : Statement F G n q m c) :
    ProbComp (Conversation (arithRed (F := F) (G := G) n q m c).moves
      × (arithRed (F := F) (G := G) n q m c).Out.Wit) := do
  let yu ← uniformSample Fˣ
  let zu ← uniformSample Fˣ
  let xu ← uniformSample Fˣ
  let fLx ← uniformSample (Fin n → F)
  let fRx ← uniformSample (Fin n → F)
  let τx ← uniformSample F
  let μ ← uniformSample F
  let AO ← uniformSample G
  let Scom ← uniformSample G
  let Trest ← uniformSample (Fin (3 * c + 5) → G)
  pure (simAssemble s yu zu xu fLx fRx τx μ AO Scom Trest)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4096 in
/-- **Perfect HVZK of the arithmetization**, assuming each statement's blinding base `h` is
perfectly hiding (`· • h` bijective, e.g. a prime-order group). -/
theorem arithRed_hvzk {n q m c : ℕ}
    (hHide : ∀ x : (arithRed (F := F) (G := G) n q m c).In.Stmt,
      Function.Bijective (· • x.h : F → G)) :
    (arithRed (F := F) (G := G) n q m c).PerfectHVZK arithRedHonest arithSim := by
  intro s w hrel
  haveI : Inhabited F := ⟨0⟩
  haveI : Inhabited G := ⟨0⟩
  haveI : Inhabited Fˣ := ⟨1⟩
  haveI : Inhabited (Fin n → F) := ⟨0⟩
  haveI : Inhabited (Fin (3 * c + 5) → F) := ⟨0⟩
  haveI : Inhabited (Fin (3 * c + 5) → G) := ⟨0⟩
  -- Prepend a dummy unused `G` sample to the prover so both sides have equal-dimension
  -- sample spaces (the simulator's pivot slot `T_{i₀}` is overwritten, hence unused).
  rw [show 𝒟[arithRedHonest (G := G) s w]
        = 𝒟[($ᵗ G) >>= fun _ => arithRedHonest (G := G) s w] from
      (evalDist_bind_const' _ _ (probFailure_uniformSample G)).symm]
  -- Fold both prover and simulator into a single uniform sample over the product of all
  -- their randomness, the form `evalDist_uniform_pure_cross` consumes.
  simp only [arithRedHonest, arithSim, evalDist_bind_uniform_pair]
  -- The bijection `f` sends the honest randomness `(dummy,α,β,ρ,sL,sR,yu,zu,τ,xu)` to the
  -- simulator randomness by *projecting* the honest assembly `r := arithAssemble …`:
  -- challenges pass through, `(fLx,fRx,τx,μ,AO,Scom)` and the non-pivot `T` come straight from
  -- `r`, and the overwritten pivot slot carries the dummy `G` sample (keeping `f` bijective).
  refine evalDist_uniform_pure_cross
    (fun p : (((((((((G × F) × F) × F) × (Fin n → F)) × (Fin n → F)) × Fˣ) × Fˣ)
                × (Fin (3 * c + 5) → F)) × Fˣ) =>
      let ⟨⟨⟨⟨⟨⟨⟨⟨⟨d, α⟩, β⟩, ρ⟩, sL⟩, sR⟩, yu⟩, zu⟩, τ⟩, xu⟩ := p
      let v := arithView s w α β ρ sL sR yu zu τ xu
      (((((((((yu, zu), xu), v.fLx), v.fRx), v.τx), v.μ), v.AO), v.Scom),
        Function.update v.T (simPivot c) d))
    ?_ ?_
  · -- bijectivity of `f`: injective + equal cardinality (|F| = |G| via the hiding base)
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · -- injective: the simulator coordinates pin down each honest sample
      intro p p' hpp
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨d, α⟩, β⟩, ρ⟩, sL⟩, sR⟩, yu⟩, zu⟩, τ⟩, xu⟩ := p
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨d', α'⟩, β'⟩, ρ'⟩, sL'⟩, sR'⟩, yu'⟩, zu'⟩, τ'⟩, xu'⟩ := p'
      simp only [Prod.mk.injEq] at hpp
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hyu, hzu⟩, hxu⟩, hfLx⟩, hfRx⟩, hτx⟩, hμ⟩, hAO⟩, hScom⟩, hTrest⟩ := hpp
      subst hyu; subst hzu; subst hxu
      obtain rfl : sL = sL' := sL_inj_of_fLx s w hfLx
      obtain rfl : sR = sR' := sR_inj_of_fRx s w hfRx
      have hbij := (hHide s).injective
      obtain rfl : β = β' := by
        simp only [arithView, arithAssemble] at hAO; exact hbij (add_left_cancel hAO)
      obtain rfl : ρ = ρ' := by
        simp only [arithView, arithAssemble] at hScom; exact hbij (add_left_cancel hScom)
      obtain rfl : α = α' := by
        simp only [arithView, arithAssemble] at hμ
        exact mul_right_cancel₀ (pow_ne_zero (c + 1) (Units.ne_zero xu)) (by linear_combination hμ)
      obtain rfl : d = d' := by
        have h := congrFun hTrest (simPivot c)
        rwa [Function.update_self, Function.update_self] at h
      obtain rfl : τ = τ' := by
        have hτne : ∀ j, j ≠ simPivot c → τ j = τ' j := fun j hj => by
          have h := congrFun hTrest j
          rw [Function.update_of_ne hj, Function.update_of_ne hj] at h
          simp only [arithView, arithAssemble] at h
          exact hbij (add_left_cancel h)
        funext j
        by_cases hj : j = simPivot c
        · subst hj
          simp only [arithView, arithAssemble] at hτx
          have hs : ∑ i, (τ i - τ' i) * (↑xu : F) ^ (tIdx i : ℕ) = 0 := by
            simp only [sub_mul, Finset.sum_sub_distrib]; linear_combination hτx
          rw [Finset.sum_eq_single_of_mem (simPivot c) (Finset.mem_univ _)
            (fun k _ hk => by rw [hτne k hk, sub_self, zero_mul])] at hs
          exact sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right (pow_ne_zero _ (Units.ne_zero xu)))
        · exact hτne j hj
      rfl
    · have hFG : Fintype.card F = Fintype.card G :=
        Fintype.card_eq.mpr ⟨Equiv.ofBijective _ (hHide s)⟩
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      rw [hFG]; ring
  · intro p
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, α⟩, β⟩, ρ⟩, sL⟩, sR⟩, yu⟩, zu⟩, τ⟩, xu⟩ := p
    have hmem : (arithAssemble s w α β ρ sL sR yu zu τ xu)
        ∈ support (arithRedHonest s w) := by
      simp only [arithRedHonest, support_bind, support_uniformSample, support_pure,
        Set.mem_iUnion, Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and]
      exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    obtain ⟨st, hst, hacc⟩ := arithRed_complete s w hrel _ hmem
    simp only [arithRed] at hst
    obtain rfl : arithOut s _ = st := Option.some.inj hst
    simp only [arithRed, relArith, Bool.and_eq_true, decide_eq_true_eq] at hacc
    obtain ⟨heq1, heq2⟩ := hacc
    simp only [simAssemble]
    refine Prod.ext (Prod.ext (Prod.ext ?_ (Prod.ext rfl rfl))
      (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))))) rfl
    · -- A_I: solved from the commitment equation `heq2`
      simp only [arithOut, arithView, arithAssemble] at heq2 ⊢
      have hx : ((↑xu : F)) ^ (c + 1) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, eq_inv_smul_iff₀ hx]
      linear_combination (norm := module) heq2
    · -- pivot T: solved from the t-polynomial equation `heq1`
      simp only [arithOut] at heq1
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (simPivot c))] at heq1
      simp only [arithView, arithAssemble] at heq1 ⊢
      rw [Function.update_idem, eq_comm, Function.update_eq_self_iff,
        inv_smul_eq_iff₀ (pow_ne_zero _ (Units.ne_zero xu))]
      -- pin the rewrite to the pivot-erased sum (the unfolded `τ_x` exposes another sum)
      rw [Finset.sum_congr (rfl : Finset.univ.erase (simPivot c) = _)
        fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
      linear_combination (norm := module) heq1

end Sigma.Protocols.GBP
