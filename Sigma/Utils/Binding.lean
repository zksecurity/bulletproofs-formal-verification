/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Utils.Vec
import Sigma.Utils.ProbDist
import Examples.Pedersen

/-!
# Binding of the generator commitment reduces to discrete log

The Generalized Bulletproofs extractor returns *either* a witness *or* a non-trivial
discrete-log relation among the commitment generators: a non-zero `v` with `⟨v, Γ⟩ = 0`
(`msm v Γ = 0`) (Bulletproofs 2017/1066, Def. 1). This file justifies the second branch — the
**Discrete Log Relation assumption**: **finding such a relation among uniformly random generators
is as hard as discrete log**. The formal result below is the one-way reduction `dlRel_le_dlog`,
with a `1/|F|` slack.

The reduction is the `n`-generator generalization of VCV-io's single-message Pedersen
binding (`pedersenCommit.binding_le_dlog`). Given a discrete-log instance `(g, h = x·g)`, set
every generator `Γᵢ = rᵢ·g + dᵢ·h` for uniform `r, d`. A non-trivial relation
`⟨v, Γ⟩ = (∑ vᵢrᵢ)·g + (∑ vᵢdᵢ)·h = 0` is a Pedersen double-opening of `0`, which yields the
discrete log `x = -(∑ vᵢrᵢ)/(∑ vᵢdᵢ)` whenever `∑ vᵢdᵢ ≠ 0`. The only loss is
`Pr[∑ vᵢdᵢ = 0 ∣ v ≠ 0] = 1/|F|`.

## Main definitions

* `Sigma.IsNontrivialDLRel` — the "break": a non-zero `v` with `msm v Γ = 0`.
* `Sigma.DLRelAdversary` / `dlRelExp` — the relation-finding game.
* `Sigma.relToBinding` — turn a relation finder into a Pedersen binding adversary.

## Main result

* `Sigma.dlRel_le_dlog` —
  `Pr[dlRelExp] ≤ Pr[dlogExp ∘ reduction] + 1/|F|`.
-/

open OracleComp OracleSpec ENNReal DiffieHellman CommitmentScheme

namespace Sigma

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-! ## The break: a non-trivial discrete-log relation -/

/-- A non-trivial discrete-log relation among generators `Γ`: a non-zero coefficient vector
the multi-scalar multiplication sends to `0`. Exhibiting one breaks the binding of any
Pedersen commitment over `Γ`. Reducible so the game below can `decide` it. -/
abbrev IsNontrivialDLRel {n : ℕ} (Γ : Fin n → G) (v : Fin n → F) : Prop :=
  v ≠ 0 ∧ msm v Γ = 0

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableType G] in
/-- Two distinct openings of the same group element give a non-trivial relation. This is how
the extractor produces relations: from a collision `msm a Γ = msm a' Γ` with `a ≠ a'`. -/
theorem isNontrivialDLRel_sub_of_openings {n : ℕ} {Γ : Fin n → G} {a a' : Fin n → F}
    (hne : a ≠ a') (h : msm a Γ = msm a' Γ) : IsNontrivialDLRel Γ (a - a') :=
  ⟨sub_ne_zero.mpr hne, by rw [msm_sub, h, sub_self]⟩

/-! ## The relation-finding game -/

/-- A relation finder: given a generator vector, try to output a non-trivial relation. -/
def DLRelAdversary (F G : Type) (n : ℕ) := (Fin n → G) → ProbComp (Fin n → F)

/-- The relation-finding experiment: sample uniform generators `Γ`, run the finder, and win
iff it returns a non-trivial relation. -/
def dlRelExp {n : ℕ} (adversary : DLRelAdversary F G n) : ProbComp Bool := do
  let Γ ← $ᵗ (Fin n → G)
  let v ← adversary Γ
  return decide (IsNontrivialDLRel Γ v)

/-! ## Reduction to Pedersen binding -/

/-- Turn a relation finder into a Pedersen binding adversary: embed `Γᵢ = rᵢ·g + dᵢ·pp`, run
the finder to get `v`, and report the relation `⟨v, Γ⟩ = ⟨v,r⟩·g + ⟨v,d⟩·pp` as two openings of
the commitment `0` — namely `(m₁, d₁) = (⟨v,d⟩, ⟨v,r⟩)` and `(m₂, d₂) = (0, 0)`. The two
openings differ exactly when `⟨v,d⟩ ≠ 0`, and the first verifies (against `0`) exactly when
`msm v Γ = 0`. -/
def relToBinding (g : G) {n : ℕ} (adversary : DLRelAdversary F G n) : BindingAdv G F G F :=
  fun pp => do
    let r ← $ᵗ (Fin n → F)
    let d ← $ᵗ (Fin n → F)
    let Γ : Fin n → G := fun i => r i • g + d i • pp
    let v ← adversary Γ
    return (0, ip v d, ip v r, 0, 0)

/-- The intermediate "decoupled" game: sample `Γ` uniformly, run the finder, then sample an
independent `d`; win iff `⟨v,d⟩ ≠ 0` and `msm v Γ = 0`. It is the binding game after the
change of variables that makes `Γ` uniform and independent of `d`. Internal bridge between
`dlRelExp` and the Pedersen binding game. -/
private def bindGame {n : ℕ} (adversary : DLRelAdversary F G n) : ProbComp Bool := do
  let Γ ← $ᵗ (Fin n → G)
  let v ← adversary Γ
  let d ← $ᵗ (Fin n → F)
  return decide (ip v d ≠ 0) && decide (msm v Γ = 0)

/-! ## The `1/|F|` defect: a non-zero linear form is uniform -/

omit [DecidableEq F] in
/-- A single coordinate of a uniform function vector is uniform on `F`. -/
private lemma probOutput_eval_eq_inv_card {n : ℕ} (j : Fin n) (a : F) :
    Pr[= a | (fun d : Fin n → F => d j) <$> ($ᵗ (Fin n → F))]
      = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  have hinj : Function.Injective (fun _ : Unit => j) := fun _ _ _ => Subsingleton.elim _ _
  have hcomp : 𝒟[(· ∘ (fun _ : Unit => j)) <$> ($ᵗ (Fin n → F))] = 𝒟[$ᵗ (Unit → F)] := by
    simpa [bind_pure_comp] using
      evalDist_uniformSample_map_comp_injective (R := F) (A := Unit) (B := Fin n) hinj
  have hsplit : (fun d : Fin n → F => d j) <$> ($ᵗ (Fin n → F))
      = (fun u : Unit → F => u ()) <$> ((· ∘ (fun _ : Unit => j)) <$> ($ᵗ (Fin n → F))) := by
    rw [Functor.map_map]; rfl
  rw [hsplit, probOutput_map_eq_of_evalDist_eq hcomp (fun u : Unit → F => u ()) a]
  have hbij : Function.Bijective (fun u : Unit → F => u ()) :=
    ⟨fun u v h => funext fun x => by cases x; exact h, fun a => ⟨fun _ => a, rfl⟩⟩
  rw [probOutput_map_bijective_uniform_cross (Unit → F) (fun u : Unit → F => u ()) hbij a,
      probOutput_uniformSample]

/-- The single-coordinate vanishing event `d j = 0` on a uniform `d` has probability
`1/|F|`. -/
private lemma probOutput_proj_zero_eq_inv_card {n : ℕ} (j : Fin n) :
    Pr[= true | (do let d ← $ᵗ (Fin n → F); pure (decide (d j = 0)))]
      = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  have hrw : (do let d ← $ᵗ (Fin n → F); pure (decide (d j = 0)))
      = (fun a : F => decide (a = 0)) <$> ((fun d : Fin n → F => d j) <$> ($ᵗ (Fin n → F))) := by
    rw [Functor.map_map, bind_pure_comp]
  rw [hrw, probOutput_map_eq_tsum_ite, tsum_eq_single (0 : F) fun a ha => by simp [ha]]
  rw [if_pos (by simp), probOutput_eval_eq_inv_card j 0]

/-- For a non-zero `v`, the linear form `d ↦ ⟨v,d⟩` evaluated on a uniform `d` vanishes with
probability exactly `1/|F|`. -/
lemma probOutput_inner_zero_eq_inv_card {n : ℕ} {v : Fin n → F} (hv : v ≠ 0) :
    Pr[= true | (do let d ← $ᵗ (Fin n → F); pure (decide (ip v d = 0)))]
      = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  -- `ip v d` is defeq `∑ i, v i * d i`; work with the explicit sum.
  show Pr[= true | (do let d ← $ᵗ (Fin n → F); pure (decide (∑ i, v i * d i = 0)))]
      = (Fintype.card F : ℝ≥0∞)⁻¹
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hj
  -- `T` replaces coordinate `j` with the value of the linear form; it is a bijection.
  set T : (Fin n → F) → (Fin n → F) := fun d => Function.update d j (∑ i, v i * d i) with hT
  have hTval : ∀ d, T d j = ∑ i, v i * d i := fun d => by simp [hT]
  have hTinj : Function.Injective T := by
    intro d d' hdd
    have hrest : ∀ i, i ≠ j → d i = d' i := by
      intro i hi
      have := congrFun hdd i
      simpa [hT, Function.update_of_ne hi] using this
    have hsum : ∑ i, v i * d i = ∑ i, v i * d' i := by
      have := congrFun hdd j; rwa [hTval, hTval] at this
    have hj2 : v j * d j = v j * d' j := by
      have e1 := (Finset.add_sum_erase Finset.univ (fun i => v i * d i) (Finset.mem_univ j)).symm
      have e2 := (Finset.add_sum_erase Finset.univ (fun i => v i * d' i) (Finset.mem_univ j)).symm
      have erest : ∑ i ∈ Finset.univ.erase j, v i * d i
          = ∑ i ∈ Finset.univ.erase j, v i * d' i :=
        Finset.sum_congr rfl fun i hi => by rw [hrest i (Finset.ne_of_mem_erase hi)]
      rw [e1, e2, erest] at hsum
      exact add_right_cancel hsum
    funext i
    by_cases hij : i = j
    · subst hij; exact mul_left_cancel₀ hj hj2
    · exact hrest i hij
  have hTbij : Function.Bijective T := Finite.injective_iff_bijective.mp hTinj
  have hform : (do let d ← $ᵗ (Fin n → F); pure (decide (∑ i, v i * d i = 0)))
      = (do let d ← $ᵗ (Fin n → F); pure (decide (T d j = 0))) :=
    bind_congr fun d => by rw [hTval]
  rw [hform,
      probOutput_bind_bijective_uniform_cross (Fin n → F) T hTbij
        (fun e => pure (decide (e j = 0))) true]
  exact probOutput_proj_zero_eq_inv_card j

/-! ## Generic probability-monad helpers

These are not Bulletproofs-specific; they are general `ProbComp`/`evalDist` facts and are
candidates for upstreaming to VCV-io. -/

/-- Weighted-sum monotonicity with additive slack: if each branch `fa b` beats `fb b` only
up to `c`, then prepending a common sample keeps the same `c` slack (the total branch mass is
at most one). -/
private lemma bound_helper {β : Type} (p : ProbComp β) (fa fb : β → ProbComp Bool)
    (c : ℝ≥0∞) (h : ∀ b, Pr[= true | fa b] ≤ Pr[= true | fb b] + c) :
    Pr[= true | p >>= fa] ≤ Pr[= true | p >>= fb] + c := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  calc ∑' b, Pr[= b | p] * Pr[= true | fa b]
      ≤ ∑' b, (Pr[= b | p] * Pr[= true | fb b] + Pr[= b | p] * c) :=
        ENNReal.tsum_le_tsum fun b => by rw [← mul_add]; gcongr; exact h b
    _ = (∑' b, Pr[= b | p] * Pr[= true | fb b]) + (∑' b, Pr[= b | p]) * c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ (∑' b, Pr[= b | p] * Pr[= true | fb b]) + 1 * c := by
        gcongr; exact tsum_probOutput_le_one
    _ = (∑' b, Pr[= b | p] * Pr[= true | fb b]) + c := by rw [one_mul]

/-! ## The reduction bound -/

omit [Fintype F] in
/-- The binding game (with the Pedersen reduction adversary) equals the decoupled game. -/
private lemma probOutput_bindingExp_relToBinding_eq_bindGame (g : G)
    (hg : Function.Bijective (· • g : F → G)) {n : ℕ} (adversary : DLRelAdversary F G n) :
    Pr[= true | (pedersenCommit g).bindingExp (relToBinding g adversary)] =
      Pr[= true | bindGame adversary] := by
  -- Maintenance note: this is a distributional-rewriting chain (unfold → reorder samples →
  -- reparameterize → drop unused sample). It is the most fragile proof here: it relies on the
  -- `simp only` normal form below, the `← msm_smul_add_smul` fold, the exact bind ordering, and
  -- a final defeq `rfl` against `bindGame`. Steps are applied via `rw` of explicitly-typed
  -- `have`s (not `.trans`) to keep `whnf` from blowing up on the large `do`-blocks.
  refine probOutput_congr rfl ?_
  -- Unfold both experiments and simplify the verification bool (the third opening is trivial,
  -- and the first opening's left side is exactly `msm v Γ`).
  simp only [CommitmentScheme.bindingExp, relToBinding, pedersenCommit, bind_assoc, pure_bind,
    zero_smul, add_zero, decide_true, Bool.and_true, ← msm_smul_add_smul]
  -- Sample `d` before `r`.
  rw [evalDist_bind_congr' fun x =>
        evalDist_bind_bind_swap' ($ᵗ (Fin n → F)) ($ᵗ (Fin n → F)) _]
  -- Reparameterize `r ↦ Γ` where `Γ i = r i • g + d i • (x • g)`; this is a bijection onto `Gⁿ`,
  -- so `Γ` becomes uniform and independent of `x, d`.
  have hrep : ∀ (x : F) (b : Fin n → F),
      𝒟[($ᵗ (Fin n → F)) >>= fun a =>
          adversary (fun i => a i • g + b i • x • g) >>= fun v =>
            pure (decide (ip v b ≠ 0) &&
              decide (msm v (fun i => a i • g + b i • x • g) = 0))]
        = 𝒟[($ᵗ (Fin n → G)) >>= fun Γ =>
            adversary Γ >>= fun v =>
              pure (decide (ip v b ≠ 0) && decide (msm v Γ = 0))] := fun x b =>
    evalDist_bind_bijective_uniform_cross' (fun (r : Fin n → F) i => r i • g + b i • x • g)
      (bij_smul_add hg (fun i => b i • x • g))
      (fun Γ => adversary Γ >>= fun v =>
        pure (decide (ip v b ≠ 0) && decide (msm v Γ = 0)))
  rw [evalDist_bind_congr' fun x => evalDist_bind_congr' fun b => hrep x b]
  -- The leading `x` sample is now unused; drop it.
  rw [evalDist_bind_const' ($ᵗ F) _ (probFailure_uniformSample (α := F))]
  -- Reorder `d, Γ, v` into `Γ, v, d`.
  rw [evalDist_bind_bind_swap' ($ᵗ (Fin n → F)) ($ᵗ (Fin n → G))
        (fun b Γ => adversary Γ >>= fun v =>
          pure (decide (ip v b ≠ 0) && decide (msm v Γ = 0))),
      evalDist_bind_congr' fun Γ =>
        evalDist_bind_bind_swap' ($ᵗ (Fin n → F)) (adversary Γ)
          (fun b v => pure (decide (ip v b ≠ 0) && decide (msm v Γ = 0)))]
  rfl

/-- The relation-finding game is no easier than the decoupled game, up to the `1/|F|` defect. -/
private lemma dlRel_le_bindGame {n : ℕ} (adversary : DLRelAdversary F G n) :
    Pr[= true | dlRelExp adversary] ≤
      Pr[= true | bindGame adversary] + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  unfold dlRelExp bindGame
  refine bound_helper _ _ _ _ fun Γ => ?_
  refine bound_helper _ _ _ _ fun v => ?_
  dsimp only
  by_cases hmsm : msm v Γ = 0
  · by_cases hv0 : v = 0
    · simp [hv0]
    · have hbool : decide (v ≠ 0 ∧ msm v Γ = 0) = true := by simp [hv0, hmsm]
      have hmtrue : decide (msm v Γ = 0) = true := by simp [hmsm]
      have hnot : (do let d ← $ᵗ (Fin n → F); pure (decide (ip v d ≠ 0)))
          = (! ·) <$> (do let d ← $ᵗ (Fin n → F); pure (decide (ip v d = 0))) := by
        simp [ne_eq, decide_not]
      simp only [hbool, probOutput_pure_self, hmtrue, Bool.and_true]
      rw [hnot, probOutput_not_map, ← probOutput_inner_zero_eq_inv_card hv0, add_comm]
      exact le_of_eq probOutput_true_add_false_of_neverFail.symm
  · simp [hmsm]

/-- **Finding a non-trivial generator relation reduces to discrete log.** A relation finder
that wins with probability `p` yields a discrete-log solver winning with probability at least
`p - 1/|F|`. -/
theorem dlRel_le_dlog (g : G) (hg : Function.Bijective (· • g : F → G)) {n : ℕ}
    (adversary : DLRelAdversary F G n) :
    Pr[= true | dlRelExp adversary] ≤
      Pr[= true | dlogExp g (pedersenCommit.dlogReduction (relToBinding g adversary))]
        + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  calc Pr[= true | dlRelExp adversary]
      ≤ Pr[= true | bindGame adversary] + (Fintype.card F : ℝ≥0∞)⁻¹ :=
        dlRel_le_bindGame adversary
    _ = Pr[= true | (pedersenCommit g).bindingExp (relToBinding g adversary)]
          + (Fintype.card F : ℝ≥0∞)⁻¹ := by
        rw [probOutput_bindingExp_relToBinding_eq_bindGame g hg adversary]
    _ ≤ Pr[= true | dlogExp g (pedersenCommit.dlogReduction (relToBinding g adversary))]
          + (Fintype.card F : ℝ≥0∞)⁻¹ := by
        gcongr
        exact pedersenCommit.binding_le_dlog hg (relToBinding g adversary)

end Sigma
