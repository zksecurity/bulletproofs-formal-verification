/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Utils.Vec
import VCVio.EvalDist.TVDist
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Distributional-rewriting helpers for `ProbComp`

Generic `evalDist`/`ProbComp` facts used to prove distribution *equalities* — the shape that
perfect honest-verifier zero-knowledge takes (`𝒟[honest] = 𝒟[simulator]`). They are the
toolkit for the *unfold → reorder → reparameterize → drop* technique: rewrite under a bind,
swap two independent samples, drop an unused leading sample, and push a uniform sample through
a bijection. Together with `bij_smul_add` (a commitment reparameterization) they let an honest
prover's `do`-block be massaged into a witness-free simulator's.

These were originally `private` inside `Sigma/Utils/Binding.lean`; they are not
Bulletproofs-specific and are candidates for upstreaming to VCV-io.
-/

open OracleComp OracleSpec ENNReal

namespace Sigma

/-- Rewrite a sub-computation under a bind, distributionally. -/
lemma evalDist_bind_congr' {α β : Type} {p : ProbComp α} {f g : α → ProbComp β}
    (h : ∀ a, 𝒟[f a] = 𝒟[g a]) : 𝒟[p >>= f] = 𝒟[p >>= g] := by
  rw [evalDist_bind, evalDist_bind]; congr 1; exact funext h

/-- Swap two independent samples, distributionally. -/
lemma evalDist_bind_bind_swap' {α β γ : Type} (p : ProbComp α) (q : ProbComp β)
    (f : α → β → ProbComp γ) :
    𝒟[p >>= fun a => q >>= fun b => f a b] = 𝒟[q >>= fun b => p >>= fun a => f a b] :=
  evalDist_ext fun z => probOutput_bind_bind_swap p q f z

/-- Drop an unused leading sample that never fails. -/
lemma evalDist_bind_const' {α β : Type} (p : ProbComp α) (q : ProbComp β)
    (hp : Pr[⊥ | p] = 0) : 𝒟[p >>= fun _ => q] = 𝒟[q] :=
  evalDist_ext fun z => by rw [probOutput_bind_const, hp, tsub_zero, one_mul]

/-- Push a uniform sample through a bijection, distributionally: reparameterizing the sampled
variable by a bijection leaves the output distribution unchanged. This is the workhorse for
turning an honest commitment (a fixed offset plus a uniform blinder) into a plain uniform
group element in the simulator. -/
lemma evalDist_bind_bijective_uniform_cross' {α β γ : Type} [SampleableType α]
    [SampleableType β] [Finite α] (f : α → β) (hf : Function.Bijective f)
    (cont : β → ProbComp γ) :
    𝒟[($ᵗ α) >>= fun a => cont (f a)] = 𝒟[($ᵗ β) >>= cont] :=
  evalDist_ext fun z => probOutput_bind_bijective_uniform_cross α f hf cont z

/-- Bundle two independent uniform samples into one uniform sample over the product: the
sequential `do a ← $A; b ← $B; k a b` has the same distribution as sampling the pair at once.
Folding this repeatedly collapses an honest prover's whole `do`-block into a single uniform
sample over the product of all its randomness, the form `evalDist_uniform_pure_cross` wants. -/
lemma evalDist_bind_uniform_pair {α β γ : Type} [Fintype α] [Fintype β] [Inhabited α]
    [Inhabited β] [SampleableType α] [SampleableType β] (k : α → β → ProbComp γ) :
    𝒟[($ᵗ α) >>= fun a => ($ᵗ β) >>= fun b => k a b]
      = 𝒟[($ᵗ (α × β)) >>= fun p => k p.1 p.2] := by
  rw [show ($ᵗ (α × β)) = (Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)) from rfl]
  simp only [map_eq_bind_pure_comp, seq_eq_bind, bind_assoc, pure_bind, Function.comp_apply]

/-- Two uniform-then-`pure` computations have the same distribution when a bijection between
their sample spaces makes the outputs agree. This is `evalDist_bind_bijective_uniform_cross'`
specialised to a `pure` continuation — the endgame of a perfect-HVZK proof once both prover
and simulator are in single-sample form. -/
lemma evalDist_uniform_pure_cross {α β γ : Type} [SampleableType α] [SampleableType β]
    [Finite α] (f : α → β) (hf : Function.Bijective f) {out : α → γ} {sout : β → γ}
    (hcomm : ∀ a, out a = sout (f a)) :
    𝒟[($ᵗ α) >>= fun a => pure (out a)] = 𝒟[($ᵗ β) >>= fun b => pure (sout b)] := by
  rw [← evalDist_bind_bijective_uniform_cross' f hf (fun b => pure (sout b))]
  exact evalDist_bind_congr' fun a => by rw [hcomm]

variable {F : Type} [Field F] {G : Type} [AddCommGroup G] [Module F G]

/-- Adding a fixed offset to a coordinatewise rescaling by `g` is a bijection `Fⁿ → Gⁿ`.
Combined with `evalDist_bind_bijective_uniform_cross'`, this lets a vector of honest
commitments `Γᵢ = rᵢ • g + offsetᵢ` (uniform blinder `r`, witness-dependent `offset`) be
resampled as a uniform `Γ : Fin n → G`, independent of the offset. -/
lemma bij_smul_add {n : ℕ} {g : G} (hg : Function.Bijective (· • g : F → G))
    (offset : Fin n → G) :
    Function.Bijective (fun (r : Fin n → F) i => r i • g + offset i) := by
  constructor
  · intro r r' h
    funext i
    exact hg.injective (add_right_cancel (congrFun h i))
  · intro Γ
    refine ⟨fun i => (Equiv.ofBijective (· • g) hg).symm (Γ i - offset i), ?_⟩
    funext i
    have h2 : (Equiv.ofBijective (· • g) hg).symm (Γ i - offset i) • g = Γ i - offset i :=
      (Equiv.ofBijective (· • g) hg).apply_symm_apply _
    show (Equiv.ofBijective (· • g) hg).symm (Γ i - offset i) • g + offset i = Γ i
    rw [h2, sub_add_cancel]

end Sigma
