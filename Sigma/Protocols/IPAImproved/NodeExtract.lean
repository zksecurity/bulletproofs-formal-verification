/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.IPAImproved.Extract
import Sigma.Protocols.IPA.NodeExtract
import Sigma.Utils.Binding

namespace Sigma.Protocols.IPAImproved

open Sigma.Protocols.IPA (IPStatement relIP splitL splitR
  ipGens combineHalf splitL_combineHalf splitR_combineHalf msm_combineHalf
  ip_combineHalf ipRelVec msm_ipRelVec ipRelVec_ne_zero memo memo_eq)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- **Node extraction (computable).** Run `extractStepData` on the four challenges
directly — plain distinctness is all the polynomial fold needs, so there is no selection step
(contrast `pickFourDistinctSq` in the arity-8 argument) — and package a witness with
`combineHalf` or a discrete-log relation with `ipRelVec`. -/
def nodeExtractData [DecidableEq F] {k : ℕ} (chal : Fin 4 → F) (a' b' : Fin 4 → Fin (2 ^ k) → F) :
    ((Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F)) ⊕
      (Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F) :=
  match extractStepData chal a' b' with
  | Sum.inl (aLo, aHi, bLo, bHi) => Sum.inl (memo (combineHalf aLo aHi), memo (combineHalf bLo bHi))
  | Sum.inr (vgL, vgR, vhL, vhR, vu) =>
      Sum.inr (memo (ipRelVec (combineHalf vgL vgR) (combineHalf vhL vhR) vu))

/-- **Correctness of `nodeExtractData`.** From the four per-challenge relations at one
node, every `Sum.inl` output is a parent witness, and every `Sum.inr` output a non-trivial
generator relation — `extractStepData_valid` packaged over `combineHalf`/`ipRelVec`. Plain
pairwise-distinct challenges in `F` (zero allowed) are the only hypothesis on the challenges. -/
lemma nodeExtractData_valid [DecidableEq F] {k : ℕ} (s : IPStatement F G k) (chal : Fin 4 → F)
    (hchal : Function.Injective chal) (L R : G) (a' b' : Fin 4 → Fin (2 ^ k) → F)
    (hC : ∀ i, chal i ^ 2 • L + chal i • s.P + R
      = msm (a' i) (foldG (chal i) (splitL s.gs) (splitR s.gs))
        + msm (b' i) (foldH (chal i) (splitL s.hs) (splitR s.hs)) + ip (a' i) (b' i) • s.u) :
    (∀ w, nodeExtractData chal a' b' = Sum.inl w → relIP s w = true) ∧
    (∀ v, nodeExtractData chal a' b' = Sum.inr v
        → IsNontrivialDLRel (ipGens s) v) := by
  obtain ⟨hwitV, hbrkV⟩ := extractStepData_valid (splitL s.gs) (splitR s.gs) (splitL s.hs)
    (splitR s.hs) s.u s.P L R hchal hC
  have hnode : nodeExtractData chal a' b'
      = (match extractStepData chal a' b' with
        | Sum.inl (aLo, aHi, bLo, bHi) =>
            Sum.inl (memo (combineHalf aLo aHi), memo (combineHalf bLo bHi))
        | Sum.inr (vgL, vgR, vhL, vhR, vu) =>
            Sum.inr (memo (ipRelVec (combineHalf vgL vgR) (combineHalf vhL vhR) vu))) := rfl
  rw [hnode]
  rcases he : extractStepData chal a' b'
      with ⟨aLo, aHi, bLo, bHi⟩ | ⟨vgL, vgR, vhL, vhR, vu⟩
  · refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · simp only [Sum.inl.injEq] at hw
      obtain rfl := hw
      have hP := hwitV aLo aHi bLo bHi he
      simp only [relIP, decide_eq_true_eq, memo_eq, msm_combineHalf, ip_combineHalf]
      rw [hP]; abel
    · exact absurd hv (by simp)
  · refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · exact absurd hw (by simp)
    · simp only [Sum.inr.injEq] at hv
      obtain rfl := hv
      obtain ⟨hne, hzero⟩ := hbrkV vgL vgR vhL vhR vu he
      rw [memo_eq]
      refine ⟨?_, ?_⟩
      · apply ipRelVec_ne_zero
        by_contra hcon
        push Not at hcon
        obtain ⟨hc1, hc2, hc3⟩ := hcon
        exact hne ⟨by rw [← splitL_combineHalf vgL vgR, hc1]; rfl,
          by rw [← splitR_combineHalf vgL vgR, hc1]; rfl,
          by rw [← splitL_combineHalf vhL vhR, hc2]; rfl,
          by rw [← splitR_combineHalf vhL vhR, hc2]; rfl, hc3⟩
      · rw [msm_ipRelVec, msm_combineHalf, msm_combineHalf, ← hzero]; abel

end Sigma.Protocols.IPAImproved
