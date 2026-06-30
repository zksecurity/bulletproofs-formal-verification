/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Theorems.ReductionCompose

/-!
# Worked example: a 2-round `(2,2)`-special-sound discrete-log reduction

A small worked instance of `Sigma.Reduction`: the **nested Schnorr** protocol is a 2-round
reduction from the discrete-logarithm relation *to the discrete-logarithm relation itself*
— each round translates the claim `P = w • g` into the claim
`A + c • P = (r + c·w) • g` about a fresh statement — and the classical 5-move protocol is
its closure (`Sigma.Reduction.close`): only the last scalar is ever sent.

## Protocol

Public generator `g : G`; statement `P : G`; witness `w : F` with `w • g = P`.

1. message `A₁ = r₁ • g`, challenge `c₁ : F`
2. message `A₂ = r₂ • g`, challenge `c₂ : F`
3. the claim is reduced to knowledge of `z = r₂ + c₂ * (r₁ + c₁ * w)` with
   `z • g = A₂ + c₂ • (A₁ + c₁ • P)` — the output statement; closing sends `z`.

## Extraction (`(2,2)`-special soundness, `Sigma.Examples.proto_sound`)

Within a `c₁`-branch, two accepting decorated paths with distinct `c₂` recover
`A₁ + c₁ • P = sᵢ • g` for `sᵢ = (c₂⁰ - c₂¹)⁻¹ * (z⁰ - z¹)` (one Schnorr step,
`Sigma.Examples.schnorr_step`). Two `c₁`-branches with distinct `c₁` then recover
`P = w • g` for `w = (c₁⁰ - c₁¹)⁻¹ * (s⁰ - s¹)` (a second Schnorr step). The
distinctness facts come from the tree's injective-challenge fields, and the extraction is
perfect: the break type is `Empty`.
-/

namespace Sigma.Examples

open Sigma.TreeK

variable {G F : Type} [AddCommGroup G] [Field F] [Module F G]

/-- One Schnorr extraction step: from two accepting equations `x • g = A + c • U` and
`y • g = A + c' • U` with distinct challenges `c ≠ c'`, recover `U` as a scalar multiple
of `g`. -/
theorem schnorr_step (g A U : G) {c c' x y : F}
    (hc : c ≠ c') (h1 : x • g = A + c • U) (h2 : y • g = A + c' • U) :
    ((c - c')⁻¹ * (x - y)) • g = U := by
  have hsub : (x - y) • g = (c - c') • U := by
    rw [sub_smul, h1, h2, sub_smul]; abel
  have hc' : c - c' ≠ 0 := sub_ne_zero.mpr hc
  rw [mul_smul, hsub, smul_smul, inv_mul_cancel₀ hc', one_smul]

variable [DecidableEq G]

/-- The discrete-logarithm relation `w • g = P`. -/
@[reducible] def relDL (g : G) : Rel where
  Stmt := G
  Wit := F
  rel := fun P w => decide (w • g = P)

/-- The 2-round nested-Schnorr protocol, as a reduction from the discrete-log relation to
*itself*: after `(A₁, c₁, A₂, c₂)` the claim `P = w • g` has been reduced to knowledge of a
discrete log of `A₂ + c₂ • (A₁ + c₁ • P)`. The classical 5-move protocol is
`(proto g).close`. Marked `@[reducible]` so that the projections `(proto g).In.Stmt`,
`(proto g).Out.Wit`, etc. unfold during instance resolution in the soundness proof. -/
@[reducible] def proto (g : G) : Reduction where
  In := relDL (F := F) g
  Out := relDL (F := F) g
  moves := [.msg G, .chal F, .msg G, .chal F]
  reduce := fun P c => some (c.2.2.1 + c.2.2.2.1 • (c.1 + c.2.1 • P))

/-- The `(2,2)` tree annotation of the nested-Schnorr reduction. -/
@[reducible] def protoMK (G F : Type) : List MoveK := [.msg G, .chal F 2, .msg G, .chal F 2]

/-- The `(2,2)`-extractor: nested Schnorr extraction over a decorated `(2,2)`-tree. The
break type is `Empty` — extraction is perfect. -/
def extract (_g : G) : G → TreeK (protoMK G F) F → F ⊕ Empty :=
  fun _P T =>
    let c₁ := T.msgSub.chalVal
    let sub := T.msgSub.chalSub
    let s : Fin 2 → F := fun i =>
      let c₂ := (sub i).msgSub.chalVal
      let z : Fin 2 → F := fun j => ((sub i).msgSub.chalSub j).leafVal
      (c₂ 0 - c₂ 1)⁻¹ * (z 0 - z 1)
    Sum.inl ((c₁ 0 - c₁ 1)⁻¹ * (s 0 - s 1))

omit [AddCommGroup G] [Field F] [Module F G] [DecidableEq G] in
/-- The `(i, j)`-th decorated root-to-leaf conversation of a `(2,2)`-tree, named via the
accessors, is one of its `paths`. -/
lemma mem_paths (T : TreeK (protoMK G F) F) (i j : Fin 2) :
    ((T.msgVal, T.msgSub.chalVal i, (T.msgSub.chalSub i).msgVal,
        (T.msgSub.chalSub i).msgSub.chalVal j, PUnit.unit),
      ((T.msgSub.chalSub i).msgSub.chalSub j).leafVal) ∈ T.paths := by
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((T.msgSub.chalVal i, (T.msgSub.chalSub i).msgVal,
    (T.msgSub.chalSub i).msgSub.chalVal j, PUnit.unit),
    ((T.msgSub.chalSub i).msgSub.chalSub j).leafVal), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨i, by simp, ?_⟩
  refine List.mem_map.2 ⟨(((T.msgSub.chalSub i).msgVal,
    (T.msgSub.chalSub i).msgSub.chalVal j, PUnit.unit),
    ((T.msgSub.chalSub i).msgSub.chalSub j).leafVal), ?_, rfl⟩
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((((T.msgSub.chalSub i).msgSub.chalVal j, PUnit.unit)),
    ((T.msgSub.chalSub i).msgSub.chalSub j).leafVal), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨j, by simp, ?_⟩
  refine List.mem_map.2 ⟨(PUnit.unit, ((T.msgSub.chalSub i).msgSub.chalSub j).leafVal),
    ?_, rfl⟩
  rw [TreeK.paths_eq_leaf]
  exact List.mem_singleton.2 rfl

/-- **The nested-Schnorr reduction is `(2,2)`-special sound** (perfectly: no break). -/
theorem proto_sound (g : G) :
    (proto (F := F) g).Sound (mk := protoMK G F) rfl (fun _ b => b.elim) (extract g) := by
  intro P T hacc
  refine ⟨fun w hw => ?_, fun b hb => b.elim⟩
  -- Each of the four decorated root-to-leaf conversations is accepting.
  have eqn : ∀ i j : Fin 2,
      ((T.msgSub.chalSub i).msgSub.chalSub j).leafVal • g =
        (T.msgSub.chalSub i).msgVal +
          (T.msgSub.chalSub i).msgSub.chalVal j • (T.msgVal + T.msgSub.chalVal i • P) := by
    intro i j
    obtain ⟨s, hs, hrel⟩ := hacc _ (mem_paths T i j)
    simp only [proto] at hs
    obtain rfl := Option.some.inj hs
    simpa [relDL] using hrel
  -- The challenges at each node are pairwise distinct.
  have hc1 : T.msgSub.chalVal 0 ≠ T.msgSub.chalVal 1 :=
    (T.msgSub.chalInj).ne (by decide)
  have hc2 : ∀ i : Fin 2,
      (T.msgSub.chalSub i).msgSub.chalVal 0 ≠ (T.msgSub.chalSub i).msgSub.chalVal 1 :=
    fun i => ((T.msgSub.chalSub i).msgSub.chalInj).ne (by decide)
  -- Inner Schnorr step, once per `c₁`-branch.
  have step1 : ∀ i : Fin 2,
      (((T.msgSub.chalSub i).msgSub.chalVal 0 - (T.msgSub.chalSub i).msgSub.chalVal 1)⁻¹ *
        (((T.msgSub.chalSub i).msgSub.chalSub 0).leafVal
          - ((T.msgSub.chalSub i).msgSub.chalSub 1).leafVal)) • g
        = T.msgVal + T.msgSub.chalVal i • P :=
    fun i => schnorr_step g ((T.msgSub.chalSub i).msgVal)
      (T.msgVal + T.msgSub.chalVal i • P) (hc2 i) (eqn i 0) (eqn i 1)
  -- Outer Schnorr step, combining the two branches, recovers the witness.
  have step2 := schnorr_step g T.msgVal P hc1 (step1 0) (step1 1)
  -- The extractor outputs exactly that witness.
  obtain rfl := Sum.inl.inj hw
  simpa only [relDL, decide_eq_true_eq] using step2

/-- The classical 5-move nested-Schnorr protocol: close the reduction — send the final
scalar and check it. Knowledge soundness is `Sigma.Reduction.close_sound` of
`Sigma.Examples.proto_sound`; the arities stay `(2,2)`. -/
def protoClosed (g : G) : Reduction := (proto (F := F) g).close

local instance : Inhabited F := ⟨0⟩

/-- The closed protocol is `(2,2)`-special sound. -/
theorem protoClosed_sound (g : G) :
    (protoClosed (F := F) g).Sound
      (mk := protoMK G F ++ [.msg F])
      (by rw [stripMoves_append]; rfl)
      (Reduction.composeBrk (proto g) (Rel.send (proto g).Out) rfl
        (fun _ b => b.elim) (fun _ b => b.elim))
      (Reduction.composeExtract (proto g) (Rel.send (proto g).Out) rfl rfl
        (extract g) (Rel.sendExtract (proto g).Out)) :=
  Reduction.close_sound (proto g) rfl (proto_sound g)

end Sigma.Examples
