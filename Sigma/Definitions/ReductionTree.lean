/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Basic
import Sigma.Definitions.Reduction

/-!
# Decorated conversation trees and knowledge soundness of a reduction

`(k₁,…,kN)`-special soundness of a `Sigma.Reduction` is stated over **decorated trees** of
conversations: the tree branches with arity `kᵢ` at the `i`-th *challenge* move (challenges
pairwise distinct, enforced by construction), passes through message moves unarily, and
carries an output witness at every leaf — the (never sent) final message that a continuation
would prove knowledge of. The arity vector `(k₁,…,kN)` is matched with the challenge moves
**in order**; message moves contribute no arity (`Sigma.chalArities`). Because moves are a
free list, two adjacent challenges need no separating dummy message round.

A reduction is **knowledge sound** (`Sigma.Reduction.Sound`, witness-or-break style) when,
from every tree all of whose decorated root-to-leaf
paths are accepting (`Sigma.Reduction.Accepting`), a (pure, computable) extractor returns a
valid input witness or a break. For a closed reduction (`Out = Rel.trivial`) the decorations
are trivial and this is classical `(k₁,…,kN)`-special soundness.

## Main definitions

* `Sigma.MoveK` — a move annotated with a branching arity at challenges; `Sigma.stripMoves`
  forgets the arities, `Sigma.chalArities` lists them (one per challenge move, in order).
* `Sigma.TreeK` — the `(k₁,…,kN)`-tree of conversations with leaf decorations.
* `Sigma.TreeK.paths` — the decorated root-to-leaf conversations of a tree.
* `Sigma.Reduction.AcceptingTree`, `Sigma.Reduction.Sound`.
-/

namespace Sigma

/-! ## Arity-annotated moves -/

/-- A move annotated with extraction data: challenge moves carry the branching arity `k`
of the tree at that move. -/
inductive MoveK where
  /-- A prover message of the given type (no branching). -/
  | msg (M : Type)
  /-- A challenge of the given type, branching `k`-fold in the tree. -/
  | chal (C : Type) (k : ℕ)

/-- Forget the arity annotation of a move. -/
@[reducible] def MoveK.strip : MoveK → Move
  | .msg M => .msg M
  | .chal C _ => .chal C

/-- Forget the arity annotations of a move list. Defined by direct recursion (rather than
`List.map`) and marked `@[reducible]` so that conversation types over concrete move-list
prefixes reduce during unification. -/
@[reducible] def stripMoves : List MoveK → List Move
  | [] => []
  | m :: ms => m.strip :: stripMoves ms

@[simp] lemma stripMoves_nil : stripMoves [] = [] := rfl

@[simp] lemma stripMoves_cons (m : MoveK) (ms : List MoveK) :
    stripMoves (m :: ms) = m.strip :: stripMoves ms := rfl

lemma stripMoves_append : ∀ mk₁ mk₂ : List MoveK,
    stripMoves (mk₁ ++ mk₂) = stripMoves mk₁ ++ stripMoves mk₂
  | [], _ => rfl
  | m :: ms, mk₂ => by
      rw [List.cons_append, stripMoves_cons, stripMoves_cons, stripMoves_append ms mk₂,
        List.cons_append]

/-- The branching arities `(k₁,…,kN)` of an annotated move list: one per **challenge**
move, in order. Message moves do not branch and contribute no arity. -/
def chalArities : List MoveK → List ℕ
  | [] => []
  | .msg _ :: ms => chalArities ms
  | .chal _ k :: ms => k :: chalArities ms

@[simp] lemma chalArities_nil : chalArities [] = [] := rfl

@[simp] lemma chalArities_msg_cons (M : Type) (ms : List MoveK) :
    chalArities (.msg M :: ms) = chalArities ms := rfl

@[simp] lemma chalArities_chal_cons (C : Type) (k : ℕ) (ms : List MoveK) :
    chalArities (.chal C k :: ms) = k :: chalArities ms := rfl

lemma chalArities_append : ∀ mk₁ mk₂ : List MoveK,
    chalArities (mk₁ ++ mk₂) = chalArities mk₁ ++ chalArities mk₂
  | [], _ => rfl
  | .msg _ :: ms, mk₂ => by
      rw [List.cons_append, chalArities_msg_cons, chalArities_msg_cons,
        chalArities_append ms mk₂]
  | .chal _ k :: ms, mk₂ => by
      rw [List.cons_append, chalArities_chal_cons, chalArities_chal_cons,
        chalArities_append ms mk₂, List.cons_append]

/-! ## Decorated trees -/

universe u

/-- A `(k₁,…,kN)`-tree of conversations over an annotated move list, with leaf decorations
of type `L` (the output witnesses). `leaf z` carries a decoration; `msg m t` passes a prover
message through unarily; `chal cs inj sub` branches over `k` pairwise-distinct challenges.
The decoration universe is polymorphic so that a tree can be decorated with *trees*
(`Sigma.TreeK.splitTree`). -/
inductive TreeK : List MoveK → Type u → Type (u + 1) where
  | leaf {L : Type u} (z : L) : TreeK [] L
  | msg {M : Type} {L : Type u} {ms : List MoveK} (m : M) (t : TreeK ms L) :
      TreeK (.msg M :: ms) L
  | chal {C : Type} {L : Type u} {k : ℕ} {ms : List MoveK}
      (cs : Fin k → C) (inj : Function.Injective cs)
      (sub : Fin k → TreeK ms L) : TreeK (.chal C k :: ms) L

namespace TreeK

variable {L : Type u} {M C : Type} {k : ℕ} {ms : List MoveK}

/-- The decoration of a leaf. -/
def leafVal : TreeK [] L → L
  | .leaf z => z

/-- The prover message of a message node. -/
def msgVal : TreeK (.msg M :: ms) L → M
  | .msg m _ => m

/-- The subtree of a message node. -/
def msgSub : TreeK (.msg M :: ms) L → TreeK ms L
  | .msg _ t => t

/-- The outgoing challenges of a challenge node. -/
def chalVal : TreeK (.chal C k :: ms) L → (Fin k → C)
  | .chal cs _ _ => cs

/-- The outgoing challenges of a challenge node are pairwise distinct. -/
def chalInj : (T : TreeK (.chal C k :: ms) L) → Function.Injective T.chalVal
  | .chal _ inj _ => inj

/-- The subtrees of a challenge node. -/
def chalSub : TreeK (.chal C k :: ms) L → (Fin k → TreeK ms L)
  | .chal _ _ sub => sub

/-- All decorated root-to-leaf conversations of a tree. -/
def paths : {ms : List MoveK} → {L : Type u} → TreeK ms L →
    List (Conversation (stripMoves ms) × L)
  | _, _, .leaf z => [(PUnit.unit, z)]
  | _, _, .msg m t => (paths t).map fun p => ((m, p.1), p.2)
  | _, _, .chal cs _ sub =>
      (List.finRange _).flatMap fun i => (paths (sub i)).map fun p => ((cs i, p.1), p.2)

@[simp] lemma paths_leaf (z : L) : paths (.leaf z) = [(PUnit.unit, z)] := rfl

@[simp] lemma paths_msg (m : M) (t : TreeK ms L) :
    paths (.msg m t) = (paths t).map fun p => ((m, p.1), p.2) := rfl

@[simp] lemma paths_chal (cs : Fin k → C) (inj : Function.Injective cs)
    (sub : Fin k → TreeK ms L) :
    paths (.chal cs inj sub)
      = (List.finRange k).flatMap fun i => (paths (sub i)).map fun p => ((cs i, p.1), p.2) :=
  rfl

/-- `paths` of a leaf, via the accessor. -/
lemma paths_eq_leaf (T : TreeK [] L) : T.paths = [(PUnit.unit, T.leafVal)] := by
  cases T; rfl

/-- `paths` of a message node, via the accessors. -/
lemma paths_eq_msg (T : TreeK (.msg M :: ms) L) :
    T.paths = T.msgSub.paths.map fun p => ((T.msgVal, p.1), p.2) := by
  cases T; rfl

/-- `paths` of a challenge node, via the accessors. -/
lemma paths_eq_chal (T : TreeK (.chal C k :: ms) L) :
    T.paths = (List.finRange k).flatMap fun i =>
      (T.chalSub i).paths.map fun p => ((T.chalVal i, p.1), p.2) := by
  cases T; rfl

/-- A tree whose challenge arities are all positive has at least one path. -/
lemma paths_ne_nil {ms : List MoveK} {L : Type u} (T : TreeK ms L) :
    (∀ a ∈ chalArities ms, 0 < a) → T.paths ≠ [] := by
  induction T with
  | leaf z => intro _; simp
  | msg m t ih =>
      intro h
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (ih (by simpa using h))
      refine List.ne_nil_of_mem (a := ((m, p.1), p.2)) ?_
      rw [paths_msg]
      exact List.mem_map.2 ⟨p, hp, rfl⟩
  | @chal C L k ms cs inj sub ih =>
      intro h
      have hk : 0 < k := h k (by simp)
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _
        (ih ⟨0, hk⟩ (fun a ha => h a (by simp [ha])))
      refine List.ne_nil_of_mem (a := ((cs ⟨0, hk⟩, p.1), p.2)) ?_
      rw [paths_chal]
      exact List.mem_flatMap.2 ⟨⟨0, hk⟩, List.mem_finRange _, List.mem_map.2 ⟨p, hp, rfl⟩⟩

end TreeK

/-! ## Knowledge soundness of a reduction -/

namespace Reduction

/-- An **accepting decorated tree** for statement `x`: every decorated root-to-leaf
conversation is accepting (`Sigma.Reduction.Accepting`). The tree's annotated move list
carries the branching arities; `hmk` ties its underlying move list to the reduction's. -/
def AcceptingTree (R : Reduction) {mk : List MoveK} (hmk : stripMoves mk = R.moves)
    (x : R.In.Stmt) (T : TreeK mk R.Out.Wit) : Prop :=
  ∀ p ∈ T.paths, R.Accepting x (hmk ▸ p.1) p.2

/-- **Knowledge soundness** of a reduction (`(k₁,…,kN)`-special soundness, witness-or-break
form), witnessed by the pure extractor `e`: from every accepting decorated tree the
extractor outputs either a valid input witness (`Sum.inl`) or a value satisfying the break
predicate `brk` (`Sum.inr`). The arities are `chalArities mk`, matched with the challenge
moves in order. For a closed reduction the decorations are trivial and this is classical
special soundness. The statement is a correctness postcondition for the supplied break
predicate: it is meaningful exactly when `brk` is a genuinely hard-to-satisfy relation —
for the inner-product towers, a non-trivial discrete-log relation among the statement
generators, whose hardness reduces to discrete log (`Sigma.dlRel_le_dlog`). -/
def Sound (R : Reduction) {mk : List MoveK} (hmk : stripMoves mk = R.moves)
    {B : Type} (brk : R.In.Stmt → B → Prop)
    (e : R.In.Stmt → TreeK mk R.Out.Wit → R.In.Wit ⊕ B) : Prop :=
  ∀ x T, R.AcceptingTree hmk x T →
    (∀ w, e x T = Sum.inl w → R.In.rel x w = true) ∧
    (∀ b, e x T = Sum.inr b → brk x b)

end Reduction

end Sigma
