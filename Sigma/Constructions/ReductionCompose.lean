/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Definitions.ReductionTree

/-!
# Sequential composition of reductions — the construction

Composition of two reductions of knowledge `R₁ : In → Mid` and `R₂ : Mid → Out`
(`Sigma.Reduction.compose`) is **concatenation plus statement plumbing**: the composite's
moves are `R₁.moves ++ R₂.moves`, and its reduce map is the Kleisli composite in `Option` —
run `R₁.reduce` on the first part of the conversation, feed the derived statement to
`R₂.reduce` on the rest. The only compatibility condition is `R₂.In = R₁.Out`. Nothing is
shared, truncated, or constrained at the seam; rejection (`none`) propagates through towers
via `Option.bind`.

The **trivial proof of knowledge** `Sigma.Rel.send` for a relation `R` sends the witness in
one move and reduces to `Rel.trivial`; its reduce map is the only place in the framework
where a verifier evaluates a relation. **Closing** a reduction (`Sigma.Reduction.close`) —
actually sending the final witness — is just composition with `Rel.send R.Out`, and a
reduction is a complete protocol exactly when `Sigma.Reduction.Closed`.

* `Sigma.Conversation.take`/`drop`/`append` — splitting and joining conversations over `++`.
* `Sigma.Reduction.compose` — the composite reduction.
* `Sigma.Rel.send`, `Sigma.Reduction.close` — the trivial PoK and closing.
* `Sigma.Reduction.composeHonest`/`composeSim` — the stitched honest prover and simulator.
* `Sigma.TreeK.splitTree`/`mapLeaves` — the tree surgery for soundness composition: a tree
  over `mk₁ ++ mk₂` *is* an `mk₁`-tree whose leaves carry `mk₂`-trees, and re-decorating
  its leaves (path-aware) yields the outer tree the outer extractor runs on.
* `Sigma.Reduction.composeExtract`/`composeBrk` — the composite extractor and break.

The theorems that completeness, knowledge soundness, and HVZK compose live in
`Sigma.Theorems.ReductionCompose`.
-/

namespace Sigma

/-! ## Splitting and joining conversations over an append -/

namespace Conversation

/-- The first `m₁`-part of a conversation over `m₁ ++ m₂`. -/
def take : (m₁ : List Move) → {m₂ : List Move} → Conversation (m₁ ++ m₂) → Conversation m₁
  | [], _, _ => PUnit.unit
  | _ :: ms, _, c => (c.1, take ms c.2)

/-- The trailing `m₂`-part of a conversation over `m₁ ++ m₂`. -/
def drop : (m₁ : List Move) → {m₂ : List Move} → Conversation (m₁ ++ m₂) → Conversation m₂
  | [], _, c => c
  | _ :: ms, _, c => drop ms c.2

/-- Concatenate two conversations. -/
def append : {m₁ m₂ : List Move} → Conversation m₁ → Conversation m₂ →
    Conversation (m₁ ++ m₂)
  | [], _, _, c₂ => c₂
  | _ :: _, _, c₁, c₂ => (c₁.1, append c₁.2 c₂)

@[simp] lemma take_append : ∀ {m₁ m₂ : List Move} (c₁ : Conversation m₁)
    (c₂ : Conversation m₂), take m₁ (append c₁ c₂) = c₁
  | [], _, _, _ => rfl
  | _ :: ms, _, c₁, c₂ => by
      show (c₁.1, take ms (append c₁.2 c₂)) = c₁
      rw [take_append c₁.2 c₂]

@[simp] lemma drop_append : ∀ {m₁ m₂ : List Move} (c₁ : Conversation m₁)
    (c₂ : Conversation m₂), drop m₁ (append c₁ c₂) = c₂
  | [], _, _, _ => rfl
  | _ :: _, _, c₁, c₂ => drop_append c₁.2 c₂

@[simp] lemma append_take_drop : ∀ (m₁ : List Move) {m₂ : List Move}
    (c : Conversation (m₁ ++ m₂)), append (take m₁ c) (drop m₁ c) = c
  | [], _, _ => rfl
  | _ :: ms, _, c => by
      show (c.1, append (take ms c.2) (drop ms c.2)) = c
      rw [append_take_drop ms c.2]
      rfl

end Conversation

/-! ## The composite reduction -/

namespace Reduction

/-- **Sequential composition** of reductions: `R₁ : In → Mid` then `R₂ : Mid → Out`
(compatibility: `h : R₂.In = R₁.Out`). Moves concatenate; the reduce map is the Kleisli
composite — `R₁.reduce` on the first part derives the statement `R₂.reduce` processes on
the rest. The composite reduces `R₁.In` to `R₂.Out`. -/
def compose (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) : Reduction where
  In := R₁.In
  Out := R₂.Out
  moves := R₁.moves ++ R₂.moves
  reduce := fun x c => (R₁.reduce x (Conversation.take R₁.moves c)).bind fun s =>
    R₂.reduce (Rel.castStmt h.symm s) (Conversation.drop R₁.moves c)

@[simp] lemma compose_In (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) :
    (R₁.compose R₂ h).In = R₁.In := rfl

@[simp] lemma compose_Out (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) :
    (R₁.compose R₂ h).Out = R₂.Out := rfl

@[simp] lemma compose_moves (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) :
    (R₁.compose R₂ h).moves = R₁.moves ++ R₂.moves := rfl

lemma compose_reduce (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) (x : R₁.In.Stmt)
    (c : Conversation (R₁.moves ++ R₂.moves)) :
    (R₁.compose R₂ h).reduce x c
      = (R₁.reduce x (Conversation.take R₁.moves c)).bind fun s =>
          R₂.reduce (Rel.castStmt h.symm s) (Conversation.drop R₁.moves c) := rfl

/-- The composite reduce map on a concatenated conversation: process the parts. -/
@[simp] lemma compose_reduce_append (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out)
    (x : R₁.In.Stmt) (c₁ : Conversation R₁.moves) (c₂ : Conversation R₂.moves) :
    (R₁.compose R₂ h).reduce x (Conversation.append c₁ c₂)
      = (R₁.reduce x c₁).bind fun s => R₂.reduce (Rel.castStmt h.symm s) c₂ := by
  rw [compose_reduce, Conversation.take_append, Conversation.drop_append]

/-- Composition with anything closed is closed, and conversely. -/
lemma compose_closed_iff (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) :
    (R₁.compose R₂ h).Closed ↔ R₂.Closed := Iff.rfl

end Reduction

/-! ## The trivial proof of knowledge, and closing -/

/-- **The trivial proof of knowledge** for a relation `R`: send the witness in one move;
nothing remains to be proven (`Out = Rel.trivial`). Its reduce map — accept iff the
transmitted message is a witness — is the only place in the framework where a verifier
evaluates a relation; every other reduction only transforms statements. (`@[reducible]` so
that instance search and unification see through its fields.) -/
@[reducible] def Rel.send (R : Rel) : Reduction where
  In := R
  Out := Rel.trivial
  moves := [.msg R.Wit]
  reduce := fun x c => if R.rel x c.1 then some PUnit.unit else none

@[simp] lemma Rel.send_In (R : Rel) : (Rel.send R).In = R := rfl

@[simp] lemma Rel.send_Out (R : Rel) : (Rel.send R).Out = Rel.trivial := rfl

namespace Reduction

/-- **Close** a reduction: compose with the trivial proof of knowledge for its output
relation, i.e. actually send the final witness and check it. The result is a complete
protocol (`Sigma.Reduction.Closed`); declining to close — composing with a nontrivial PoK
for `R.Out` instead — is exactly compression in the sense of Attema–Cramer. -/
def close (R : Reduction) : Reduction := R.compose (Rel.send R.Out) rfl

@[simp] lemma close_In (R : Reduction) : R.close.In = R.In := rfl

@[simp] lemma close_Out (R : Reduction) : R.close.Out = Rel.trivial := rfl

@[simp] lemma close_moves (R : Reduction) : R.close.moves = R.moves ++ [.msg R.Out.Wit] :=
  rfl

/-- Closing produces a closed reduction. -/
lemma close_closed (R : Reduction) : R.close.Closed := rfl

end Reduction

/-! ## Joining tree paths over an append

`joinCK` is the arity-level join of conversations (recursing on the annotated move list, so
no `stripMoves_append` cast is needed to state it); `joinCK_heq_append` reconciles it with
the plain `Conversation.append` across that cast. -/

/-- Arity-level join of conversations over annotated move lists. -/
def joinCK : (mk₁ : List MoveK) → {mk₂ : List MoveK} →
    Conversation (stripMoves mk₁) → Conversation (stripMoves mk₂) →
    Conversation (stripMoves (mk₁ ++ mk₂))
  | [], _, _, c₂ => c₂
  | _ :: ms, _, c₁, c₂ => (c₁.1, joinCK ms c₁.2 c₂)

/-- `HEq` congruence for a pair whose first component is fixed and whose second varies
across a type equality. -/
lemma heq_pair {A : Type} {B₁ B₂ : Type} (a : A) {x : B₁} {y : B₂}
    (hB : B₁ = B₂) (hxy : HEq x y) : HEq ((a, x) : A × B₁) ((a, y) : A × B₂) := by
  subst hB; obtain rfl := eq_of_heq hxy; rfl

/-- The arity-level join is the plain `Conversation.append`, up to the `stripMoves_append`
type identity. -/
lemma joinCK_heq_append : ∀ (mk₁ : List MoveK) {mk₂ : List MoveK}
    (c₁ : Conversation (stripMoves mk₁)) (c₂ : Conversation (stripMoves mk₂)),
    HEq (joinCK mk₁ c₁ c₂) (Conversation.append c₁ c₂)
  | [], _, _, _ => HEq.rfl
  | _ :: ms, mk₂, c₁, c₂ =>
      heq_pair c₁.1 (congrArg Conversation (stripMoves_append ms mk₂))
        (joinCK_heq_append ms c₁.2 c₂)

/-- `Conversation.append` respects move-list equalities (`HEq` form). -/
lemma append_heq_congr {m₁ m₁' m₂ m₂' : List Move} (h₁ : m₁ = m₁') (h₂ : m₂ = m₂')
    {a : Conversation m₁} {a' : Conversation m₁'} (ha : HEq a a')
    {b : Conversation m₂} {b' : Conversation m₂'} (hb : HEq b b') :
    HEq (Conversation.append a b) (Conversation.append a' b') := by
  subst h₁; subst h₂
  rw [eq_of_heq ha, eq_of_heq hb]

/-- **Step 2 (acceptance factoring, the cast bridge).** The composite reduce map on a cast
tree-path join processes the cast parts: outer reduce, then inner reduce at the plumbed
statement. Stated at the composite's own move-list cast so that, by proof irrelevance, it
rewrites the accepting condition of a composite tree directly; the cast plumbing is
`joinCK_heq_append` and `append_heq_congr`, followed by `compose_reduce_append`. -/
lemma Reduction.compose_reduce_joinCK (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out)
    {mk₁ mk₂ : List MoveK} (hm₁ : stripMoves mk₁ = R₁.moves)
    (hm₂ : stripMoves mk₂ = R₂.moves)
    (hmk : stripMoves (mk₁ ++ mk₂) = (R₁.compose R₂ h).moves) (x : R₁.In.Stmt)
    (c₁ : Conversation (stripMoves mk₁)) (c₂ : Conversation (stripMoves mk₂)) :
    (R₁.compose R₂ h).reduce x (hmk ▸ joinCK mk₁ c₁ c₂)
      = (R₁.reduce x (hm₁ ▸ c₁)).bind fun s =>
          R₂.reduce (Rel.castStmt h.symm s) (hm₂ ▸ c₂) := by
  have hcast : (hmk ▸ joinCK mk₁ c₁ c₂ : Conversation (R₁.compose R₂ h).moves)
      = Conversation.append (hm₁ ▸ c₁) (hm₂ ▸ c₂) := by
    apply eq_of_heq
    refine (eqRec_heq _ _).trans ((joinCK_heq_append mk₁ c₁ c₂).trans ?_)
    exact append_heq_congr hm₁ hm₂ (eqRec_heq _ _).symm (eqRec_heq _ _).symm
  rw [hcast, Reduction.compose_reduce_append]

/-! ## Tree surgery: split and re-decorate -/

namespace TreeK

universe u v

variable {L : Type u} {L' : Type v}

/-- **Step 1 (split the composite tree).** A tree over `mk₁ ++ mk₂` *is* an `mk₁`-tree
whose leaf decorations are the `mk₂`-subtrees hanging off the outer paths: message and
challenge nodes are copied, and the recursion bottoms out by storing the remaining subtree
at the leaf. -/
def splitTree : (mk₁ : List MoveK) → {mk₂ : List MoveK} → {L : Type u} →
    TreeK (mk₁ ++ mk₂) L → TreeK mk₁ (TreeK mk₂ L)
  | [], _, _, T => .leaf T
  | .msg _ :: ms, _, _, T => .msg T.msgVal (splitTree ms T.msgSub)
  | .chal _ _ :: ms, _, _, T => .chal T.chalVal T.chalInj fun i => splitTree ms (T.chalSub i)

/-- **Step 1 (path factoring).** The decorated paths of a composite tree factor through
the split: each is an outer leaf-path `joinCK`-joined with a decorated path of the subtree
stored at that leaf. By induction on `mk₁`, pushing `List.map`/`List.flatMap` through the
per-node path constructors. -/
lemma paths_splitTree : ∀ (mk₁ : List MoveK) {mk₂ : List MoveK} {L : Type u}
    (T : TreeK (mk₁ ++ mk₂) L),
    T.paths = (splitTree mk₁ T).paths.flatMap fun pS =>
      pS.2.paths.map fun qz => (joinCK mk₁ pS.1 qz.1, qz.2)
  | [], _, _, T => by
      simp only [splitTree, paths_leaf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        joinCK]
      simp
  | .msg M :: ms, mk₂, _, T => by
      cases T with
      | msg m t =>
          simp only [List.cons_append, splitTree, msgVal, msgSub, paths_msg,
            List.flatMap_map]
          rw [paths_splitTree ms t, List.map_flatMap]
          simp only [List.map_map]
          rfl
  | .chal C k :: ms, mk₂, _, T => by
      cases T with
      | chal cs inj sub =>
          simp only [List.cons_append, splitTree, chalVal, chalSub, paths_chal,
            List.flatMap_assoc, List.flatMap_map]
          refine congrArg (fun g => List.flatMap g (List.finRange k)) (funext fun i => ?_)
          rw [paths_splitTree ms (sub i), List.map_flatMap]
          simp only [List.map_map]
          rfl

/-- **Step 5 (re-decorate, worker).** Replace each leaf decoration by a function of the
root-to-leaf conversation and the old decoration. The continuation `cont` rebuilds the full
path (the leaf's new value may depend on the whole conversation — the derived statement
does); use `Sigma.TreeK.mapLeaves` at the root. -/
def mapLeavesAux {mkF : List MoveK} (f : Conversation (stripMoves mkF) → L → L') :
    {mk : List MoveK} → (cont : Conversation (stripMoves mk) → Conversation (stripMoves mkF)) →
    TreeK mk L → TreeK mk L'
  | [], cont, T => .leaf (f (cont PUnit.unit) T.leafVal)
  | .msg _ :: _, cont, T =>
      .msg T.msgVal (mapLeavesAux f (fun c => cont (T.msgVal, c)) T.msgSub)
  | .chal _ _ :: _, cont, T =>
      .chal T.chalVal T.chalInj fun i =>
        mapLeavesAux f (fun c => cont (T.chalVal i, c)) (T.chalSub i)

/-- Re-decorate the leaves of a tree by a function of the full root-to-leaf conversation
and the old decoration. -/
def mapLeaves {mk : List MoveK} (f : Conversation (stripMoves mk) → L → L')
    (T : TreeK mk L) : TreeK mk L' :=
  mapLeavesAux f id T

/-- **Step 5 (re-decorated paths).** The decorated paths of a re-decorated tree: same
conversations, new decorations computed from them. By induction on the move list, as
`paths_splitTree`. -/
lemma paths_mapLeavesAux {mkF : List MoveK} (f : Conversation (stripMoves mkF) → L → L') :
    ∀ {mk : List MoveK}
      (cont : Conversation (stripMoves mk) → Conversation (stripMoves mkF))
      (T : TreeK mk L),
      (mapLeavesAux f cont T).paths = T.paths.map fun p => (p.1, f (cont p.1) p.2)
  | [], cont, T => by
      cases T with
      | leaf z => simp only [mapLeavesAux, leafVal, paths_leaf, List.map_cons, List.map_nil]
  | .msg M :: ms, cont, T => by
      cases T with
      | msg m t =>
          simp only [mapLeavesAux, msgVal, msgSub, paths_msg]
          rw [paths_mapLeavesAux f (fun c => cont (m, c)) t, List.map_map, List.map_map]
          rfl
  | .chal C k :: ms, cont, T => by
      cases T with
      | chal cs inj sub =>
          simp only [mapLeavesAux, chalVal, chalSub, paths_chal, List.map_flatMap]
          refine congrArg (fun g => List.flatMap g (List.finRange k)) (funext fun i => ?_)
          rw [paths_mapLeavesAux f (fun c => cont (cs i, c)) (sub i), List.map_map,
            List.map_map]
          rfl

/-- The decorated paths of `Sigma.TreeK.mapLeaves`. -/
lemma paths_mapLeaves {mk : List MoveK} (f : Conversation (stripMoves mk) → L → L')
    (T : TreeK mk L) :
    (mapLeaves f T).paths = T.paths.map fun p => (p.1, f p.1 p.2) :=
  paths_mapLeavesAux f id T

end TreeK

/-! ## The composite extractor and break predicate -/

namespace Reduction

variable {B₁ B₂ : Type}

/-- **Step 3 (per-leaf inner extraction).** Derive the inner statement from the outer path
via `R₁.reduce` and run `R₂`'s extractor on the hanging subtree. The `none` branch is
unreachable on accepting trees and returns a placeholder witness. -/
def composeRes (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out)
    {mk₁ mk₂ : List MoveK} (hm₁ : stripMoves mk₁ = R₁.moves) [Inhabited R₂.In.Wit]
    (e₂ : R₂.In.Stmt → TreeK mk₂ R₂.Out.Wit → R₂.In.Wit ⊕ B₂) (x : R₁.In.Stmt)
    (c : Conversation (stripMoves mk₁)) (S : TreeK mk₂ R₂.Out.Wit) : R₂.In.Wit ⊕ B₂ :=
  match R₁.reduce x (hm₁ ▸ c) with
  | some s => e₂ (Rel.castStmt h.symm s) S
  | none => Sum.inl default

/-- **The composite extractor** (Steps 1, 3–5 as data). Split the tree (`TreeK.splitTree`);
at each outer leaf run `R₂`'s extractor on the hanging subtree at the plumbed statement
(`Sigma.Reduction.composeRes`). If some leaf reports a break, return it (Step 4); otherwise
re-decorate each leaf with its extracted `R₁`-output witness (`TreeK.mapLeaves`) and run
`R₁`'s extractor on the resulting outer tree (Step 5). Built from the sub-extractors — no
`Classical.choice` at the seam. -/
def composeExtract (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out)
    {mk₁ mk₂ : List MoveK} (hm₁ : stripMoves mk₁ = R₁.moves) [Inhabited R₂.In.Wit]
    (e₁ : R₁.In.Stmt → TreeK mk₁ R₁.Out.Wit → R₁.In.Wit ⊕ B₁)
    (e₂ : R₂.In.Stmt → TreeK mk₂ R₂.Out.Wit → R₂.In.Wit ⊕ B₂)
    (x : R₁.In.Stmt) (T : TreeK (mk₁ ++ mk₂) R₂.Out.Wit) : R₁.In.Wit ⊕ (B₁ ⊕ B₂) :=
  match (TreeK.splitTree mk₁ T).paths.findSome?
      (fun pS => (composeRes R₁ R₂ h hm₁ e₂ x pS.1 pS.2).getRight?) with
  | some b₂ => Sum.inr (Sum.inr b₂)
  | none =>
      match e₁ x ((TreeK.splitTree mk₁ T).mapLeaves fun c S =>
          Rel.castWit h ((composeRes R₁ R₂ h hm₁ e₂ x c S).getLeft?.getD default)) with
      | Sum.inl w => Sum.inl w
      | Sum.inr b₁ => Sum.inr (Sum.inl b₁)

/-- **Step 4 (the composite break).** An outer break, or an inner break at some statement
the outer reduction can actually derive from a conversation. -/
def composeBrk (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out)
    (brk₁ : R₁.In.Stmt → B₁ → Prop) (brk₂ : R₂.In.Stmt → B₂ → Prop) :
    R₁.In.Stmt → B₁ ⊕ B₂ → Prop
  | x, .inl b₁ => brk₁ x b₁
  | x, .inr b₂ => ∃ (c : Conversation R₁.moves) (s : R₁.Out.Stmt),
      R₁.reduce x c = some s ∧ brk₂ (Rel.castStmt h.symm s) b₂

/-! ## The stitched honest prover and simulator -/

/-- The shared continuation of the composite honest prover and simulator: given the outer
(conversation, output-witness) pair, derive the inner statement, run the inner honest
prover on the carried witness, and concatenate. -/
def composeCont (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) [Inhabited R₂.In.Stmt]
    (H₂ : R₂.In.Stmt → R₂.In.Wit → ProbComp (Conversation R₂.moves × R₂.Out.Wit))
    (x : R₁.In.Stmt) (p : Conversation R₁.moves × R₁.Out.Wit) :
    ProbComp (Conversation (R₁.moves ++ R₂.moves) × R₂.Out.Wit) :=
  H₂ ((R₁.reduce x p.1).elim default (Rel.castStmt h.symm)) (Rel.castWit h.symm p.2) >>=
    fun p₂ => pure (Conversation.append p.1 p₂.1, p₂.2)

/-- The stitched composite honest prover: run the outer prover, plumb the derived statement
and the carried output witness into the inner prover, and concatenate the conversations. -/
def composeHonest (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) [Inhabited R₂.In.Stmt]
    (H₁ : R₁.In.Stmt → R₁.In.Wit → ProbComp (Conversation R₁.moves × R₁.Out.Wit))
    (H₂ : R₂.In.Stmt → R₂.In.Wit → ProbComp (Conversation R₂.moves × R₂.Out.Wit)) :
    R₁.In.Stmt → R₁.In.Wit →
      ProbComp (Conversation (R₁.moves ++ R₂.moves) × R₂.Out.Wit) :=
  fun x w => H₁ x w >>= composeCont R₁ R₂ h H₂ x

/-- The composite simulator: as `Sigma.Reduction.composeHonest`, but the outer
(conversation, output-witness) pair comes from the outer *simulator*. Only the outer
reduction carries a zero-knowledge obligation; the inner contributes its honest prover. -/
def composeSim (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) [Inhabited R₂.In.Stmt]
    (S₁ : R₁.In.Stmt → ProbComp (Conversation R₁.moves × R₁.Out.Wit))
    (H₂ : R₂.In.Stmt → R₂.In.Wit → ProbComp (Conversation R₂.moves × R₂.Out.Wit)) :
    R₁.In.Stmt → ProbComp (Conversation (R₁.moves ++ R₂.moves) × R₂.Out.Wit) :=
  fun x => S₁ x >>= composeCont R₁ R₂ h H₂ x

end Reduction

end Sigma
