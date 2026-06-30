/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib.Data.List.Basic
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.TVDist

/-!
# Reductions of knowledge: one interface for every public-coin protocol

A protocol is a **reduction** between two relations (`Sigma.Rel`): the prover claims
knowledge of a witness for the *input* relation, and after the conversation the claim has
been *reduced* to knowledge of a witness for the *output* relation — the witness being the
protocol's final message, which is **never sent**. There is no separate verifier: the single
map `reduce : In.Stmt → Conversation moves → Option Out.Stmt` both rejects (`none`) and
derives the output statement (`some s`). Closing a tower of reductions — actually sending
the final witness — is itself just composition with the trivial proof of knowledge
`Rel.send` (`Sigma.Constructions.ReductionCompose`), whose `reduce` is the only place in the
framework where a verifier evaluates a relation.

The conversation shape is a bare list of `Sigma.Move`s — prover messages and public-coin
challenges. No move is special: there is no distinguished first message or trailing
challenge, and adjacent moves in the same direction are allowed (so no "dummy" unit-message
rounds are ever needed to separate two challenges). `Sigma.rounds` counts the number of
direction *transitions* of a move list — the classical "(2n+1)-move" count is insensitive
to coalescing adjacent same-direction moves, and so is `rounds`.

## Main definitions

* `Sigma.Rel` — a relation: statement type, witness type, decision predicate.
* `Sigma.Rel.trivial` — the trivial relation; `Sigma.Reduction.Closed` ("composition is
  done") means the output relation is `Rel.trivial`.
* `Sigma.Move`, `Sigma.Conversation` — moves and the data of a full conversation.
* `Sigma.rounds` — the number of direction transitions of a move list.
* `Sigma.Reduction` — the one protocol interface: `In`, `Out`, `moves`, `reduce`.
* `Sigma.Reduction.Accepting` — a conversation/output-witness pair is accepting.
* `Sigma.Reduction.Complete` — honest completeness, for a supplied honest prover.
* `Sigma.Reduction.HVZK` / `Sigma.Reduction.PerfectHVZK` — honest-verifier zero-knowledge
  of the joint (conversation, output-witness) distribution.

Knowledge soundness lives in `Sigma.Definitions.ReductionTree` (it needs trees of
conversations); the composition operator and its theorems live in
`Sigma.Constructions.ReductionCompose` and `Sigma.Theorems.ReductionCompose`.
-/

namespace Sigma

/-! ## Relations -/

/-- A relation: a statement type, a witness type, and a decision predicate. Protocols are
*reductions* between two such relations, and the same triple shape is used for both ends. -/
structure Rel where
  /-- The statement (public input) type. -/
  Stmt : Type
  /-- The witness type. -/
  Wit : Type
  /-- The decision predicate. -/
  rel : Stmt → Wit → Bool

/-- The trivial relation: nothing left to prove. A reduction whose output relation is
`Rel.trivial` is a *complete protocol* (`Sigma.Reduction.Closed`). -/
def Rel.trivial : Rel := ⟨PUnit, PUnit, fun _ _ => true⟩

/-- Transport a statement along an equality of relations. -/
def Rel.castStmt {R S : Rel} (h : R = S) (x : R.Stmt) : S.Stmt := h ▸ x

/-- Transport a witness along an equality of relations. -/
def Rel.castWit {R S : Rel} (h : R = S) (w : R.Wit) : S.Wit := h ▸ w

@[simp] lemma Rel.castStmt_rfl {R : Rel} (x : R.Stmt) : Rel.castStmt rfl x = x := rfl

@[simp] lemma Rel.castWit_rfl {R : Rel} (w : R.Wit) : Rel.castWit rfl w = w := rfl

/-- The decision predicate is invariant under transport on both sides. -/
lemma Rel.rel_castStmt_castWit {R S : Rel} (h : R = S) (x : R.Stmt) (w : R.Wit) :
    S.rel (Rel.castStmt h x) (Rel.castWit h w) = R.rel x w := by cases h; rfl

/-- Transporting only the witness: the predicate at the transported witness equals the
original predicate at the back-transported statement. -/
lemma Rel.rel_castWit {R S : Rel} (h : R = S) (x : S.Stmt) (w : R.Wit) :
    S.rel x (Rel.castWit h w) = R.rel (Rel.castStmt h.symm x) w := by cases h; rfl

/-! ## Moves and conversations -/

/-- A single move of a public-coin protocol: a prover message or a uniformly random
verifier challenge. No move is distinguished — protocols are free lists of moves, and
adjacent moves in the same direction are allowed. -/
inductive Move where
  /-- A prover message of the given type. -/
  | msg (M : Type)
  /-- A public-coin verifier challenge of the given type. -/
  | chal (C : Type)

/-- The data transmitted by a move. -/
@[reducible] def Move.Data : Move → Type
  | .msg M => M
  | .chal C => C

/-- Whether a move is a prover message (`true`) or a challenge (`false`). -/
def Move.isMsg : Move → Bool
  | .msg _ => true
  | .chal _ => false

/-- The data of a full conversation: one value per move, in order. -/
@[reducible] def Conversation : List Move → Type
  | [] => PUnit
  | m :: ms => m.Data × Conversation ms

/-! ## Counting rounds

`rounds` counts the number of **direction transitions** of a move list. Adjacent moves in
the same direction coalesce — `[.msg M₁, .msg M₂]` is one round of communication, exactly
like `[.msg (M₁ × M₂)]` — so a classical `(2n+1)`-move protocol (a message followed by `n`
challenge–response pairs) has `rounds = 2n`. -/

/-- The number of direction transitions of a move list. Insensitive to coalescing adjacent
same-direction moves; a classical `(2n+1)`-move protocol has `rounds = 2n`. -/
def rounds : List Move → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: ms => (if a.isMsg = b.isMsg then 0 else 1) + rounds (b :: ms)

@[simp] lemma rounds_nil : rounds [] = 0 := rfl

@[simp] lemma rounds_singleton (m : Move) : rounds [m] = 0 := rfl

lemma rounds_cons_cons (a b : Move) (ms : List Move) :
    rounds (a :: b :: ms) = (if a.isMsg = b.isMsg then 0 else 1) + rounds (b :: ms) := rfl

/-- **Coalescing**: an adjacent pair of moves in the same direction contributes no round. -/
lemma rounds_cons_cons_of_eq {a b : Move} (h : a.isMsg = b.isMsg) (ms : List Move) :
    rounds (a :: b :: ms) = rounds (b :: ms) := by
  rw [rounds_cons_cons, if_pos h, Nat.zero_add]

/-- A transition between adjacent moves of different directions contributes one round. -/
lemma rounds_cons_cons_of_ne {a b : Move} (h : ¬ a.isMsg = b.isMsg) (ms : List Move) :
    rounds (a :: b :: ms) = rounds (b :: ms) + 1 := by
  rw [rounds_cons_cons, if_neg h, Nat.add_comm]

/-! ## The one protocol interface -/

/-- A public-coin protocol, as a **reduction of knowledge** from the input relation `In` to
the output relation `Out`: the prover claims knowledge of an `In`-witness for a statement
`x`, and after the conversation the claim has been reduced to knowledge of an `Out`-witness
— the (virtual) final message, which is *not sent* — for the statement `reduce x c`
derives. `reduce` returning `none` is rejection; there is no separate verifier. -/
structure Reduction where
  /-- The input relation: what the prover claims to know a witness for. -/
  In : Rel
  /-- The output relation: what remains to be proven after the conversation. -/
  Out : Rel
  /-- The conversation shape. -/
  moves : List Move
  /-- Process a conversation: reject (`none`) or derive the output statement (`some`). -/
  reduce : In.Stmt → Conversation moves → Option Out.Stmt

namespace Reduction

/-- "Composition is done": nothing remains to be proven. A closed reduction is a complete
protocol; its classical acceptance predicate is `Sigma.Reduction.accepts`. -/
def Closed (R : Reduction) : Prop := R.Out = Rel.trivial

/-- Classical acceptance of a **closed** reduction: the reduce map succeeds. This is only
meaningful once composition is done (`R.Closed`) — for an open reduction, acceptance is
relative to an output witness (`Sigma.Reduction.Accepting`) — so the hypothesis is part of
the signature. On a closed reduction it is the full verification predicate
(`Sigma.Reduction.Closed.accepting_iff_accepts`). -/
def accepts (R : Reduction) (_hR : R.Closed) (x : R.In.Stmt) (c : Conversation R.moves) :
    Bool :=
  (R.reduce x c).isSome

/-- A conversation, together with an output witness for the statement it derives, is
**accepting**: `reduce` succeeds and the output witness satisfies the output relation. This
is the uniform acceptance notion: completeness produces accepting pairs, and knowledge
soundness extracts from trees of accepting pairs. -/
def Accepting (R : Reduction) (x : R.In.Stmt) (c : Conversation R.moves) (z : R.Out.Wit) :
    Prop :=
  ∃ s, R.reduce x c = some s ∧ R.Out.rel s z = true

/-- For a closed reduction the output witness carries no information, and `Accepting`
collapses to classical acceptance. -/
lemma Closed.accepting_iff_accepts {R : Reduction} (hR : R.Closed) (x : R.In.Stmt)
    (c : Conversation R.moves) (z : R.Out.Wit) :
    R.Accepting x c z ↔ R.accepts hR x c = true := by
  obtain ⟨In, Out, moves, reduce⟩ := R
  obtain rfl : Out = Rel.trivial := hR
  simp only [Accepting, accepts, Option.isSome_iff_exists]
  exact ⟨fun ⟨s, hs, _⟩ => ⟨s, hs⟩, fun ⟨s, hs⟩ => ⟨s, hs, rfl⟩⟩

/-! ## Completeness and honest-verifier zero-knowledge

The honest prover of a reduction outputs the conversation *together with* the output
witness it would hand to a continuation (for a closed reduction the latter is trivial).
The honest prover
and the simulator are supplied as explicit arguments. -/

/-- Honest completeness of a reduction for a supplied honest prover `H`: **a satisfied
input relation yields a satisfied output relation**. On every statement–witness pair
satisfying `In`, every (conversation, output-witness) pair the prover produces is accepting
— the reduce map succeeds and the output witness satisfies `Out` at the derived statement. -/
def Complete (R : Reduction)
    (H : R.In.Stmt → R.In.Wit → ProbComp (Conversation R.moves × R.Out.Wit)) : Prop :=
  ∀ x w, R.In.rel x w = true → ∀ p ∈ support (H x w), R.Accepting x p.1 p.2

/-- **Perfect honest-verifier zero-knowledge** of a reduction: for every valid
statement–witness pair, the witness-free simulator reproduces the honest prover's joint
distribution over the conversation and the output witness exactly. -/
def PerfectHVZK (R : Reduction)
    (H : R.In.Stmt → R.In.Wit → ProbComp (Conversation R.moves × R.Out.Wit))
    (S : R.In.Stmt → ProbComp (Conversation R.moves × R.Out.Wit)) : Prop :=
  ∀ x w, R.In.rel x w = true → 𝒟[H x w] = 𝒟[S x]

/-- **Honest-verifier zero-knowledge** of a reduction, to within total variation distance
`ζ`: the honest and simulated joint distributions over (conversation, output witness) are
`ζ`-close on every valid statement–witness pair. -/
def HVZK (R : Reduction)
    (H : R.In.Stmt → R.In.Wit → ProbComp (Conversation R.moves × R.Out.Wit))
    (S : R.In.Stmt → ProbComp (Conversation R.moves × R.Out.Wit)) (ζ : ℝ) : Prop :=
  ∀ x w, R.In.rel x w = true → tvDist (H x w) (S x) ≤ ζ

/-- Perfect HVZK is exactly HVZK with `ζ = 0`. -/
theorem perfectHVZK_iff_hvzk_zero (R : Reduction)
    (H : R.In.Stmt → R.In.Wit → ProbComp (Conversation R.moves × R.Out.Wit))
    (S : R.In.Stmt → ProbComp (Conversation R.moves × R.Out.Wit)) :
    R.PerfectHVZK H S ↔ R.HVZK H S 0 := by
  constructor
  · intro h x w hx
    exact le_of_eq ((tvDist_eq_zero_iff (H x w) (S x)).mpr (h x w hx))
  · intro h x w hx
    exact (tvDist_eq_zero_iff (H x w) (S x)).mp
      (le_antisymm (h x w hx) (tvDist_nonneg (H x w) (S x)))

end Reduction

end Sigma
