/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.DSL.Poly
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Endpoint DSL and formal semantics

The DSL has separate endpoint languages for the honest prover and verifier/reducer. Both
are indexed by the exact `List Sigma.Move` they implement, so a `send` contributes a
`Move.msg`, a `recv` of a prover message consumes a `Move.msg`, and a verifier `sample`
/ prover `recv` contributes a public-coin `Move.chal`.

The formal semantics are executable Lean functions:

* `Prover.run` samples prover-private randomness and public coins and produces a full
  `Conversation` together with the output witness.
* `Verifier.reduce` consumes a `Conversation`; any failed `assert` returns `none`.
* `Verifier.toReduction` lowers a verifier endpoint to the repository's canonical
  `Sigma.Reduction` record.

This is the intended replacement path for hand-written prover/verifier specifications:
protocol modules define endpoint programs, then export the old reduction/honest-prover
names by elaborating those programs.
-/

namespace Sigma.DSL

open OracleComp OracleSpec

/-- Honest prover endpoint. The only observable semantics are `run`, and protocol files
construct endpoints through the combinators in `Sigma.DSL.Prover`. -/
structure Prover (In Out : Rel) (ms : List Move) where
  /-- Execute the honest endpoint, producing the conversation and carried output witness. -/
  run : In.Stmt -> In.Wit -> ProbComp (Conversation ms × Out.Wit)
  /-- The support semantics generated compositionally from DSL operations. -/
  supportSpec : In.Stmt -> In.Wit -> Conversation ms × Out.Wit -> Prop
  /-- The generated support semantics agree with the probabilistic semantics. -/
  support_iff : ∀ x w p, p ∈ support (run x w) ↔ supportSpec x w p

/-- Verifier/reducer endpoint. The only observable semantics are `reduce`, and protocol
files construct endpoints through the combinators in `Sigma.DSL.Verifier`. -/
structure Verifier (In Out : Rel) (ms : List Move) where
  /-- Consume a conversation, rejecting with `none` or returning the derived statement. -/
  reduce : In.Stmt -> Conversation ms -> Option Out.Stmt

namespace Prover

/-- Return the output witness carried to the next reduction. -/
def ret {In Out : Rel} (w : In.Stmt -> In.Wit -> Out.Wit) : Prover In Out [] where
  run x wit := pure (PUnit.unit, w x wit)
  supportSpec x wit p := p = (PUnit.unit, w x wit)
  support_iff x wit p := by simp

/-- Sample prover-private randomness. This does not change the transcript shape. -/
def sample {In Out : Rel} {A : Type} [SampleableType A] {ms : List Move}
    (k : A -> Prover In Out ms) : Prover In Out ms where
  run x w := do
    let a <- uniformSample A
    (k a).run x w
  supportSpec x w p := ∃ a : A, (k a).supportSpec x w p
  support_iff x w p := by
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨a, _ha, hp⟩
      exact ⟨a, ((k a).support_iff x w p).mp hp⟩
    · rintro ⟨a, hp⟩
      exact ⟨a, by simp [support_uniformSample], ((k a).support_iff x w p).mpr hp⟩

/-- Send a prover message. The sent value is also bound for later code. -/
def send {In Out : Rel} {M : Type} {ms : List Move} (m : In.Stmt -> In.Wit -> M)
    (k : M -> Prover In Out ms) : Prover In Out (Move.msg M :: ms) where
  run x w := do
    let msg := m x w
    let rest <- (k msg).run x w
    pure ((msg, rest.1), rest.2)
  supportSpec x w p :=
    ∃ rest : Conversation ms × Out.Wit,
      (k (m x w)).supportSpec x w rest ∧ p = ((m x w, rest.1), rest.2)
  support_iff x w p := by
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨rest, hrest, hpure⟩
      rw [mem_support_pure_iff] at hpure
      exact ⟨rest, ((k (m x w)).support_iff x w rest).mp hrest, hpure⟩
    · rintro ⟨rest, hrest, hp⟩
      exact ⟨rest, ((k (m x w)).support_iff x w rest).mpr hrest, by simp [hp]⟩

/-- Receive a public-coin challenge. Honest execution samples it. -/
def recv {In Out : Rel} {C : Type} [SampleableType C] {ms : List Move}
    (k : C -> Prover In Out ms) : Prover In Out (Move.chal C :: ms) where
  run x w := do
    let c <- uniformSample C
    let rest <- (k c).run x w
    pure ((c, rest.1), rest.2)
  supportSpec x w p :=
    ∃ c : C, ∃ rest : Conversation ms × Out.Wit,
      (k c).supportSpec x w rest ∧ p = ((c, rest.1), rest.2)
  support_iff x w p := by
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨c, _hc, hcont⟩
      rw [mem_support_bind_iff] at hcont
      rcases hcont with ⟨rest, hrest, hpure⟩
      rw [mem_support_pure_iff] at hpure
      exact ⟨c, rest, ((k c).support_iff x w rest).mp hrest, hpure⟩
    · rintro ⟨c, rest, hrest, hp⟩
      refine ⟨c, by simp [support_uniformSample], ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨rest, ((k c).support_iff x w rest).mpr hrest, by simp [hp]⟩

@[simp]
lemma mem_support_ret_iff {In Out : Rel} (out : In.Stmt -> In.Wit -> Out.Wit)
    (x : In.Stmt) (w : In.Wit) (p : Conversation [] × Out.Wit) :
    p ∈ support ((ret out).run x w) ↔ p = (PUnit.unit, out x w) := by
  simp [ret]

@[simp]
lemma mem_support_sample_iff {In Out : Rel} {A : Type} [SampleableType A]
    {ms : List Move} (k : A -> Prover In Out ms) (x : In.Stmt) (w : In.Wit)
    (p : Conversation ms × Out.Wit) :
    p ∈ support ((sample k).run x w) ↔ ∃ a : A, p ∈ support ((k a).run x w) := by
  constructor
  · intro hp
    rcases ((sample k).support_iff x w p).mp hp with ⟨a, hp⟩
    exact ⟨a, ((k a).support_iff x w p).mpr hp⟩
  · rintro ⟨a, hp⟩
    exact ((sample k).support_iff x w p).mpr ⟨a, ((k a).support_iff x w p).mp hp⟩

@[simp]
lemma mem_support_send_iff {In Out : Rel} {M : Type} {ms : List Move}
    (msg : In.Stmt -> In.Wit -> M) (k : M -> Prover In Out ms)
    (x : In.Stmt) (w : In.Wit) (p : Conversation (Move.msg M :: ms) × Out.Wit) :
    p ∈ support ((send msg k).run x w) ↔
      ∃ rest : Conversation ms × Out.Wit,
        rest ∈ support ((k (msg x w)).run x w) ∧ p = ((msg x w, rest.1), rest.2) := by
  constructor
  · intro hp
    rcases ((send msg k).support_iff x w p).mp hp with ⟨rest, hrest, hp⟩
    exact ⟨rest, ((k (msg x w)).support_iff x w rest).mpr hrest, hp⟩
  · rintro ⟨rest, hrest, hp⟩
    exact ((send msg k).support_iff x w p).mpr
      ⟨rest, ((k (msg x w)).support_iff x w rest).mp hrest, hp⟩

@[simp]
lemma mem_support_recv_iff {In Out : Rel} {C : Type} [SampleableType C]
    {ms : List Move} (k : C -> Prover In Out ms) (x : In.Stmt) (w : In.Wit)
    (p : Conversation (Move.chal C :: ms) × Out.Wit) :
    p ∈ support ((recv k).run x w) ↔
      ∃ c : C, ∃ rest : Conversation ms × Out.Wit,
        rest ∈ support ((k c).run x w) ∧ p = ((c, rest.1), rest.2) := by
  constructor
  · intro hp
    rcases ((recv k).support_iff x w p).mp hp with ⟨c, rest, hrest, hp⟩
    exact ⟨c, rest, ((k c).support_iff x w rest).mpr hrest, hp⟩
  · rintro ⟨c, rest, hrest, hp⟩
    exact ((recv k).support_iff x w p).mpr
      ⟨c, rest, ((k c).support_iff x w rest).mp hrest, hp⟩

end Prover

namespace Verifier

/-- Return the derived output statement. -/
def ret {In Out : Rel} (s : In.Stmt -> Out.Stmt) : Verifier In Out [] where
  reduce x _ := some (s x)

/-- Receive a prover message. Tuple messages are ordinary message types. -/
def recv {In Out : Rel} {M : Type} {ms : List Move} (k : M -> Verifier In Out ms) :
    Verifier In Out (Move.msg M :: ms) where
  reduce x c := (k c.1).reduce x c.2

/-- Consume a public-coin challenge from the conversation. -/
def sample {In Out : Rel} {C : Type} {ms : List Move} (k : C -> Verifier In Out ms) :
    Verifier In Out (Move.chal C :: ms) where
  reduce x c := (k c.1).reduce x c.2

/-- Assert a public predicate. All assertions must be satisfied; otherwise reduction
returns `none`. -/
def assert {In Out : Rel} {ms : List Move} (p : In.Stmt -> Bool)
    (k : Verifier In Out ms) : Verifier In Out ms where
  reduce x c := if p x then k.reduce x c else none

/-- Lower a verifier endpoint to the canonical `Reduction` interface. -/
def toReduction {In Out : Rel} {ms : List Move} (v : Verifier In Out ms) : Reduction where
  In := In
  Out := Out
  moves := ms
  reduce := v.reduce

end Verifier

end Sigma.DSL
