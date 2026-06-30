/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Definitions.Reduction

/-!
# Core surface types for the protocol DSL

This module contains the type-level conventions used by the endpoint DSL. The DSL is
embedded in Lean, so its formal semantics are Lean definitions over `Sigma.Rel`,
`Sigma.Move`, `Sigma.Conversation`, and `Sigma.Reduction`.

The main user-facing convention is the fixed-length vector type notation `[A; n]`, which is
definitionally `Fin n -> A`. This matches the existing GBP formalization, where scalar and
group vectors are functions out of a finite index type.
-/

namespace Sigma.DSL

universe u

/-- Endpoint role. This is metadata for DSL front-ends; the executable semantics are given
by the separate `Prover` and `Verifier` endpoint languages in `Sigma.DSL.Endpoint`. -/
inductive Role where
  /-- Prover endpoint. -/
  | prover
  /-- Verifier endpoint. -/
  | verifier
deriving DecidableEq, Repr

/-- Fixed-length vectors in the DSL. -/
abbrev Vec (A : Type u) (n : Nat) : Type u := Fin n -> A

/-- DSL notation for fixed-length vectors: `[F; n]` elaborates to `Fin n -> F`. -/
scoped notation "[" A "; " n "]" => Vec A n

end Sigma.DSL
