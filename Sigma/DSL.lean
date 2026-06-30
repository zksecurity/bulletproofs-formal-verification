/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.DSL.Types
import Sigma.DSL.Algebra
import Sigma.DSL.Poly
import Sigma.DSL.Endpoint

/-!
# Protocol DSL

This module re-exports the Lean-internal DSL for writing generic-group and generic-field
prover/verifier endpoints. The endpoint semantics live in `Sigma.DSL.Endpoint`; algebraic
surface notation and polynomial helpers are re-exported here for protocol modules and
future lowering passes.
-/
