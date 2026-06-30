/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.DSL.Types
import Sigma.Utils.Vec

/-!
# Algebraic notation for the protocol DSL

The DSL uses one inner-product notation for both scalar inner products and multi-scalar
multiplication:

* `⟪a, b⟫ : F` for `a b : [F; n]`;
* `⟪a, gs⟫ : G` for `a : [F; n]` and `gs : [G; n]`.

The notation is backed by a small typeclass so future backends can add more vector-like
containers without changing protocol code.
-/

namespace Sigma.DSL

universe u

/-- Overloaded inner-product/MSM operation used by the DSL surface syntax. -/
class Inner (A B C : Type u) where
  /-- Evaluate the inner-product-like operation. -/
  inner : A -> B -> C

export Inner (inner)

/-- Scalar-vector inner product. -/
instance (priority := 1000) ipInner {F ι : Type} [Field F] [Fintype ι] :
    Inner (ι -> F) (ι -> F) F where
  inner := Sigma.ip

/-- Multi-scalar multiplication, written with the same inner-product notation. -/
instance (priority := 100) msmInner {F G ι : Type} [Field F] [AddCommGroup G]
    [Module F G] [Fintype ι] : Inner (ι -> F) (ι -> G) G where
  inner := Sigma.msm

scoped notation "⟪" a ", " b "⟫" => Inner.inner a b

end Sigma.DSL
