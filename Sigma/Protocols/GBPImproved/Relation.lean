/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Utils.Vec
import Sigma.Protocols.GBP.Relation

/-!
# The improved Generalized Bulletproofs relation `R_GBP'`

The improved protocol (report section "More Efficient Protocol with Tighter Security") proves a
*tighter* relation than `Sigma.Protocols.GBP.rel`: the vector commitments carry **no** `𝐇`-component,
so the witness has no auxiliary `aux⁽ⁱ⁾` openings. Everything else is unchanged, so we reuse the
`Statement` of the base relation verbatim and only redefine the witness and the relation.

The vector-commitment opening becomes `AC⁽ⁱ⁾ = ⟨aC⁽ⁱ⁾, 𝐆⟩ + γC⁽ⁱ⁾·H` (dropping `⟨aux⁽ⁱ⁾, 𝐇⟩`);
the binding challenge of the improved arithmetization is what forces any stray `𝐇`-component inert,
so this relation is provable exactly when the application guarantees `aux⁽ⁱ⁾ = 0`.

Dimensions: `n` gates, `q` constraints, `m` scalar commitments, `c` vector commitments.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP

open scoped Matrix

/-- The improved Generalized Bulletproofs witness: as in `Sigma.Protocols.GBP.Witness` but **without**
the auxiliary `𝐇`-openings `aux⁽ⁱ⁾`. -/
structure Witness (F : Type) (n m c : ℕ) where
  /-- Left wires `a_L`. -/
  aL : Fin n → F
  /-- Right wires `a_R`. -/
  aR : Fin n → F
  /-- Output wires `a_O`. -/
  aO : Fin n → F
  /-- Scalar-commitment openings `v_k`. -/
  v  : Fin m → F
  /-- Scalar-commitment blinders `γ_k`. -/
  γ  : Fin m → F
  /-- Pre-committed vectors `a_C⁽ⁱ⁾`. -/
  aC : Fin c → (Fin n → F)
  /-- Vector-commitment blinders `γ_C⁽ⁱ⁾`. -/
  γC : Fin c → F

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The improved Generalized Bulletproofs relation `R_GBP'`: identical to `Sigma.Protocols.GBP.rel`
except the vector-commitment openings carry no `𝐇`-component:
`AC⁽ⁱ⁾ = ⟨aC⁽ⁱ⁾, 𝐆⟩ + γC⁽ⁱ⁾·H` (no `⟨aux⁽ⁱ⁾, 𝐇⟩` term). The four families of equations:

* the `q` R1CS rows `0 = WL·aL + WR·aR + WO·aO + Σ WC⁽ⁱ⁾·aC⁽ⁱ⁾ + WV·v + c`,
* the Hadamard constraint `0 = aL ∘ aR − aO`,
* the (tightened) vector-commitment openings `AC⁽ⁱ⁾ = ⟨aC⁽ⁱ⁾, 𝐆⟩ + γC⁽ⁱ⁾·H`,
* the scalar-commitment openings `V_k = v_k·G + γ_k·H`. -/
def rel {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c) : Bool :=
  decide (s.WL *ᵥ w.aL + s.WR *ᵥ w.aR + s.WO *ᵥ w.aO
            + (∑ i, s.WC i *ᵥ w.aC i) + s.WV *ᵥ w.v + s.cc = 0) &&
  decide (hadamard w.aL w.aR - w.aO = 0) &&
  decide (∀ i, s.AC i = msm (w.aC i) s.gs + w.γC i • s.h) &&
  decide (∀ k, s.V k = w.v k • s.g + w.γ k • s.h)

end Sigma.Protocols.GBPImproved
