/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Utils.Vec

/-!
# The Generalized Bulletproofs relation

Statement, witness, and relation for Generalized Bulletproofs (report section
"Generalized Bulletproofs"). The witness is `(aL, aR, aO)`, the scalar-commitment openings
`v` and the pre-committed vectors `aC⁽ⁱ⁾` (with auxiliary `aux⁽ⁱ⁾`), together with their
blinders. The relation checks the four equations:

* the `q` R1CS rows `0 = WL·aL + WR·aR + WO·aO + Σ WC⁽ⁱ⁾·aC⁽ⁱ⁾ + WV·v + c`,
* the Hadamard constraint `0 = aL ∘ aR − aO`,
* the vector-commitment openings `AC⁽ⁱ⁾ = ⟨aC⁽ⁱ⁾, 𝐆⟩ + ⟨aux⁽ⁱ⁾, 𝐇⟩ + γC⁽ⁱ⁾·H`,
* the scalar-commitment openings `V_k = v_k·G + γ_k·H`.

Dimensions: `n` gates, `q` constraints, `m` scalar commitments, `c` vector commitments.
-/

namespace Sigma.Protocols.GBP

open scoped Matrix

/-- Public inputs of a Generalized Bulletproofs instance: the generators, the weight
matrices with constant `c`, and the vector/scalar commitments. -/
structure Statement (F G : Type) [Field F] (n q m c : ℕ) where
  /-- Generator vector `𝐆`. -/
  gs : Fin n → G
  /-- Generator vector `𝐇`. -/
  hs : Fin n → G
  /-- Scalar-commitment base `G`. -/
  g  : G
  /-- Blinding base `H`. -/
  h  : G
  /-- Left weight matrix `W_L`. -/
  WL : Matrix (Fin q) (Fin n) F
  /-- Right weight matrix `W_R`. -/
  WR : Matrix (Fin q) (Fin n) F
  /-- Output weight matrix `W_O`. -/
  WO : Matrix (Fin q) (Fin n) F
  /-- Per-vector-commitment weight matrices `W_C⁽ⁱ⁾`. -/
  WC : Fin c → Matrix (Fin q) (Fin n) F
  /-- Scalar-commitment weight matrix `W_V`. -/
  WV : Matrix (Fin q) (Fin m) F
  /-- Constant vector (the report writes it bold, distinct from the italic scalar count `c` =
  number of vector commitments). Field named `cc`, not `c`: Lean identifiers carry no bold/italic
  distinction, so the bare `c` is reserved for the vector-commitment count. -/
  cc : Fin q → F
  /-- Vector commitments `A_C⁽ⁱ⁾`. -/
  AC : Fin c → G
  /-- Scalar commitments `V_k`. -/
  V  : Fin m → G
  /-- **`W_V` has full column rank `m`**: some choice of `m` rows forms an invertible minor.
  The scalar commitments `V_k` enter the protocol only through the aggregate `msm wV V`, so without
  full rank an accepting transcript pins down only combinations `∑ₖ W_V[ℓ,k]·V_k`, not the individual
  `V_k` — and a malformed `V_k ∉ span(g,h)` can accept with no witness and no discrete-log relation.
  Requiring it here makes the relation extractable: the soundness extractor inverts `W_V` — in
  polynomial time, by Gaussian elimination (`Sigma.gaussLeftInv`). -/
  hWV : ∃ r : Fin m → Fin q, (WV.submatrix r id).det ≠ 0

/-- The Generalized Bulletproofs witness: the wire assignments, the scalar-commitment
openings, the pre-committed vectors and their auxiliary parts, and all blinders. -/
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
  aC  : Fin c → (Fin n → F)
  /-- Auxiliary openings `aux⁽ⁱ⁾` (the `𝐇`-part of each vector commitment). -/
  aux : Fin c → (Fin n → F)
  /-- Vector-commitment blinders `γ_C⁽ⁱ⁾`. -/
  γC  : Fin c → F

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The Generalized Bulletproofs relation: `rel s w = true` iff the witness `w` satisfies all
four families of equations of the statement `s`. -/
def rel {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c) : Bool :=
  decide (s.WL *ᵥ w.aL + s.WR *ᵥ w.aR + s.WO *ᵥ w.aO
            + (∑ i, s.WC i *ᵥ w.aC i) + s.WV *ᵥ w.v + s.cc = 0) &&
  decide (hadamard w.aL w.aR - w.aO = 0) &&
  decide (∀ i, s.AC i = msm (w.aC i) s.gs + msm (w.aux i) s.hs + w.γC i • s.h) &&
  decide (∀ k, s.V k = w.v k • s.g + w.γ k • s.h)

end Sigma.Protocols.GBP
