/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Utils.Vec

/-!
# Relations of the Bulletproofs inner-product argument

The statements and relations of the inner-product argument, shared by the protocol definition
(`Sigma.Protocols.IPA.InnerProduct`) and the value-folding adaptor (`Sigma.Protocols.IPA.ValueFold`):

* `IPStatement` / `relIP` — the standard (value-folded) inner-product relation
  `P = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩ + ⟨a, b⟩·u`.
* `IPStatementV` / `relIPV` — the inner-product relation with the value made explicit (report
  `R_IP`): `P = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩ + μ·H ∧ t̂ = ⟨a, b⟩`.
-/

namespace Sigma.Protocols.IPA

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## The standard inner-product relation -/

/-- The inner-product statement: commitment `P`, generator vectors `𝐠, 𝐡` of length
`2^(k+1)`, and the value-binding generator `u`. -/
structure IPStatement (F G : Type) (k : ℕ) where
  /-- The commitment `P`. -/
  P : G
  /-- Generator vector `𝐠`. -/
  gs : Fin (2 ^ (k + 1)) → G
  /-- Generator vector `𝐡`. -/
  hs : Fin (2 ^ (k + 1)) → G
  /-- Value-binding generator `u`. -/
  u : G

variable [DecidableEq F] [DecidableEq G]

/-- The inner-product relation `P = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩ + ⟨a, b⟩·u`. -/
def relIP {k : ℕ} (s : IPStatement F G k)
    (ab : (Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F)) : Bool :=
  decide (s.P = msm ab.1 s.gs + msm ab.2 s.hs + (ip ab.1 ab.2) • s.u)

/-! ## The value-explicit relation `R_IP` -/

/-- The inner-product statement with the value made explicit (report `R_IP`): commitment `P`,
generators `𝐠, 𝐡`, blinding base `H`, value base `G`, and the revealed blinding `μ` and claimed
inner product `t̂`. -/
structure IPStatementV (F G : Type) (k : ℕ) where
  /-- The commitment `P`. -/
  P : G
  /-- Generator vector `𝐠`. -/
  gs : Fin (2 ^ (k + 1)) → G
  /-- Generator vector `𝐡`. -/
  hs : Fin (2 ^ (k + 1)) → G
  /-- Blinding base `H`. -/
  hgen : G
  /-- Value base `G` (the fold uses `u = ξ·G`). -/
  ggen : G
  /-- Revealed blinding `μ`. -/
  mu : F
  /-- Claimed inner product `t̂`. -/
  tHat : F
  /-- The `t`-polynomial blinding `τx` (carried through to the arithmetization leaf; not used by
  the inner-product relation itself). -/
  tauX : F

/-- The `R_IP` relation: `P = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩ + μ·H  ∧  t̂ = ⟨a, b⟩`. -/
def relIPV {k : ℕ} (x : IPStatementV F G k)
    (ab : (Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F)) : Bool :=
  decide (x.P = msm ab.1 x.gs + msm ab.2 x.hs + x.mu • x.hgen ∧ x.tHat = ip ab.1 ab.2)

end Sigma.Protocols.IPA
