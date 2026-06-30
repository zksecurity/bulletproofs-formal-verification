/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Constructions.ReductionCompose
import Sigma.Utils.Vec
import Sigma.Protocols.GBP.Arithmetization
import Sigma.Protocols.GBPImproved.Relation
import Sigma.Protocols.GBPImproved.Arithmetization

/-!
# The pre-binding-challenge ordering of the improved arithmetization

The message-ordering **variant** of the improved arithmetization in which the prover's full
opening `(τ_x, μ_L, μ_R, f_L(x), f_R(x))` is sent *before* the binding challenge `r`, on
which the conversation ends (a **closed** reduction: `Out = Rel.trivial`, no trailing dummy
message). This is **not** the protocol of record —
`Sigma.Protocols.GBPImproved.arithRed'` places the opening vectors *after* `r`, matching
the composition with the inner-product argument, and adds the binding offset — but it is kept as
the formal record of what the message ordering alone provides:

* because the two `r`-children of a node of the tree of accepting transcripts share the opening, the affine-in-`r`
  `eq2` pins the split openings *exactly* (`P_L` against `(𝐆, H)` only, `P_R` against
  `(𝐲⁻¹⊙𝐇, H)` only), so this ordering achieves the tight relation `R_GBP'` with **no binding
  offset** (`Sigma.Protocols.GBPImproved.arithRedPreR_sound`);
* with the opening (or an argument of knowledge of it) after `r`, the per-`r` opening of
  `P_L + r·P_R` may depend on `r`, stray `𝐇`-mass becomes absorbable, and the offset is what
  restores `R_GBP'` (see the scope note in `Sigma.Protocols.GBPImproved.ArithmetizationSound`).
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- The moves of the pre-`r`-ordering variant: the opening is the last message, and the
conversation ends on the binding challenge `r`. -/
@[reducible] def arithMovesPreR (F G : Type) [Monoid F] (n c : ℕ) : List Move :=
  [ .msg (G × G × G × G × G), .chal Fˣ, .chal Fˣ, .msg (Fin (2 * c + 5) → G),
    .chal Fˣ, .msg (F × F × F × (Fin n → F) × (Fin n → F)), .chal Fˣ ]

variable [DecidableEq F] [DecidableEq G]

/-- The verifier of the pre-`r`-ordering variant: identical to `arithVerify'` except that the
opening `(τ_x, μ_L, μ_R, a, b)` is read from the round-3 message (before `r`) and there is no
binding offset. -/
def arithVerifyPreR {n q m c : ℕ} (s : Statement F G n q m c)
    (cv : Conversation (arithMovesPreR F G n c)) : Bool :=
  let ⟨init, yu, zu, Tcoef, xu, opening, ru, _⟩ := cv
  let ⟨AL, AR, AO, SL, SR⟩ := init
  let y : F := ↑yu
  let z : F := ↑zu
  let x : F := ↑xu
  let ⟨τx, μL, μR, a, b⟩ := opening
  let r : F := ↑ru
  let vy := powers y n
  let yinv := vinv vy
  let vz := powers z q
  let wL := z • (vz ᵥ* s.WL)
  let wR := z • (vz ᵥ* s.WR)
  let wO := z • (vz ᵥ* s.WO)
  let wC := fun j => z • (vz ᵥ* s.WC j)
  let wV := z • (vz ᵥ* s.WV)
  let wc := z * ip vz s.cc
  let δ := ip (hadamard yinv wR) wL
  let h' := yinv ⊙ s.hs
  let h'' : Fin n → G := fun i => r • h' i
  let μ := μL + r * μR
  let tHat := ip a b
  let WtL := msm wL h'
  let WtR := msm (hadamard yinv wR) s.gs
  let WtO := msm (wO - vy) h'
  let Wtk := fun j => msm (wC j) h'
  let PL : G := (AL + WtR) + x • AO
              + (∑ j : Fin c, x ^ (j.val + 2) • s.AC j) + x ^ (c + 2) • SL
  let PR : G := (∑ j : Fin c, x ^ (c - j.val - 1) • Wtk j) + x ^ c • WtO
              + x ^ (c + 1) • (AR + WtL) + x ^ (c + 2) • SR
  let P : G := PL + r • PR
  decide (tHat • s.g + τx • s.h
      = x ^ (c + 1) • ((δ - wc) • s.g - msm wV s.V)
        + (∑ i : Fin (2 * c + 5), if i.val = c + 1 then (0 : G) else x ^ i.val • Tcoef i)) &&
  decide (P = msm a s.gs + msm b h'' + μ • s.h)

/-- The pre-`r`-ordering variant as a **closed** reduction for
`Sigma.Protocols.GBPImproved.rel`: everything is sent, the conversation ends on the binding
challenge `r`, and nothing remains to be proven. -/
def arithRedPreR (n q m c : ℕ) : Reduction where
  In := relGBP' F G n q m c
  Out := Rel.trivial
  moves := arithMovesPreR F G n c
  reduce := fun s c => if arithVerifyPreR s c then some PUnit.unit else none

end Sigma.Protocols.GBPImproved
