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
import VCVio.OracleComp.Constructions.SampleableType

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP

open OracleComp OracleSpec
open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- The moves of the improved arithmetization: the split first message, the adjacent
challenges `y, z`, the coefficient commitments, and the adjacent challenges `x, r` — on
which the conversation ends. The scalar openings `(τ_x, μ = μ_L + r·μ_R)` are carried in the
(virtual) final message, alongside the opening vectors. -/
@[reducible] def arithMoves' (F G : Type) [Monoid F] (c : ℕ) : List Move :=
  [ .msg (G × G × G × G × G), .chal Fˣ, .chal F,
    .msg (Fin (2 * c + 5) → G), .chal Fˣ, .chal Fˣ ]

/-- The improved arithmetization's output statement: the bases, the `T`-target, the
recombined commitment `P = P_L + r·P_R`, and the generator vectors `(𝐆, r·(𝐲⁻¹⊙𝐇))`. The
scalar openings `(τ_x, μ)` are *witness* components of the output relation, not statement
fields. -/
structure ArithOpen' (F G : Type) (n : ℕ) where
  /-- Scalar-commitment base `G`. -/
  g : G
  /-- Blinding base `H`. -/
  h : G
  /-- The combined `T`-commitment target of the `t`-polynomial equation. -/
  Tx : G
  /-- The recombined commitment `P = P_L + r·P_R`. -/
  P : G
  /-- Generator vector `𝐆`. -/
  gs : Fin n → G
  /-- The `r`-scaled `y`-folded generator vector `r·(𝐲⁻¹ ⊙ 𝐇)`. -/
  hs : Fin n → G

variable [DecidableEq F] [DecidableEq G]

/-- The improved arithmetization's output relation: the opening `(τ_x, μ, a, b)` satisfies
the two verifier equations, with `t̂ := ⟨a, b⟩`. -/
@[reducible] def relArith' (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (n : ℕ) : Rel where
  Stmt := ArithOpen' F G n
  Wit := F × F × (Fin n → F) × (Fin n → F)
  rel := fun s w =>
    decide (ip w.2.2.1 w.2.2.2 • s.g + w.1 • s.h = s.Tx) &&
    decide (s.P = msm w.2.2.1 s.gs + msm w.2.2.2 s.hs + w.2.1 • s.h)

/-- The improved Generalized Bulletproofs relation as a relation triple. -/
@[reducible] def relGBP' (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (n q m c : ℕ) : Rel where
  Stmt := Statement F G n q m c
  Wit := Witness F n m c
  rel := rel

/-- The output statement of the improved arithmetization: recompute the public challenge
vectors, weights, `δ`, the split commitments `P_L` (including the binding offset
`z^{q+1}·𝟙` on the mask slot) and `P_R`, recombine with the binding challenge `r`
(`P = P_L + r·P_R`, generators `r·(𝐲⁻¹⊙𝐇)`), and package the `T`-target. -/
def arithOut' {n q m c : ℕ} (s : Statement F G n q m c)
    (cv : Conversation (arithMoves' F G c)) : ArithOpen' F G n :=
  let ⟨init, yu, z, Tcoef, xu, ru, _⟩ := cv
  let ⟨AL, AR, AO, SL, SR⟩ := init
  let y : F := ↑yu
  let x : F := ↑xu
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
  -- The binding offset: a public full-support vector with the fresh weight `z^{q+1}`.
  let offL : Fin n → F := fun _ => z ^ (q + 1)
  let WtL := msm wL h'
  let WtR := msm (hadamard yinv wR) s.gs
  let WtO := msm (wO - vy) h'
  let Wtk := fun j => msm (wC j) h'
  let PL : G := (AL + WtR) + x • AO
              + (∑ j : Fin c, x ^ (j.val + 2) • s.AC j)
              + x ^ (c + 2) • (SL + msm offL s.gs)
  let PR : G := (∑ j : Fin c, x ^ (c - j.val - 1) • Wtk j) + x ^ c • WtO
              + x ^ (c + 1) • (AR + WtL) + x ^ (c + 2) • SR
  -- The relation is written `… + W_V·v + c = 0`, so `w_c` and `⟨w_V, V⟩` are *subtracted*
  -- in the `T`-target (cf. monero-oxide `arithmetic_circuit_proof.rs`). The binding offset
  -- needs no `eq1` correction: its slot has no partner at the target degree.
  { g := s.g
    h := s.h
    Tx := x ^ (c + 1) • ((δ - wc) • s.g - msm wV s.V)
        + (∑ i : Fin (2 * c + 5), if i.val = c + 1 then (0 : G) else x ^ i.val • Tcoef i)
    P := PL + r • PR
    gs := s.gs
    hs := h'' }

/-- **The improved Generalized Bulletproofs arithmetization** as a reduction of knowledge
from `Sigma.Protocols.GBPImproved.rel` to the opening relation
`Sigma.Protocols.GBPImproved.relArith'`. -/
def arithRed' (n q m c : ℕ) : Reduction where
  In := relGBP' F G n q m c
  Out := relArith' F G n
  moves := arithMoves' F G c
  reduce := fun s c => some (arithOut' s c)

variable [SampleableType F] [SampleableType Fˣ]

/-- The honest improved-arithmetization prover: sample the blinders and masking vectors
`s_L, s_R`, form the split commitments `(A_L, A_R, A_O, S_L, S_R)`, then on the challenges
`y, z, x` build the vector polynomials `f_L, f_R` (no `aux` term; the mask slot of `f_L`
carries the binding offset `z^{q+1}·𝟙`) and the coefficient commitments `{T_i}`; the binding
challenge `r` ends the conversation, and the (virtual) final message is
`(τ_x, μ_L + r·μ_R, f_L(x), f_R(x))` — the scalar openings and the opening vectors, carried
as the output witness. -/
def arithAssemble' {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    (αL αR β ρL ρR : F) (sL sR : Fin n → F) (yu : Fˣ) (z : F) (τ : Fin (2 * c + 5) → F)
    (xu ru : Fˣ) :
    Conversation (arithRed' (F := F) (G := G) n q m c).moves
      × (arithRed' (F := F) (G := G) n q m c).Out.Wit :=
  let AL : G := msm w.aL s.gs + αL • s.h
  let AR : G := msm w.aR s.hs + αR • s.h
  let AO : G := msm w.aO s.gs + β • s.h
  let SL : G := msm sL s.gs + ρL • s.h
  let SR : G := msm sR s.hs + ρR • s.h
  let y : F := ↑yu
  let vy := powers y n
  let yinv := vinv vy
  let vz := powers z q
  let wL := z • (vz ᵥ* s.WL)
  let wR := z • (vz ᵥ* s.WR)
  let wO := z • (vz ᵥ* s.WO)
  let wC := fun j => z • (vz ᵥ* s.WC j)
  let wV := z • (vz ᵥ* s.WV)
  -- The vector polynomials `f_L(X), f_R(X)` as coefficient families indexed by power `0..c+2`.
  -- The layout places each secret/weight on its own monomial so that the `2 + c` inner products of
  -- GBP Arith 4 all land on the *target monomial* `X^{c+1}` of `t(X) = ⟨f_L(X), f_R(X)⟩`:
  -- `(0,c+1)` pairs `a_L+w_R∘y⁻¹` with `y∘a_R+w_L`; `(1,c)` pairs `a_O` with `w_O−y`;
  -- `(j+2, c−j−1)` pairs `a_C⁽ʲ⁾` with `w_C⁽ʲ⁾`. (No `y∘aux` term — this is the tighter `R_GBP'`.)
  -- `f_L(X)`:  `X^0 ↦ a_L + w_R∘y⁻¹`,  `X^1 ↦ a_O`,  `X^{j+2} ↦ a_C⁽ʲ⁾`,
  --            `X^{c+2} ↦ s_L + z^{q+1}·𝟙` (the mask plus the binding offset).
  let fL : Fin (c + 3) → (Fin n → F) := fun p =>
      (if (p : ℕ) = 0 then (fun i => w.aL i + wR i * yinv i) else 0)
      + (if (p : ℕ) = 1 then w.aO else 0)
      + (∑ j : Fin c, if (p : ℕ) = j.val + 2 then w.aC j else 0)
      + (if (p : ℕ) = c + 2 then (fun i => sL i + z ^ (q + 1)) else 0)
  -- `f_R(X)`:  `X^{c−j−1} ↦ w_C⁽ʲ⁾`,  `X^c ↦ w_O − y`,  `X^{c+1} ↦ y∘a_R + w_L`,  `X^{c+2} ↦ y∘s_R`.
  let fR : Fin (c + 3) → (Fin n → F) := fun p =>
      (∑ j : Fin c, if (p : ℕ) = c - j.val - 1 then wC j else 0)
      + (if (p : ℕ) = c then (fun i => wO i - vy i) else 0)
      + (if (p : ℕ) = c + 1 then (fun i => vy i * w.aR i + wL i) else 0)
      + (if (p : ℕ) = c + 2 then (fun i => vy i * sR i) else 0)
  -- `t(X) = ⟨f_L(X), f_R(X)⟩`, coefficient by coefficient (a convolution)
  let tcoeff : ℕ → F := fun d => ∑ p : Fin (c + 3), ∑ ℓ : Fin (c + 3),
      if (p : ℕ) + (ℓ : ℕ) = d then ip (fL p) (fR ℓ) else 0
  let T : Fin (2 * c + 5) → G := fun i => tcoeff i.val • s.g + τ i • s.h
  let x : F := ↑xu
  let fLx : Fin n → F := fun i => ∑ p : Fin (c + 3), x ^ (p : ℕ) * fL p i
  let fRx : Fin n → F := fun i => ∑ p : Fin (c + 3), x ^ (p : ℕ) * fR p i
  let τx : F := (∑ i : Fin (2 * c + 5), if i.val = c + 1 then (0 : F) else τ i * x ^ i.val)
                  - x ^ (c + 1) * ip wV w.γ
  let μL : F := αL + β * x + (∑ j : Fin c, w.γC j * x ^ (j.val + 2)) + ρL * x ^ (c + 2)
  let μR : F := αR * x ^ (c + 1) + ρR * x ^ (c + 2)
  (((AL, AR, AO, SL, SR), yu, z, T, xu, ru, PUnit.unit),
    (τx, μL + (↑ru : F) * μR, fLx, fRx))

/-- The honest improved-arithmetization prover: sample the blinders, masks, challenges and
coefficient blinders, then assemble the conversation and carried opening (`arithAssemble'`). -/
def arithHonest' {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c) :
    ProbComp (Conversation (arithRed' (F := F) (G := G) n q m c).moves
      × (arithRed' (F := F) (G := G) n q m c).Out.Wit) := do
  let αL ← uniformSample F
  let αR ← uniformSample F
  let β ← uniformSample F
  let ρL ← uniformSample F
  let ρR ← uniformSample F
  let sL ← uniformSample (Fin n → F)
  let sR ← uniformSample (Fin n → F)
  let yu ← uniformSample Fˣ
  let z ← uniformSample F
  let τ ← uniformSample (Fin (2 * c + 5) → F)
  let xu ← uniformSample Fˣ
  let ru ← uniformSample Fˣ
  pure (arithAssemble' s w αL αR β ρL ρR sL sR yu z τ xu ru)

end Sigma.Protocols.GBPImproved
