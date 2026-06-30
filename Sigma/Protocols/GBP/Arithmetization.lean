/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Constructions.ReductionCompose
import Sigma.Utils.Vec
import Sigma.Protocols.GBP.Relation
import VCVio.OracleComp.Constructions.SampleableType

namespace Sigma.Protocols.GBP

open OracleComp OracleSpec
open scoped Matrix

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- The target monomial degree `n' = 2c+2` (`c` = number of vector commitments). -/
@[reducible] def nPrime (c : ℕ) : ℕ := 2 * c + 2

/-- The degree carried by the `i`-th transmitted coefficient commitment: the increasing
enumeration of `{c+1, …, 2n'+2} \ {n'}`, the support of the honest `t`-polynomial. (`f_L` has
no coefficient below degree `c+1`, so neither does `t = ⟨f_L, f_R⟩`; the special degree `n'`
is recomputed by the verifier and never sent.) The `{T_i}` message is the dense tuple of these
`3c+5` commitments: `c+1+i` below the gap at `n'`, `c+2+i` above it. -/
def tIdx {c : ℕ} (i : Fin (3 * c + 5)) : Fin (2 * nPrime c + 3) :=
  if (i : ℕ) ≤ c then ⟨c + 1 + (i : ℕ), by have := i.isLt; simp only [nPrime]; omega⟩
  else ⟨c + 2 + (i : ℕ), by have := i.isLt; simp only [nPrime]; omega⟩

/-- The transmitted degree, as a natural number (unfolding lemma for `tIdx`). -/
lemma tIdx_val {c : ℕ} (i : Fin (3 * c + 5)) :
    (tIdx i : ℕ) = if (i : ℕ) ≤ c then c + 1 + (i : ℕ) else c + 2 + (i : ℕ) := by
  rw [tIdx]; split <;> rfl

/-- The transmitted degrees avoid the special degree `n'` (the gap of the enumeration). -/
lemma tIdx_ne {c : ℕ} (i : Fin (3 * c + 5)) : (tIdx i : ℕ) ≠ nPrime c := by
  have := i.isLt
  rw [tIdx_val]
  split <;> (simp only [nPrime]; omega)

/-- The dense enumeration is injective: distinct slots carry distinct degrees. -/
lemma tIdx_inj {c : ℕ} : Function.Injective (tIdx (c := c)) := by
  intro i j h
  have hv : (tIdx i : ℕ) = (tIdx j : ℕ) := by rw [h]
  rw [tIdx_val, tIdx_val] at hv
  refine Fin.ext ?_
  split at hv <;> split at hv <;> omega

/-- The dense enumeration is onto the support: every degree `≥ c+1` other than `n'` is some
`tIdx i` (`d−(c+1)` below the gap, `d−(c+2)` above it). -/
lemma tIdx_surj {c : ℕ} (d : Fin (2 * nPrime c + 3)) (hge : c + 1 ≤ (d : ℕ))
    (hne : (d : ℕ) ≠ nPrime c) : ∃ i : Fin (3 * c + 5), tIdx i = d := by
  have hd := d.isLt
  simp only [nPrime] at hd hne
  by_cases hlt : (d : ℕ) ≤ 2 * c + 1
  · refine ⟨⟨(d : ℕ) - (c + 1), by omega⟩, Fin.ext ?_⟩
    rw [tIdx_val]
    show (if (d : ℕ) - (c + 1) ≤ c then c + 1 + ((d : ℕ) - (c + 1))
      else c + 2 + ((d : ℕ) - (c + 1))) = (d : ℕ)
    rw [if_pos (by omega)]
    omega
  · refine ⟨⟨(d : ℕ) - (c + 2), by omega⟩, Fin.ext ?_⟩
    rw [tIdx_val]
    show (if (d : ℕ) - (c + 2) ≤ c then c + 1 + ((d : ℕ) - (c + 2))
      else c + 2 + ((d : ℕ) - (c + 2))) = (d : ℕ)
    rw [if_neg (by omega)]
    omega

/-- The arithmetization's full opening `(τ_x, μ, f_L(x), f_R(x))` — the reduction's output
witness, never sent. -/
@[reducible] def Opening (F : Type) (n : ℕ) := F × F × (Fin n → F) × (Fin n → F)

/-- The moves of the arithmetization: first message `(A_I, A_O, S)`, the **adjacent**
challenges `y, z`, the coefficient commitments `{T_i}` — sent as a dense tuple, one
commitment per support degree `tIdx i` of the `t`-polynomial — and the challenge `x`. -/
@[reducible] def arithMoves (F G : Type) [Monoid F] (c : ℕ) : List Move :=
  [.msg (G × G × G), .chal Fˣ, .chal Fˣ, .msg (Fin (3 * c + 5) → G), .chal Fˣ]

/-- The arithmetization's output statement: the bases, the combined `T`-commitment target,
the commitment `P`, and the generator vectors — everything the two verifier equations
read. -/
structure ArithOpen (F G : Type) (n : ℕ) where
  /-- Scalar-commitment base `G`. -/
  g : G
  /-- Blinding base `H`. -/
  h : G
  /-- The combined `T`-commitment target of the `t`-polynomial equation. -/
  Tx : G
  /-- The commitment `P` the opening must hit. -/
  P : G
  /-- Generator vector `𝐆`. -/
  gs : Fin n → G
  /-- The `y`-folded generator vector `𝐡' = y⁻¹ ⊙ 𝐇`. -/
  hs : Fin n → G

variable [DecidableEq F] [DecidableEq G]

/-- The arithmetization's output relation: the opening `(τ_x, μ, f_L, f_R)` satisfies the
two verifier equations. -/
@[reducible] def relArith (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (n : ℕ) : Rel where
  Stmt := ArithOpen F G n
  Wit := Opening F n
  rel := fun s w =>
    decide (ip w.2.2.1 w.2.2.2 • s.g + w.1 • s.h = s.Tx) &&
    decide (s.P = msm w.2.2.1 s.gs + msm w.2.2.2 s.hs + w.2.1 • s.h)

/-- The Generalized Bulletproofs relation as a relation triple. -/
@[reducible] def relGBP (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (n q m c : ℕ) : Rel where
  Stmt := Statement F G n q m c
  Wit := Witness F n m c
  rel := rel

/-- The output statement of the arithmetization: recompute the public challenge vectors,
weights, `δ`, the commitment `P`, and the `T`-target (report lines 489–490). -/
def arithOut {n q m c : ℕ} (s : Statement F G n q m c)
    (cv : Conversation (arithMoves F G c)) : ArithOpen F G n :=
  let AI := cv.1.1
  let AO := cv.1.2.1
  let Scom := cv.1.2.2
  let y : F := ↑cv.2.1
  let z : F := ↑cv.2.2.1
  let Tcoef := cv.2.2.2.1
  let x : F := ↑cv.2.2.2.2.1
  let np := nPrime c
  let vy := powers y n
  let yinv := vinv vy
  let vz := powers z q
  let wL := z • (vz ᵥ* s.WL)
  let wR := z • (vz ᵥ* s.WR)
  let wO := z • (vz ᵥ* s.WO)
  let wC := fun k => z • (vz ᵥ* s.WC k)
  let wV := z • (vz ᵥ* s.WV)
  let wc := z * ip vz s.cc
  let δ := ip (hadamard yinv wR) wL
  let h' := yinv ⊙ s.hs
  let WtL := msm wL h'
  let WtR := msm (hadamard yinv wR) s.gs
  let WtO := msm (wO - vy) h'
  let Wtk := fun k => msm (wC k) h'
  -- The relation is written `… + W_V·v + c = 0` (not `= W_V·v + c`), so the `w_c` and `⟨w_V, V⟩`
  -- contributions are *subtracted* here (cf. monero-oxide `arithmetic_circuit_proof.rs`).
  { g := s.g
    h := s.h
    Tx := x ^ np • ((δ - wc) • s.g - msm wV s.V)
        + (∑ i : Fin (3 * c + 5), x ^ (tIdx i : ℕ) • Tcoef i)
    P := WtO + (∑ k : Fin c, x ^ (k.val + 1) • Wtk k)
        + x ^ (c + 1) • (AI + WtL + WtR)
        + (∑ k : Fin c, x ^ (np - (k.val + 1)) • s.AC k)
        + x ^ np • AO + x ^ (np + 1) • Scom
    gs := s.gs
    hs := h' }

/-- **The Generalized Bulletproofs arithmetization** as a reduction of knowledge from
`Sigma.Protocols.GBP.rel` to the opening relation `Sigma.Protocols.GBP.relArith`. The
reduce map only packages the output statement; both verifier equations live in the output
relation, on the never-sent opening. -/
def arithRed (n q m c : ℕ) : Reduction where
  In := relGBP F G n q m c
  Out := relArith F G n
  moves := arithMoves F G c
  reduce := fun s c => some (arithOut s c)

variable [SampleableType F] [SampleableType Fˣ]

/-- The honest arithmetization prover's **deterministic output assembly**: given the sampled
blinders `(α, β, ρ)`, masks `(s_L, s_R)`, challenges `(y, z, x)` and coefficient blinders `τ`,
build the conversation and the carried opening. Factoring this out of `arithRedHonest` lets the
zero-knowledge proof name the output map and reparameterize the randomness, rather than match a
large inlined `do`-block. -/
def arithAssemble {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c)
    (α β ρ : F) (sL sR : Fin n → F) (yu zu : Fˣ) (τ : Fin (3 * c + 5) → F) (xu : Fˣ) :
    Conversation (arithRed (F := F) (G := G) n q m c).moves
      × (arithRed (F := F) (G := G) n q m c).Out.Wit :=
  let AI : G := msm w.aL s.gs + msm w.aR s.hs + α • s.h
  let AO : G := msm w.aO s.gs + β • s.h
  let Scom : G := msm sL s.gs + msm sR s.hs + ρ • s.h
  let y : F := ↑yu
  let z : F := ↑zu
  let np := nPrime c
  let vy := powers y n
  let yinv := vinv vy
  let vz := powers z q
  let wL := z • (vz ᵥ* s.WL)
  let wR := z • (vz ᵥ* s.WR)
  let wO := z • (vz ᵥ* s.WO)
  let wC := fun k => z • (vz ᵥ* s.WC k)
  let wV := z • (vz ᵥ* s.WV)
  -- vector polynomials `f_L(X), f_R(X)` as coefficient families indexed by power `0..n'+1`
  let fL : Fin (np + 2) → (Fin n → F) := fun p =>
      (if (p : ℕ) = c + 1 then (fun i => w.aL i + wR i * yinv i) else 0)
      + (∑ k : Fin c, if (p : ℕ) = np - (k.val + 1) then w.aC k else 0)
      + (if (p : ℕ) = np then w.aO else 0)
      + (if (p : ℕ) = np + 1 then sL else 0)
  let fR : Fin (np + 2) → (Fin n → F) := fun p =>
      (if (p : ℕ) = 0 then (fun i => wO i - vy i) else 0)
      + (∑ k : Fin c, if (p : ℕ) = k.val + 1 then wC k else 0)
      + (if (p : ℕ) = c + 1 then (fun i => vy i * w.aR i + wL i) else 0)
      + (∑ k : Fin c, if (p : ℕ) = np - (k.val + 1) then (fun i => vy i * w.aux k i) else 0)
      + (if (p : ℕ) = np + 1 then (fun i => vy i * sR i) else 0)
  -- `t(X) = ⟨f_L(X), f_R(X)⟩`, coefficient by coefficient (a convolution)
  let tcoeff : ℕ → F := fun d => ∑ p : Fin (np + 2), ∑ ℓ : Fin (np + 2),
      if (p : ℕ) + (ℓ : ℕ) = d then ip (fL p) (fR ℓ) else 0
  let T : Fin (3 * c + 5) → G := fun i => tcoeff (tIdx i : ℕ) • s.g + τ i • s.h
  let x : F := ↑xu
  let fLx : Fin n → F := fun i => ∑ p : Fin (np + 2), x ^ (p : ℕ) * fL p i
  let fRx : Fin n → F := fun i => ∑ p : Fin (np + 2), x ^ (p : ℕ) * fR p i
  -- The `⟨w_V, γ⟩` term is subtracted (matching `arithOut`): the relation is `… + W_V·v + c = 0`.
  let τx : F := (∑ i : Fin (3 * c + 5), τ i * x ^ (tIdx i : ℕ))
                  - x ^ np * ip wV w.γ
  let μ : F := α * x ^ (c + 1) + β * x ^ np + ρ * x ^ (np + 1)
                + (∑ k : Fin c, w.γC k * x ^ (np - (k.val + 1)))
  (((AI, AO, Scom), yu, zu, T, xu, PUnit.unit), (τx, μ, fLx, fRx))

/-- The honest arithmetization prover: sample the blinders, masks, challenges and coefficient
blinders, then assemble the conversation and carried opening (`arithAssemble`). -/
def arithRedHonest {n q m c : ℕ} (s : Statement F G n q m c) (w : Witness F n m c) :
    ProbComp (Conversation (arithRed (F := F) (G := G) n q m c).moves
      × (arithRed (F := F) (G := G) n q m c).Out.Wit) := do
  let α ← uniformSample F
  let β ← uniformSample F
  let ρ ← uniformSample F
  let sL ← uniformSample (Fin n → F)
  let sR ← uniformSample (Fin n → F)
  let yu ← uniformSample Fˣ
  let zu ← uniformSample Fˣ
  let τ ← uniformSample (Fin (3 * c + 5) → F)
  let xu ← uniformSample Fˣ
  pure (arithAssemble s w α β ρ sL sR yu zu τ xu)

end Sigma.Protocols.GBP
