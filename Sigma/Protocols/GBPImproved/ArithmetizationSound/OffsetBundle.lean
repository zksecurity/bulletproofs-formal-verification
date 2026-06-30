/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetExtract

/-!
# Offset-protocol soundness: bundle openings, `eq1` recoveries, and the candidate witness

The per-bundle inverse-Vandermonde opening coefficients of the offset protocol's two split
verifier polynomials, in **three blocks** each (`bcoefL`: the `𝐆`-quadrant, the `𝐇'`-stray
quadrant, and the interpolated `muLF`-blinder of `P_L`; `bcoefR`: the `𝐆`-stray quadrant,
the `𝐇'`-quadrant, and the interpolated `muRF`-blinder of `P_R`), with their correctness `bundle_openL/R`; the
`eq1` recoveries at target `c+1` (`eqDj/eqAj/eqCj`, `eq1_open` — using the child-`0` opening's
inner product, which `eq1` pins across the `r`-children); the candidate witness `candWitness`
(no `aux` fields; the `v, γ` recovery restricts to the first `q+1` of the `q+2` `z`-children);
and the unconditional clause 4 (`clause4_holds`). -/

namespace Sigma.Protocols.GBPImproved.Offset

open Sigma.Protocols.GBP Sigma.Protocols.GBPImproved
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## The per-bundle opening coefficients -/

/-- The opening coefficients (in the `(𝐆, 𝐲⁻¹⊙𝐇, h)` basis) of the `𝐆`-side verifier
coefficient `PcoefL' p` (with the offset folded into the `S_L`-argument),
inverse-Vandermonde-extracted from the per-node quadrants: the `a*`-quadrants, the
`β`-stray quadrants, and the interpolated `muLF`-blinders. -/
def bcoefL {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (p : Fin (2 * c + 5)) :
    (Fin n → F) × (Fin n → F) × F :=
  let vinvm := vandInv (fun l => (chalXO tree i j l)) p
  (∑ l, vinvm l • aStarF tree i j l,
   ∑ l, vinvm l • betaF tree i j l,
   ∑ l, vinvm l • muLF tree i j l)

/-- The opening coefficients of the `𝐇`-side verifier coefficient `PcoefR' ℓ`: the
`α`-stray quadrants, the `b*`-quadrants, and the interpolated `muRF`-blinders. -/
def bcoefR {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (ℓ : Fin (2 * c + 5)) :
    (Fin n → F) × (Fin n → F) × F :=
  let vinvm := vandInv (fun l => (chalXO tree i j l)) ℓ
  (∑ l, vinvm l • alphaF tree i j l,
   ∑ l, vinvm l • bStarF tree i j l,
   ∑ l, vinvm l • muRF tree i j l)

/-- **`𝐆`-side extraction correctness.** Under acceptance, `bcoefL i j p` is a genuine
three-block opening of the offset-shifted `PcoefL' p`. -/
lemma bundle_openL {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (p : Fin (2 * c + 5)) :
    PcoefL' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
        (rootO tree).1 (rootO tree).2.2.1
        ((rootO tree).2.2.2.1
          + msm (fun _ => (chalZO tree i j) ^ (q + 1)) s.gs) p
      = msm (bcoefL s tree i j p).1 s.gs
        + msm (bcoefL s tree i j p).2.1 (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
        + (bcoefL s tree i j p).2.2 • s.h := by
  have hext := coeff_open3 s.gs (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs) s.h
    (PcoefL' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
      (rootO tree).1 (rootO tree).2.2.1
      ((rootO tree).2.2.2.1
        + msm (fun _ => (chalZO tree i j) ^ (q + 1)) s.gs))
    (fun l => (chalXO tree i j l)) (chalX_inj tree i j)
    (fun l => aStarF tree i j l) (fun l => betaF tree i j l)
    (fun l => muLF tree i j l)
    (fun l => (node_quad_open s tree hacc i j l).1) p
  rw [hext]; simp only [bcoefL, vandInv_eq (chalX_inj tree i j)]

/-- **`𝐇`-side extraction correctness.** Under acceptance, `bcoefR i j ℓ` is a genuine
three-block opening of `PcoefR' ℓ`. -/
lemma bundle_openR {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (ℓ : Fin (2 * c + 5)) :
    PcoefR' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
        (rootO tree).2.1 (rootO tree).2.2.2.2 ℓ
      = msm (bcoefR s tree i j ℓ).1 s.gs
        + msm (bcoefR s tree i j ℓ).2.1 (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)
        + (bcoefR s tree i j ℓ).2.2 • s.h := by
  have hext := coeff_open3 s.gs (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs) s.h
    (PcoefR' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
      (rootO tree).2.1 (rootO tree).2.2.2.2)
    (fun l => (chalXO tree i j l)) (chalX_inj tree i j)
    (fun l => alphaF tree i j l) (fun l => bStarF tree i j l)
    (fun l => muRF tree i j l)
    (fun l => (node_quad_open s tree hacc i j l).2) ℓ
  rw [hext]; simp only [bcoefR, vandInv_eq (chalX_inj tree i j)]

/-! ## `eq1` recoveries at target `c+1` -/

/-- The `eq1` special degree-`(c+1)` coefficient `D` (the public `g`-part `δ − w_c`) at bundle
`(i, j)`. -/
def eqDj {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : F :=
  ip (hadamard (vinv (powers ((chalYO tree i : Fˣ) : F) n))
        ((chalZO tree i j)
          • (powers (chalZO tree i j) q ᵥ* s.WR)))
      ((chalZO tree i j)
        • (powers (chalZO tree i j) q ᵥ* s.WL))
    - (chalZO tree i j)
        * ip (powers (chalZO tree i j) q) s.cc

/-- The recovered `eq1` `g`-coefficient of `⟨w_V, V⟩` at bundle `(i, j)`: `D` minus the
inverse-Vandermonde of the child-`0` inner products `⟨a₀, b₀⟩`. -/
def eqAj {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : F :=
  eqDj s tree i j - ∑ l, vandInv (fun l => (chalXO tree i j l)) ⟨c + 1, by omega⟩ l
    * ip (leafA tree i j l 0) (leafB tree i j l 0)

/-- The recovered `eq1` `h`-coefficient of `⟨w_V, V⟩` at bundle `(i, j)`
(inverse-Vandermonde of the child-`0` `τ_x`-openings). -/
def eqCj {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : F :=
  -∑ l, vandInv (fun l => (chalXO tree i j l)) ⟨c + 1, by omega⟩ l
    * leafTau tree i j l 0

/-- **eq1 opening at an arbitrary bundle.** The aggregate `msm (z·(𝐳·W_V)) V` is the
`(g, h)`-combination `eqAj·g + eqCj·h` recovered from the bundle's `x`-children (via the
child-`0` leaves). -/
lemma eq1_open {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) :
    msm ((chalZO tree i j)
        • (powers (chalZO tree i j) q ᵥ* s.WV)) s.V
      = eqAj s tree i j • s.g + eqCj s tree i j • s.h := by
  have heq1 := fun (l : Fin (2 * c + 5)) =>
    verify_eq1 s (rootO tree).1 (rootO tree).2.1 (rootO tree).2.2.1
      (rootO tree).2.2.2.1 (rootO tree).2.2.2.2 (chalYO tree i)
      (chalZO tree i j) (rawXO tree i j l)
      (chalRO tree i j l 0)
      (tcomO tree i j) _ _ _ _ (path_verify s tree hacc i j l 0)
  rw [eqAj, eqCj, eqDj]
  simp only [vandInv_eq (chalX_inj tree i j)]
  exact eq1_special_extract' (by omega) s.g s.h
    (msm ((chalZO tree i j)
      • (powers (chalZO tree i j) q ᵥ* s.WV)) s.V) _
    (fun l => (chalXO tree i j l)) (chalX_inj tree i j)
    _ _ _ heq1

/-! ## The candidate witness -/

/-- **The candidate witness, recovered (computably) from the transcript tree.** Every field is
a fixed inverse-Vandermonde combination of the per-node quadrants and blinders of the
`y`-branch `⟨0, hn⟩` (reference `z`-child `0`), plus the computed left inverse of `W_V` for the
`v, γ` openings (over the *first `q+1`* of the `q+2` `z`-children). No `aux` fields, no
discrete-log computation, no `Classical.choice` — interpolation is the polynomial-time Lagrange
form `Sigma.vandInv`, and `W_V` is inverted by Gaussian elimination (`Sigma.gaussLeftInv`). For
`n = 0` the witness is irrelevant and set to `0`.

* `aL` reads off the `bcoefL` `𝐆`-block at slot `0` minus the public `w_R∘y⁻¹`;
* `aR` reads off the `bcoefR` `𝐇'`-block at slot `c+1` minus the public `w_L`, rescaled;
* `aO`, `aC⁽ᵏ⁾`, `γ_C⁽ᵏ⁾` read off the `bcoefL` blocks at slots `1` and `k+2`. -/
def candWitness {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c) :
    Witness F n m c :=
  if hn : 0 < n then
    let yinv : Fin n → F := vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n)
    let zch : Fin (q + 1) → F := fun j =>
      (chalZO tree ⟨0, hn⟩ (Fin.castLE (by omega) j))
    let z0 : F := (chalZO tree ⟨0, hn⟩ 0)
    let wR' : Fin n → F := z0 • (powers z0 q ᵥ* s.WR)
    let wL' : Fin n → F := z0 • (powers z0 q ᵥ* s.WL)
    let cL : Fin (2 * c + 5) → (Fin n → F) × (Fin n → F) × F :=
      fun p => bcoefL s tree ⟨0, hn⟩ 0 p
    let cR : Fin (2 * c + 5) → (Fin n → F) × (Fin n → F) × F :=
      fun p => bcoefR s tree ⟨0, hn⟩ 0 p
    let pAC : Fin c → Fin (2 * c + 5) := fun k => ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩
    let Aj : Fin (q + 1) → F := fun j => eqAj s tree ⟨0, hn⟩ (Fin.castLE (by omega) j)
    let Cj : Fin (q + 1) → F := fun j => eqCj s tree ⟨0, hn⟩ (Fin.castLE (by omega) j)
    let Mmat : Matrix (Fin m) (Fin q) F := gaussLeftInv s.WV
    ⟨fun t => (cL ⟨0, by omega⟩).1 t - wR' t * yinv t,
     fun t => ((cR ⟨c + 1, by omega⟩).2.1 t - wL' t) * yinv t,
     (cL ⟨1, by omega⟩).1,
     fun k => ∑ ℓ : Fin q, Mmat k ℓ * (∑ j, vandInv zch ℓ.succ j * Aj j),
     fun k => ∑ ℓ : Fin q, Mmat k ℓ * (∑ j, vandInv zch ℓ.succ j * Cj j),
     fun k => (cL (pAC k)).1,
     fun k => (cL (pAC k)).2.2⟩
  else ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- **Clause 4 holds under acceptance** (with `W_V` full column rank): the scalar-commitment
openings are recovered from the `eq1` `(c+1)`-coefficients over the first `q+1` `z`-children
(`eq1_open` + `V_recover` + the Gaussian-elimination left inverse `gaussLeftInv s.WV`). -/
lemma clause4_holds {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree) (k : Fin m) :
    s.V k = (candWitness s tree).v k • s.g + (candWitness s tree).γ k • s.h := by
  have hI : ∀ j : Fin (q + 1),
      msm ((chalZO tree ⟨0, hn⟩ (Fin.castLE (by omega) j))
        • (powers (chalZO tree ⟨0, hn⟩ (Fin.castLE (by omega) j)) q
            ᵥ* s.WV)) s.V
      = eqAj s tree ⟨0, hn⟩ (Fin.castLE (by omega) j) • s.g
        + eqCj s tree ⟨0, hn⟩ (Fin.castLE (by omega) j) • s.h :=
    fun j => eq1_open s tree hacc ⟨0, hn⟩ (Fin.castLE (by omega) j)
  have hV := V_recover s (fun j : Fin (q + 1) =>
      (chalZO tree ⟨0, hn⟩ (Fin.castLE (by omega) j)))
    (chalZres_inj tree ⟨0, hn⟩) (gaussLeftInv s.WV) (gaussLeftInv_correct s.WV s.hWV)
    (fun j => eqAj s tree ⟨0, hn⟩ (Fin.castLE (by omega) j))
    (fun j => eqCj s tree ⟨0, hn⟩ (Fin.castLE (by omega) j)) hI k
  simp only [candWitness, dif_pos hn,
    vandInv_eq (chalZres_inj tree ⟨0, hn⟩)]
  exact hV

end Sigma.Protocols.GBPImproved.Offset
