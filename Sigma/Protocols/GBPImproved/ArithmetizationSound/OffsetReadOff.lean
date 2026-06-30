/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetBundle

/-!
# Offset-protocol soundness: collision candidates and read-offs

The `gens`-coefficient opening vectors of the two split verifier polynomials (three blocks
each), the structural candidates — the `A_L`/`S_L`/`A_R` commitments after public subtraction
(`alCand`/`slCand`/`arCand`; the `S_L` public part is the **binding offset** `z^{q+1}·𝟙`), the
public `𝐇`-side slots (`pubVecR`), cross-bundle differences, high-degree openings, the `eq1`
`(g,h)` collision `ghCand` — plus the two candidate families specific to the post-`r` opening:

* `famCand` (per `(i,j,l)`): the third `r`-child's opening — vectors *and* blinder — either
  lies on the family interpolated from the first two children, or its deviation is a
  discrete-log relation;
* `tHatCand` (per `(i,j,l)`, children `1, 2`): `eq1`'s right-hand side is fixed before `r`, so
  the openings `(⟨a_e, b_e⟩, τ_{x,e})` agree across the `r`-children or their difference is a
  relation on `(g, h)`.

Everything opens against `gens s = (𝐆, 𝐇, g, h)`; `bundleCands`/`relCandList`/`relCand`
package the candidates with the uniform `msm · gens = 0` proof.
-/

namespace Sigma.Protocols.GBPImproved.Offset

open Sigma.Protocols.GBP Sigma.Protocols.GBPImproved
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## Opening vectors against `gens` -/

/-- The `gens`-coefficient vector of the bundle-`(i,j)` opening of the (offset-shifted)
`PcoefL' p`: `𝐆`-quadrant, `𝐇`-rescaled stray quadrant, and `μ_L`-part. -/
def pOpenVecL {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (p : Fin (2 * c + 5)) : Fin (n + n + 2) → F :=
  gvec (bcoefL s tree i j p).1
    (hadamard (bcoefL s tree i j p).2.1 (vinv (powers ((chalYO tree i : Fˣ) : F) n)))
    (bcoefL s tree i j p).2.2

/-- `pOpenVecL i j p` is a `gens`-opening of the offset-shifted `PcoefL' p`. -/
lemma pOpenVecL_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (p : Fin (2 * c + 5)) :
    msm (pOpenVecL s tree i j p) (gens s)
      = PcoefL' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
          (rootO tree).1 (rootO tree).2.2.1
          ((rootO tree).2.2.2.1
            + msm (fun _ => (chalZO tree i j) ^ (q + 1)) s.gs) p := by
  have hconv : msm (hadamard (bcoefL s tree i j p).2.1
        (vinv (powers ((chalYO tree i : Fˣ) : F) n))) s.hs
      = msm (bcoefL s tree i j p).2.1 (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs) :=
    (msm_vsmul _ _ _).symm
  rw [pOpenVecL, gvec, gens_msm, zero_smul, add_zero, hconv]
  exact (bundle_openL s tree hacc i j p).symm

/-- The `gens`-coefficient vector of the bundle-`(i,j)` opening of `PcoefR' ℓ`. -/
def pOpenVecR {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (ℓ : Fin (2 * c + 5)) : Fin (n + n + 2) → F :=
  gvec (bcoefR s tree i j ℓ).1
    (hadamard (bcoefR s tree i j ℓ).2.1 (vinv (powers ((chalYO tree i : Fˣ) : F) n)))
    (bcoefR s tree i j ℓ).2.2

/-- `pOpenVecR i j ℓ` is a `gens`-opening of `PcoefR' ℓ`. -/
lemma pOpenVecR_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (ℓ : Fin (2 * c + 5)) :
    msm (pOpenVecR s tree i j ℓ) (gens s)
      = PcoefR' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
          (rootO tree).2.1 (rootO tree).2.2.2.2 ℓ := by
  have hconv : msm (hadamard (bcoefR s tree i j ℓ).2.1
        (vinv (powers ((chalYO tree i : Fˣ) : F) n))) s.hs
      = msm (bcoefR s tree i j ℓ).2.1 (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs) :=
    (msm_vsmul _ _ _).symm
  rw [pOpenVecR, gvec, gens_msm, zero_smul, add_zero, hconv]
  exact (bundle_openR s tree hacc i j ℓ).symm

/-! ## Structural candidates -/

/-- The `gens`-vector opening the public pure-`𝐆` part `W̃_R` of the slot-`0` coefficient. -/
def alPubVec {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : Fin (n + n + 2) → F :=
  gvec (hadamard (vinv (powers ((chalYO tree i : Fˣ) : F) n))
      ((chalZO tree i j)
        • (powers (chalZO tree i j) q ᵥ* s.WR))) 0 0

omit [DecidableEq F] [DecidableEq G] in
lemma alPubVec_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) :
    msm (alPubVec s tree i j) (gens s)
      = msm (hadamard (vinv (powers ((chalYO tree i : Fˣ) : F) n))
          ((chalZO tree i j)
            • (powers (chalZO tree i j) q ᵥ* s.WR))) s.gs := by
  rw [alPubVec, gvec, gens_msm, msm_zero_left, zero_smul, zero_smul, add_zero, add_zero,
    add_zero]

/-- The `gens`-vector opening the **binding offset** `⟨z^{q+1}·𝟙, 𝐆⟩` — the public pure-`𝐆`
part of the slot-`(c+2)` coefficient. -/
def slPubVec {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : Fin (n + n + 2) → F :=
  gvec (fun _ => (chalZO tree i j) ^ (q + 1)) 0 0

omit [DecidableEq F] [DecidableEq G] in
lemma slPubVec_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) :
    msm (slPubVec s tree i j) (gens s)
      = msm (fun _ => (chalZO tree i j) ^ (q + 1)) s.gs := by
  rw [slPubVec, gvec, gens_msm, msm_zero_left, zero_smul, zero_smul, add_zero, add_zero,
    add_zero]

/-- The `gens`-vector opening of the commitment `A_L` at bundle `(i,j)`. -/
def alCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : Fin (n + n + 2) → F :=
  pOpenVecL s tree i j ⟨0, by omega⟩ - alPubVec s tree i j

lemma alCand_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) :
    msm (alCand s tree i j) (gens s) = (rootO tree).1 := by
  rw [alCand, msm_sub_left, pOpenVecL_opens s tree hacc i j ⟨0, by omega⟩, alPubVec_opens,
    PcoefL'_AL]
  abel

/-- The `gens`-vector opening of the commitment `S_L` at bundle `(i,j)`: the slot-`(c+2)`
opening with the **binding offset subtracted off**. -/
def slCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : Fin (n + n + 2) → F :=
  pOpenVecL s tree i j ⟨c + 2, by omega⟩ - slPubVec s tree i j

lemma slCand_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) :
    msm (slCand s tree i j) (gens s) = (rootO tree).2.2.2.1 := by
  rw [slCand, msm_sub_left, pOpenVecL_opens s tree hacc i j ⟨c + 2, by omega⟩, slPubVec_opens,
    PcoefL'_SL]
  abel

/-- The `gens`-vector opening of the commitment `A_R` at bundle `(i,j)`. -/
def arCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : Fin (n + n + 2) → F :=
  pOpenVecR s tree i j ⟨c + 1, by omega⟩
    - hsVec ((chalZO tree i j)
        • (powers (chalZO tree i j) q ᵥ* s.WL))
      (vinv (powers ((chalYO tree i : Fˣ) : F) n))

lemma arCand_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) :
    msm (arCand s tree i j) (gens s) = (rootO tree).2.1 := by
  rw [arCand, msm_sub_left, pOpenVecR_opens s tree hacc i j ⟨c + 1, by omega⟩, hsVec_opens,
    PcoefR'_AR]
  abel

/-- **The public-`𝐇`-side collision candidate** at slot `ℓ` with public coefficient `cH`. -/
def pubVecR {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (ℓ : Fin (2 * c + 5)) (cH : Fin n → F) :
    Fin (n + n + 2) → F :=
  pOpenVecR s tree i j ℓ - hsVec cH (vinv (powers ((chalYO tree i : Fˣ) : F) n))

lemma pubVecR_msm {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (ℓ : Fin (2 * c + 5)) (cH : Fin n → F)
    (hP : PcoefR' s ((chalYO tree i : Fˣ) : F) (chalZO tree i j)
        (rootO tree).2.1 (rootO tree).2.2.2.2 ℓ
      = msm cH (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs)) :
    msm (pubVecR s tree i j ℓ cH) (gens s) = 0 := by
  rw [pubVecR, msm_sub_left, pOpenVecR_opens s tree hacc i j ℓ, hsVec_opens, hP, sub_self]

/-! ## The family- and value-consistency candidates -/

/-- **The quadrant-family candidate** at node `(i,j,l)`: the deviation of the third
`r`-child's opening — including its blinder `μ₂` against the interpolated `muLF + r₂·muRF` —
from the family interpolated by the first two. Always opens `0` (`famCand_msm_zero`); its
vanishing puts the third child on the family. -/
def famCand {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) : Fin (n + n + 2) → F :=
  gvec (aStarF tree i j l + rch tree i j l 2 • alphaF tree i j l - leafA tree i j l 2)
    (hadamard (betaF tree i j l + rch tree i j l 2 • bStarF tree i j l
        - rch tree i j l 2 • leafB tree i j l 2)
      (vinv (powers ((chalYO tree i : Fˣ) : F) n)))
    (muLF tree i j l + rch tree i j l 2 * muRF tree i j l - leafMu tree i j l 2)

set_option maxHeartbeats 800000 in
/-- The family candidate is a genuine relation: `msm · gens = 0` (substituting the quadrant
openings into the third child's `eq2`). -/
lemma famCand_msm_zero {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) :
    msm (famCand s tree i j l) (gens s) = 0 := by
  have h2 := verify_eq2 s (rootO tree).1 (rootO tree).2.1 (rootO tree).2.2.1
    (rootO tree).2.2.2.1 (rootO tree).2.2.2.2 (chalYO tree i) (chalZO tree i j)
    (rawXO tree i j l)
    (chalRO tree i j l 2)
    (tcomO tree i j)
    (leafTau tree i j l 2) (leafMu tree i j l 2)
    (leafA tree i j l 2) (leafB tree i j l 2) (path_verify s tree hacc i j l 2)
  have hq := node_quad_open s tree hacc i j l
  rw [hq.1, hq.2] at h2
  have hconv : msm (hadamard (betaF tree i j l + rch tree i j l 2 • bStarF tree i j l
        - rch tree i j l 2 • leafB tree i j l 2)
      (vinv (powers ((chalYO tree i : Fˣ) : F) n))) s.hs
      = msm (betaF tree i j l + rch tree i j l 2 • bStarF tree i j l
          - rch tree i j l 2 • leafB tree i j l 2)
        (vinv (powers ((chalYO tree i : Fˣ) : F) n) ⊙ s.hs) := (msm_vsmul _ _ _).symm
  rw [famCand, gvec, gens_msm, zero_smul, add_zero, hconv]
  simp only [msm_sub_left, msm_add_left, msm_smul_left]
  simp only [rch]
  linear_combination (norm := module) h2

/-- **The `t̂`-consistency candidate** at node `(i,j,l)`, child `e`: the differences of the
inner products `⟨a_e, b_e⟩ − ⟨a₀, b₀⟩` and of the `τ_x`-openings `τ_{x,e} − τ_{x,0}` as a
relation on `(g, h)`. Always opens `0` (`eq1`'s right-hand side is fixed before `r`). -/
def tHatCand {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) : Fin (n + n + 2) → F :=
  ghVec (ip (leafA tree i j l e) (leafB tree i j l e)
      - ip (leafA tree i j l 0) (leafB tree i j l 0))
    (leafTau tree i j l e - leafTau tree i j l 0)

/-- The `t̂`-consistency candidate is a genuine relation: `msm · gens = 0`. -/
lemma tHatCand_msm_zero {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3) :
    msm (tHatCand s tree i j l e) (gens s) = 0 := by
  have hc := verify_eq1 s (rootO tree).1 (rootO tree).2.1 (rootO tree).2.2.1
    (rootO tree).2.2.2.1 (rootO tree).2.2.2.2 (chalYO tree i) (chalZO tree i j)
    (rawXO tree i j l)
    (chalRO tree i j l e)
    (tcomO tree i j)
    (leafTau tree i j l e) (leafMu tree i j l e)
    (leafA tree i j l e) (leafB tree i j l e) (path_verify s tree hacc i j l e)
  have h0 := verify_eq1 s (rootO tree).1 (rootO tree).2.1 (rootO tree).2.2.1
    (rootO tree).2.2.2.1 (rootO tree).2.2.2.2 (chalYO tree i) (chalZO tree i j)
    (rawXO tree i j l)
    (chalRO tree i j l 0)
    (tcomO tree i j)
    (leafTau tree i j l 0) (leafMu tree i j l 0)
    (leafA tree i j l 0) (leafB tree i j l 0) (path_verify s tree hacc i j l 0)
  have hdiff := hc.trans h0.symm
  rw [tHatCand, ghVec_opens]
  linear_combination (norm := module) hdiff

/-! ## The `eq1` collision candidate -/

/-- **The eq1 `(g, h)` collision candidate at bundle `(i, j)`**: the recovered `eq1`
`(c+1)`-coefficient opening vs. the `candWitness`-`v/γ` reconstruction. -/
def ghCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) : Fin (n + n + 2) → F :=
  ghVec (eqAj s tree i j - ip ((chalZO tree i j)
            • (powers (chalZO tree i j) q ᵥ* s.WV))
          (candWitness s tree).v)
        (eqCj s tree i j - ip ((chalZO tree i j)
            • (powers (chalZO tree i j) q ᵥ* s.WV))
          (candWitness s tree).γ)

/-- The `ghCand` candidate is a genuine relation: `msm · gens = 0`. -/
lemma ghCand_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) :
    msm (ghCand s tree i j) (gens s) = 0 := by
  have he : eqAj s tree i j • s.g + eqCj s tree i j • s.h
      = ip ((chalZO tree i j)
            • (powers (chalZO tree i j) q ᵥ* s.WV))
          (candWitness s tree).v • s.g
        + ip ((chalZO tree i j)
            • (powers (chalZO tree i j) q ᵥ* s.WV))
          (candWitness s tree).γ • s.h :=
    (eq1_open s tree hacc i j).symm.trans
      (msm_wv_open s.V s.g s.h _ _ _ (fun k => clause4_holds hn s tree hacc k))
  rw [ghCand, ghVec_opens, sub_smul, sub_smul]
  rw [← sub_eq_zero] at he
  rw [← he]; abel

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- `ghCand = 0` is exactly `Heq` at bundle `(i, j)`. -/
lemma heq_of_ghCand_zero {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (h0 : (ghCand s tree i j : Fin (n + n + 2) → F) = 0) :
    eqAj s tree i j = ip ((chalZO tree i j)
        • (powers (chalZO tree i j) q ᵥ* s.WV))
      (candWitness s tree).v :=
  sub_eq_zero.mp (ghVec_eq_zero h0).1

/-! ## The candidate list -/

/-- **The per-bundle collision candidates** at bundle `(i, j)` (reference `(⟨0,hn⟩, 0)`):
the `A_L`/`A_O`/`S_L` and `A_R`/`S_R` cross-bundle differences (after the public — for `S_L`,
the binding-offset — subtractions), the public `W̃_O`/`W̃_C⁽ᵏ⁾` differences, the eq1 `(g,h)`
candidate, the high-degree openings of both sides, and the per-node quadrant-family and
`t̂`-consistency candidates. -/
def bundleCands {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c) (hn : 0 < n)
    (i : Fin n) (j : Fin (q + 2)) : List (Fin (n + n + 2) → F) :=
  (alCand s tree i j - alCand s tree ⟨0, hn⟩ 0)
    :: (pOpenVecL s tree i j ⟨1, by omega⟩ - pOpenVecL s tree ⟨0, hn⟩ 0 ⟨1, by omega⟩)
    :: (slCand s tree i j - slCand s tree ⟨0, hn⟩ 0)
    :: pubVecR s tree i j ⟨c, by omega⟩
        ((chalZO tree i j)
            • (powers (chalZO tree i j) q ᵥ* s.WO)
          - powers ((chalYO tree i : Fˣ) : F) n)
    :: (arCand s tree i j - arCand s tree ⟨0, hn⟩ 0)
    :: (pOpenVecR s tree i j ⟨c + 2, by omega⟩ - pOpenVecR s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩)
    :: ghCand s tree i j
    :: ((List.finRange c).map (fun (k : Fin c) =>
          pOpenVecL s tree i j ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩
            - pOpenVecL s tree ⟨0, hn⟩ 0 ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩)
      ++ (List.finRange c).map (fun (k : Fin c) =>
          pubVecR s tree i j ⟨c - (k : ℕ) - 1, by have := k.isLt; omega⟩
            ((chalZO tree i j)
              • (powers (chalZO tree i j) q ᵥ* s.WC k)))
      ++ ((List.finRange (2 * c + 5)).filter
            (fun (p : Fin (2 * c + 5)) => decide (c + 3 ≤ (p : ℕ)))).map
          (fun p => pOpenVecL s tree i j p)
      ++ ((List.finRange (2 * c + 5)).filter
            (fun (p : Fin (2 * c + 5)) => decide (c + 3 ≤ (p : ℕ)))).map
          (fun p => pOpenVecR s tree i j p)
      ++ (List.finRange (2 * c + 5)).map (fun l => famCand s tree i j l)
      ++ (List.finRange (2 * c + 5)).map (fun l => tHatCand s tree i j l 1)
      ++ (List.finRange (2 * c + 5)).map (fun l => tHatCand s tree i j l 2))

/-- **Every per-bundle candidate opens `0`.** -/
lemma bundleCands_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 2)) (rc : Fin (n + n + 2) → F)
    (hc : rc ∈ bundleCands s tree hn i j) :
    msm rc (gens s) = 0 := by
  rw [bundleCands] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, alCand_opens s tree hacc i j, alCand_opens s tree hacc ⟨0, hn⟩ 0,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, pOpenVecL_opens s tree hacc i j ⟨1, by omega⟩,
      pOpenVecL_opens s tree hacc ⟨0, hn⟩ 0 ⟨1, by omega⟩, PcoefL'_AO, PcoefL'_AO, sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, slCand_opens s tree hacc i j, slCand_opens s tree hacc ⟨0, hn⟩ 0,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · exact pubVecR_msm s tree hacc i j _ _ (PcoefR'_WtO s _ _ _ _)
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, arCand_opens s tree hacc i j, arCand_opens s tree hacc ⟨0, hn⟩ 0,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, pOpenVecR_opens s tree hacc i j ⟨c + 2, by omega⟩,
      pOpenVecR_opens s tree hacc ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩, PcoefR'_SR, PcoefR'_SR,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ghCand_msm_zero hn s tree hacc i j
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · rcases List.mem_append.mp hc with hc | hc
            · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
              rw [msm_sub_left,
                pOpenVecL_opens s tree hacc i j ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩,
                pOpenVecL_opens s tree hacc ⟨0, hn⟩ 0 ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩,
                PcoefL'_AC, PcoefL'_AC, sub_self]
            · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
              exact pubVecR_msm s tree hacc i j _ _ (PcoefR'_Wtk s _ _ _ _ k)
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
            rw [pOpenVecL_opens s tree hacc i j p,
              PcoefL'_high_zero _ _ _ _ _ _ _ (of_decide_eq_true (List.mem_filter.mp hp).2)]
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
          rw [pOpenVecR_opens s tree hacc i j p,
            PcoefR'_high_zero _ _ _ _ _ _ (of_decide_eq_true (List.mem_filter.mp hp).2)]
      · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
        exact famCand_msm_zero s tree hacc i j l
    · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
      exact tHatCand_msm_zero s tree hacc i j l 1
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
    exact tHatCand_msm_zero s tree hacc i j l 2

/-- The full candidate list: the per-bundle candidates over the **entire** `n × (q+2)` grid
(the offset elimination argument needs every `z`-child of every `y`-branch). -/
def relCandList {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c) (hn : 0 < n) :
    List (Fin (n + n + 2) → F) :=
  (List.finRange n).flatMap (fun i =>
    (List.finRange (q + 2)).flatMap (fun j => bundleCands s tree hn i j))

/-- **The collision candidate** (computable): the first genuine non-trivial discrete-log
relation in `relCandList`, or `0` if none. -/
def relCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c) :
    Fin (n + n + 2) → F :=
  if hn : 0 < n then
    ((relCandList s tree hn).find? (fun v => decide (IsNontrivialDLRel (gens s) v))).getD 0
  else 0

/-- Every candidate in `relCandList` opens `0`. -/
lemma relCandList_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (rc : Fin (n + n + 2) → F) (hc : rc ∈ relCandList s tree hn) :
    msm rc (gens s) = 0 := by
  simp only [relCandList, List.mem_flatMap, List.mem_finRange, true_and] at hc
  obtain ⟨i, j, hj⟩ := hc
  exact bundleCands_msm_zero hn s tree hacc _ _ rc hj

end Sigma.Protocols.GBPImproved.Offset
