/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.Extract

/-!
# Improved-arithmetization soundness: collision candidates and read-offs

The `gens`-coefficient opening vectors of the split verifier coefficients (`pOpenVecL` with no
`𝐇`-block, `pOpenVecR` with no `𝐆`-block), the structural candidates — public `𝐇`-side slots
(`pubVecR'`), the `A_L`/`A_R` commitments after public subtraction (`alCand`/`arCand`), the
cross-bundle differences, the high-degree openings, and the `eq1` `(g,h)` collision `ghCand'` —
together with the comprehensive per-bundle candidate list `bundleCands'` and its uniform
`msm · gens = 0` proof. Reading the extracted `bcoefL`/`bcoefR` off the *vanishing* candidates
(`*_readoff`) recovers the honest coefficient families slot by slot.

Everything opens against the same generator family `gens s = (𝐆, 𝐇, g, h)` as the base proof,
so a non-vanishing candidate is a non-trivial discrete-log relation among the GBP generators.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## Opening vectors against `gens` -/

/-- The `gens`-coefficient vector of the bundle-`(i,j)` opening of `PcoefL' p`: `𝐆`-part and
`h`-part only — the binding interpolation guarantees there is **no** `𝐇`-block. -/
def pOpenVecL {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * c + 5)) : Fin (n + n + 2) → F :=
  gvec (bcoefL s tree i j p).1 0 (bcoefL s tree i j p).2

/-- `pOpenVecL i j p` is a `gens`-opening of `PcoefL' p`. -/
lemma pOpenVecL_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * c + 5)) :
    msm (pOpenVecL s tree i j p) (gens s)
      = PcoefL' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
          (rootP tree).1 (rootP tree).2.2.1 (rootP tree).2.2.2.1 p := by
  rw [pOpenVecL, gvec, gens_msm, msm_zero_left, zero_smul, add_zero, add_zero]
  exact (bundle_openL s tree hacc i j p).symm

/-- The `gens`-coefficient vector of the bundle-`(i,j)` opening of `PcoefR' ℓ`: `𝐇`-part (in
the `𝐇`-basis, rescaled by `y⁻¹`) and `h`-part only — no `𝐆`-block. -/
def pOpenVecR {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (ℓ : Fin (2 * c + 5)) : Fin (n + n + 2) → F :=
  gvec 0 (hadamard (bcoefR s tree i j ℓ).1 (vinv (powers ((chalYP tree i : Fˣ) : F) n)))
    (bcoefR s tree i j ℓ).2

/-- `pOpenVecR i j ℓ` is a `gens`-opening of `PcoefR' ℓ`. -/
lemma pOpenVecR_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (ℓ : Fin (2 * c + 5)) :
    msm (pOpenVecR s tree i j ℓ) (gens s)
      = PcoefR' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
          (rootP tree).2.1 (rootP tree).2.2.2.2 ℓ := by
  have hconv : msm (hadamard (bcoefR s tree i j ℓ).1
        (vinv (powers ((chalYP tree i : Fˣ) : F) n))) s.hs
      = msm (bcoefR s tree i j ℓ).1 (vinv (powers ((chalYP tree i : Fˣ) : F) n) ⊙ s.hs) :=
    (msm_vsmul (bcoefR s tree i j ℓ).1 (vinv (powers ((chalYP tree i : Fˣ) : F) n)) s.hs).symm
  rw [pOpenVecR, gvec, gens_msm, msm_zero_left, zero_add, zero_smul, add_zero, hconv]
  exact (bundle_openR s tree hacc i j ℓ).symm

/-! ## Structural candidates -/

/-- The `gens`-vector opening the public pure-`𝐆` part `W̃_R` of `PcoefL' 0`. -/
def alPubVec {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : Fin (n + n + 2) → F :=
  gvec (hadamard (vinv (powers ((chalYP tree i : Fˣ) : F) n))
      (((chalZP tree i j : Fˣ) : F)
        • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WR))) 0 0

omit [DecidableEq F] [DecidableEq G] in
lemma alPubVec_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (alPubVec s tree i j) (gens s)
      = msm (hadamard (vinv (powers ((chalYP tree i : Fˣ) : F) n))
          (((chalZP tree i j : Fˣ) : F)
            • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WR))) s.gs := by
  rw [alPubVec, gvec, gens_msm, msm_zero_left, zero_smul, zero_smul, add_zero, add_zero,
    add_zero]

/-- The `gens`-vector opening of the commitment `A_L` at bundle `(i,j)`: the `PcoefL' 0`
opening with the public `W̃_R` part subtracted off. -/
def alCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : Fin (n + n + 2) → F :=
  pOpenVecL s tree i j ⟨0, by omega⟩ - alPubVec s tree i j

lemma alCand_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (alCand s tree i j) (gens s) = (rootP tree).1 := by
  rw [alCand, msm_sub_left, pOpenVecL_opens s tree hacc i j ⟨0, by omega⟩, alPubVec_opens,
    PcoefL'_AL]
  abel

/-- The `gens`-vector opening of the commitment `A_R` at bundle `(i,j)`: the `PcoefR' (c+1)`
opening with the public pure-`𝐡'` part `W̃_L` subtracted off. -/
def arCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : Fin (n + n + 2) → F :=
  pOpenVecR s tree i j ⟨c + 1, by omega⟩
    - hsVec (((chalZP tree i j : Fˣ) : F)
        • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WL))
      (vinv (powers ((chalYP tree i : Fˣ) : F) n))

lemma arCand_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (arCand s tree i j) (gens s) = (rootP tree).2.1 := by
  rw [arCand, msm_sub_left, pOpenVecR_opens s tree hacc i j ⟨c + 1, by omega⟩, hsVec_opens,
    PcoefR'_AR]
  abel

/-- **The public-`𝐇`-side collision candidate** at slot `ℓ` with public coefficient `cH`
(`ℓ = c−k−1` ↦ `w_C⁽ᵏ⁾`, `ℓ = c` ↦ `w_O − 𝐲`): the difference `pOpenVecR − hsVec cH yinv`
opens `PcoefR' ℓ − PcoefR' ℓ = 0`. -/
def pubVecR' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (ℓ : Fin (2 * c + 5)) (cH : Fin n → F) :
    Fin (n + n + 2) → F :=
  pOpenVecR s tree i j ℓ - hsVec cH (vinv (powers ((chalYP tree i : Fˣ) : F) n))

lemma pubVecR'_msm {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (ℓ : Fin (2 * c + 5)) (cH : Fin n → F)
    (hP : PcoefR' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
        (rootP tree).2.1 (rootP tree).2.2.2.2 ℓ
      = msm cH (vinv (powers ((chalYP tree i : Fˣ) : F) n) ⊙ s.hs)) :
    msm (pubVecR' s tree i j ℓ cH) (gens s) = 0 := by
  rw [pubVecR', msm_sub_left, pOpenVecR_opens s tree hacc i j ℓ, hsVec_opens, hP, sub_self]

/-! ## Read-offs from vanishing candidates -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `pubVecR' = 0` reads off as: the extracted `𝐇'`-coefficient is the public `cH` (and the
`h`-part is `0`). -/
lemma pubVecR'_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (ℓ : Fin (2 * c + 5)) (cH : Fin n → F)
    (h0 : (pubVecR' s tree i j ℓ cH : Fin (n + n + 2) → F) = 0) :
    (bcoefR s tree i j ℓ).1 = cH ∧ (bcoefR s tree i j ℓ).2 = 0 := by
  rw [pubVecR', sub_eq_zero, pOpenVecR, hsVec] at h0
  obtain ⟨_, h2, h3⟩ := gvec_inj h0
  exact ⟨hadamard_yinv_cancel (chalYP tree i) _ _ h2, h3⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Cross-bundle `𝐆`-side read-off.** Two bundles opening the same challenge-independent
commitment give equal `𝐆`- and `h`-coefficients (no basis rescaling on the `𝐆` side). -/
lemma pOpenVecL_diff_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (i' : Fin n) (j' : Fin (q + 1)) (p : Fin (2 * c + 5))
    (h0 : (pOpenVecL s tree i j p - pOpenVecL s tree i' j' p : Fin (n + n + 2) → F) = 0) :
    (bcoefL s tree i j p).1 = (bcoefL s tree i' j' p).1
      ∧ (bcoefL s tree i j p).2 = (bcoefL s tree i' j' p).2 := by
  rw [sub_eq_zero, pOpenVecL, pOpenVecL] at h0
  obtain ⟨h1, _, h3⟩ := gvec_inj h0
  exact ⟨h1, h3⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Cross-bundle `𝐇`-side read-off.** The `𝐇'`-coefficients rescale into the `i`-bundle
basis (`hadamard_yinv_rescale`); the `h`-parts agree. -/
lemma pOpenVecR_diff_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (i' : Fin n) (j' : Fin (q + 1)) (ℓ : Fin (2 * c + 5))
    (h0 : (pOpenVecR s tree i j ℓ - pOpenVecR s tree i' j' ℓ : Fin (n + n + 2) → F) = 0) :
    (bcoefR s tree i j ℓ).1
      = hadamard (powers ((chalYP tree i : Fˣ) : F) n)
          (hadamard (bcoefR s tree i' j' ℓ).1 (vinv (powers ((chalYP tree i' : Fˣ) : F) n)))
      ∧ (bcoefR s tree i j ℓ).2 = (bcoefR s tree i' j' ℓ).2 := by
  rw [sub_eq_zero, pOpenVecR, pOpenVecR] at h0
  obtain ⟨_, h2, h3⟩ := gvec_inj h0
  exact ⟨hadamard_yinv_rescale (chalYP tree i) (chalYP tree i') _ _ h2, h3⟩

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The `A_L` read-off.** The vanishing `A_L` cross-bundle candidate forces the `bcoefL`
slot-`0` coefficient to `aL + (z·W_R)∘y⁻¹` — exactly `honestFL'` at degree `0`, with
`candWitness'.aL` the reference value. -/
lemma alCand_readoff {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1))
    (h0 : (alCand s tree i j - alCand s tree ⟨0, hn⟩ 0 : Fin (n + n + 2) → F) = 0) :
    (bcoefL s tree i j ⟨0, by omega⟩).1
      = fun t => (candWitness' s tree).aL t
          + (((chalZP tree i j : Fˣ) : F)
              • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WR)) t
            * vinv (powers ((chalYP tree i : Fˣ) : F) n) t := by
  rw [alCand, alCand, pOpenVecL, pOpenVecL, alPubVec, alPubVec, gvec_sub, gvec_sub,
    gvec_sub] at h0
  obtain ⟨hG, _, _⟩ := gvec_eq_zero h0
  simp only [candWitness', dif_pos hn]
  funext t
  have hgt := congrFun hG t
  simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hgt ⊢
  linear_combination hgt

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The `A_R` read-off.** The vanishing `A_R` cross-bundle candidate forces the `bcoefR`
slot-`(c+1)` coefficient to `𝐲∘aR + z·W_L` — exactly `honestFR'` at degree `c+1`, with
`candWitness'.aR` the reference value (rescaled across the `y`-bases). -/
lemma arCand_readoff {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1))
    (h0 : (arCand s tree i j - arCand s tree ⟨0, hn⟩ 0 : Fin (n + n + 2) → F) = 0) :
    (bcoefR s tree i j ⟨c + 1, by omega⟩).1
      = fun t => powers ((chalYP tree i : Fˣ) : F) n t * (candWitness' s tree).aR t
          + (((chalZP tree i j : Fˣ) : F)
              • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WL)) t := by
  rw [arCand, arCand, pOpenVecR, pOpenVecR, hsVec, hsVec, gvec_sub, gvec_sub, gvec_sub] at h0
  obtain ⟨_, hH, _⟩ := gvec_eq_zero h0
  have hHt : hadamard ((bcoefR s tree i j ⟨c + 1, by omega⟩).1
        - ((chalZP tree i j : Fˣ) : F)
          • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WL))
        (vinv (powers ((chalYP tree i : Fˣ) : F) n))
      = hadamard ((bcoefR s tree ⟨0, hn⟩ 0 ⟨c + 1, by omega⟩).1
        - ((chalZP tree ⟨0, hn⟩ 0 : Fˣ) : F)
          • (powers ((chalZP tree ⟨0, hn⟩ 0 : Fˣ) : F) q ᵥ* s.WL))
        (vinv (powers ((chalYP tree ⟨0, hn⟩ : Fˣ) : F) n)) := by
    funext t
    have hht := congrFun hH t
    simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hht ⊢
    linear_combination hht
  have hrescale := hadamard_yinv_rescale (chalYP tree i) (chalYP tree ⟨0, hn⟩) _ _ hHt
  simp only [candWitness', dif_pos hn]
  funext t
  have := congrFun hrescale t
  simp only [Pi.sub_apply, hadamard] at this ⊢
  linear_combination this

/-! ## The `eq1` collision candidate -/

/-- **The eq1 `(g, h)` collision candidate at bundle `(i, j)`.** The difference between the
recovered `eq1` `(c+1)`-coefficient opening (`eqAj'·g + eqCj'·h`) and the `candWitness'`-`v/γ`
reconstruction. Both open the same group element `msm (z·(𝐳·W_V)) V`, so this candidate always
has `msm · gens = 0`; its vanishing is exactly `star_at_bundle'`'s `Heq`. -/
def ghCand' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : Fin (n + n + 2) → F :=
  ghVec (eqAj' s tree i j - ip (((chalZP tree i j : Fˣ) : F)
            • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV))
          (candWitness' s tree).v)
        (eqCj' s tree i j - ip (((chalZP tree i j : Fˣ) : F)
            • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV))
          (candWitness' s tree).γ)

/-- The `ghCand'` candidate is a genuine relation: `msm · gens = 0`. -/
lemma ghCand'_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (ghCand' s tree i j) (gens s) = 0 := by
  have he : eqAj' s tree i j • s.g + eqCj' s tree i j • s.h
      = ip (((chalZP tree i j : Fˣ) : F)
            • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV))
          (candWitness' s tree).v • s.g
        + ip (((chalZP tree i j : Fˣ) : F)
            • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV))
          (candWitness' s tree).γ • s.h :=
    (eq1_open' s tree hacc i j).symm.trans
      (msm_wv_open s.V s.g s.h _ _ _ (fun k => clause4_holds' hn s tree hacc k))
  rw [ghCand', ghVec_opens, sub_smul, sub_smul]
  rw [← sub_eq_zero] at he
  rw [← he]; abel

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- `ghCand' = 0` is exactly `Heq` at bundle `(i, j)`: the recovered `eqAj'` equals the
`candWitness'`-`v` reconstruction `⟨z·(𝐳·W_V), v⟩`. -/
lemma heq_of_ghCand'_zero {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (h0 : (ghCand' s tree i j : Fin (n + n + 2) → F) = 0) :
    eqAj' s tree i j = ip (((chalZP tree i j : Fˣ) : F)
        • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV))
      (candWitness' s tree).v :=
  sub_eq_zero.mp (ghVec_eq_zero h0).1

/-! ## Leaf-data recovery -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **`𝐆`-side data recovery.** Each `x`-child's sent `a`-vector is the `bcoefL`-`𝐆` polynomial
evaluated at that child's `x`-challenge (the inverse-Vandermonde recovery). -/
lemma leafA_recover {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (l : Fin (2 * c + 5)) :
    (openP tree i j l).2.2.2.1
      = ∑ p : Fin (2 * c + 5),
          ((chalXP tree i j l : Fˣ) : F) ^ (p : ℕ)
            • (bcoefL s tree i j p).1 := by
  rw [vandermonde_recover (fun l => ((chalXP tree i j l : Fˣ) : F))
    (chalX_inj' tree i j)
    (fun l => (openP tree i j l).2.2.2.1) l]
  exact Finset.sum_congr rfl fun p _ => by simp only [bcoefL, vandInv_eq (chalX_inj' tree i j)]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **`𝐇`-side data recovery.** Each `x`-child's sent `b`-vector is the `bcoefR`-`𝐇'`
polynomial evaluated at that child's `x`-challenge. -/
lemma leafB_recover {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (l : Fin (2 * c + 5)) :
    (openP tree i j l).2.2.2.2
      = ∑ ℓ : Fin (2 * c + 5),
          ((chalXP tree i j l : Fˣ) : F) ^ (ℓ : ℕ)
            • (bcoefR s tree i j ℓ).1 := by
  rw [vandermonde_recover (fun l => ((chalXP tree i j l : Fˣ) : F))
    (chalX_inj' tree i j)
    (fun l => (openP tree i j l).2.2.2.2) l]
  exact Finset.sum_congr rfl fun ℓ _ => by simp only [bcoefR, vandInv_eq (chalX_inj' tree i j)]

/-! ## The candidate list -/

/-- **The per-bundle collision candidates** at bundle `(i, j)` (reference bundle `(⟨0,hn⟩, 0)`):
the `A_L`/`A_O`/`S_L` `𝐆`-side and `A_R`/`S_R` `𝐇`-side cross-bundle opening differences, the
public `W̃_O`/`W̃_C⁽ᵏ⁾` structural differences, the eq1 `(g,h)` candidate, and the high-degree
openings of both sides (which open `0`). Each has `msm · gens = 0`
(`bundleCands'_msm_zero`), so a nonzero one is a genuine discrete-log relation. -/
def bundleCands' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c) (hn : 0 < n)
    (i : Fin n) (j : Fin (q + 1)) : List (Fin (n + n + 2) → F) :=
  (alCand s tree i j - alCand s tree ⟨0, hn⟩ 0)
    :: (pOpenVecL s tree i j ⟨1, by omega⟩ - pOpenVecL s tree ⟨0, hn⟩ 0 ⟨1, by omega⟩)
    :: (pOpenVecL s tree i j ⟨c + 2, by omega⟩ - pOpenVecL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩)
    :: pubVecR' s tree i j ⟨c, by omega⟩
        (((chalZP tree i j : Fˣ) : F)
            • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WO)
          - powers ((chalYP tree i : Fˣ) : F) n)
    :: (arCand s tree i j - arCand s tree ⟨0, hn⟩ 0)
    :: (pOpenVecR s tree i j ⟨c + 2, by omega⟩ - pOpenVecR s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩)
    :: ghCand' s tree i j
    :: ((List.finRange c).map (fun (k : Fin c) =>
          pOpenVecL s tree i j ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩
            - pOpenVecL s tree ⟨0, hn⟩ 0 ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩)
      ++ (List.finRange c).map (fun (k : Fin c) =>
          pubVecR' s tree i j ⟨c - (k : ℕ) - 1, by have := k.isLt; omega⟩
            (((chalZP tree i j : Fˣ) : F)
              • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WC k)))
      ++ ((List.finRange (2 * c + 5)).filter
            (fun (p : Fin (2 * c + 5)) => decide (c + 3 ≤ (p : ℕ)))).map
          (fun p => pOpenVecL s tree i j p)
      ++ ((List.finRange (2 * c + 5)).filter
            (fun (p : Fin (2 * c + 5)) => decide (c + 3 ≤ (p : ℕ)))).map
          (fun p => pOpenVecR s tree i j p))

/-- **Every per-bundle candidate opens `0`.** Cross-bundle differences open challenge-
independent commitments twice (`PcoefL'_AO/AC/SL`, `PcoefR'_SR`, `alCand_opens`,
`arCand_opens`); public ones via `pubVecR'_msm` + `PcoefR'_WtO/Wtk`; `ghCand'` via
`ghCand'_msm_zero`; the high-degree ones open the vanishing coefficients directly. -/
lemma bundleCands'_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (rc : Fin (n + n + 2) → F)
    (hc : rc ∈ bundleCands' s tree hn i j) :
    msm rc (gens s) = 0 := by
  rw [bundleCands'] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, alCand_opens s tree hacc i j, alCand_opens s tree hacc ⟨0, hn⟩ 0,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, pOpenVecL_opens s tree hacc i j ⟨1, by omega⟩,
      pOpenVecL_opens s tree hacc ⟨0, hn⟩ 0 ⟨1, by omega⟩, PcoefL'_AO, PcoefL'_AO, sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, pOpenVecL_opens s tree hacc i j ⟨c + 2, by omega⟩,
      pOpenVecL_opens s tree hacc ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩, PcoefL'_SL, PcoefL'_SL,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · exact pubVecR'_msm s tree hacc i j _ _ (PcoefR'_WtO s _ _ _ _)
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, arCand_opens s tree hacc i j, arCand_opens s tree hacc ⟨0, hn⟩ 0,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, pOpenVecR_opens s tree hacc i j ⟨c + 2, by omega⟩,
      pOpenVecR_opens s tree hacc ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩, PcoefR'_SR, PcoefR'_SR,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ghCand'_msm_zero hn s tree hacc i j
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
        rw [msm_sub_left,
          pOpenVecL_opens s tree hacc i j ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩,
          pOpenVecL_opens s tree hacc ⟨0, hn⟩ 0 ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩,
          PcoefL'_AC, PcoefL'_AC, sub_self]
      · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
        exact pubVecR'_msm s tree hacc i j _ _ (PcoefR'_Wtk s _ _ _ _ k)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      rw [pOpenVecL_opens s tree hacc i j p,
        PcoefL'_high_zero _ _ _ _ _ _ _ (of_decide_eq_true (List.mem_filter.mp hp).2)]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    rw [pOpenVecR_opens s tree hacc i j p,
      PcoefR'_high_zero _ _ _ _ _ _ (of_decide_eq_true (List.mem_filter.mp hp).2)]

/-! ## High-degree vanishing -/

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- When all bundle candidates are `0`, the extracted `bcoefL` above degree `c+2` vanishes. -/
lemma bcoefL_high_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1))
    (hbz : ∀ rc ∈ bundleCands' s tree hn i j, rc = 0)
    (p : Fin (2 * c + 5)) (hp : c + 3 ≤ (p : ℕ)) :
    (bcoefL s tree i j p).1 = 0 := by
  have hmem : pOpenVecL s tree i j p ∈ bundleCands' s tree hn i j := by
    rw [bundleCands']
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ ?_))))))
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨p,
      List.mem_filter.mpr ⟨List.mem_finRange p, decide_eq_true hp⟩, rfl⟩))
  have h0 := hbz _ hmem
  rw [pOpenVecL] at h0
  exact (gvec_eq_zero h0).1

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- When all bundle candidates are `0`, the extracted `bcoefR` above degree `c+2` vanishes. -/
lemma bcoefR_high_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1))
    (hbz : ∀ rc ∈ bundleCands' s tree hn i j, rc = 0)
    (ℓ : Fin (2 * c + 5)) (hq : c + 3 ≤ (ℓ : ℕ)) :
    (bcoefR s tree i j ℓ).1 = 0 := by
  have hmem : pOpenVecR s tree i j ℓ ∈ bundleCands' s tree hn i j := by
    rw [bundleCands']
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ ?_))))))
    exact List.mem_append_right _ (List.mem_map.mpr ⟨ℓ,
      List.mem_filter.mpr ⟨List.mem_finRange ℓ, decide_eq_true hq⟩, rfl⟩)
  have h0 := hbz _ hmem
  rw [pOpenVecR] at h0
  obtain ⟨_, hH, _⟩ := gvec_eq_zero h0
  refine hadamard_yinv_cancel (chalYP tree i) _ 0 ?_
  rw [hH]; funext t; simp [hadamard]

/-! ## The full candidate list and the collision candidate -/

/-- The full candidate list: per-bundle candidates over the `i₀`-row (all `j`) and the
`j = 0`-column (all `i`) — the "L"-shape that `clauses12_of_LZ` consumes. -/
def relCandList' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c) (hn : 0 < n) :
    List (Fin (n + n + 2) → F) :=
  (List.finRange (q + 1)).flatMap (fun j => bundleCands' s tree hn ⟨0, hn⟩ j)
    ++ (List.finRange n).flatMap (fun i => bundleCands' s tree hn i 0)

/-- **The collision candidate** (computable): the first genuine non-trivial discrete-log
relation in `relCandList'`, or `0` if none. -/
def relCand' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c) :
    Fin (n + n + 2) → F :=
  if hn : 0 < n then
    ((relCandList' s tree hn).find? (fun v => decide (IsNontrivialDLRel (gens s) v))).getD 0
  else 0

/-- Every candidate in `relCandList'` opens `0`. -/
lemma relCandList'_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (rc : Fin (n + n + 2) → F) (hc : rc ∈ relCandList' s tree hn) :
    msm rc (gens s) = 0 := by
  simp only [relCandList', List.mem_append, List.mem_flatMap, List.mem_finRange,
    true_and] at hc
  rcases hc with ⟨j, hj⟩ | ⟨i, hi⟩
  · exact bundleCands'_msm_zero hn s tree hacc _ _ rc hj
  · exact bundleCands'_msm_zero hn s tree hacc _ _ rc hi

end Sigma.Protocols.GBPImproved
