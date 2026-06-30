/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetReadOff

/-!
# Offset-protocol soundness: pinning the quadrants

Reading the extracted three-block coefficients off the vanishing collision candidates: the
public `𝐇`-side slots (`pubVecR_readoff`), the cross-bundle differences
(`pOpenVecL/R_diff_readoff`), the `A_L`/`S_L`/`A_R` commitments after public subtraction
(`alCand_readoff`, `slCand_readoff` — the `S_L` `𝐆`-block re-emerges with the *current
bundle's* binding offset `z^{q+1}·𝟙` — and `arCand_readoff`), the high-degree vanishing, and
the quadrant-polynomial recoveries (`leafAStar/Beta/BStar_recover`).

The stray pinning `strayW_pin` shows the `𝐇'`-stray block of every `P_L`-coefficient is the
*same* fixed `𝐇`-basis vector `strayW ℓ` across all bundles (rescaled by `𝐲`); the offset
elimination argument will force these to zero.

`node_facts` assembles the per-node consequences of the `famCand`/`tHatCand` candidates: all
three `r`-children lie on the quadrant family, and the three-point `t̂`-quadratic forces
`⟨a*, β⟩ = 0`, `⟨α, b*⟩ = 0`, and `⟨a_e, b_e⟩ = ⟨a*, b*⟩ + ⟨α, β⟩` for every child.
-/

namespace Sigma.Protocols.GBPImproved.Offset

open Sigma.Protocols.GBP Sigma.Protocols.GBPImproved
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## Read-offs from vanishing candidates -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `pubVecR = 0` reads off as: the `𝐆`-stray block vanishes and the `𝐇'`-block is the public
`cH`. -/
lemma pubVecR_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (ℓ : Fin (2 * c + 5)) (cH : Fin n → F)
    (h0 : (pubVecR s tree i j ℓ cH : Fin (n + n + 2) → F) = 0) :
    (bcoefR s tree i j ℓ).1 = 0 ∧ (bcoefR s tree i j ℓ).2.1 = cH := by
  rw [pubVecR, sub_eq_zero, pOpenVecR, hsVec] at h0
  obtain ⟨h1, h2, _⟩ := gvec_inj h0
  exact ⟨h1, hadamard_yinv_cancel (chalYO tree i) _ _ h2⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Cross-bundle `𝐆`-side read-off** (three blocks): equal `𝐆`-blocks, `𝐇'`-blocks rescaled
into the `i`-bundle basis, equal blinder blocks. -/
lemma pOpenVecL_diff_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (i' : Fin n) (j' : Fin (q + 2)) (p : Fin (2 * c + 5))
    (h0 : (pOpenVecL s tree i j p - pOpenVecL s tree i' j' p : Fin (n + n + 2) → F) = 0) :
    (bcoefL s tree i j p).1 = (bcoefL s tree i' j' p).1
      ∧ (bcoefL s tree i j p).2.1 = hadamard (powers ((chalYO tree i : Fˣ) : F) n)
          (hadamard (bcoefL s tree i' j' p).2.1 (vinv (powers ((chalYO tree i' : Fˣ) : F) n)))
      ∧ (bcoefL s tree i j p).2.2 = (bcoefL s tree i' j' p).2.2 := by
  rw [sub_eq_zero, pOpenVecL, pOpenVecL] at h0
  obtain ⟨h1, h2, h3⟩ := gvec_inj h0
  exact ⟨h1, hadamard_yinv_rescale (chalYO tree i) (chalYO tree i') _ _ h2, h3⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Cross-bundle `𝐇`-side read-off** (three blocks). -/
lemma pOpenVecR_diff_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (i' : Fin n) (j' : Fin (q + 2)) (ℓ : Fin (2 * c + 5))
    (h0 : (pOpenVecR s tree i j ℓ - pOpenVecR s tree i' j' ℓ : Fin (n + n + 2) → F) = 0) :
    (bcoefR s tree i j ℓ).1 = (bcoefR s tree i' j' ℓ).1
      ∧ (bcoefR s tree i j ℓ).2.1 = hadamard (powers ((chalYO tree i : Fˣ) : F) n)
          (hadamard (bcoefR s tree i' j' ℓ).2.1 (vinv (powers ((chalYO tree i' : Fˣ) : F) n)))
      ∧ (bcoefR s tree i j ℓ).2.2 = (bcoefR s tree i' j' ℓ).2.2 := by
  rw [sub_eq_zero, pOpenVecR, pOpenVecR] at h0
  obtain ⟨h1, h2, h3⟩ := gvec_inj h0
  exact ⟨h1, hadamard_yinv_rescale (chalYO tree i) (chalYO tree i') _ _ h2, h3⟩

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The `A_L` read-off**: the slot-`0` `𝐆`-block is `aL + (z·W_R)∘y⁻¹` (with
`candWitness.aL` the reference value), and the `𝐇'`-stray block rescales. -/
lemma alCand_readoff {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (h0 : (alCand s tree i j - alCand s tree ⟨0, hn⟩ 0 : Fin (n + n + 2) → F) = 0) :
    ((bcoefL s tree i j ⟨0, by omega⟩).1
      = fun t => (candWitness s tree).aL t
          + ((chalZO tree i j)
              • (powers (chalZO tree i j) q ᵥ* s.WR)) t
            * vinv (powers ((chalYO tree i : Fˣ) : F) n) t)
    ∧ (bcoefL s tree i j ⟨0, by omega⟩).2.1
      = hadamard (powers ((chalYO tree i : Fˣ) : F) n)
          (hadamard (bcoefL s tree ⟨0, hn⟩ 0 ⟨0, by omega⟩).2.1
            (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n))) := by
  rw [alCand, alCand, pOpenVecL, pOpenVecL, alPubVec, alPubVec, gvec_sub, gvec_sub,
    gvec_sub] at h0
  obtain ⟨hG, hH, _⟩ := gvec_eq_zero h0
  constructor
  · simp only [candWitness, dif_pos hn]
    funext t
    have hgt := congrFun hG t
    simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hgt ⊢
    linear_combination hgt
  · have hHt : hadamard (bcoefL s tree i j ⟨0, by omega⟩).2.1
        (vinv (powers ((chalYO tree i : Fˣ) : F) n))
        = hadamard (bcoefL s tree ⟨0, hn⟩ 0 ⟨0, by omega⟩).2.1
          (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n)) := by
      funext t
      have hht := congrFun hH t
      simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hht ⊢
      linear_combination hht
    exact hadamard_yinv_rescale (chalYO tree i) (chalYO tree ⟨0, hn⟩) _ _ hHt

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The `S_L` read-off**: the slot-`(c+2)` `𝐆`-block is the fixed committed part plus the
*current bundle's* binding offset `z^{q+1}·𝟙`, and the `𝐇'`-stray block rescales. -/
lemma slCand_readoff {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (h0 : (slCand s tree i j - slCand s tree ⟨0, hn⟩ 0 : Fin (n + n + 2) → F) = 0) :
    ((bcoefL s tree i j ⟨c + 2, by omega⟩).1
      = fun t => ((bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1 t
            - (chalZO tree ⟨0, hn⟩ 0) ^ (q + 1))
          + (chalZO tree i j) ^ (q + 1))
    ∧ (bcoefL s tree i j ⟨c + 2, by omega⟩).2.1
      = hadamard (powers ((chalYO tree i : Fˣ) : F) n)
          (hadamard (bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).2.1
            (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n))) := by
  rw [slCand, slCand, pOpenVecL, pOpenVecL, slPubVec, slPubVec, gvec_sub, gvec_sub,
    gvec_sub] at h0
  obtain ⟨hG, hH, _⟩ := gvec_eq_zero h0
  constructor
  · funext t
    have hgt := congrFun hG t
    simp only [Pi.sub_apply, Pi.zero_apply] at hgt ⊢
    linear_combination hgt
  · have hHt : hadamard (bcoefL s tree i j ⟨c + 2, by omega⟩).2.1
        (vinv (powers ((chalYO tree i : Fˣ) : F) n))
        = hadamard (bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).2.1
          (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n)) := by
      funext t
      have hht := congrFun hH t
      simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hht ⊢
      linear_combination hht
    exact hadamard_yinv_rescale (chalYO tree i) (chalYO tree ⟨0, hn⟩) _ _ hHt

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The `A_R` read-off**: the slot-`(c+1)` `𝐇'`-block is `𝐲∘aR + w_L` with
`candWitness.aR` the reference value. -/
lemma arCand_readoff {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (h0 : (arCand s tree i j - arCand s tree ⟨0, hn⟩ 0 : Fin (n + n + 2) → F) = 0) :
    (bcoefR s tree i j ⟨c + 1, by omega⟩).2.1
      = fun t => powers ((chalYO tree i : Fˣ) : F) n t * (candWitness s tree).aR t
          + ((chalZO tree i j)
              • (powers (chalZO tree i j) q ᵥ* s.WL)) t := by
  rw [arCand, arCand, pOpenVecR, pOpenVecR, hsVec, hsVec, gvec_sub, gvec_sub, gvec_sub] at h0
  obtain ⟨_, hH, _⟩ := gvec_eq_zero h0
  have hHt : hadamard ((bcoefR s tree i j ⟨c + 1, by omega⟩).2.1
        - (chalZO tree i j)
          • (powers (chalZO tree i j) q ᵥ* s.WL))
        (vinv (powers ((chalYO tree i : Fˣ) : F) n))
      = hadamard ((bcoefR s tree ⟨0, hn⟩ 0 ⟨c + 1, by omega⟩).2.1
        - (chalZO tree ⟨0, hn⟩ 0)
          • (powers (chalZO tree ⟨0, hn⟩ 0) q ᵥ* s.WL))
        (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n)) := by
    funext t
    have hht := congrFun hH t
    simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hht ⊢
    linear_combination hht
  have hrescale := hadamard_yinv_rescale (chalYO tree i) (chalYO tree ⟨0, hn⟩) _ _ hHt
  simp only [candWitness, dif_pos hn]
  funext t
  have := congrFun hrescale t
  simp only [Pi.sub_apply, hadamard] at this ⊢
  linear_combination this

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- When all bundle candidates are `0`, both extracted `P_L`-blocks vanish above degree
`c+2`. -/
lemma bcoefL_high_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (p : Fin (2 * c + 5)) (hp : c + 3 ≤ (p : ℕ)) :
    (bcoefL s tree i j p).1 = 0 ∧ (bcoefL s tree i j p).2.1 = 0 := by
  have hmem : pOpenVecL s tree i j p ∈ bundleCands s tree hn i j := by
    rw [bundleCands]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ ?_))))))
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨p, List.mem_filter.mpr
          ⟨List.mem_finRange p, decide_eq_true hp⟩, rfl⟩)))))
  have h0 := hbz _ hmem
  rw [pOpenVecL] at h0
  obtain ⟨h1, h2, _⟩ := gvec_eq_zero h0
  refine ⟨h1, hadamard_yinv_cancel (chalYO tree i) _ 0 ?_⟩
  rw [h2]; funext t; simp [hadamard]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- When all bundle candidates are `0`, both extracted `P_R`-blocks vanish above degree
`c+2`. -/
lemma bcoefR_high_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (ℓ : Fin (2 * c + 5)) (hq : c + 3 ≤ (ℓ : ℕ)) :
    (bcoefR s tree i j ℓ).1 = 0 ∧ (bcoefR s tree i j ℓ).2.1 = 0 := by
  have hmem : pOpenVecR s tree i j ℓ ∈ bundleCands s tree hn i j := by
    rw [bundleCands]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ ?_))))))
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨ℓ, List.mem_filter.mpr
        ⟨List.mem_finRange ℓ, decide_eq_true hq⟩, rfl⟩))))
  have h0 := hbz _ hmem
  rw [pOpenVecR] at h0
  obtain ⟨h1, h2, _⟩ := gvec_eq_zero h0
  refine ⟨h1, hadamard_yinv_cancel (chalYO tree i) _ 0 ?_⟩
  rw [h2]; funext t; simp [hadamard]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `famCand = 0` puts the third `r`-child on the quadrant family. -/
lemma famCand_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5))
    (h0 : (famCand s tree i j l : Fin (n + n + 2) → F) = 0) :
    leafA tree i j l 2 = aStarF tree i j l + rch tree i j l 2 • alphaF tree i j l
    ∧ rch tree i j l 2 • leafB tree i j l 2
      = betaF tree i j l + rch tree i j l 2 • bStarF tree i j l := by
  rw [famCand] at h0
  obtain ⟨hG, hH, _⟩ := gvec_eq_zero h0
  constructor
  · exact (sub_eq_zero.mp hG).symm
  · have hz : betaF tree i j l + rch tree i j l 2 • bStarF tree i j l
        - rch tree i j l 2 • leafB tree i j l 2 = 0 := by
      refine hadamard_yinv_cancel (chalYO tree i) _ 0 ?_
      rw [hH]; funext t; simp [hadamard]
    have := sub_eq_zero.mp hz
    exact this.symm

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `tHatCand = 0` pins the child's inner product to the child-`0` value. -/
lemma tHatCand_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) (e : Fin 3)
    (h0 : (tHatCand s tree i j l e : Fin (n + n + 2) → F) = 0) :
    ip (leafA tree i j l e) (leafB tree i j l e)
      = ip (leafA tree i j l 0) (leafB tree i j l 0) :=
  sub_eq_zero.mp (ghVec_eq_zero h0).1

/-! ## Quadrant-polynomial recoveries -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `a*`-quadrant is the `bcoefL`-`𝐆` polynomial evaluated at the node's `x`-challenge. -/
lemma leafAStar_recover {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) :
    aStarF tree i j l
      = ∑ p : Fin (2 * c + 5),
          (chalXO tree i j l) ^ (p : ℕ)
            • (bcoefL s tree i j p).1 := by
  rw [vandermonde_recover (fun l => (chalXO tree i j l))
    (chalX_inj tree i j) (fun l => aStarF tree i j l) l]
  exact Finset.sum_congr rfl fun p _ => by simp only [bcoefL, vandInv_eq (chalX_inj tree i j)]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `β`-stray quadrant is the `bcoefL`-`𝐇'` polynomial evaluated at the node's
`x`-challenge. -/
lemma leafBeta_recover {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) :
    betaF tree i j l
      = ∑ p : Fin (2 * c + 5),
          (chalXO tree i j l) ^ (p : ℕ)
            • (bcoefL s tree i j p).2.1 := by
  rw [vandermonde_recover (fun l => (chalXO tree i j l))
    (chalX_inj tree i j) (fun l => betaF tree i j l) l]
  exact Finset.sum_congr rfl fun p _ => by simp only [bcoefL, vandInv_eq (chalX_inj tree i j)]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `b*`-quadrant is the `bcoefR`-`𝐇'` polynomial evaluated at the node's `x`-challenge. -/
lemma leafBStar_recover {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)) :
    bStarF tree i j l
      = ∑ ℓ : Fin (2 * c + 5),
          (chalXO tree i j l) ^ (ℓ : ℕ)
            • (bcoefR s tree i j ℓ).2.1 := by
  rw [vandermonde_recover (fun l => (chalXO tree i j l))
    (chalX_inj tree i j) (fun l => bStarF tree i j l) l]
  exact Finset.sum_congr rfl fun ℓ _ => by simp only [bcoefR, vandInv_eq (chalX_inj tree i j)]

/-! ## The stray pinning -/

/-- The residual stray: the fixed `𝐇`-basis component `β` of the slot-`ℓ` `P_L`-coefficient (read
off at the reference bundle, the same for every `(y,z)` up to the `𝐲`-rescaling). Step 4
(`strayW_zero`) forces every `strayW ℓ` to zero. -/
def strayW {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hn : 0 < n) (ℓ : Fin (c + 3)) : Fin n → F :=
  hadamard (bcoefL s tree ⟨0, hn⟩ 0 ⟨(ℓ : ℕ), by omega⟩).2.1
    (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n))

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The stray pinning.** When the bundle's candidates vanish, the `𝐇'`-stray block of every
`P_L`-coefficient is the fixed `strayW ℓ`, rescaled by the bundle's `𝐲`. -/
lemma strayW_pin {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0) (ℓ : Fin (c + 3)) :
    (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1
      = hadamard (powers ((chalYO tree i : Fˣ) : F) n) (strayW s tree hn ℓ) := by
  rcases q_slot_casesL ℓ with hq | hq | ⟨k, hq⟩ | hq
  · have hqi : ℓ = ⟨0, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_self)
    rw [hqi]
    exact (alCand_readoff hn s tree i j hc).2
  · have hqi : ℓ = ⟨1, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hqi]
    exact (pOpenVecL_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).2.1
  · have hqi : ℓ = ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))))))))))))))
    rw [hqi]
    exact (pOpenVecL_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).2.1
  · have hqi : ℓ = ⟨c + 2, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [hqi]
    exact (slCand_readoff hn s tree i j hc).2

/-! ## The per-node facts -/

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Steps 1–2 (per-node interpolation in `r`, and the `t̂`-quadratic).** *Step 1:* the three
`r`-children share `(P_L, P_R)` fixed before `r`, so the second verifier check
`P_L + r P_R = ⟨a_r,𝐆⟩ + r⟨b_r,𝐡'⟩ + μ_r·H` at the first two children interpolates them into
the quadrants `a*, β, α, b*` and the blinders `muLF, muRF` (`node_quad_open`), with
`a_r = a* + r α` and `b_r = r⁻¹ β + b*` on the family; `famCand`-vanishing puts the third
child — vectors and blinder — on it too. *Step 2:* the `eq1`-pinned `t̂` (`tHatCand`) fixes
`⟨a_r, b_r⟩ = ⟨a*,β⟩ r⁻¹ + C + ⟨α,b*⟩ r` independently of `r`; a Laurent quadratic constant at three
distinct nonzero `r` has zero `r⁻¹`- and `r`-coefficients, forcing `⟨a*, β⟩ = ⟨α, b*⟩ = 0` and
`⟨a_r, b_r⟩ = ⟨a*, b*⟩ + ⟨α, β⟩`. (Three points are needed, fixing the `r`-arity at `3`.) -/
lemma node_facts {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0) (l : Fin (2 * c + 5)) :
    ip (aStarF tree i j l) (betaF tree i j l) = 0
    ∧ ip (alphaF tree i j l) (bStarF tree i j l) = 0
    ∧ ∀ e : Fin 3, ip (leafA tree i j l e) (leafB tree i j l e)
        = ip (aStarF tree i j l) (bStarF tree i j l)
          + ip (alphaF tree i j l) (betaF tree i j l) := by
  -- membership of the three per-node candidates
  have hfam := hbz _ (by
    rw [bundleCands]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)))))))))))
  have ht1 := hbz _ (by
    rw [bundleCands]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩))))))))))
  have ht2 := hbz _ (by
    rw [bundleCands]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)))))))))
  -- all three children lie on the quadrant family
  have onA : ∀ e : Fin 3,
      leafA tree i j l e = aStarF tree i j l + rch tree i j l e • alphaF tree i j l := by
    intro e
    fin_cases e
    · exact (quad_family01 tree i j l 0).1
    · exact (quad_family01 tree i j l 1).1
    · exact (famCand_readoff s tree i j l hfam).1
  have onBsmul : ∀ e : Fin 3,
      rch tree i j l e • leafB tree i j l e
        = betaF tree i j l + rch tree i j l e • bStarF tree i j l := by
    intro e
    fin_cases e
    · exact (quad_family01 tree i j l 0).2
    · exact (quad_family01 tree i j l 1).2
    · exact (famCand_readoff s tree i j l hfam).2
  have onB : ∀ e : Fin 3,
      leafB tree i j l e
        = (rch tree i j l e)⁻¹ • betaF tree i j l + bStarF tree i j l := by
    intro e
    have h := congrArg (fun v : Fin n → F => (rch tree i j l e)⁻¹ • v) (onBsmul e)
    simp only at h
    rw [inv_smul_smul₀ (rch_ne_zero tree i j l e)] at h
    rw [h, smul_add, smul_smul, inv_mul_cancel₀ (rch_ne_zero tree i j l e), one_smul]
  -- the quadratic form of each child's inner product
  have hq : ∀ e : Fin 3,
      ip (leafA tree i j l e) (leafB tree i j l e)
        = ip (aStarF tree i j l) (betaF tree i j l) * (rch tree i j l e)⁻¹
          + (ip (aStarF tree i j l) (bStarF tree i j l)
              + ip (alphaF tree i j l) (betaF tree i j l))
          + ip (alphaF tree i j l) (bStarF tree i j l) * rch tree i j l e := by
    intro e
    rw [onA e, onB e]
    exact ip_quad (rch_ne_zero tree i j l e) _ _ _ _
  -- the three values agree, so the quadratic is constant at three distinct nonzero points
  have e0 := (hq 0).symm
  have e1 := (hq 1).symm.trans (tHatCand_readoff s tree i j l 1 ht1)
  have e2 := (hq 2).symm.trans (tHatCand_readoff s tree i j l 2 ht2)
  have hkey := tHat_quad (rch_inj tree i j l (by decide)) (rch_inj tree i j l (by decide))
    (rch_inj tree i j l (by decide)) (rch_ne_zero tree i j l 0) (rch_ne_zero tree i j l 1)
    (rch_ne_zero tree i j l 2) e0 e1 e2
  refine ⟨hkey.1, hkey.2.1, fun c => ?_⟩
  rw [hq c, hkey.1, hkey.2.1]
  ring

end Sigma.Protocols.GBPImproved.Offset
