/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetEliminate

/-!
# Computational special soundness of the improved arithmetization (protocol of record)

`(k₁, k₂, k₃, k₄) = (n, q+2, 2c+5, 3)`-special soundness of
`Sigma.Protocols.GBPImproved.arithRed'` — the improved arithmetization whose final
message is the inner-product witness `(f_L(x), f_R(x))`, sent *after* the binding challenge
`r`, with the **binding offset** `z^{q+1}·𝟙` on the mask slot of `f_L` — in the computational
sense of `Sigma.Reduction.Sound`: from any `(n, q+2, 2c+5, 3)`-tree of accepting transcripts a
deterministic extractor returns **either** a witness for the tight relation `R_GBP'` (no
auxiliary `𝐇`-openings) **or** a non-trivial discrete-log relation among the generators
`Γ = 𝐆 ⧺ 𝐇 ⧺ [g, h]` — a nonzero `v` with `⟨v, Γ⟩ = 0` (Bulletproofs 2017/1066, Thm 1 / Def 1).

Proof outline — each step is discharged by the named lemma (Steps 1, 2 in `OffsetPin`/`OffsetBundle`,
Step 4 in `OffsetEliminate`):

* Step 1 — interpolation in `r` (`node_facts`): three `r`-children pin `(P_L, P_R)` to quadrants
  `a*, β, α, b*`.
* Step 2 — the `t̂`-quadratic forces the cross terms to zero, `⟨a*,β⟩ = ⟨α,b*⟩ = 0` (`node_facts`;
  fixes the `r`-arity at `3`).
* Step 3 — `x`-Vandermonde read-off (`bcoefLG_eq`, `bcoefRH_eq`): the `P_L` `𝐆`-blocks match `f_L`,
  the `P_L` `𝐡'`-blocks are the residual strays `β`, and the `P_R` `𝐡'`-blocks match `f_R`.
* Step 4 — the offset eliminates the residual strays (`strayW_zero`; fixes the `z`-arity
  at `q+2`).
* Step 5 — witness or relation (`star_of_hbz`, tight `clause3_holds`, `relCand_valid`).

This is what the after-`r` ordering alone cannot give, and what the offset provides: the tight relation
`R_GBP'` with *no* `𝐇`-component in the vector commitments. `W_V` full column rank is intrinsic
(`s.hWV`); `0 < n`. The spec (`Relation`, `Arithmetization`) is unchanged; this file is additive.
-/

namespace Sigma.Protocols.GBPImproved.Offset

open Sigma.Protocols.GBP Sigma.Protocols.GBPImproved
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 3 (`x`-Vandermonde read-off, `𝐆`-quadrant).** When the bundle's candidates vanish, the
`bcoefL`-`𝐆` block of the `P_L`-side representation at every degree `ℓ ≤ c+2` equals the honest
`f_L` coefficient, the mask slot carrying the committed part plus the *bundle's* binding offset
`z^{q+1}·𝟙`. (The `𝐡'`-block at each degree is the residual stray `β`, killed in Step 4.) -/
lemma bcoefLG_eq {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0) (ℓ : Fin (c + 3)) :
    (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).1
      = honestFL' s (chalYO tree i) (chalZO tree i j)
          (candWitness s tree).aL (candWitness s tree).aO
          (fun t => ((bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1 t
              - (chalZO tree ⟨0, hn⟩ 0) ^ (q + 1))
            + (chalZO tree i j) ^ (q + 1))
          (candWitness s tree).aC ℓ := by
  rcases q_slot_casesL ℓ with hq | hq | ⟨k, hq⟩ | hq
  · have hqi : ℓ = ⟨0, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_self)
    rw [hqi, honestFL'_at_AL]
    exact (alCand_readoff hn s tree i j hc).1
  · have hqi : ℓ = ⟨1, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hqi, honestFL'_at_AO, (pOpenVecL_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]
    simp only [candWitness, dif_pos hn]
  · have hqi : ℓ = ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))))))))))))))
    rw [hqi, honestFL'_at_AC, (pOpenVecL_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]
    simp only [candWitness, dif_pos hn]
  · have hqi : ℓ = ⟨c + 2, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [hqi, honestFL'_at_SL]
    exact (slCand_readoff hn s tree i j hc).1

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 3 (`x`-Vandermonde read-off, `𝐡'`-quadrant).** Companion to `bcoefLG_eq` on the `P_R`
side: the `bcoefR`-`𝐡'` block at every degree equals the honest `f_R` coefficient (public weights,
`𝐲∘aR + w_L`, `𝐲∘sR`). -/
lemma bcoefRH_eq {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0) (ℓ : Fin (c + 3)) :
    (bcoefR s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1
      = honestFR' s (chalYO tree i) (chalZO tree i j)
          (candWitness s tree).aR
          (hadamard (bcoefR s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).2.1
            (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n))) ℓ := by
  rcases q_slot_casesR ℓ with ⟨k, hq⟩ | hq | hq | hq
  · have hqi : ℓ = ⟨c - (k : ℕ) - 1, by have := k.isLt; omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
                (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))))))))))))))
    rw [hqi, honestFR'_at_WtC]
    exact (pubVecR_readoff s tree i j _ _ hc).2
  · have hqi : ℓ = ⟨c, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [hqi, honestFR'_at_WtO]
    exact (pubVecR_readoff s tree i j _ _ hc).2
  · have hqi : ℓ = ⟨c + 1, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self))))
    rw [hqi, honestFR'_at_AR]
    exact arCand_readoff hn s tree i j hc
  · have hqi : ℓ = ⟨c + 2, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))))
    rw [hqi, honestFR'_at_SR, (pOpenVecR_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).2.1]
    funext t; simp only [hadamard]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 5 (per-bundle relation `(★)`).** With the strays eliminated (Step 4), the quadrant families
are the honest `f_L, f_R`, each node's `t̂` equals their convolution value (`tHat_eq_quad`), and the
`eq1` collision supplies `Heq`; `star_at_bundle'` then pins the per-bundle identity `(★)`:
`∑_g y^g (aL∘aR − aO)_g + ∑_q z^{ℓ+1} (W_L aL + ⋯ + W_V v + c)_q = 0`. -/
lemma star_of_hbz {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (hstray : ∀ ℓ : Fin (c + 3), strayW s tree hn ℓ = 0) :
    (∑ g : Fin n, ((chalYO tree i : Fˣ) : F) ^ (g : ℕ)
        * ((candWitness s tree).aL g * (candWitness s tree).aR g
            - (candWitness s tree).aO g))
      + ∑ ℓ : Fin q, (chalZO tree i j) ^ ((ℓ : ℕ) + 1)
          * (s.WL *ᵥ (candWitness s tree).aL + s.WR *ᵥ (candWitness s tree).aR
              + s.WO *ᵥ (candWitness s tree).aO
              + (∑ k, s.WC k *ᵥ (candWitness s tree).aC k)
              + s.WV *ᵥ (candWitness s tree).v + s.cc) ℓ = 0 := by
  set sL : Fin n → F := fun t => ((bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1 t
      - (chalZO tree ⟨0, hn⟩ 0) ^ (q + 1))
    + (chalZO tree i j) ^ (q + 1) with hsL
  set sR : Fin n → F := hadamard (bcoefR s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).2.1
    (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n)) with hsR
  have hHla : ∀ l : Fin (2 * c + 5),
      aStarF tree i j l
        = fun t => ∑ p : Fin (c + 3),
          (chalXO tree i j l) ^ (p : ℕ)
            * honestFL' s (chalYO tree i) (chalZO tree i j)
                (candWitness s tree).aL (candWitness s tree).aO sL
                (candWitness s tree).aC p t := by
    intro l
    rw [leafAStar_recover s tree i j l,
      sum_truncate' (chalXO tree i j l)
        (fun p => (bcoefL s tree i j p).1)
        (fun ℓ => honestFL' s (chalYO tree i) (chalZO tree i j)
          (candWitness s tree).aL (candWitness s tree).aO sL (candWitness s tree).aC ℓ)
        (fun ℓ => bcoefLG_eq hn s tree i j hbz ℓ)
        (fun p hp => (bcoefL_high_zero hn s tree i j hbz p hp).1)]
    funext t; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hHlb : ∀ l : Fin (2 * c + 5),
      bStarF tree i j l
        = fun t => ∑ ℓ : Fin (c + 3),
          (chalXO tree i j l) ^ (ℓ : ℕ)
            * honestFR' s (chalYO tree i) (chalZO tree i j)
                (candWitness s tree).aR sR ℓ t := by
    intro l
    rw [leafBStar_recover s tree i j l,
      sum_truncate' (chalXO tree i j l)
        (fun ℓ => (bcoefR s tree i j ℓ).2.1)
        (fun ℓ => honestFR' s (chalYO tree i) (chalZO tree i j)
          (candWitness s tree).aR sR ℓ)
        (fun ℓ => bcoefRH_eq hn s tree i j hbz ℓ)
        (fun ℓ hq => (bcoefR_high_zero hn s tree i j hbz ℓ hq).2)]
    funext t; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hHeq := heq_of_ghCand_zero s tree i j (hbz _ (by
    rw [bundleCands]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))))
  have hHeqfull : (∑ l, (Matrix.vandermonde
        (fun l => (chalXO tree i j l)))⁻¹ ⟨c + 1, by omega⟩ l
        • ip (aStarF tree i j l) (bStarF tree i j l))
      = (ip (hadamard (vinv (powers ((chalYO tree i : Fˣ) : F) n))
              ((chalZO tree i j)
                • powers (chalZO tree i j) q ᵥ* s.WR))
            ((chalZO tree i j)
              • powers (chalZO tree i j) q ᵥ* s.WL)
          - (chalZO tree i j)
              * ip (powers (chalZO tree i j) q) s.cc)
        - ip ((chalZO tree i j)
            • (powers (chalZO tree i j) q ᵥ* s.WV))
          (candWitness s tree).v := by
    have hq : ∀ l : Fin (2 * c + 5),
        ip (aStarF tree i j l) (bStarF tree i j l)
          = ip (leafA tree i j l 0) (leafB tree i j l 0) :=
      fun l => (tHat_eq_quad hn s tree i j hbz hstray l).symm
    have hsum : (∑ l, (Matrix.vandermonde
          (fun l => (chalXO tree i j l)))⁻¹ ⟨c + 1, by omega⟩ l
          • ip (aStarF tree i j l) (bStarF tree i j l))
        = eqDj s tree i j - eqAj s tree i j := by
      simp only [hq]
      rw [eqAj]; simp only [vandInv_eq (chalX_inj tree i j), smul_eq_mul]; ring
    rw [hsum, hHeq, eqDj]
  have hst := star_at_bundle' s (chalYO tree i) (chalZO tree i j)
    (candWitness s tree).aL (candWitness s tree).aR (candWitness s tree).aO sL sR
    (candWitness s tree).aC (candWitness s tree).v
    (fun l => (chalXO tree i j l)) (chalX_inj tree i j)
    (fun l => aStarF tree i j l) (fun l => bStarF tree i j l)
    hHla hHlb hHeqfull
  simpa only [powers] using hst

/-- **Step 5 (tight clause 3).** The tight vector-commitment clause `A_C⁽ᵏ⁾ = ⟨aC,𝐆⟩ + γC·h`,
with **no** `𝐇`-component. This is exactly where the elimination argument (Step 4) is needed: the degree-`(k+2)`
`𝐡'`-block is the residual stray, which Step 4 (`strayW_zero`) forces to `0`. -/
lemma clause3_holds {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (hstray : ∀ ℓ : Fin (c + 3), strayW s tree hn ℓ = 0) (k : Fin c) :
    s.AC k = msm ((candWitness s tree).aC k) s.gs + (candWitness s tree).γC k • s.h := by
  have hp := bundle_openL s tree hacc ⟨0, hn⟩ 0 ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩
  rw [PcoefL'_AC] at hp
  have hzH : (bcoefL s tree ⟨0, hn⟩ 0 ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩).2.1 = 0 := by
    have h := hstray ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩
    refine hadamard_yinv_cancel (chalYO tree ⟨0, hn⟩) _ 0 ?_
    rw [show hadamard (0 : Fin n → F)
        (vinv (powers ((chalYO tree ⟨0, hn⟩ : Fˣ) : F) n)) = 0 from by
      funext t; simp [hadamard]]
    exact h
  rw [hzH, msm_zero_left, add_zero] at hp
  simp only [candWitness, dif_pos hn]
  exact hp

/-- **Step 5 (witness or relation).** On an accepting tree, if the recovered `candWitness` fails
`rel`, then `relCand` is a genuine non-trivial discrete-log relation among `gens s`.

Contrapositive: every candidate opens `0` (`relCandList_msm_zero`), so if `relCand` were trivial
then all candidates vanish. The node facts (`node_facts`, Steps 1–2) feed the elimination argument
(`strayW_zero`, Step 4); Step 3 read-offs then give `(★)` on the `i₀`-row and `j=0`-column
(`star_of_hbz`), `clauses12_of_LZ` deaggregates to clauses 1, 2, and `clause3_holds`/`clause4_holds`
supply the tight clauses 3, 4. Hence `rel s candWitness = true`, contradicting `hfail`. -/
theorem relCand_valid {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hacc : (arithRed' (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK' F G n q c) rfl s tree)
    (hfail : rel s (candWitness s tree) ≠ true) :
    IsNontrivialDLRel (gens s) (relCand s tree) := by
  by_contra hcontra
  have hzero : ∀ rc ∈ relCandList s tree hn, rc = 0 := by
    intro c hmem
    by_contra hcne
    apply hcontra
    have hex : ∃ x ∈ relCandList s tree hn, decide (IsNontrivialDLRel (gens s) x) = true :=
      ⟨c, hmem, decide_eq_true ⟨hcne, relCandList_msm_zero hn s tree hacc c hmem⟩⟩
    have hp := find?_getD_prop (fun v => decide (IsNontrivialDLRel (gens s) v))
      (relCandList s tree hn) 0 hex
    rw [relCand, dif_pos hn]
    exact of_decide_eq_true hp
  have hbzAll : ∀ (i : Fin n) (j : Fin (q + 2)), ∀ rc ∈ bundleCands s tree hn i j, rc = 0 :=
    fun i j rc hc => hzero rc (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_flatMap.mpr ⟨j, List.mem_finRange j, hc⟩⟩)
  have hnodeAll : ∀ (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)),
      ip (aStarF tree i j l) (betaF tree i j l) = 0 :=
    fun i j l => (node_facts hn s tree i j (hbzAll i j) l).1
  have hstray := strayW_zero hn s tree hbzAll hnodeAll
  have hclauses12 := clauses12_of_LZ hn s (candWitness s tree).aL (candWitness s tree).aR
    (candWitness s tree).aO (candWitness s tree).aC (candWitness s tree).v
    (fun i => ((chalYO tree i : Fˣ) : F)) (chalY_inj tree)
    (fun i j => (chalZO tree i (Fin.castLE (by omega) j)))
    (chalZres_inj tree ⟨0, hn⟩)
    (fun j => star_of_hbz hn s tree ⟨0, hn⟩ (Fin.castLE (by omega) j)
      (hbzAll ⟨0, hn⟩ (Fin.castLE (by omega) j)) hstray)
    (fun i => star_of_hbz hn s tree i (Fin.castLE (by omega) 0)
      (hbzAll i (Fin.castLE (by omega) 0)) hstray)
  exact hfail (by
    simp only [rel, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hclauses12.1, hclauses12.2⟩,
        fun k => clause3_holds hn s tree hacc hstray k⟩,
      fun k => clause4_holds hn s tree hacc k⟩)

/-! ## The extractor -/

/-- The extractor: compute `candWitness` (explicit Vandermonde recovery, poly-time), check
the decidable `rel`; on failure return the (explicit, computed) collision candidate if it
is a genuine relation. No `Classical.choice` over an existence and no discrete-log
inversion. -/
def arithExtractData {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c) :
    Witness F n m c ⊕ (Fin (n + n + 2) → F) :=
  if rel s (candWitness s tree) = true then
    Sum.inl (candWitness s tree)
  else if IsNontrivialDLRel (gens s) (relCand s tree) then
    Sum.inr (relCand s tree)
  else
    Sum.inl (candWitness s tree)

end Sigma.Protocols.GBPImproved.Offset

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- **Knowledge soundness (`(n, q+2, 2c+5, 3)`-special soundness) of the improved
arithmetization reduction** (the protocol of record: the opening vectors are the never-sent
output witness, decorating the leaves after the binding challenge; binding offset on the
mask slot). From an accepting decorated tree the extractor returns **either** a valid
`R_GBP'` witness — in particular every vector commitment opens with *no* `𝐇`-component —
**or** a non-trivial discrete-log relation among `gens s`. -/
theorem arithRed'_sound {n q m c : ℕ} (hn : 0 < n) :
    (arithRed' (F := F) (G := G) n q m c).Sound (mk := Offset.arithMK' F G n q c) rfl
      (brk := fun s v => IsNontrivialDLRel (gens s) v) Offset.arithExtractData := by
  intro s tree hacc
  by_cases h : rel s (Offset.candWitness s tree) = true
  · have he : Offset.arithExtractData s tree = Sum.inl (Offset.candWitness s tree) := if_pos h
    exact ⟨fun w hw => by rw [he] at hw; obtain rfl := Sum.inl.inj hw; exact h,
           fun v hv => by rw [he] at hv; simp at hv⟩
  · have hbrk : IsNontrivialDLRel (gens s) (Offset.relCand s tree) :=
      Offset.relCand_valid hn s tree hacc h
    have he : Offset.arithExtractData s tree = Sum.inr (Offset.relCand s tree) := by
      rw [Offset.arithExtractData, if_neg h, if_pos hbrk]
    exact ⟨fun w hw => by rw [he] at hw; simp at hw,
           fun v hv => by rw [he] at hv; obtain rfl := Sum.inr.inj hv; exact hbrk⟩

end Sigma.Protocols.GBPImproved
