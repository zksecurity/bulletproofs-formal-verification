/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBP.ArithmetizationSound.ReadOff
/-!
# Computational special soundness of the Generalized Bulletproofs arithmetization

`(k₁, k₂, k₃) = (n, q+1, 2·nPrime c + 3)`-special soundness of the arithmetization protocol
(`Sigma.Protocols.GBP.arithRed`), in the witness-or-break sense of `Sigma.Reduction.Sound`: from
any `(n, q+1, 2·nPrime c+3)`-tree of accepting transcripts a deterministic extractor returns
**either** a witness for `R_GBP` **or** a non-trivial discrete-log relation among the generators
`Γ = 𝐆 ⧺ 𝐇 ⧺ [g, h]` — a nonzero `v` with `⟨v, Γ⟩ = 0` (Bulletproofs 2017/1066, Thm 1 / Def 1).
The tree fixes the first message `(A_I, A_O, S)` at the root and branches on the three challenges
`y, z, x`: `n` distinct children on `y`, under each `q+1` distinct on `z` (carrying `{T_i}`), under
each `2·nPrime c+3` distinct on `x` (carrying the opening); every root-to-leaf path accepts. The
three arities are forced by the three interpolations below.

Proof outline — each step is discharged by the named lemma (Step 3, 4 live in `Openings`,
the Vandermonde and convolution cores in `Pcoef`):

* Step 1 — `x`-Vandermonde read-off (`bcoefG_eq`, `bcoefH_eq`; `eq2_extract`).
* Step 2 — per-bundle relation `(★)` (`star_of_hbz`; `tcoeff_expand`, `star_at_bundle`).
* Step 3 — deaggregation over `z` then `y` (`clauses12_of_LZ`).
* Step 4 — commitment openings (`clause3_holds`, `clause4_holds`).
* Step 5 — witness or relation (`relCand_valid`, `arithExtract`).

Unlike the improved arithmetization, the vector commitments here carry the `⟨aux, 𝐇⟩` slack the
circuit cannot reach; the proof tolerates it (clause 3 keeps `aux`) rather than removing it.
`W_V` full column rank is intrinsic (`s.hWV`); `0 < n`. The spec (`Relation`, `Arithmetization`)
is unchanged; this file is additive.
-/

namespace Sigma.Protocols.GBP

open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 1 (`x`-Vandermonde read-off, `𝐆`-side).** Fix `(y, z)`. The `2·nPrime c+3` children
sharing them use distinct `x`, so inverting the Vandermonde in `x` (`eq2_extract`) writes each
degree-`p` coefficient of the verifier's `P(X)` as a representation in the `(𝐆, 𝐡', H)` basis.
When the bundle's candidates all vanish, the `𝐆`-block at every degree `ℓ ≤ n'+1` equals the
honest `f_L` coefficient: public degrees give `0`, the `A_I` slot `aL + (z·WR)⊙yinv`, and the
`A_C/A_O/S` slots the reference wires. -/
lemma bcoefG_eq {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0) (ℓ : Fin (nPrime c + 2)) :
    (bcoef s tree i j ⟨(ℓ : ℕ), by omega⟩).1
      = honestFL s (chalY tree i) (chalZ tree i j)
          (candWitness s tree).aL (candWitness s tree).aO
          (bcoef s tree ⟨0, hn⟩ 0 ⟨nPrime c + 1, by omega⟩).1 (candWitness s tree).aC ℓ := by
  rcases q_slot_cases ℓ with hq | ⟨k, hq⟩ | hq | ⟨k, hq⟩ | hq | hq
  · have hqi : ℓ = ⟨0, by simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_self)
    rw [hqi, honestFL_at_pub s _ _ _ _ _ _ _ (Or.inl rfl), (pubVec_readoff s tree i j _ _ hc).1]
  · have hqi : ℓ = ⟨(k : ℕ) + 1, by have := k.isLt; simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))))))))
    rw [hqi, honestFL_at_pub s _ _ _ _ _ _ _ (Or.inr ⟨k, rfl⟩), (pubVec_readoff s tree i j _ _ hc).1]
  · have hqi : ℓ = ⟨c + 1, by simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hqi, honestFL_at_AI, (aiCand_readoff hn s tree i j hc).1]
  · have hqi : ℓ = ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))))))))
    rw [hqi, honestFL_at_AC, (pOpenVec_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]
    simp only [candWitness, dif_pos hn]
  · have hqi : ℓ = ⟨nPrime c, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))
    rw [hqi, honestFL_at_AO, (pOpenVec_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]
    simp only [candWitness, dif_pos hn]
  · have hqi : ℓ = ⟨nPrime c + 1, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [hqi, honestFL_at_S, (pOpenVec_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 1 (`x`-Vandermonde read-off, `𝐡'`-side).** Companion to `bcoefG_eq`: the `𝐡'`-block of
the same representation equals the honest `f_R` coefficient at every degree `ℓ ≠ n'`. The lone
degree `n'` (the `A_O` `𝐇`-part) is unconstrained — the base relation tolerates this slack — and
is absorbed downstream by `conv_eq`. Cross-bundle degrees rescale into the `i`-bundle `h'`-basis. -/
lemma bcoefH_eq {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0) (ℓ : Fin (nPrime c + 2)) (hqne : (ℓ : ℕ) ≠ nPrime c) :
    (bcoef s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1
      = honestFR s (chalY tree i) (chalZ tree i j) (candWitness s tree).aR
          (hadamard (bcoef s tree ⟨0, hn⟩ 0 ⟨nPrime c + 1, by omega⟩).2.1
            (vinv (powers ((chalY tree ⟨0, hn⟩ : Fˣ) : F) n))) (candWitness s tree).aux ℓ := by
  rcases q_slot_cases ℓ with hq | ⟨k, hq⟩ | hq | ⟨k, hq⟩ | hq | hq
  · have hqi : ℓ = ⟨0, by simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_self)
    rw [hqi, honestFR_at_WtO]; exact (pubVec_readoff s tree i j _ _ hc).2
  · have hqi : ℓ = ⟨(k : ℕ) + 1, by have := k.isLt; simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))))))))
    rw [hqi, honestFR_at_WtC]; exact (pubVec_readoff s tree i j _ _ hc).2
  · have hqi : ℓ = ⟨c + 1, by simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hqi, honestFR_at_WL]; exact (aiCand_readoff hn s tree i j hc).2
  · have hqi : ℓ = ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))))))))
    rw [hqi, honestFR_at_aux, (pOpenVec_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).2]
    funext i'; simp only [candWitness, dif_pos hn, hadamard]
  · exact absurd hq hqne
  · have hqi : ℓ = ⟨nPrime c + 1, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [hqi, honestFR_at_sR, (pOpenVec_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).2]
    funext i'; simp only [hadamard]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 2 (per-bundle relation `(★)`).** When every candidate at the L-bundle `(i, j)` vanishes,
Step 1 makes the leaf openings the honest `f_L, f_R` (`bcoefG_eq`/`bcoefH_eq`/`bcoef_high_zero`
fed through `leafG/H_recover` and `sum_truncate`). The `n'`-coefficient of `⟨f_L, f_R⟩` expands
without invoking any constraint (`tcoeff_expand`) to `δ` plus the linear `R1CS` form plus the
Hadamard term; with the `eq1` opening (`heq_of_ghCand_zero`), `star_at_bundle` pins the per-bundle
identity `(★)`: `∑_g y^g (aL∘aR − aO)_g + ∑_q z^{ℓ+1} (W_L aL + ⋯ + W_V v + c)_q = 0`. -/
lemma star_of_hbz {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0) :
    (∑ g : Fin n, ((chalY tree i : Fˣ) : F) ^ (g : ℕ)
        * ((candWitness s tree).aL g * (candWitness s tree).aR g - (candWitness s tree).aO g))
      + ∑ ℓ : Fin q, ((chalZ tree i j : Fˣ) : F) ^ ((ℓ : ℕ) + 1)
          * (s.WL *ᵥ (candWitness s tree).aL + s.WR *ᵥ (candWitness s tree).aR
              + s.WO *ᵥ (candWitness s tree).aO + (∑ k, s.WC k *ᵥ (candWitness s tree).aC k)
              + s.WV *ᵥ (candWitness s tree).v + s.cc) ℓ = 0 := by
  set sL := (bcoef s tree ⟨0, hn⟩ 0 ⟨nPrime c + 1, by omega⟩).1 with hsL
  set sR := hadamard (bcoef s tree ⟨0, hn⟩ 0 ⟨nPrime c + 1, by omega⟩).2.1
    (vinv (powers ((chalY tree ⟨0, hn⟩ : Fˣ) : F) n)) with hsR
  set fR := fun ℓ : Fin (nPrime c + 2) => (bcoef s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1 with hfR
  have hHla : ∀ l : Fin (2 * nPrime c + 3),
      (leafO tree i j l).2.2.1
        = fun i' => ∑ p : Fin (nPrime c + 2),
          ((chalX tree i j l : Fˣ) : F) ^ (p : ℕ)
            * honestFL s (chalY tree i) (chalZ tree i j) (candWitness s tree).aL
                (candWitness s tree).aO sL (candWitness s tree).aC p i' := by
    intro l
    rw [leafG_recover s tree i j l,
      sum_truncate ((chalX tree i j l : Fˣ) : F)
        (fun p => (bcoef s tree i j p).1)
        (fun ℓ => honestFL s (chalY tree i) (chalZ tree i j) (candWitness s tree).aL
          (candWitness s tree).aO sL (candWitness s tree).aC ℓ)
        (fun ℓ => bcoefG_eq hn s tree i j hbz ℓ)
        (fun p hp => (bcoef_high_zero hn s tree i j hbz p hp).1)]
    funext i'; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hHlb : ∀ l : Fin (2 * nPrime c + 3),
      (leafO tree i j l).2.2.2
        = fun i' => ∑ ℓ : Fin (nPrime c + 2),
          ((chalX tree i j l : Fˣ) : F) ^ (ℓ : ℕ) * fR ℓ i' := by
    intro l
    rw [leafH_recover s tree i j l,
      sum_truncate ((chalX tree i j l : Fˣ) : F)
        (fun p => (bcoef s tree i j p).2.1) fR (fun ℓ => rfl)
        (fun p hp => (bcoef_high_zero hn s tree i j hbz p hp).2)]
    funext i'; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hHconv := conv_eq s (chalY tree i) (chalZ tree i j) (candWitness s tree).aL
    (candWitness s tree).aR (candWitness s tree).aO sL sR (candWitness s tree).aC (candWitness s tree).aux
    fR (fun ℓ hqne => bcoefH_eq hn s tree i j hbz ℓ hqne)
  have hHeq := heq_of_ghCand_zero s tree i j (hbz _ (by rw [bundleCands]; exact List.mem_cons_of_mem _ (
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  have hHeqfull : (∑ l, (Matrix.vandermonde
        (fun l => ((chalX tree i j l : Fˣ) : F)))⁻¹ ⟨nPrime c, by omega⟩ l
        • ip ((leafO tree i j l).2.2.1)
            ((leafO tree i j l).2.2.2))
      = (ip (hadamard (vinv (powers ((chalY tree i : Fˣ) : F) n))
              (((chalZ tree i j : Fˣ) : F) • powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WR))
            (((chalZ tree i j : Fˣ) : F) • powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL)
          - ((chalZ tree i j : Fˣ) : F) * ip (powers ((chalZ tree i j : Fˣ) : F) q) s.cc)
        - ip (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WV)) (candWitness s tree).v := by
    have hsum : (∑ l, (Matrix.vandermonde
          (fun l => ((chalX tree i j l : Fˣ) : F)))⁻¹ ⟨nPrime c, by omega⟩ l
          • ip ((leafO tree i j l).2.2.1)
              ((leafO tree i j l).2.2.2))
        = eqDj s tree i j - eqAj s tree i j := by
      rw [eqAj]; simp only [vandInv_eq (chalX_inj tree i j), smul_eq_mul]; ring
    rw [hsum, hHeq, eqDj]
  have hst := star_at_bundle s (chalY tree i) (chalZ tree i j) (candWitness s tree).aL
    (candWitness s tree).aR (candWitness s tree).aO sL sR (candWitness s tree).aC (candWitness s tree).aux
    (candWitness s tree).v (fun l => ((chalX tree i j l : Fˣ) : F)) (chalX_inj tree i j)
    (fun l => (leafO tree i j l).2.2.1)
    (fun l => (leafO tree i j l).2.2.2)
    hHla fR hHlb hHconv hHeqfull
  simpa only [powers] using hst

/-- **Step 5 (witness or relation).** On an accepting tree, if the explicitly-recovered
`candWitness` fails `rel`, then `relCand` is a genuine non-trivial discrete-log relation among
`gens s`.

Contrapositive: every candidate has `msm · gens = 0` (`relCandList_msm_zero`) — the difference
candidates open equal commitments, the high-degree ones open `0` directly; so if `relCand` were
trivial, `find?` (`find?_getD_prop`) shows *every* candidate vanishes. Step 2 (`star_of_hbz`) then gives `(★)` on the `i₀`-row and `j=0`-
column; Step 3 (`clauses12_of_LZ`) deaggregates these to relation clauses 1, 2; Step 4
(`clause3_holds`, `clause4_holds`) supplies clauses 3, 4. Hence `rel s candWitness = true`,
contradicting `hfail`. -/
theorem relCand_valid {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
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
  have hbz_row : ∀ j : Fin (q + 1), ∀ rc ∈ bundleCands s tree hn ⟨0, hn⟩ j, rc = 0 := fun j rc hc =>
    hzero rc (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, hc⟩))
  have hbz_col : ∀ i : Fin n, ∀ rc ∈ bundleCands s tree hn i 0, rc = 0 := fun i rc hc =>
    hzero rc (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hc⟩))
  have hclauses12 := clauses12_of_LZ hn s (candWitness s tree).aL (candWitness s tree).aR
    (candWitness s tree).aO (candWitness s tree).aC (candWitness s tree).v
    (fun i => ((chalY tree i : Fˣ) : F)) (chalY_inj tree)
    (fun i j => ((chalZ tree i j : Fˣ) : F)) (chalZ_inj tree ⟨0, hn⟩)
    (fun j => star_of_hbz hn s tree ⟨0, hn⟩ j (hbz_row j))
    (fun i => star_of_hbz hn s tree i 0 (hbz_col i))
  exact hfail (by
    simp only [rel, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hclauses12.1, hclauses12.2⟩, fun k => clause3_holds hn s tree hacc k⟩,
      fun k => clause4_holds hn s tree hacc k⟩)

/-- The extractor. It **computes** `candWitness` (explicit Lagrange-form Vandermonde recovery
`vandInv` and the Gaussian-elimination `gaussLeftInv` — genuinely poly-time, no `d!`-permutation
sums and no minor search) and
checks the *decidable* relation `rel s candWitness`; on success it returns the witness. On failure
it checks the *decidable* `IsNontrivialDLRel (gens s) (relCand …)` for the (explicit, computed)
collision candidate and, if it is a genuine relation, returns it as the break. There is **no
`Classical.choice` over an existence and no discrete-log inversion** — both branches are decidable
tests on explicitly-recovered data. -/
def arithExtract {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) : Witness F n m c ⊕ (Fin (n + n + 2) → F) :=
  if rel s (candWitness s tree) = true then
    Sum.inl (candWitness s tree)
  else if IsNontrivialDLRel (gens s) (relCand s tree) then
    Sum.inr (relCand s tree)
  else
    Sum.inl (candWitness s tree)

/-- **Knowledge soundness (`(n, q+1, 2·nPrime c+3)`-special soundness) of the arithmetization
reduction.** From an accepting decorated tree the extractor returns **either** a witness
(`Sum.inl`, valid by the `rel` check) **or** a non-trivial discrete-log relation among `gens s`
(`Sum.inr`, real by `relCand_valid`). The `W_V`-full-column-rank precondition is intrinsic to the
statement (`s.hWV`). (`0 < n` is still necessary: for `n = 0` the tree is path-free, acceptance is
vacuous, and a statement with `c ≠ 0` has no witness and no relation.) -/
theorem arithRed_sound {n q m c : ℕ} (hn : 0 < n) :
    (arithRed (F := F) (G := G) n q m c).Sound (mk := arithMK F G n q c) rfl
      (brk := fun s v => IsNontrivialDLRel (gens s) v) arithExtract := by
  intro s tree hacc
  by_cases h : rel s (candWitness s tree) = true
  · have he : arithExtract s tree = Sum.inl (candWitness s tree) := if_pos h
    exact ⟨fun w hw => by rw [he] at hw; obtain rfl := Sum.inl.inj hw; exact h,
           fun v hv => by rw [he] at hv; simp at hv⟩
  · have hbrk : IsNontrivialDLRel (gens s) (relCand s tree) :=
      relCand_valid hn s tree hacc h
    have he : arithExtract s tree = Sum.inr (relCand s tree) := by
      rw [arithExtract, if_neg h, if_pos hbrk]
    exact ⟨fun w hw => by rw [he] at hw; simp at hw,
           fun v hv => by rw [he] at hv; obtain rfl := Sum.inr.inj hv; exact hbrk⟩

end Sigma.Protocols.GBP
