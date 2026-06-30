/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.ReadOff
import Sigma.Protocols.GBPImproved.ArithmetizationSound.Honest
import Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetSound

/-!
# Computational special soundness of the pre-`r`-ordering improved arithmetization

`(k₁, k₂, k₃, k₄) = (n, q+1, 2c+5, 2)`-special soundness of the **pre-binding-challenge
ordering variant** `Sigma.Protocols.GBPImproved.arithRedPreR` — the improved
arithmetization with the opening `(τ_x, μ_L, μ_R, f_L(x), f_R(x))` sent *before* the binding
challenge `r` — in the witness-or-break sense of `Sigma.Reduction.Sound`: from an accepting
`(n, q+1, 2c+5, 2)`-tree the extractor returns **either** a witness for the *tighter* relation
`R_GBP'` (no auxiliary `𝐇`-openings) **or** a non-trivial discrete-log relation among the
generators `(𝐆, 𝐇, g, h)`. Notably, this ordering needs **no binding offset**.

Compared to the base proof (`Sigma.Protocols.GBP.arithmetization_compSpeciallySound`):

* the new fourth round is the **binding challenge** `r`, of arity `2`. Because the prover's
  opening is sent *before* `r` and the `eq2` identity is affine in `r`, the two `r`-children
  interpolate (`r_interpolate`/`node_open`) to *exact* split openings: `P_L(x)` opens against
  `(𝐆, H)` only and `P_R(x)` against `(𝐲⁻¹⊙𝐇, H)` only. Every `𝐇`-mass on the `𝐆`-side is
  forced to zero outright, which is why the extracted witness needs no `aux` fields and the
  *tight* clause 3 (`A_C⁽ᵏ⁾ = ⟨a_C⁽ᵏ⁾,𝐆⟩ + γ_C⁽ᵏ⁾·H`) holds under acceptance alone
  (`clause3_holds'`);
* the `x`-round arity shrinks from `4c+7` to `2c+5` (the `t`-polynomial has degree `2c+4`);
* the read-off layer is *denser but simpler*: every degree `0…c+2` of both split coefficient
  families is a named slot, so no `conv_eq`-style escape hatch is needed.

The single added precondition is, as in the base proof, that `W_V` has a left inverse (full
column rank `m`), already intrinsic to the statement (`s.hWV`).

## Scope: the message ordering is load-bearing, and the binding offset replaces it

The interpolation step needs the *same* `(a, b)` at both `r`-children, which this ordering
provides by construction (the opening is part of the shared transcript prefix). With the
opening — sent in the clear, or proven by the inner-product argument — *after* `r` (the
ordering of the protocol of record `Sigma.Protocols.GBPImproved.arithRed'`, forced in
the log-size variant by the `r`-scaled IPA generators), the per-`r` opening of `P_L + r·P_R`
may depend on `r`, and **without further measures `R_GBP'` fails**. Concretely, on the
statement with all-zero weight matrices, `m = 0`, and `A_C⁽⁰⁾ := hs 0` (a pure `𝐇`-generator,
so `R_GBP'` has no witness), the prover that runs the protocol honestly on the wires `0` except
for `b_r := f_R(x) + r⁻¹·x²·(e₀ ⊙ 𝐲)` passes `eq1`, the `t̂ = ⟨a, b_r⟩` check (`a = 0`), and
opens `P(r)` genuinely at every challenge — an accepting tree exists over a free module whose
generators admit no non-trivial discrete-log relation, so no extractor can be
knowledge soundness for `R_GBP'`. More generally the `t̂`-consistency across `r`-children
constrains stray `𝐇`-mass `β` only through `⟨f_L\text{-side}, β⟩`, which vanishes on
coordinates where all `f_L`-slots are zero (e.g. padding gates).

The **binding offset** `z^{q+1}·𝟙` on the mask slot of `f_L` — part of the spec'd
`arithRed'` — closes exactly this gap: the pairing then contains
`z^{q+1}·Σ_t β_t·y^t`, which nothing committed before `z` can produce or cancel, so the `z`-
and `y`-subtrees force `β = 0`. Its `(n, q+2, 2c+5, 3)`-special soundness for `R_GBP'` is
**proven** in `Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetSound`
(`Sigma.Protocols.GBPImproved.arithRed'_sound`, imported here); the
present file's theorem remains the formal record that the pre-`r` ordering alone — with no
offset — already achieves `R_GBP'`.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The degree-by-degree `𝐆`-side read-off.** When all bundle candidates vanish, the
extracted `bcoefL`-`𝐆` coefficient at every degree `ℓ ≤ c+2` equals the honest `f_L`
coefficient: `A_L` gives `aL + (z·W_R)∘y⁻¹`, and the `A_O/A_C/S_L` slots give the reference
wires. -/
lemma bcoefL_eq {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1))
    (hbz : ∀ rc ∈ bundleCands' s tree hn i j, rc = 0) (ℓ : Fin (c + 3)) :
    (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).1
      = honestFL' s (chalYP tree i) ↑(chalZP tree i j)
          (candWitness' s tree).aL (candWitness' s tree).aO
          (bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1 (candWitness' s tree).aC ℓ := by
  rcases q_slot_casesL ℓ with hq | hq | ⟨k, hq⟩ | hq
  · have hqi : ℓ = ⟨0, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_self)
    rw [hqi, honestFL'_at_AL, alCand_readoff hn s tree i j hc]
  · have hqi : ℓ = ⟨1, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hqi, honestFL'_at_AO, (pOpenVecL_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]
    simp only [candWitness', dif_pos hn]
  · have hqi : ℓ = ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)))))))))))
    rw [hqi, honestFL'_at_AC, (pOpenVecL_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]
    simp only [candWitness', dif_pos hn]
  · have hqi : ℓ = ⟨c + 2, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [hqi, honestFL'_at_SL, (pOpenVecL_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The degree-by-degree `𝐇`-side read-off.** The extracted `bcoefR`-`𝐇'` coefficient at
every degree `ℓ ≤ c+2` equals the honest `f_R` coefficient: public weights at the `W̃_C/W̃_O`
slots, `𝐲∘aR + w_L` at the `A_R` slot, `𝐲∘sR` at the `S_R` slot (cross-bundle slots rescale
into the `i`-bundle `𝐡'`-basis). -/
lemma bcoefR_eq {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1))
    (hbz : ∀ rc ∈ bundleCands' s tree hn i j, rc = 0) (ℓ : Fin (c + 3)) :
    (bcoefR s tree i j ⟨(ℓ : ℕ), by omega⟩).1
      = honestFR' s (chalYP tree i) ↑(chalZP tree i j)
          (candWitness' s tree).aR
          (hadamard (bcoefR s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1
            (vinv (powers ((chalYP tree ⟨0, hn⟩ : Fˣ) : F) n))) ℓ := by
  rcases q_slot_casesR ℓ with ⟨k, hq⟩ | hq | hq | hq
  · have hqi : ℓ = ⟨c - (k : ℕ) - 1, by have := k.isLt; omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
              (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)))))))))))
    rw [hqi, honestFR'_at_WtC]
    exact (pubVecR'_readoff s tree i j _ _ hc).1
  · have hqi : ℓ = ⟨c, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [hqi, honestFR'_at_WtO]
    exact (pubVecR'_readoff s tree i j _ _ hc).1
  · have hqi : ℓ = ⟨c + 1, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self))))
    rw [hqi, honestFR'_at_AR, arCand_readoff hn s tree i j hc]
  · have hqi : ℓ = ⟨c + 2, by omega⟩ := Fin.ext hq
    have hc := hbz _ (by
      rw [bundleCands']
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))))
    rw [hqi, honestFR'_at_SR, (pOpenVecR_diff_readoff s tree i j ⟨0, hn⟩ 0 _ hc).1]
    funext t; simp only [hadamard]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The per-bundle `(★)`.** When every candidate at an L-bundle `(i,j)` vanishes, the
read-offs make the `x`-children's data the honest `f_L`/`f_R` polynomials (`Hla`/`Hlb`),
`heq_of_ghCand'_zero` supplies `Heq`, and `star_at_bundle'` yields the `(★)` relation. -/
lemma star_of_hbz' {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (hbz : ∀ rc ∈ bundleCands' s tree hn i j, rc = 0) :
    (∑ g : Fin n, ((chalYP tree i : Fˣ) : F) ^ (g : ℕ)
        * ((candWitness' s tree).aL g * (candWitness' s tree).aR g
            - (candWitness' s tree).aO g))
      + ∑ ℓ : Fin q, ((chalZP tree i j : Fˣ) : F) ^ ((ℓ : ℕ) + 1)
          * (s.WL *ᵥ (candWitness' s tree).aL + s.WR *ᵥ (candWitness' s tree).aR
              + s.WO *ᵥ (candWitness' s tree).aO
              + (∑ k, s.WC k *ᵥ (candWitness' s tree).aC k)
              + s.WV *ᵥ (candWitness' s tree).v + s.cc) ℓ = 0 := by
  set sL := (bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1 with hsL
  set sR := hadamard (bcoefR s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1
    (vinv (powers ((chalYP tree ⟨0, hn⟩ : Fˣ) : F) n)) with hsR
  have hHla : ∀ l : Fin (2 * c + 5),
      (openP tree i j l).2.2.2.1
        = fun t => ∑ p : Fin (c + 3),
          ((chalXP tree i j l : Fˣ) : F) ^ (p : ℕ)
            * honestFL' s (chalYP tree i) ↑(chalZP tree i j)
                (candWitness' s tree).aL (candWitness' s tree).aO sL
                (candWitness' s tree).aC p t := by
    intro l
    rw [leafA_recover s tree i j l,
      sum_truncate' ((chalXP tree i j l : Fˣ) : F)
        (fun p => (bcoefL s tree i j p).1)
        (fun ℓ => honestFL' s (chalYP tree i) ↑(chalZP tree i j)
          (candWitness' s tree).aL (candWitness' s tree).aO sL (candWitness' s tree).aC ℓ)
        (fun ℓ => bcoefL_eq hn s tree i j hbz ℓ)
        (fun p hp => bcoefL_high_zero hn s tree i j hbz p hp)]
    funext t; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hHlb : ∀ l : Fin (2 * c + 5),
      (openP tree i j l).2.2.2.2
        = fun t => ∑ ℓ : Fin (c + 3),
          ((chalXP tree i j l : Fˣ) : F) ^ (ℓ : ℕ)
            * honestFR' s (chalYP tree i) ↑(chalZP tree i j)
                (candWitness' s tree).aR sR ℓ t := by
    intro l
    rw [leafB_recover s tree i j l,
      sum_truncate' ((chalXP tree i j l : Fˣ) : F)
        (fun ℓ => (bcoefR s tree i j ℓ).1)
        (fun ℓ => honestFR' s (chalYP tree i) ↑(chalZP tree i j)
          (candWitness' s tree).aR sR ℓ)
        (fun ℓ => bcoefR_eq hn s tree i j hbz ℓ)
        (fun ℓ hq => bcoefR_high_zero hn s tree i j hbz ℓ hq)]
    funext t; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hHeq := heq_of_ghCand'_zero s tree i j (hbz _ (by
    rw [bundleCands']
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))))
  have hHeqfull : (∑ l, (Matrix.vandermonde
        (fun l => ((chalXP tree i j l : Fˣ) : F)))⁻¹ ⟨c + 1, by omega⟩ l
        • ip ((openP tree i j l).2.2.2.1)
            ((openP tree i j l).2.2.2.2))
      = (ip (hadamard (vinv (powers ((chalYP tree i : Fˣ) : F) n))
              (((chalZP tree i j : Fˣ) : F)
                • powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WR))
            (((chalZP tree i j : Fˣ) : F)
              • powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WL)
          - ((chalZP tree i j : Fˣ) : F)
              * ip (powers ((chalZP tree i j : Fˣ) : F) q) s.cc)
        - ip (((chalZP tree i j : Fˣ) : F)
            • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV))
          (candWitness' s tree).v := by
    have hsum : (∑ l, (Matrix.vandermonde
          (fun l => ((chalXP tree i j l : Fˣ) : F)))⁻¹ ⟨c + 1, by omega⟩ l
          • ip ((openP tree i j l).2.2.2.1)
              ((openP tree i j l).2.2.2.2))
        = eqDj' s tree i j - eqAj' s tree i j := by
      rw [eqAj']; simp only [vandInv_eq (chalX_inj' tree i j), smul_eq_mul]; ring
    rw [hsum, hHeq, eqDj']
  have hst := star_at_bundle' s (chalYP tree i) ↑(chalZP tree i j)
    (candWitness' s tree).aL (candWitness' s tree).aR (candWitness' s tree).aO sL sR
    (candWitness' s tree).aC (candWitness' s tree).v
    (fun l => ((chalXP tree i j l : Fˣ) : F)) (chalX_inj' tree i j)
    (fun l => (openP tree i j l).2.2.2.1)
    (fun l => (openP tree i j l).2.2.2.2)
    hHla hHlb hHeqfull
  simpa only [powers] using hst

/-- **The computational core.** On an accepting tree with `W_V` full rank, if the
explicitly-recovered `candWitness'` fails `rel`, then `relCand'` is a genuine non-trivial
discrete-log relation among `gens s`.

By contradiction: if `relCand'` is *not* a non-trivial relation, then (since every candidate
opens `0` and `find?` would surface any nonzero one) *every* candidate is `0`. The per-bundle
read-offs (`star_of_hbz'`) then give `(★)` on the `i₀`-row and `j = 0`-column, which
`clauses12_of_LZ` deaggregates to clauses 1, 2; with `clause3_holds'`/`clause4_holds'` this
makes `rel s candWitness' = true`, contradicting `hfail`. -/
theorem relCand'_valid {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (hfail : rel s (candWitness' s tree) ≠ true) :
    IsNontrivialDLRel (gens s) (relCand' s tree) := by
  by_contra hcontra
  have hzero : ∀ rc ∈ relCandList' s tree hn, rc = 0 := by
    intro c hmem
    by_contra hcne
    apply hcontra
    have hex : ∃ x ∈ relCandList' s tree hn, decide (IsNontrivialDLRel (gens s) x) = true :=
      ⟨c, hmem, decide_eq_true ⟨hcne, relCandList'_msm_zero hn s tree hacc c hmem⟩⟩
    have hp := find?_getD_prop (fun v => decide (IsNontrivialDLRel (gens s) v))
      (relCandList' s tree hn) 0 hex
    rw [relCand', dif_pos hn]
    exact of_decide_eq_true hp
  have hbz_row : ∀ j : Fin (q + 1), ∀ rc ∈ bundleCands' s tree hn ⟨0, hn⟩ j, rc = 0 :=
    fun j rc hc =>
      hzero rc (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, hc⟩))
  have hbz_col : ∀ i : Fin n, ∀ rc ∈ bundleCands' s tree hn i 0, rc = 0 := fun i rc hc =>
    hzero rc (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hc⟩))
  have hclauses12 := clauses12_of_LZ hn s (candWitness' s tree).aL (candWitness' s tree).aR
    (candWitness' s tree).aO (candWitness' s tree).aC (candWitness' s tree).v
    (fun i => ((chalYP tree i : Fˣ) : F)) (chalY_inj' tree)
    (fun i j => ((chalZP tree i j : Fˣ) : F)) (chalZ_inj' tree ⟨0, hn⟩)
    (fun j => star_of_hbz' hn s tree ⟨0, hn⟩ j (hbz_row j))
    (fun i => star_of_hbz' hn s tree i 0 (hbz_col i))
  exact hfail (by
    simp only [rel, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hclauses12.1, hclauses12.2⟩, fun k => clause3_holds' hn s tree hacc k⟩,
      fun k => clause4_holds' hn s tree hacc k⟩)

/-! ## The extractor and the headline theorems -/

/-- The extractor. It **computes** `candWitness'` (explicit Vandermonde recovery, poly-time)
and checks the *decidable* relation `rel s candWitness'`; on success it returns the witness.
On failure it checks the *decidable* `IsNontrivialDLRel (gens s) (relCand' …)` for the
(explicit, computed) collision candidate and, if it is a genuine relation, returns it as the
break. No `Classical.choice` over an existence and no discrete-log inversion. -/
def arithExtractData' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c) :
    Witness F n m c ⊕ (Fin (n + n + 2) → F) :=
  if rel s (candWitness' s tree) = true then
    Sum.inl (candWitness' s tree)
  else if IsNontrivialDLRel (gens s) (relCand' s tree) then
    Sum.inr (relCand' s tree)
  else
    Sum.inl (candWitness' s tree)

/-- **Knowledge soundness (`(n, q+1, 2c+5, 2)`-special soundness) of the pre-`r`-ordering
variant** — the formal record that the message ordering alone (with no binding offset)
achieves the tight relation `R_GBP'`. The variant is a closed reduction, so this is
classical special soundness: from an accepting tree (trivial decorations) the extractor
returns **either** a valid `R_GBP'` witness (`Sum.inl` — in particular every vector
commitment opens with *no* `𝐇`-component) **or** a non-trivial discrete-log relation among
`gens s` (`Sum.inr`, real by `relCand'_valid`). The `W_V`-full-column-rank precondition is
intrinsic to the statement (`s.hWV`); `0 < n` is still necessary. -/
theorem arithRedPreR_sound {n q m c : ℕ} (hn : 0 < n) :
    (arithRedPreR (F := F) (G := G) n q m c).Sound
      (mk := arithMKPreR F G n q c) rfl
      (brk := fun s v => IsNontrivialDLRel (gens s) v) arithExtractData' := by
  intro s tree hacc
  by_cases h : rel s (candWitness' s tree) = true
  · have he : arithExtractData' s tree = Sum.inl (candWitness' s tree) := if_pos h
    exact ⟨fun w hw => by rw [he] at hw; obtain rfl := Sum.inl.inj hw; exact h,
           fun v hv => by rw [he] at hv; simp at hv⟩
  · have hbrk : IsNontrivialDLRel (gens s) (relCand' s tree) :=
      relCand'_valid hn s tree hacc h
    have he : arithExtractData' s tree = Sum.inr (relCand' s tree) := by
      rw [arithExtractData', if_neg h, if_pos hbrk]
    exact ⟨fun w hw => by rw [he] at hw; simp at hw,
           fun v hv => by rw [he] at hv; obtain rfl := Sum.inr.inj hv; exact hbrk⟩

end Sigma.Protocols.GBPImproved
