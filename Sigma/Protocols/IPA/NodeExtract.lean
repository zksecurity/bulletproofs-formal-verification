/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.IPA.Fold
import Sigma.Protocols.IPA.Extract
import Sigma.Utils.Binding

/-!
# Node extraction for the Bulletproofs inner-product argument

The per-node extractor of the Bulletproofs folding round (2017/1066, Protocol 2): from the
witnesses decorating **eight** accepting branches at one node — i.e. eight openings of the
folded statement at pairwise-distinct challenges — `nodeExtractData` reconstructs *either*
an opening of the parent inner-product statement *or* a non-trivial discrete-log relation
among the parent generators `𝐠 ⧺ 𝐡 ⧺ [u]` (`nodeExtractData_valid`). This is the entire
per-round soundness content of `Sigma.Protocols.IPA.foldRed_sound`
(`Sigma.Protocols.IPA.Reductions`); the tower assembles it by composition alone.

Per round, the 1066 extractor uses **four** challenges with pairwise distinct squares
(`xᵢ ≠ ±xⱼ`). The tree spec only guarantees *distinct* challenges (`Function.Injective`),
so the arity is **8**: any 8 distinct nonzero challenges contain 4 with pairwise distinct
squares (each square value has ≤2 preimages `±x`), and the extractor selects those 4
(`pickFourDistinctSq`, computably; `exists_four_distinct_sq` proves the selection
succeeds). Arity **7** is the tight minimum by the same pigeonhole; we use 8. As usual for
arity statements, the result is vacuous over fields with fewer than 8 nonzero elements,
where no injective `Fin 8 → Fˣ` challenge map exists.

At the selected challenges the verifier fold `P' = P + ξ²L + ξ⁻²R` gives a
`(ξ², 1, ξ⁻²)`-Vandermonde system whose inversion reconstructs openings of `L, P, R`,
hence the parent witness `(a, b)` — or, if two openings of one generator disagree, a
non-trivial discrete-log relation (the reconstruction core `extractStepData` lives in
`Sigma.Protocols.IPA.Extract`). Witnesses are packaged with `combineHalf` (the inverse of
`splitL`/`splitR`) and relations with `ipRelVec`; both are wrapped in the memoizing
identity `memo` for polynomial-time evaluation.
-/

namespace Sigma.Protocols.IPA

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ## The generator family and the break -/

/-- The generator family of an inner-product statement: `𝐠 ⧺ 𝐡 ⧺ [u]`, of length
`2^(k+1) + 2^(k+1) + 1`. A non-trivial discrete-log relation among these is the "break"
returned by the extractor's `Sum.inr` branch. -/
def ipGens {k : ℕ} (s : IPStatement F G k) : Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → G :=
  Fin.append (Fin.append s.gs s.hs) (fun _ : Fin 1 => s.u)

/-! ## Pigeonhole: eight distinct challenges contain four with distinct squares -/

/-- Among eight distinct field elements there are four with pairwise distinct squares: each
square value has at most two preimages (`±x`), so the squaring map has image of size `≥ 4`.
This is why arity `8` suffices with only the spec's distinct-challenge guarantee.

Proof-only existence lemma (it uses `Classical.choose` internally); the extractor's data path
selects the four indices with the *computable* `pickFourDistinctSq`, and this lemma is used only to
prove that selection succeeds (`pickFourDistinctSq_spec`). -/
lemma exists_four_distinct_sq {c : Fin 8 → F} (hc : Function.Injective c) :
    ∃ s : Fin 4 → Fin 8, Function.Injective (fun k => (c (s k)) ^ 2) := by
  classical
  letI : DecidableEq F := Classical.decEq F
  set sq : Fin 8 → F := fun a => (c a) ^ 2 with hsqdef
  have hfib : ∀ b ∈ Finset.univ.image sq, (Finset.univ.filter (fun a => sq a = b)).card ≤ 2 := by
    intro b _
    by_cases hb : ∃ a₀, sq a₀ = b
    · obtain ⟨a₀, ha₀⟩ := hb
      have hmaps : Set.MapsTo c ↑(Finset.univ.filter (fun a => sq a = b))
          ↑({c a₀, -c a₀} : Finset F) := by
        intro a ha
        rw [Finset.mem_coe, Finset.mem_filter] at ha
        have e1 : (c a) ^ 2 = b := by simpa [hsqdef] using ha.2
        have e2 : (c a₀) ^ 2 = b := by simpa [hsqdef] using ha₀
        have hsqeq : (c a - c a₀) * (c a + c a₀) = 0 := by linear_combination e1 - e2
        rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
        rcases mul_eq_zero.mp hsqeq with h | h
        · exact Or.inl (by linear_combination h)
        · exact Or.inr (by linear_combination h)
      calc (Finset.univ.filter (fun a => sq a = b)).card
          ≤ ({c a₀, -c a₀} : Finset F).card :=
            Finset.card_le_card_of_injOn c hmaps (fun x _ y _ h => hc h)
        _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    · have hempty : Finset.univ.filter (fun a => sq a = b) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; exact fun a _ => fun he => hb ⟨a, he⟩
      rw [hempty]; simp
  have hcard : 4 ≤ (Finset.univ.image sq).card := by
    have h8 : (Finset.univ : Finset (Fin 8)).card ≤ 2 * (Finset.univ.image sq).card :=
      Finset.card_le_mul_card_image _ _ hfib
    simp only [Finset.card_univ, Fintype.card_fin] at h8
    omega
  obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq hcard
  set e := T'.equivFin with he
  set emb : Fin 4 → F := fun k => (e.symm (finCongr hT'card.symm k)).1
  have hmem : ∀ k, ∃ a, sq a = emb k := fun k => by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hT'sub (e.symm (finCongr hT'card.symm k)).2)
    exact ⟨a, ha⟩
  refine ⟨fun k => Classical.choose (hmem k), ?_⟩
  have hsk : ∀ k, sq (Classical.choose (hmem k)) = emb k := fun k => Classical.choose_spec (hmem k)
  intro k1 k2 h
  have hval : emb k1 = emb k2 := by rw [← hsk k1, ← hsk k2]; exact h
  exact (finCongr hT'card.symm).injective (e.symm.injective (Subtype.ext hval))

/-- Explicit enumeration of all length-4 index selections (a fixed, constant-size list, built
over the computable `List.finRange`). -/
def allSel : List (Fin 4 → Fin 8) :=
  (List.finRange 8).flatMap fun i0 => (List.finRange 8).flatMap fun i1 =>
    (List.finRange 8).flatMap fun i2 => (List.finRange 8).map fun i3 =>
      (![i0, i1, i2, i3] : Fin 4 → Fin 8)

/-- Every length-4 index selection appears in `allSel`. -/
lemma mem_allSel (s : Fin 4 → Fin 8) : s ∈ allSel := by
  have hs : s = ![s 0, s 1, s 2, s 3] := by funext k; fin_cases k <;> rfl
  rw [hs, allSel]
  simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨s 0, s 1, s 2, s 3, rfl⟩

/-- A **computable** selection of four challenges with pairwise distinct squares: scan the fixed,
constant-size list `allSel` for a selection whose squares are injective. Total (a `0`-fallback on
the impossible empty case); on an injective challenge vector it succeeds, by
`pickFourDistinctSq_spec`. This replaces the `Classical.choose` of `exists_four_distinct_sq` in the
extractor's data path. -/
def pickFourDistinctSq [DecidableEq F] (c : Fin 8 → F) : Fin 4 → Fin 8 :=
  (allSel.find? fun s => decide (Function.Injective fun k => (c (s k)) ^ 2)).getD ![0, 0, 0, 0]

/-- On an injective challenge vector, `pickFourDistinctSq` yields four indices whose challenge
squares are pairwise distinct. -/
lemma pickFourDistinctSq_spec [DecidableEq F] {c : Fin 8 → F} (hc : Function.Injective c) :
    Function.Injective (fun k => (c (pickFourDistinctSq c k)) ^ 2) := by
  obtain ⟨s, hs⟩ := exists_four_distinct_sq hc
  have hsP : (fun s => decide (Function.Injective fun k => (c (s k)) ^ 2)) s = true := by
    simpa using hs
  rw [pickFourDistinctSq]
  cases hfind : allSel.find? (fun s => decide (Function.Injective fun k => (c (s k)) ^ 2)) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd hsP (hfind s (mem_allSel s))
  | some t =>
    simp only [Option.getD_some]
    have hPt := List.find?_some hfind
    exact of_decide_eq_true hPt

/-! ## Combining halves (the inverse of `splitL`/`splitR`) -/

/-- Combine a lower and upper half into a length-`2^(t+1)` vector; the inverse of
`splitL`/`splitR`. -/
def combineHalf {α : Type*} {t : ℕ} (lo hi : Fin (2 ^ t) → α) : Fin (2 ^ (t + 1)) → α :=
  fun j => Fin.addCases lo hi (Fin.cast (by rw [pow_succ]; ring) j)

@[simp] lemma splitL_combineHalf {α : Type*} {t : ℕ} (lo hi : Fin (2 ^ t) → α) :
    splitL (combineHalf lo hi) = lo := by
  funext i
  simp only [splitL, combineHalf]
  rw [show (Fin.cast (by rw [pow_succ]; ring) (Fin.cast (by rw [pow_succ]; omega)
        (i.castAdd (2 ^ t))) : Fin (2 ^ t + 2 ^ t)) = Fin.castAdd (2 ^ t) i from Fin.ext (by simp),
    Fin.addCases_left]

@[simp] lemma splitR_combineHalf {α : Type*} {t : ℕ} (lo hi : Fin (2 ^ t) → α) :
    splitR (combineHalf lo hi) = hi := by
  funext i
  simp only [splitR, combineHalf]
  rw [show (Fin.cast (by rw [pow_succ]; ring) (Fin.cast (by rw [pow_succ]; omega)
        (Fin.natAdd (2 ^ t) i)) : Fin (2 ^ t + 2 ^ t)) = Fin.natAdd (2 ^ t) i from Fin.ext (by simp),
    Fin.addCases_right]

omit [DecidableEq G] in
lemma msm_combineHalf {t : ℕ} (clo chi : Fin (2 ^ t) → F) (gs : Fin (2 ^ (t + 1)) → G) :
    msm (combineHalf clo chi) gs = msm clo (splitL gs) + msm chi (splitR gs) := by
  rw [msm_split (combineHalf clo chi) gs, splitL_combineHalf, splitR_combineHalf]

lemma ip_combineHalf {t : ℕ} (alo ahi blo bhi : Fin (2 ^ t) → F) :
    ip (combineHalf alo ahi) (combineHalf blo bhi) = ip alo blo + ip ahi bhi := by
  rw [ip_split (combineHalf alo ahi) (combineHalf blo bhi), splitL_combineHalf, splitR_combineHalf,
    splitL_combineHalf, splitR_combineHalf]

/-! ## Discrete-log relation vectors over the generator family `ipGens` -/

/-- A discrete-log relation vector built from `𝐠`, `𝐡`, and `u` component coefficients. -/
def ipRelVec {k : ℕ} (vg vh : Fin (2 ^ (k + 1)) → F) (vu : F) :
    Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F :=
  Fin.append (Fin.append vg vh) ![vu]

omit [DecidableEq G] in
lemma msm_ipRelVec {k : ℕ} (s : IPStatement F G k) (vg vh : Fin (2 ^ (k + 1)) → F) (vu : F) :
    msm (ipRelVec vg vh vu) (ipGens s) = msm vg s.gs + msm vh s.hs + vu • s.u := by
  unfold ipRelVec ipGens
  rw [msm_append, msm_append]
  congr 1
  simp [msm]

lemma ipRelVec_ne_zero {k : ℕ} {vg vh : Fin (2 ^ (k + 1)) → F} {vu : F}
    (h : vg ≠ 0 ∨ vh ≠ 0 ∨ vu ≠ 0) : ipRelVec vg vh vu ≠ 0 := by
  intro hz
  simp only [ipRelVec] at hz
  rcases h with h | h | h
  · exact h (funext fun i => by
      have := congrFun hz (Fin.castAdd 1 (Fin.castAdd (2 ^ (k + 1)) i))
      rwa [Fin.append_left, Fin.append_left, Pi.zero_apply] at this)
  · exact h (funext fun i => by
      have := congrFun hz (Fin.castAdd 1 (Fin.natAdd (2 ^ (k + 1)) i))
      rwa [Fin.append_left, Fin.append_right, Pi.zero_apply] at this)
  · exact h (by
      have := congrFun hz (Fin.natAdd (2 ^ (k + 1) + 2 ^ (k + 1)) 0)
      rw [Fin.append_right, Pi.zero_apply] at this
      simpa using this)

/-! ## Memoization (for polynomial-time evaluation) -/

/-- **Memoizing identity** on finite functions: tabulate `f` into a concrete (array-backed) vector
once, then read entries back in `O(1)`. Propositionally `memo f = f` (`memo_eq`), so proofs simply
strip it; operationally it computes each entry once. The extractor wraps every reconstructed vector
in `memo` so that coordinate accesses do not re-run the closure that produced them — this is what
turns the naive (recomputing) evaluation into a polynomial-time one. -/
def memo {n : ℕ} {α : Type*} (f : Fin n → α) : Fin n → α := (Vector.ofFn f).get

@[simp] lemma memo_eq {n : ℕ} {α : Type*} (f : Fin n → α) : memo f = f := by
  funext i; exact Vector.get_ofFn f i

/-! ## Node extraction and lifting breaks through a fold -/

/-- **Step 1 (node extraction, computable).** Select four challenges with pairwise distinct squares
(`pickFourDistinctSq`), run the reconstruction core `extractStepData`, and package the result as a
parent witness via `combineHalf` or a discrete-log relation via `ipRelVec`. -/
def nodeExtractData [DecidableEq F] {k : ℕ} (chal : Fin 8 → F) (a' b' : Fin 8 → Fin (2 ^ k) → F) :
    ((Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F)) ⊕
      (Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F) :=
  let sel := pickFourDistinctSq chal
  match extractStepData (fun j => chal (sel j)) (fun j => a' (sel j)) (fun j => b' (sel j)) with
  | Sum.inl (aLo, aHi, bLo, bHi) => Sum.inl (memo (combineHalf aLo aHi), memo (combineHalf bLo bHi))
  | Sum.inr (vgL, vgR, vhL, vhR, vu) =>
      Sum.inr (memo (ipRelVec (combineHalf vgL vgR) (combineHalf vhL vhR) vu))

/-- **Step 1 (correctness of `nodeExtractData`).** From the eight per-challenge accept relations at
one node, every `Sum.inl` output is a parent witness, and every `Sum.inr` output a non-trivial
generator relation. -/
lemma nodeExtractData_valid [DecidableEq F] {k : ℕ} (s : IPStatement F G k) (chal : Fin 8 → Fˣ)
    (hchal : Function.Injective chal) (L R : G) (a' b' : Fin 8 → Fin (2 ^ k) → F)
    (hC : ∀ i, s.P + ((chal i : F)) ^ 2 • L + (((chal i : F))⁻¹) ^ 2 • R
      = msm (a' i) (foldG (chal i : F) (splitL s.gs) (splitR s.gs))
        + msm (b' i) (foldH (chal i : F) (splitL s.hs) (splitR s.hs)) + ip (a' i) (b' i) • s.u) :
    (∀ w, nodeExtractData (fun i => (chal i : F)) a' b' = Sum.inl w → relIP s w = true) ∧
    (∀ v, nodeExtractData (fun i => (chal i : F)) a' b' = Sum.inr v
        → IsNontrivialDLRel (ipGens s) v) := by
  have hchal' : Function.Injective (fun i => (chal i : F)) := fun x y h => hchal (Units.ext h)
  set sel := pickFourDistinctSq (fun i => (chal i : F)) with hseldef
  have hsel : Function.Injective (fun j => ((chal (sel j) : F)) ^ 2) := pickFourDistinctSq_spec hchal'
  have hξ0 : ∀ j, (chal (sel j) : F) ≠ 0 := fun j => (chal (sel j)).ne_zero
  have hCsel : ∀ j : Fin 4, s.P + ((chal (sel j) : F)) ^ 2 • L + (((chal (sel j) : F))⁻¹) ^ 2 • R
      = msm (a' (sel j)) (foldG (chal (sel j) : F) (splitL s.gs) (splitR s.gs))
        + msm (b' (sel j)) (foldH (chal (sel j) : F) (splitL s.hs) (splitR s.hs))
        + ip (a' (sel j)) (b' (sel j)) • s.u := fun j => hC (sel j)
  obtain ⟨hwitV, hbrkV⟩ := extractStepData_valid (splitL s.gs) (splitR s.gs) (splitL s.hs)
    (splitR s.hs) s.u s.P L R hξ0 hsel hCsel
  have hnode : nodeExtractData (fun i => (chal i : F)) a' b'
      = (match extractStepData (fun j => (chal (sel j) : F)) (fun j => a' (sel j))
              (fun j => b' (sel j)) with
        | Sum.inl (aLo, aHi, bLo, bHi) =>
            Sum.inl (memo (combineHalf aLo aHi), memo (combineHalf bLo bHi))
        | Sum.inr (vgL, vgR, vhL, vhR, vu) =>
            Sum.inr (memo (ipRelVec (combineHalf vgL vgR) (combineHalf vhL vhR) vu))) := rfl
  rw [hnode]
  rcases he : extractStepData (fun j => (chal (sel j) : F)) (fun j => a' (sel j))
      (fun j => b' (sel j)) with ⟨aLo, aHi, bLo, bHi⟩ | ⟨vgL, vgR, vhL, vhR, vu⟩
  · refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · simp only [Sum.inl.injEq] at hw
      obtain rfl := hw
      have hP := hwitV aLo aHi bLo bHi he
      simp only [relIP, decide_eq_true_eq, memo_eq, msm_combineHalf, ip_combineHalf]
      rw [hP]; abel
    · exact absurd hv (by simp)
  · refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · exact absurd hw (by simp)
    · simp only [Sum.inr.injEq] at hv
      obtain rfl := hv
      obtain ⟨hne, hzero⟩ := hbrkV vgL vgR vhL vhR vu he
      rw [memo_eq]
      refine ⟨?_, ?_⟩
      · apply ipRelVec_ne_zero
        by_contra hcon
        push Not at hcon
        obtain ⟨hc1, hc2, hc3⟩ := hcon
        exact hne ⟨by rw [← splitL_combineHalf vgL vgR, hc1]; rfl,
          by rw [← splitR_combineHalf vgL vgR, hc1]; rfl,
          by rw [← splitL_combineHalf vhL vhR, hc2]; rfl,
          by rw [← splitR_combineHalf vhL vhR, hc2]; rfl, hc3⟩
      · rw [msm_ipRelVec, msm_combineHalf, msm_combineHalf, ← hzero]; abel

end Sigma.Protocols.IPA
