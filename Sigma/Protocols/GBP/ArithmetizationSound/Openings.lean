/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBP.ArithmetizationSound.Extract

/-!
# Arithmetization soundness: openings, clauses, and the eq1 collision

The deaggregation of `(★)` into the R1CS and Hadamard clauses (`clauses12_of_star/_consistent/_LZ`);
the `gens`-coefficient openings of the verifier commitments (`pOpenVec`, `aiOpenVec`, `hsVec`,
`ghVec`) and their `msm`-vanishing facts; the witness-opening clauses 3/4 (`clause3_holds`,
`clause4_holds`); and the `eq1` `(g, h)` collision candidate carrying `star_at_bundle`'s `Heq`
(`ghCand`, `heq_of_ghCand_zero`).
-/

namespace Sigma.Protocols.GBP

open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Deaggregation glue:** the per-bundle relation `(★)` — Hadamard scalar at `yᵢ` plus the
`z`-polynomial of R1CS rows — holding at all `(i, j)` forces both R1CS (`= 0`, clause 1) and the
Hadamard constraint (`aL ∘ aR − aO = 0`, clause 2), via `star_deaggregate_z` (per `yᵢ`, over the
`q+1` `z`-children) then `hadamard_deaggregate` (over the `n` `y`-children). -/
lemma clauses12_of_star {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (aL aR aO : Fin n → F) (aC : Fin c → Fin n → F) (v : Fin m → F)
    (y : Fin n → F) (hy : Function.Injective y)
    (z : Fin n → Fin (q + 1) → F) (hz : ∀ i, Function.Injective (z i))
    (hstar : ∀ (i : Fin n) (j : Fin (q + 1)),
        (∑ g : Fin n, (y i) ^ (g : ℕ) * (aL g * aR g - aO g))
          + ∑ ℓ : Fin q, (z i j) ^ ((ℓ : ℕ) + 1)
              * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k)
                  + s.WV *ᵥ v + s.cc) ℓ = 0) :
    (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k) + s.WV *ᵥ v + s.cc = 0)
      ∧ hadamard aL aR - aO = 0 := by
  have hdeag : ∀ i : Fin n, (∑ g : Fin n, (y i) ^ (g : ℕ) * (aL g * aR g - aO g)) = 0
      ∧ ∀ ℓ, (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k)
          + s.WV *ᵥ v + s.cc) ℓ = 0 :=
    fun i => star_deaggregate_z (z i) (hz i) _ _ (hstar i)
  refine ⟨funext fun ℓ => (hdeag ⟨0, hn⟩).2 ℓ, funext fun g => ?_⟩
  simp only [hadamard, Pi.sub_apply, Pi.zero_apply]
  exact hadamard_deaggregate y hy (fun g => aL g * aR g - aO g) (fun i => (hdeag i).1) g

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Consistency ⇒ clauses 1,2.** Given, at every bundle `(i,j)`, that the leaf data are the honest
polynomials (`Hla`/`Hlb`) and the eq1 identity (`Heq`), `star_at_bundle` yields `(★)` at every bundle
and `clauses12_of_star` deaggregates to R1CS (clause 1) and Hadamard (clause 2). -/
lemma clauses12_of_consistent {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (aL aR aO sL sR : Fin n → F) (aC aux : Fin c → Fin n → F) (v : Fin m → F)
    (yu : Fin n → Fˣ) (hy : Function.Injective (fun i => ((yu i : Fˣ) : F)))
    (zu : Fin n → Fin (q + 1) → Fˣ) (hz : ∀ i, Function.Injective (fun j => ((zu i j : Fˣ) : F)))
    (x : Fin n → Fin (q + 1) → Fin (2 * nPrime c + 3) → F) (hx : ∀ i j, Function.Injective (x i j))
    (la lb : Fin n → Fin (q + 1) → Fin (2 * nPrime c + 3) → (Fin n → F))
    (Hla : ∀ i j l, la i j l = fun i' => ∑ p : Fin (nPrime c + 2),
      (x i j l) ^ (p : ℕ) * honestFL s (yu i) (zu i j) aL aO sL aC p i')
    (fR : Fin n → Fin (q + 1) → Fin (nPrime c + 2) → (Fin n → F))
    (Hlb : ∀ i j l, lb i j l = fun i' => ∑ ℓ : Fin (nPrime c + 2), (x i j l) ^ (ℓ : ℕ) * fR i j ℓ i')
    (Hconv : ∀ i j, (∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
          if (p : ℕ) + (ℓ : ℕ) = nPrime c then
            ip (honestFL s (yu i) (zu i j) aL aO sL aC p) (fR i j ℓ) else 0)
        = ∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
          if (p : ℕ) + (ℓ : ℕ) = nPrime c then
            ip (honestFL s (yu i) (zu i j) aL aO sL aC p)
              (honestFR s (yu i) (zu i j) aR sR aux ℓ) else 0)
    (Heq : ∀ i j, (∑ l, (Matrix.vandermonde (x i j))⁻¹ ⟨nPrime c, by omega⟩ l • ip (la i j l) (lb i j l))
      = (ip (hadamard (vinv (powers ((yu i : Fˣ) : F) n))
              (((zu i j : Fˣ) : F) • powers ((zu i j : Fˣ) : F) q ᵥ* s.WR))
            (((zu i j : Fˣ) : F) • powers ((zu i j : Fˣ) : F) q ᵥ* s.WL)
          - ((zu i j : Fˣ) : F) * ip (powers ((zu i j : Fˣ) : F) q) s.cc)
        - ip (((zu i j : Fˣ) : F) • (powers ((zu i j : Fˣ) : F) q ᵥ* s.WV)) v) :
    (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k) + s.WV *ᵥ v + s.cc = 0)
      ∧ hadamard aL aR - aO = 0 := by
  refine clauses12_of_star hn s aL aR aO aC v (fun i => ((yu i : Fˣ) : F)) hy
    (fun i j => ((zu i j : Fˣ) : F)) hz (fun i j => ?_)
  have hst := star_at_bundle s (yu i) (zu i j) aL aR aO sL sR aC aux v (x i j) (hx i j)
    (la i j) (lb i j) (Hla i j) (fR i j) (Hlb i j) (Hconv i j) (Heq i j)
  simpa only [powers] using hst

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Step 3 (L-shaped deaggregation).** It suffices to know `(★)` on the `i₀`-row (all `q+1`
`z`-children, which `star_deaggregate_z` turns into R1CS rows `= 0`, clause 1) and on the
`j=0`-column (all `n` `y`-children, which — *once the rows vanish* — `hadamard_deaggregate` turns
into each Hadamard scalar `= 0`, clause 2). Avoids `(★)` on the full `n·(q+1)` grid; the column
needs only a single `z` per `y`. -/
lemma clauses12_of_LZ {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (aL aR aO : Fin n → F) (aC : Fin c → Fin n → F) (v : Fin m → F)
    (y : Fin n → F) (hy : Function.Injective y)
    (z : Fin n → Fin (q + 1) → F) (hz0 : Function.Injective (z ⟨0, hn⟩))
    (hrow : ∀ j : Fin (q + 1),
        (∑ g : Fin n, (y ⟨0, hn⟩) ^ (g : ℕ) * (aL g * aR g - aO g))
          + ∑ ℓ : Fin q, (z ⟨0, hn⟩ j) ^ ((ℓ : ℕ) + 1)
              * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k)
                  + s.WV *ᵥ v + s.cc) ℓ = 0)
    (hcol : ∀ i : Fin n,
        (∑ g : Fin n, (y i) ^ (g : ℕ) * (aL g * aR g - aO g))
          + ∑ ℓ : Fin q, (z i 0) ^ ((ℓ : ℕ) + 1)
              * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k)
                  + s.WV *ᵥ v + s.cc) ℓ = 0) :
    (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k) + s.WV *ᵥ v + s.cc = 0)
      ∧ hadamard aL aR - aO = 0 := by
  obtain ⟨_, hrows⟩ := star_deaggregate_z (z ⟨0, hn⟩) hz0
    (∑ g : Fin n, (y ⟨0, hn⟩) ^ (g : ℕ) * (aL g * aR g - aO g))
    (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k) + s.WV *ᵥ v + s.cc) hrow
  refine ⟨funext fun ℓ => hrows ℓ, ?_⟩
  have hhad : ∀ i : Fin n, (∑ g : Fin n, (y i) ^ (g : ℕ) * (aL g * aR g - aO g)) = 0 := by
    intro i
    have hzero : (∑ ℓ : Fin q, (z i 0) ^ ((ℓ : ℕ) + 1)
        * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k) + s.WV *ᵥ v + s.cc) ℓ) = 0 :=
      Finset.sum_eq_zero (fun ℓ _ => by rw [hrows ℓ, mul_zero])
    have hc := hcol i
    rw [hzero, add_zero] at hc
    exact hc
  funext g
  simp only [hadamard, Pi.sub_apply, Pi.zero_apply]
  exact hadamard_deaggregate y hy (fun g => aL g * aR g - aO g) hhad g

omit [DecidableEq F] [DecidableEq G] in
/-- A vanishing `gvec` has vanishing blocks: the basis change "candidate `= 0` ⇒ the two openings
agree" reads off as `a = a'`, `b = b'`, `c = c'`. -/
lemma gvec_eq_zero {n : ℕ} {a b : Fin n → F} {c : F} (h : gvec a b c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [gvec] at h
  obtain ⟨hab, hc⟩ := append_eq_zero h
  obtain ⟨ha, hb⟩ := append_eq_zero hab
  exact ⟨ha, hb, by simpa using congrFun hc 1⟩

omit [DecidableEq F] [DecidableEq G] in
/-- `gvec` is injective in its blocks: two equal `gens`-vectors have equal openings. -/
lemma gvec_inj {n : ℕ} {a a' b b' : Fin n → F} {c c' : F} (h : gvec a b c = gvec a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [gvec] at h
  have hab : Fin.append a b = Fin.append a' b' :=
    funext fun i => by simpa [Fin.append_left] using congrFun h (Fin.castAdd 2 i)
  have hc : (![0, c] : Fin 2 → F) = ![0, c'] :=
    funext fun i => by simpa [Fin.append_right] using congrFun h (Fin.natAdd (n + n) i)
  refine ⟨funext fun i => ?_, funext fun i => ?_, by simpa using congrFun hc 1⟩
  · simpa [Fin.append_left] using congrFun hab (Fin.castAdd n i)
  · have hbi := congrFun hab (Fin.natAdd n i); rwa [Fin.append_right, Fin.append_right] at hbi

/-- A pure `(g, h)`-coefficient vector against `gens s` (the `𝐆`/`𝐇` blocks are `0`). The eq1
`(g,h)` collision candidate lives here. -/
def ghVec {n : ℕ} (cg ch : F) : Fin (n + n + 2) → F :=
  Fin.append (Fin.append (0 : Fin n → F) (0 : Fin n → F)) ![cg, ch]

omit [DecidableEq F] [DecidableEq G] in
lemma ghVec_opens {n q m c : ℕ} (s : Statement F G n q m c) (cg ch : F) :
    msm (ghVec cg ch) (gens s) = cg • s.g + ch • s.h := by
  rw [ghVec, gens_msm, msm_zero_left, msm_zero_left, zero_add, zero_add]

omit [DecidableEq F] [DecidableEq G] in
/-- A vanishing `ghVec` has vanishing coefficients. -/
lemma ghVec_eq_zero {n : ℕ} {cg ch : F} (h : (ghVec cg ch : Fin (n + n + 2) → F) = 0) :
    cg = 0 ∧ ch = 0 := by
  rw [ghVec] at h
  obtain ⟨_, hcd⟩ := append_eq_zero h
  exact ⟨by simpa using congrFun hcd 0, by simpa using congrFun hcd 1⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `find?`-plumbing: if some element of `l` satisfies the (decidable) predicate `p`, then the
`getD`-defaulted `find?` result does too. Reduces `relCand_valid` to *exhibiting* one non-trivial
collision candidate. -/
lemma find?_getD_prop {α : Type*} (p : α → Bool) (l : List α) (d : α)
    (h : ∃ x ∈ l, p x = true) : p ((l.find? p).getD d) = true := by
  obtain ⟨x, hx, hpx⟩ := h
  cases hf : l.find? p with
  | none =>
      rw [List.find?_eq_none] at hf
      exact absurd hpx (by simpa using hf x hx)
  | some a =>
      rw [Option.getD_some]
      exact List.find?_some hf

/-- **Step 1 (`eq2` extraction correctness).** Under acceptance, `bcoef i j p` is a genuine opening
of the verifier coefficient `Pcoef p` (in the `(𝐆, h', h)` basis) — the inverse-Vandermonde of the
bundle's `x`-leaf data. The bridge from `vandInv` (the efficient Lagrange inverse the extractor
computes with) to the proven `eq2_extract` (which uses `Matrix.inv`), via `vandInv_eq`. -/
lemma bundle_open {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) :
    Pcoef s ((chalY tree i : Fˣ) : F) ((chalZ tree i j : Fˣ) : F)
        (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2 p
      = msm (bcoef s tree i j p).1 s.gs
        + msm (bcoef s tree i j p).2.1 (vinv (powers ((chalY tree i : Fˣ) : F) n) ⊙ s.hs)
        + (bcoef s tree i j p).2.2 • s.h := by
  have heq2 : ∀ l : Fin (2 * nPrime c + 3),
      (∑ p' : Fin (2 * nPrime c + 3), ((chalX tree i j l : Fˣ) : F) ^ (p' : ℕ)
          • Pcoef s ((chalY tree i : Fˣ) : F) ((chalZ tree i j : Fˣ) : F)
              (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2 p')
        = msm (leafO tree i j l).2.2.1 s.gs
          + msm (leafO tree i j l).2.2.2
              (vinv (powers ((chalY tree i : Fˣ) : F) n) ⊙ s.hs)
          + (leafO tree i j l).2.1 • s.h :=
    fun l => arithVerify_eq2 s (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2
      (chalY tree i) (chalZ tree i j)
      (chalX tree i j l) (tcomT tree i j)
      _ _ _ _ (path_verify s tree hacc i j l)
  have hext := eq2_extract s ((chalY tree i : Fˣ) : F) ((chalZ tree i j : Fˣ) : F)
    (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2
    (fun l => ((chalX tree i j l : Fˣ) : F)) (chalX_inj tree i j)
    (fun l => (leafO tree i j l).2.2.1)
    (fun l => (leafO tree i j l).2.2.2)
    (fun l => (leafO tree i j l).2.1) heq2 p
  rw [hext]; simp only [bcoef, vandInv_eq (chalX_inj tree i j)]

/-- The `gens`-coefficient vector of the bundle-`(i,j)` opening of `Pcoef p` (in the `(𝐆, 𝐇, h)`
basis: the extracted `h'`-coefficients rescaled by `yinv`). -/
def pOpenVec {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) : Fin (n + n + 2) → F :=
  gvec (bcoef s tree i j p).1
    (hadamard (bcoef s tree i j p).2.1 (vinv (powers ((chalY tree i : Fˣ) : F) n)))
    (bcoef s tree i j p).2.2

/-- `pOpenVec i j p` is a `gens`-opening of `Pcoef p` (so the *difference* of two such, for the same
challenge-independent commitment, has `msm · gens = 0` — a relation candidate). -/
lemma pOpenVec_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) :
    msm (pOpenVec s tree i j p) (gens s)
      = Pcoef s ((chalY tree i : Fˣ) : F) ((chalZ tree i j : Fˣ) : F)
          (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2 p := by
  have hconv : msm (hadamard (bcoef s tree i j p).2.1
        (vinv (powers ((chalY tree i : Fˣ) : F) n))) s.hs
      = msm (bcoef s tree i j p).2.1 (vinv (powers ((chalY tree i : Fˣ) : F) n) ⊙ s.hs) :=
    (msm_vsmul (bcoef s tree i j p).2.1 (vinv (powers ((chalY tree i : Fˣ) : F) n)) s.hs).symm
  rw [pOpenVec, gvec, gens_msm, zero_smul, add_zero, hconv]
  exact (bundle_open s tree hacc i j p).symm

/-- The `msm` of a cross-bundle candidate difference is the difference of the two `Pcoef p` values;
for a challenge-independent commitment (`Pcoef_AO/AC/S`) those coincide, so the candidate is a
genuine discrete-log relation (`msm · gens = 0`). -/
lemma pOpenVec_msm_diff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i i' : Fin n) (j j' : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) :
    msm (pOpenVec s tree i j p - pOpenVec s tree i' j' p) (gens s)
      = Pcoef s ((chalY tree i : Fˣ) : F) ((chalZ tree i j : Fˣ) : F)
          (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2 p
        - Pcoef s ((chalY tree i' : Fˣ) : F) ((chalZ tree i' j' : Fˣ) : F)
          (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2 p := by
  rw [msm_sub_left, pOpenVec_opens s tree hacc i j p, pOpenVec_opens s tree hacc i' j' p]

/-- Above degree `n'+1` the verifier coefficient vanishes, so `pOpenVec i j p` opens `0`: its own
`gens`-vector is already a relation (`msm = 0`). -/
lemma pOpenVec_high_msm_zero {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) (hp : nPrime c + 2 ≤ (p : ℕ)) :
    msm (pOpenVec s tree i j p) (gens s) = 0 := by
  rw [pOpenVec_opens s tree hacc i j p, Pcoef_high_zero _ _ _ _ _ _ _ hp]

/-- The `gens`-vector opening the public `WtL + WtR` part of `Pcoef (c+1)` at bundle `(i,j)`. -/
def aiPubVec {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    Fin (n + n + 2) → F :=
  gvec (hadamard (vinv (powers ((chalY tree i : Fˣ) : F) n))
          (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WR)))
       (hadamard (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL))
          (vinv (powers ((chalY tree i : Fˣ) : F) n))) 0

omit [DecidableEq F] [DecidableEq G] in
/-- `aiPubVec i j` opens `WtL + WtR` (the public part of `Pcoef (c+1)`), in the exact form of
`Pcoef_AI`'s public summands. -/
lemma aiPubVec_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    msm (aiPubVec s tree i j) (gens s)
      = msm (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL))
          (vinv (powers ((chalY tree i : Fˣ) : F) n) ⊙ s.hs)
        + msm (hadamard (vinv (powers ((chalY tree i : Fˣ) : F) n))
            (((chalZ tree i j : Fˣ) : F)
              • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WR))) s.gs := by
  have hconv : msm (hadamard (((chalZ tree i j : Fˣ) : F)
          • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL))
        (vinv (powers ((chalY tree i : Fˣ) : F) n))) s.hs
      = msm (((chalZ tree i j : Fˣ) : F)
          • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL))
        (vinv (powers ((chalY tree i : Fˣ) : F) n) ⊙ s.hs) :=
    (msm_vsmul _ _ _).symm
  rw [aiPubVec, gvec, gens_msm, zero_smul, zero_smul, add_zero, add_zero, hconv, add_comm]

/-- The `gens`-vector opening of the commitment `A_I` at bundle `(i,j)`: the `Pcoef (c+1)` opening
with the public `WtL/WtR` part subtracted off. Being a challenge-independent commitment, the
*difference* of two such (at different bundles) has `msm · gens = 0`. -/
def aiOpenVec {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    Fin (n + n + 2) → F :=
  pOpenVec s tree i j ⟨c + 1, by simp only [nPrime]; omega⟩ - aiPubVec s tree i j

lemma aiOpenVec_opens {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (aiOpenVec s tree i j) (gens s) = (rootT tree).1 := by
  rw [aiOpenVec, msm_sub_left,
    pOpenVec_opens s tree hacc i j ⟨c + 1, by simp only [nPrime]; omega⟩, aiPubVec_opens, Pcoef_AI]
  abel

/-- The `gens`-vector of a pure `𝐇`-opening (no `𝐆`/`h` part): `msm c (yinv ⊙ 𝐇)`. The structural
opening of the *public* verifier coefficients `Pcoef 0 = WtO`, `Pcoef (k+1) = Wtk`. -/
def hsVec {n : ℕ} (c yinv : Fin n → F) : Fin (n + n + 2) → F := gvec 0 (hadamard c yinv) 0

omit [DecidableEq F] [DecidableEq G] in
lemma hsVec_opens {n q m c : ℕ} (s : Statement F G n q m c) (c yinv : Fin n → F) :
    msm (hsVec c yinv) (gens s) = msm c (yinv ⊙ s.hs) := by
  rw [hsVec, gvec, gens_msm, msm_zero_left, zero_add, zero_smul, add_zero, zero_smul, add_zero]
  exact (msm_vsmul c yinv s.hs).symm

/-- **Step 4 (clause 3, vector commitments).** The opening `A_C⁽ᵏ⁾ = ⟨aC,𝐆⟩+⟨aux,𝐇⟩+γC·h` is
satisfied by the recovered `candWitness` fields: they are the `(0,0)`-bundle `bcoef` opening of
`Pcoef (n'−(k+1)) = A_C⁽ᵏ⁾` (`bundle_open` + `Pcoef_AC`), with the `h'`→`𝐇` rescaling (`msm_vsmul`).
The base relation keeps the `⟨aux,𝐇⟩` slack, so no `𝐇`-component need vanish here. -/
lemma clause3_holds {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree) (k : Fin c) :
    s.AC k = msm ((candWitness s tree).aC k) s.gs + msm ((candWitness s tree).aux k) s.hs
      + (candWitness s tree).γC k • s.h := by
  have hp := bundle_open s tree hacc ⟨0, hn⟩ 0
    ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩
  rw [Pcoef_AC] at hp
  simp only [msm_vsmul] at hp
  simp only [candWitness, dif_pos hn]
  exact hp

/-- **Clause 4 holds under acceptance** (with `W_V` full rank). The scalar-commitment opening
`V_k = v_k·g + γ_k·h` is satisfied by the recovered `candWitness` fields: the `eq1` `n'`-coefficients
`eqAj/eqCj` give `msm wV V = eqAj·g + eqCj·h` at each `z`-child (`eq1_special_extract`), and
`V_recover` (with the Gaussian-elimination left inverse `gaussLeftInv s.WV`, correct under `s.hWV`
by `gaussLeftInv_correct`) inverts the `z`-Vandermonde and `W_V` to the per-`k` opening — exactly
`candWitness.v/γ` (modulo `vandInv_eq`). -/
lemma clause4_holds {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree) (k : Fin m) :
    s.V k = (candWitness s tree).v k • s.g + (candWitness s tree).γ k • s.h := by
  have heq1 := fun (j : Fin (q + 1)) (l : Fin (2 * nPrime c + 3)) =>
    arithVerify_eq1 s (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2
      (chalY tree ⟨0, hn⟩) (chalZ tree ⟨0, hn⟩ j)
      (chalX tree ⟨0, hn⟩ j l) (tcomT tree ⟨0, hn⟩ j)
      _ _ _ _ (path_verify s tree hacc ⟨0, hn⟩ j l)
  have hI : ∀ j, msm (((chalZ tree ⟨0, hn⟩ j : Fˣ) : F)
        • (powers ((chalZ tree ⟨0, hn⟩ j : Fˣ) : F) q ᵥ* s.WV)) s.V
      = eqAj s tree ⟨0, hn⟩ j • s.g + eqCj s tree ⟨0, hn⟩ j • s.h := by
    intro j
    rw [eqAj, eqCj]
    simp only [vandInv_eq (chalX_inj tree ⟨0, hn⟩ j)]
    exact eq1_special_extract s _ _ _ (chalX_inj tree ⟨0, hn⟩ j) _ _ _ _ (heq1 j)
  have hV := V_recover s (fun j => ((chalZ tree ⟨0, hn⟩ j : Fˣ) : F))
    (chalZ_inj tree ⟨0, hn⟩) (gaussLeftInv s.WV) (gaussLeftInv_correct s.WV s.hWV)
    (fun j => eqAj s tree ⟨0, hn⟩ j) (fun j => eqCj s tree ⟨0, hn⟩ j) hI k
  simp only [candWitness, dif_pos hn, vandInv_eq (chalZ_inj tree ⟨0, hn⟩)]
  exact hV

omit [DecidableEq F] [DecidableEq G] in
/-- A `(g, h)`-decomposed `V` aggregates linearly: `msm w V = ⟨w, v⟩·g + ⟨w, γ⟩·h`. -/
lemma msm_wv_open {ι : Type*} [Fintype ι] (V : ι → G) (gg hh : G) (w vk γk : ι → F)
    (hV : ∀ k, V k = vk k • gg + γk k • hh) :
    msm w V = ip w vk • gg + ip w γk • hh := by
  simp only [msm, hV, ip, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]

/-- **eq1 opening at an arbitrary bundle.** Generalizes `clause4_holds`'s `hI` from the `i₀`-row to
any bundle `(i, j)`: the aggregate `msm (z·(powers ᵥ* W_V)) V` is the `(g, h)`-combination
`eqAj·g + eqCj·h` recovered from the bundle's `x`-leaf data. -/
lemma eq1_open {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (((chalZ tree i j : Fˣ) : F)
        • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WV)) s.V
      = eqAj s tree i j • s.g + eqCj s tree i j • s.h := by
  have heq1 := fun (l : Fin (2 * nPrime c + 3)) =>
    arithVerify_eq1 s (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2
      (chalY tree i) (chalZ tree i j)
      (chalX tree i j l) (tcomT tree i j)
      _ _ _ _ (path_verify s tree hacc i j l)
  rw [eqAj, eqCj]
  simp only [vandInv_eq (chalX_inj tree i j)]
  exact eq1_special_extract s _ _ _ (chalX_inj tree i j) _ _ _ _ heq1

/-- **The eq1 `(g, h)` collision candidate at bundle `(i, j)`.** The difference between the recovered
`eq1` `n'`-coefficient opening (`eqAj·g + eqCj·h`) and the `candWitness`-`v/γ` reconstruction
(`⟨z·(…W_V), v⟩·g + ⟨…, γ⟩·h`). Both open the *same* group element `msm (z·(…W_V)) V`, so this
candidate always has `msm · gens = 0`; its vanishing is exactly `star_at_bundle`'s `Heq`. -/
def ghCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : Fin (n + n + 2) → F :=
  ghVec (eqAj s tree i j - ip (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WV)) (candWitness s tree).v)
        (eqCj s tree i j - ip (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WV)) (candWitness s tree).γ)

/-- The `ghCand` candidate is a genuine relation: `msm · gens = 0`. (Both terms open `msm (z·(…W_V)) V`
— `eq1_open` and `clause4_holds`+`msm_wv_open` — so their difference vanishes.) -/
lemma ghCand_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (ghCand s tree i j) (gens s) = 0 := by
  have he : eqAj s tree i j • s.g + eqCj s tree i j • s.h
      = ip (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WV)) (candWitness s tree).v • s.g
        + ip (((chalZ tree i j : Fˣ) : F)
            • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WV)) (candWitness s tree).γ • s.h :=
    (eq1_open s tree hacc i j).symm.trans
      (msm_wv_open s.V s.g s.h _ _ _ (fun k => clause4_holds hn s tree hacc k))
  rw [ghCand, ghVec_opens, sub_smul, sub_smul]
  rw [← sub_eq_zero] at he
  rw [← he]; abel

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- `ghCand = 0` is exactly `Heq` at bundle `(i, j)`: the recovered `eqAj` equals the
`candWitness`-`v` reconstruction `⟨z·(…W_V), v⟩`. -/
lemma heq_of_ghCand_zero {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (h0 : (ghCand s tree i j : Fin (n + n + 2) → F) = 0) :
    eqAj s tree i j = ip (((chalZ tree i j : Fˣ) : F)
        • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WV)) (candWitness s tree).v :=
  sub_eq_zero.mp (ghVec_eq_zero h0).1

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Pointwise cancellation of the nonzero `yinv = vinv (powers y n)`: `a ⊙ yinv = b ⊙ yinv ⇒ a = b`. -/
lemma hadamard_yinv_cancel {n : ℕ} (yu : Fˣ) (a b : Fin n → F)
    (h : hadamard a (vinv (powers ((yu : Fˣ) : F) n)) = hadamard b (vinv (powers ((yu : Fˣ) : F) n))) :
    a = b := by
  funext i
  have hyi : ((powers ((yu : Fˣ) : F) n) i)⁻¹ ≠ 0 :=
    inv_ne_zero (by simp only [powers]; exact pow_ne_zero _ (Units.ne_zero yu))
  have hi := congrFun h i
  simp only [hadamard, vinv] at hi
  exact mul_right_cancel₀ hyi hi

/-- **The public-coefficient collision candidate.** For a degree-`p` *public* verifier coefficient
(`p = 0` ↦ `WtO`, `p = k+1` ↦ `Wtk`), whose structural opening is the pure-`h'` vector `hsVec cH yinv`,
the difference `pOpenVec - hsVec` opens `Pcoef p - Pcoef p = 0`. Forces the extracted `𝐆`-part to
vanish and the `𝐇`-part to be the public `cH`. -/
def pubVec {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) (cH : Fin n → F) :
    Fin (n + n + 2) → F :=
  pOpenVec s tree i j p - hsVec cH (vinv (powers ((chalY tree i : Fˣ) : F) n))

lemma pubVec_msm {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) (cH : Fin n → F)
    (hP : Pcoef s ((chalY tree i : Fˣ) : F) ((chalZ tree i j : Fˣ) : F)
        (rootT tree).1 (rootT tree).2.1 (rootT tree).2.2 p
      = msm cH (vinv (powers ((chalY tree i : Fˣ) : F) n) ⊙ s.hs)) :
    msm (pubVec s tree i j p cH) (gens s) = 0 := by
  rw [pubVec, msm_sub_left, pOpenVec_opens s tree hacc i j p, hsVec_opens, hP, sub_self]
