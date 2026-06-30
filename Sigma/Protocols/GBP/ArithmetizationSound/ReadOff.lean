/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBP.ArithmetizationSound.Openings

/-!
# Arithmetization soundness: read-offs and the candidate list

Reading the extracted `bcoef` off the vanishing collision candidates — public
(`pubVec_readoff`), cross-bundle (`pOpenVec_diff_readoff`), and `A_I` (`aiCand_readoff`); the
honest-coefficient evaluations (`honestFL_at_*`, `honestFR_at_*`); degree truncation
(`sum_truncate`) and leaf recovery (`leafG/H_recover`); and the comprehensive candidate list
(`bundleCands`, `relCandList`, `relCand`) with its uniform `msm = 0` proofs.
-/

namespace Sigma.Protocols.GBP

open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `pubVec = 0` reads off as: the extracted `𝐆`-part is `0` and the `𝐇`-part is the public `cH`. -/
lemma pubVec_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) (cH : Fin n → F)
    (h0 : (pubVec s tree i j p cH : Fin (n + n + 2) → F) = 0) :
    (bcoef s tree i j p).1 = 0 ∧ (bcoef s tree i j p).2.1 = cH := by
  rw [pubVec, sub_eq_zero, pOpenVec, hsVec] at h0
  obtain ⟨h1, h2, _⟩ := gvec_inj h0
  exact ⟨h1, hadamard_yinv_cancel (chalY tree i) _ _ h2⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `h'`-basis rescaling between bundles: `a ⊙ yinv_i = b ⊙ yinv_{i'} ⇒ a = powers y_i ⊙ (b ⊙ yinv_{i'})`
— turns a cross-bundle `𝐇`-opening consistency into the `i`-bundle `𝐇`-coefficient. -/
lemma hadamard_yinv_rescale {n : ℕ} (yi yi' : Fˣ) (a b : Fin n → F)
    (h : hadamard a (vinv (powers ((yi : Fˣ) : F) n)) = hadamard b (vinv (powers ((yi' : Fˣ) : F) n))) :
    a = hadamard (powers ((yi : Fˣ) : F) n) (hadamard b (vinv (powers ((yi' : Fˣ) : F) n))) := by
  funext t
  have hyi : (powers ((yi : Fˣ) : F) n) t ≠ 0 := by
    simp only [powers]; exact pow_ne_zero _ (Units.ne_zero yi)
  have hit := congrFun h t
  simp only [hadamard, vinv] at hit ⊢
  rw [mul_comm (powers ((yi : Fˣ) : F) n t), ← hit, mul_assoc, inv_mul_cancel₀ hyi, mul_one]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Cross-bundle commitment read-off.** `pOpenVec i j p − pOpenVec i' j' p = 0` (the two bundles
open the *same* challenge-independent commitment) gives the `𝐆`-part equal across bundles and the
`𝐇`-part rescaled into the `i`-bundle `h'`-basis. -/
lemma pOpenVec_diff_readoff {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (i' : Fin n) (j' : Fin (q + 1)) (p : Fin (2 * nPrime c + 3))
    (h0 : (pOpenVec s tree i j p - pOpenVec s tree i' j' p : Fin (n + n + 2) → F) = 0) :
    (bcoef s tree i j p).1 = (bcoef s tree i' j' p).1
      ∧ (bcoef s tree i j p).2.1 = hadamard (powers ((chalY tree i : Fˣ) : F) n)
          (hadamard (bcoef s tree i' j' p).2.1 (vinv (powers ((chalY tree i' : Fˣ) : F) n))) := by
  rw [sub_eq_zero, pOpenVec, pOpenVec] at h0
  obtain ⟨h1, h2, _⟩ := gvec_inj h0
  exact ⟨h1, hadamard_yinv_rescale (chalY tree i) (chalY tree i') _ _ h2⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `gvec` is additive: a difference of `gvec`s is the `gvec` of the differences (needed because the
`A_I` candidate `aiOpenVec = pOpenVec − aiPubVec` is a difference, not a bare `gvec`). -/
lemma gvec_sub {n : ℕ} (a a' b b' : Fin n → F) (c c' : F) :
    (gvec a b c - gvec a' b' c' : Fin (n + n + 2) → F) = gvec (a - a') (b - b') (c - c') := by
  have happ : ∀ {p ℓ : ℕ} (x x' : Fin p → F) (y y' : Fin ℓ → F),
      (Fin.append x y - Fin.append x' y' : Fin (p + ℓ) → F) = Fin.append (x - x') (y - y') := by
    intro p ℓ x x' y y'
    funext t
    refine Fin.addCases (fun i => ?_) (fun i => ?_) t
    · simp only [Pi.sub_apply, Fin.append_left]
    · simp only [Pi.sub_apply, Fin.append_right]
  simp only [gvec, happ]
  congr 1
  funext t
  fin_cases t <;> simp [Pi.sub_apply]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `aiOpenVec` in explicit `gvec` form (its `pOpenVec`/`aiPubVec` blocks combined). -/
lemma aiOpenVec_gvec {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    aiOpenVec s tree i j
      = gvec ((bcoef s tree i j ⟨c + 1, by simp only [nPrime]; omega⟩).1
            - hadamard (vinv (powers ((chalY tree i : Fˣ) : F) n))
                (((chalZ tree i j : Fˣ) : F)
                  • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WR)))
          (hadamard (bcoef s tree i j ⟨c + 1, by simp only [nPrime]; omega⟩).2.1
                (vinv (powers ((chalY tree i : Fˣ) : F) n))
            - hadamard (((chalZ tree i j : Fˣ) : F)
                  • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL))
                (vinv (powers ((chalY tree i : Fˣ) : F) n)))
          (bcoef s tree i j ⟨c + 1, by simp only [nPrime]; omega⟩).2.2 := by
  rw [aiOpenVec, pOpenVec, aiPubVec, gvec_sub, sub_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL` at degree `c+1` (the `A_I` slot). -/
lemma honestFL_at_AI {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) :
    honestFL s yu zu aL aO sL aC ⟨c + 1, by simp only [nPrime]; omega⟩
      = fun i => aL i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i := by
  simp only [honestFL, if_true,
    Finset.sum_eq_zero (fun (k : Fin c) _ => if_neg (show ¬(c + 1 = nPrime c - ((k : ℕ) + 1)) by
      have := k.isLt; simp only [nPrime]; omega)),
    show (c + 1 = nPrime c) = False from eq_false (by simp only [nPrime]; omega),
    show (c + 1 = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    if_false, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL` at degree `n'−(k+1)` (the `A_C⁽ᵏ⁾` slot). -/
lemma honestFL_at_AC {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) (k : Fin c) :
    honestFL s yu zu aL aO sL aC ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩
      = aC k := by
  have hkv := k.isLt
  have hac : ∀ x : Fin c, (nPrime c - ((k : ℕ) + 1) = nPrime c - ((x : ℕ) + 1)) = (x = k) := fun x =>
    by rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by have := x.isLt; simp only [nPrime] at h; omega),
      fun h => by rw [h]⟩
  simp only [honestFL,
    show ¬(nPrime c - ((k : ℕ) + 1) = c + 1) from (by simp only [nPrime]; omega),
    show ¬(nPrime c - ((k : ℕ) + 1) = nPrime c) from (by simp only [nPrime]; omega),
    show ¬(nPrime c - ((k : ℕ) + 1) = nPrime c + 1) from (by simp only [nPrime]; omega),
    hac, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL` at degree `n'` (the `A_O` slot). -/
lemma honestFL_at_AO {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) :
    honestFL s yu zu aL aO sL aC ⟨nPrime c, by omega⟩ = aO := by
  have hac : ∀ k : Fin c, ¬(nPrime c = nPrime c - ((k : ℕ) + 1)) :=
    fun k => by have := k.isLt; simp only [nPrime]; omega
  simp only [honestFL,
    show ¬(nPrime c = c + 1) from (by simp only [nPrime]; omega),
    show ¬(nPrime c = nPrime c + 1) from (by omega), hac,
    Finset.sum_const_zero, if_false, if_true, add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL` at degree `n'+1` (the `S` slot). -/
lemma honestFL_at_S {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) :
    honestFL s yu zu aL aO sL aC ⟨nPrime c + 1, by omega⟩ = sL := by
  have hac : ∀ k : Fin c, ¬(nPrime c + 1 = nPrime c - ((k : ℕ) + 1)) :=
    fun k => by have := k.isLt; simp only [nPrime]; omega
  simp only [honestFL,
    show ¬(nPrime c + 1 = c + 1) from (by simp only [nPrime]; omega),
    show ¬(nPrime c + 1 = nPrime c) from (by omega), hac,
    Finset.sum_const_zero, if_false, if_true, add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFL` vanishes at the public degrees `0` and `k+1`. -/
lemma honestFL_at_pub {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) (p : Fin (nPrime c + 2))
    (h0 : (p : ℕ) = 0 ∨ ∃ k : Fin c, (p : ℕ) = (k : ℕ) + 1) :
    honestFL s yu zu aL aO sL aC p = 0 := by
  have hp : (p : ℕ) ≤ c := by
    rcases h0 with h | ⟨k, hk⟩
    · omega
    · have := k.isLt; omega
  simp only [honestFL,
    show ¬((p : ℕ) = c + 1) from (by omega),
    show ¬((p : ℕ) = nPrime c) from (by simp only [nPrime]; omega),
    show ¬((p : ℕ) = nPrime c + 1) from (by simp only [nPrime]; omega),
    Finset.sum_eq_zero (fun (k : Fin c) _ => if_neg (show ¬((p : ℕ) = nPrime c - ((k : ℕ) + 1)) by
      have := k.isLt; simp only [nPrime]; omega)), if_false, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR` at degree `0` (the `WtO` slot). -/
lemma honestFR_at_WtO {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aR sR : Fin n → F) (aux : Fin c → Fin n → F) :
    honestFR s yu zu aR sR aux ⟨0, by simp only [nPrime]; omega⟩
      = fun i => ((↑zu : F) • powers (↑zu) q ᵥ* s.WO) i - powers (↑yu) n i := by
  simp only [honestFR, if_true,
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬((0 : ℕ) = (x : ℕ) + 1) by omega)),
    Finset.sum_eq_zero (fun (k : Fin c) _ => if_neg (show ¬((0 : ℕ) = nPrime c - ((k : ℕ) + 1)) by
      have := k.isLt; simp only [nPrime]; omega)),
    show ((0 : ℕ) = c + 1) = False from eq_false (by omega),
    show ((0 : ℕ) = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    if_false, add_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR` at degree `k+1` (the `WtC⁽ᵏ⁾` slot). -/
lemma honestFR_at_WtC {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aR sR : Fin n → F) (aux : Fin c → Fin n → F) (k : Fin c) :
    honestFR s yu zu aR sR aux ⟨(k : ℕ) + 1, by have := k.isLt; simp only [nPrime]; omega⟩
      = (↑zu : F) • powers (↑zu) q ᵥ* s.WC k := by
  have hkv := k.isLt
  have hwc : ∀ x : Fin c, ((k : ℕ) + 1 = (x : ℕ) + 1) = (x = k) := fun x =>
    by rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  have hac : ∀ x : Fin c, ((k : ℕ) + 1 = nPrime c - ((x : ℕ) + 1)) = False :=
    fun x => eq_false (by have := x.isLt; simp only [nPrime]; omega)
  simp only [honestFR,
    show ((k : ℕ) + 1 = 0) = False from eq_false (by omega),
    show ((k : ℕ) + 1 = c + 1) = False from eq_false (by omega),
    show ((k : ℕ) + 1 = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    hwc, hac, if_false, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR` at degree `c+1` (the `WtL`+`aR` slot). -/
lemma honestFR_at_WL {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aR sR : Fin n → F) (aux : Fin c → Fin n → F) :
    honestFR s yu zu aR sR aux ⟨c + 1, by simp only [nPrime]; omega⟩
      = fun i => powers (↑yu) n i * aR i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WL) i := by
  simp only [honestFR, if_true,
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬(c + 1 = (x : ℕ) + 1) by
      have := x.isLt; omega)),
    Finset.sum_eq_zero (fun (k : Fin c) _ => if_neg (show ¬(c + 1 = nPrime c - ((k : ℕ) + 1)) by
      have := k.isLt; simp only [nPrime]; omega)),
    show ((c + 1 : ℕ) = 0) = False from eq_false (by omega),
    show ((c + 1 : ℕ) = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    if_false, add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR` at degree `n'−(k+1)` (the `aux⁽ᵏ⁾` slot). -/
lemma honestFR_at_aux {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aR sR : Fin n → F) (aux : Fin c → Fin n → F) (k : Fin c) :
    honestFR s yu zu aR sR aux ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩
      = fun i => powers (↑yu) n i * aux k i := by
  have hkv := k.isLt
  have hac : ∀ x : Fin c, (nPrime c - ((k : ℕ) + 1) = nPrime c - ((x : ℕ) + 1)) = (x = k) := fun x =>
    by rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by have := x.isLt; simp only [nPrime] at h; omega),
      fun h => by rw [h]⟩
  have hwc : ∀ x : Fin c, (nPrime c - ((k : ℕ) + 1) = (x : ℕ) + 1) = False :=
    fun x => eq_false (by have := x.isLt; simp only [nPrime]; omega)
  simp only [honestFR,
    show (nPrime c - ((k : ℕ) + 1) = 0) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c - ((k : ℕ) + 1) = c + 1) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c - ((k : ℕ) + 1) = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    hwc, hac, if_false, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `honestFR` at degree `n'+1` (the `S`+`sR` slot). -/
lemma honestFR_at_sR {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aR sR : Fin n → F) (aux : Fin c → Fin n → F) :
    honestFR s yu zu aR sR aux ⟨nPrime c + 1, by omega⟩ = fun i => powers (↑yu) n i * sR i := by
  have hwc : ∀ x : Fin c, ¬(nPrime c + 1 = (x : ℕ) + 1) :=
    fun x => by have := x.isLt; simp only [nPrime]; omega
  have hac : ∀ k : Fin c, ¬(nPrime c + 1 = nPrime c - ((k : ℕ) + 1)) :=
    fun k => by have := k.isLt; simp only [nPrime]; omega
  simp only [honestFR, if_true,
    show ((nPrime c + 1 : ℕ) = 0) = False from eq_false (by simp only [nPrime]; omega),
    show ((nPrime c + 1 : ℕ) = c + 1) = False from eq_false (by simp only [nPrime]; omega),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (hwc x)),
    Finset.sum_eq_zero (fun (k : Fin c) _ => if_neg (hac k)),
    if_false, add_zero, zero_add]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Degree truncation.** A degree-`2n'+2` polynomial whose coefficients agree with a degree-`n'+1`
one below `n'+2` and vanish above collapses to the lower-degree sum. (Lets `vandermonde_recover`'s
full `2n'+3`-coefficient reconstruction be read as the `n'+2`-term honest `f_L`/`f_R`.) -/
lemma sum_truncate {M : Type*} [AddCommMonoid M] [Module F M] {np : ℕ} (x : F)
    (c : Fin (2 * np + 3) → M) (d : Fin (np + 2) → M)
    (H1 : ∀ ℓ : Fin (np + 2), c ⟨(ℓ : ℕ), by omega⟩ = d ℓ)
    (H2 : ∀ p : Fin (2 * np + 3), np + 2 ≤ (p : ℕ) → c p = 0) :
    (∑ p : Fin (2 * np + 3), x ^ (p : ℕ) • c p) = ∑ ℓ : Fin (np + 2), x ^ (ℓ : ℕ) • d ℓ := by
  have e1 : (∑ p : Fin (2 * np + 3), x ^ (p : ℕ) • c p)
      = ∑ p ∈ Finset.range (2 * np + 3), x ^ p • (if h : p < 2 * np + 3 then c ⟨p, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun p => x ^ p • (if h : p < 2 * np + 3 then c ⟨p, h⟩ else 0)) (2 * np + 3)]
    exact Finset.sum_congr rfl fun p _ => by rw [dif_pos p.isLt]
  have e2 : (∑ ℓ : Fin (np + 2), x ^ (ℓ : ℕ) • d ℓ)
      = ∑ p ∈ Finset.range (np + 2), x ^ p • (if h : p < np + 2 then d ⟨p, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun p => x ^ p • (if h : p < np + 2 then d ⟨p, h⟩ else 0)) (np + 2)]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [dif_pos ℓ.isLt]
  rw [e1, e2]
  have hsub : Finset.range (np + 2) ⊆ Finset.range (2 * np + 3) :=
    fun a ha => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ha) (by omega))
  have hzero : ∀ p ∈ Finset.range (2 * np + 3), p ∉ Finset.range (np + 2) →
      x ^ p • (if h : p < 2 * np + 3 then c ⟨p, h⟩ else 0) = 0 := by
    intro p hp hpn
    rw [Finset.mem_range] at hp hpn
    have hpge : np + 2 ≤ p := by omega
    rw [dif_pos (show p < 2 * np + 3 by omega), H2 ⟨p, by omega⟩ hpge, smul_zero]
  rw [← Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl fun p hp => by
    rw [Finset.mem_range] at hp
    rw [dif_pos (show p < 2 * np + 3 by omega), dif_pos hp, H1 ⟨p, hp⟩]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Leaf `𝐆`-data recovery.** Each leaf's sent `a`-vector is the `bcoef`-`𝐆` polynomial evaluated
at that leaf's `x`-challenge (the inverse-Vandermonde recovery, `vandInv_eq`). -/
lemma leafG_recover {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (l : Fin (2 * nPrime c + 3)) :
    (leafO tree i j l).2.2.1
      = ∑ p : Fin (2 * nPrime c + 3),
          ((chalX tree i j l : Fˣ) : F) ^ (p : ℕ) • (bcoef s tree i j p).1 := by
  rw [vandermonde_recover (fun l => ((chalX tree i j l : Fˣ) : F))
    (chalX_inj tree i j) (fun l => (leafO tree i j l).2.2.1) l]
  exact Finset.sum_congr rfl fun p _ => by simp only [bcoef, vandInv_eq (chalX_inj tree i j)]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Leaf `𝐇`-data recovery.** Each leaf's sent `b`-vector is the `bcoef`-`𝐇` polynomial evaluated
at that leaf's `x`-challenge. -/
lemma leafH_recover {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (l : Fin (2 * nPrime c + 3)) :
    (leafO tree i j l).2.2.2
      = ∑ p : Fin (2 * nPrime c + 3),
          ((chalX tree i j l : Fˣ) : F) ^ (p : ℕ) • (bcoef s tree i j p).2.1 := by
  rw [vandermonde_recover (fun l => ((chalX tree i j l : Fˣ) : F))
    (chalX_inj tree i j) (fun l => (leafO tree i j l).2.2.2) l]
  exact Finset.sum_congr rfl fun p _ => by simp only [bcoef, vandInv_eq (chalX_inj tree i j)]

/-- **Step 5 (the per-bundle collision candidates)** at bundle `(i, j)` (reference bundle
`(⟨0,hn⟩, 0)`): the public `WtO`/`Wtk` structural differences (`pubVec`), the `A_I`/`A_O`/`A_C⁽ᵏ⁾`/`S`
cross-bundle opening differences, the eq1 `(g,h)` candidate (`ghCand`), and the high-degree openings
(which open `0`). Each has `msm · gens = 0` (`bundleCands_msm_zero`) — the difference candidates open
equal commitments, the high-degree ones open `0` directly; a nonzero one is therefore a non-trivial
discrete-log relation. -/
def bundleCands {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (hn : 0 < n)
    (i : Fin n) (j : Fin (q + 1)) : List (Fin (n + n + 2) → F) :=
  pubVec s tree i j ⟨0, by simp only [nPrime]; omega⟩
      (((chalZ tree i j : Fˣ) : F)
        • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WO) - powers ((chalY tree i : Fˣ) : F) n)
    :: (aiOpenVec s tree i j - aiOpenVec s tree ⟨0, hn⟩ 0)
    :: (pOpenVec s tree i j ⟨nPrime c, by omega⟩ - pOpenVec s tree ⟨0, hn⟩ 0 ⟨nPrime c, by omega⟩)
    :: (pOpenVec s tree i j ⟨nPrime c + 1, by omega⟩ - pOpenVec s tree ⟨0, hn⟩ 0 ⟨nPrime c + 1, by omega⟩)
    :: ghCand s tree i j
    :: ((List.finRange c).map (fun (k : Fin c) => pubVec s tree i j
          ⟨(k : ℕ) + 1, by have := k.isLt; simp only [nPrime]; omega⟩
          (((chalZ tree i j : Fˣ) : F) • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WC k)))
      ++ (List.finRange c).map (fun (k : Fin c) =>
          pOpenVec s tree i j ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩
          - pOpenVec s tree ⟨0, hn⟩ 0 ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩)
      ++ ((List.finRange (2 * nPrime c + 3)).filter
            (fun (p : Fin (2 * nPrime c + 3)) => decide (nPrime c + 2 ≤ (p : ℕ)))).map
          (fun (p : Fin (2 * nPrime c + 3)) => pOpenVec s tree i j p))

/-- The full candidate list: per-bundle candidates over the `i₀`-row (all `j`) and the `j=0`-column
(all `i`) — the "L"-shape that `clauses12_of_LZ` consumes. -/
def relCandList {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (hn : 0 < n) :
    List (Fin (n + n + 2) → F) :=
  (List.finRange (q + 1)).flatMap (fun j => bundleCands s tree hn ⟨0, hn⟩ j)
    ++ (List.finRange n).flatMap (fun i => bundleCands s tree hn i 0)

/-- **The collision candidate** (computable): the first genuine non-trivial discrete-log relation in
`relCandList`, or `0` if none. -/
def relCand {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) : Fin (n + n + 2) → F :=
  if hn : 0 < n then
    ((relCandList s tree hn).find? (fun v => decide (IsNontrivialDLRel (gens s) v))).getD 0
  else 0

/-- **Every per-bundle candidate opens `0`.** Public ones via `pubVec_msm`+`Pcoef_WtO/Wtk`; the
`A_I` via `aiOpenVec_opens` (both bundles open `A_I`); `A_O/A_C/S` via `pOpenVec_msm_diff`+`Pcoef_*`
(challenge-independent commitments); `ghCand` via `ghCand_msm_zero`; high-degree via
`pOpenVec_high_msm_zero`. -/
lemma bundleCands_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (rc : Fin (n + n + 2) → F) (hc : rc ∈ bundleCands s tree hn i j) :
    msm rc (gens s) = 0 := by
  rw [bundleCands] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact pubVec_msm s tree hacc i j _ _ (Pcoef_WtO s _ _ _ _ _)
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [msm_sub_left, aiOpenVec_opens s tree hacc i j, aiOpenVec_opens s tree hacc ⟨0, hn⟩ 0,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [pOpenVec_msm_diff s tree hacc i ⟨0, hn⟩ j 0 ⟨nPrime c, by omega⟩, Pcoef_AO, Pcoef_AO,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [pOpenVec_msm_diff s tree hacc i ⟨0, hn⟩ j 0 ⟨nPrime c + 1, by omega⟩, Pcoef_S, Pcoef_S,
      sub_self]
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ghCand_msm_zero hn s tree hacc i j
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
      exact pubVec_msm s tree hacc i j _ _ (Pcoef_Wtk s _ _ _ _ _ k)
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
      rw [pOpenVec_msm_diff s tree hacc i ⟨0, hn⟩ j 0
          ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩,
        Pcoef_AC, Pcoef_AC, sub_self]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact pOpenVec_high_msm_zero s tree hacc i j p (of_decide_eq_true (List.mem_filter.mp hp).2)

/-- Every candidate in `relCandList` opens `0`. -/
lemma relCandList_msm_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (rc : Fin (n + n + 2) → F) (hc : rc ∈ relCandList s tree hn) :
    msm rc (gens s) = 0 := by
  simp only [relCandList, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨j, hj⟩ | ⟨i, hi⟩
  · exact bundleCands_msm_zero hn s tree hacc _ _ rc hj
  · exact bundleCands_msm_zero hn s tree hacc _ _ rc hi

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **High-degree vanishing.** When all bundle candidates are `0`, the extracted `bcoef` above degree
`n'+1` vanishes (both `𝐆` and `𝐇` parts) — the high `pOpenVec` opens `0`, so its `gvec` blocks are `0`. -/
lemma bcoef_high_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (p : Fin (2 * nPrime c + 3)) (hp : nPrime c + 2 ≤ (p : ℕ)) :
    (bcoef s tree i j p).1 = 0 ∧ (bcoef s tree i j p).2.1 = 0 := by
  have hmem : pOpenVec s tree i j p ∈ bundleCands s tree hn i j := by
    rw [bundleCands]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))))
    exact List.mem_append_right _ (List.mem_map.mpr ⟨p, List.mem_filter.mpr
      ⟨List.mem_finRange p, decide_eq_true hp⟩, rfl⟩)
  have h0 := hbz _ hmem
  rw [pOpenVec] at h0
  obtain ⟨hg, hh, _⟩ := gvec_eq_zero h0
  refine ⟨hg, hadamard_yinv_cancel (chalY tree i) _ 0 ?_⟩
  rw [hh]; funext t; simp [hadamard]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The `A_I` read-off.** The vanishing `A_I` cross-bundle candidate forces the `bcoef`-`𝐆` part to
`aL + (z·WR)⊙yinv` and the `𝐇` part to `(powers y)·aR + z·WL` — exactly `honestFL`/`honestFR` at
degree `c+1`. (`aiOpenVec_gvec` + `gvec_sub` + `gvec_inj`, with `candWitness.aL/aR` the reference.) -/
lemma aiCand_readoff {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (h0 : (aiOpenVec s tree i j - aiOpenVec s tree ⟨0, hn⟩ 0 : Fin (n + n + 2) → F) = 0) :
    (bcoef s tree i j ⟨c + 1, by simp only [nPrime]; omega⟩).1
        = (fun t => (candWitness s tree).aL t
            + (((chalZ tree i j : Fˣ) : F)
                • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WR)) t
              * vinv (powers ((chalY tree i : Fˣ) : F) n) t)
      ∧ (bcoef s tree i j ⟨c + 1, by simp only [nPrime]; omega⟩).2.1
        = (fun t => powers ((chalY tree i : Fˣ) : F) n t * (candWitness s tree).aR t
            + (((chalZ tree i j : Fˣ) : F)
                • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL)) t) := by
  rw [aiOpenVec_gvec, aiOpenVec_gvec, gvec_sub] at h0
  obtain ⟨hG, hH, _⟩ := gvec_eq_zero h0
  simp only [candWitness, dif_pos hn]
  constructor
  · funext t
    have hgt := congrFun hG t
    simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hgt ⊢
    linear_combination hgt
  · have hHt : hadamard ((bcoef s tree i j ⟨c + 1, by simp only [nPrime]; omega⟩).2.1
            - ((chalZ tree i j : Fˣ) : F)
              • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL))
          (vinv (powers ((chalY tree i : Fˣ) : F) n))
        = hadamard ((bcoef s tree ⟨0, hn⟩ 0 ⟨c + 1, by simp only [nPrime]; omega⟩).2.1
            - ((chalZ tree ⟨0, hn⟩ 0 : Fˣ) : F)
              • (powers ((chalZ tree ⟨0, hn⟩ 0 : Fˣ) : F) q ᵥ* s.WL))
          (vinv (powers ((chalY tree ⟨0, hn⟩ : Fˣ) : F) n)) := by
      funext t
      have hht := congrFun hH t
      simp only [Pi.sub_apply, Pi.zero_apply, hadamard] at hht ⊢
      linear_combination hht
    have hrescale := hadamard_yinv_rescale (chalY tree i) (chalY tree ⟨0, hn⟩) _ _ hHt
    funext t
    have := congrFun hrescale t
    simp only [Pi.sub_apply, hadamard] at this ⊢
    linear_combination this

/-- Every degree `ℓ : Fin (n'+2)` lands in exactly one `f_L`/`f_R` slot: public `0`/`k+1`, `A_I` at
`c+1`, `A_C` at `n'−(k+1)`, `A_O` at `n'`, or `S` at `n'+1`. -/
lemma q_slot_cases {c : ℕ} (ℓ : Fin (nPrime c + 2)) :
    (ℓ : ℕ) = 0 ∨ (∃ k : Fin c, (ℓ : ℕ) = (k : ℕ) + 1) ∨ (ℓ : ℕ) = c + 1
      ∨ (∃ k : Fin c, (ℓ : ℕ) = nPrime c - ((k : ℕ) + 1)) ∨ (ℓ : ℕ) = nPrime c
      ∨ (ℓ : ℕ) = nPrime c + 1 := by
  have hql : (ℓ : ℕ) < nPrime c + 2 := ℓ.isLt
  rcases lt_trichotomy (ℓ : ℕ) (c + 1) with h | h | h
  · rcases Nat.eq_zero_or_pos (ℓ : ℕ) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨⟨(ℓ : ℕ) - 1, by omega⟩, by simp only; omega⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases lt_trichotomy (ℓ : ℕ) (nPrime c) with h2 | h2 | h2
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨nPrime c - 1 - (ℓ : ℕ), by simp only [nPrime] at *; omega⟩, ?_⟩)))
      simp only; simp only [nPrime] at *; omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp only [nPrime] at *; omega)))))
