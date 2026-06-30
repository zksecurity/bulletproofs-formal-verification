/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBP.Arithmetization
import Sigma.Utils.Binding
import Sigma.Utils.Vandermonde
import Sigma.Protocols.GBP.ArithmetizationComplete

/-!
# Arithmetization soundness: verifier coefficients and the `t`-polynomial

The verifier-commitment coefficient family `Pcoef` and the lemmas pinning each degree to a public
weight or a prover commitment (`Pcoef_WtO/Wtk/AC/high_zero`); the two verifier checks restated for
extraction (`arithVerify_eq1/eq2`, `eq2_extract` — with the dense `{T_i}` message scattered onto
the full degree range by `tScatter`/`eq1_RHS_repackage`); the honest sparse `f_L`/`f_R`
coefficient families (`honestFL`/`honestFR`) with the constraint-free `t`-polynomial expansion
(`tcoeff_expand`/`tcoeff_recover`); and the `z`/`y`-deaggregation primitives.
-/

namespace Sigma.Protocols.GBP

open OracleComp
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The commitment generators of a statement, concatenated as `(𝐆, 𝐇, g, h)` (length `n+n+2`);
a non-trivial discrete-log relation among these is the extractor's "break". Indexed by
`Fin (n + n + 2)` so that it is *definitionally* the `Fin.append`, which makes the multi-scalar
multiplication split blockwise (`msm_append`). -/
def gens {n q m c : ℕ} (s : Statement F G n q m c) : Fin (n + n + 2) → G :=
  Fin.append (Fin.append s.gs s.hs) ![s.g, s.h]

omit [DecidableEq F] [DecidableEq G] in
/-- `msm` of an explicit `(a, b, c, d)` block vector against `gens s` opens in the four bases. -/
lemma gens_msm {n q m c : ℕ} (s : Statement F G n q m c) (a b : Fin n → F) (c d : F) :
    msm (Fin.append (Fin.append a b) ![c, d]) (gens s)
      = msm a s.gs + msm b s.hs + c • s.g + d • s.h := by
  rw [gens, msm_append, msm_append]
  have : msm ![c, d] ![s.g, s.h] = c • s.g + d • s.h := by simp [msm, Fin.sum_univ_two]
  rw [this]; abel

omit [DecidableEq F] [DecidableEq G] in
/-- A vanishing `Fin.append` vector has vanishing blocks. -/
lemma append_eq_zero {p ℓ : ℕ} {A : Fin p → F} {B : Fin ℓ → F} (h : Fin.append A B = 0) :
    A = 0 ∧ B = 0 := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · simpa [Fin.append_left] using congrFun h (Fin.castAdd ℓ i)
  · simpa [Fin.append_right] using congrFun h (Fin.natAdd p i)

omit [DecidableEq F] [DecidableEq G] in
/-- **Under binding, an opening in the basis `(𝐆, 𝐇, g, h)` is unique.** -/
lemma open_unique {n q m c : ℕ} {s : Statement F G n q m c}
    (hbind : ∀ v : Fin (n + n + 2) → F, msm v (gens s) = 0 → v = 0)
    {a a' b b' : Fin n → F} {c c' d d' : F}
    (h : msm a s.gs + msm b s.hs + c • s.g + d • s.h
       = msm a' s.gs + msm b' s.hs + c' • s.g + d' • s.h) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hz : msm (Fin.append (Fin.append (a - a') (b - b')) ![c - c', d - d']) (gens s) = 0 := by
    rw [gens_msm]
    have hd : msm (a - a') s.gs + msm (b - b') s.hs + (c - c') • s.g + (d - d') • s.h
        = (msm a s.gs + msm b s.hs + c • s.g + d • s.h)
          - (msm a' s.gs + msm b' s.hs + c' • s.g + d' • s.h) := by
      simp only [msm_sub_left, sub_smul]; abel
    rw [hd, h, sub_self]
  obtain ⟨hAB, hCD⟩ := append_eq_zero (hbind _ hz)
  obtain ⟨ha, hb⟩ := append_eq_zero hAB
  have hc : c - c' = 0 := by simpa using congrFun hCD 0
  have hd : d - d' = 0 := by simpa using congrFun hCD 1
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb, sub_eq_zero.mp hc, sub_eq_zero.mp hd⟩

/-- The `x`-power coefficient family of the verifier's commitment `P` (one group element per
degree `0 … 2n'+2`): `WtO` at `0`, `Wtk k` at `k+1`, `A_I+WtL+WtR` at `c+1`, `A_C k` at
`n'-(k+1)`, `A_O` at `n'`, `S` at `n'+1`, and `0` elsewhere. -/
def Pcoef {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G)
    (p : Fin (2 * nPrime c + 3)) : G :=
  let vy := powers y n
  let yinv := vinv vy
  let vz := powers z q
  let h' := yinv ⊙ s.hs
  (if (p : ℕ) = 0 then msm (z • (vz ᵥ* s.WO) - vy) h' else 0)
  + (∑ k : Fin c, if (p : ℕ) = k.val + 1 then msm (z • (vz ᵥ* s.WC k)) h' else 0)
  + (if (p : ℕ) = c + 1 then AI + msm (z • (vz ᵥ* s.WL)) h' + msm (hadamard yinv (z • (vz ᵥ* s.WR))) s.gs
      else 0)
  + (∑ k : Fin c, if (p : ℕ) = nPrime c - (k.val + 1) then s.AC k else 0)
  + (if (p : ℕ) = nPrime c then AO else 0)
  + (if (p : ℕ) = nPrime c + 1 then Scom else 0)

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier's commitment `P` is the degree-`(2n'+2)` polynomial `∑ₚ xᵖ · Pcoef p` evaluated
at the challenge `x` (a repackaging of the `arithVerify` definition of `P`). -/
lemma P_repackage {n q m c : ℕ} (s : Statement F G n q m c) (y z x : F) (AI AO Scom : G) :
    msm (z • (powers z q ᵥ* s.WO) - powers y n) (vinv (powers y n) ⊙ s.hs)
        + (∑ k : Fin c, x ^ (k.val + 1) • msm (z • (powers z q ᵥ* s.WC k)) (vinv (powers y n) ⊙ s.hs))
        + x ^ (c + 1) • (AI + msm (z • (powers z q ᵥ* s.WL)) (vinv (powers y n) ⊙ s.hs)
            + msm (hadamard (vinv (powers y n)) (z • (powers z q ᵥ* s.WR))) s.gs)
        + (∑ k : Fin c, x ^ (nPrime c - (k.val + 1)) • s.AC k)
        + x ^ nPrime c • AO + x ^ (nPrime c + 1) • Scom
      = ∑ p : Fin (2 * nPrime c + 3), x ^ (p : ℕ) • Pcoef s y z AI AO Scom p := by
  simp only [Pcoef, smul_add, Finset.sum_add_distrib]
  rw [sum_pow_smul_ite x 0 (by omega),
    sum_pow_smul_sum_ite x (fun k => k.val + 1) (fun k => by simp only [nPrime]; have := k.isLt; omega),
    sum_pow_smul_ite x (c + 1) (by simp only [nPrime]; omega),
    sum_pow_smul_sum_ite x (fun k => nPrime c - (k.val + 1)) (fun k => by simp only [nPrime]; omega),
    sum_pow_smul_ite x (nPrime c) (by omega),
    sum_pow_smul_ite x (nPrime c + 1) (by omega)]
  simp only [pow_zero, one_smul, smul_add]

omit [DecidableEq F] [DecidableEq G] in
/-- **Step 1 (`x`-Vandermonde extraction, `eq2`).** From the `2n'+3` accepting `eq2` equations at
distinct `x`, each coefficient `Pcoef p` opens in the `(𝐆, h', h)` basis, the openings being the
inverse-Vandermonde combinations of the prover's sent `(a, b, μ)`. This is the core inversion
behind the per-degree read-offs `bcoefG_eq`/`bcoefH_eq`. -/
lemma eq2_extract {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G)
    (x : Fin (2 * nPrime c + 3) → F) (hx : Function.Injective x)
    (a b : Fin (2 * nPrime c + 3) → (Fin n → F)) (μ : Fin (2 * nPrime c + 3) → F)
    (heq : ∀ l, (∑ p : Fin (2 * nPrime c + 3), x l ^ (p : ℕ) • Pcoef s y z AI AO Scom p)
      = msm (a l) s.gs + msm (b l) (vinv (powers y n) ⊙ s.hs) + μ l • s.h)
    (p : Fin (2 * nPrime c + 3)) :
    Pcoef s y z AI AO Scom p
      = msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • a l) s.gs
        + msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • b l) (vinv (powers y n) ⊙ s.hs)
        + (∑ l, (Matrix.vandermonde x)⁻¹ p l • μ l) • s.h := by
  set h' := vinv (powers y n) ⊙ s.hs
  refine congrFun (vandermonde_coeff_unique x hx (Pcoef s y z AI AO Scom)
    (fun p => msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • a l) s.gs
      + msm (∑ l, (Matrix.vandermonde x)⁻¹ p l • b l) h'
      + (∑ l, (Matrix.vandermonde x)⁻¹ p l • μ l) • s.h) ?_) p
  intro l
  rw [heq l]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · rw [show (∑ ℓ : Fin (2 * nPrime c + 3), x l ^ (ℓ : ℕ)
            • msm (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • a l') s.gs)
          = msm (∑ ℓ : Fin (2 * nPrime c + 3), x l ^ (ℓ : ℕ)
            • (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • a l')) s.gs from by
        rw [msm_sum_left]; exact Finset.sum_congr rfl fun ℓ _ => (msm_smul_left _ _ _).symm]
      rw [← vandermonde_recover x hx a l]
    · rw [show (∑ ℓ : Fin (2 * nPrime c + 3), x l ^ (ℓ : ℕ)
            • msm (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • b l') h')
          = msm (∑ ℓ : Fin (2 * nPrime c + 3), x l ^ (ℓ : ℕ)
            • (∑ l', (Matrix.vandermonde x)⁻¹ ℓ l' • b l')) h' from by
        rw [msm_sum_left]; exact Finset.sum_congr rfl fun ℓ _ => (msm_smul_left _ _ _).symm]
      rw [← vandermonde_recover x hx b l]
  · simp only [← smul_assoc, ← Finset.sum_smul]
    rw [← vandermonde_recover x hx μ l]

set_option maxHeartbeats 1600000 in
/-- The verifier's second check (`eq2`), restated as `∑ₚ xᵖ·Pcoef p = msm a 𝐆 + msm b h' + μ·h`
via `P_repackage` (transcript given in destructured form to keep projections cheap). -/
lemma arithVerify_eq2 {n q m c : ℕ} (s : Statement F G n q m c)
    (AI AO Scom : G) (yu zu xu : Fˣ) (T : Fin (3 * c + 5) → G)
    (τx μ : F) (a b : Fin n → F)
    (h : (relArith F G n).rel (arithOut s ((AI, AO, Scom), yu, zu, T, xu, PUnit.unit))
      (τx, μ, a, b) = true) :
    (∑ p : Fin (2 * nPrime c + 3), (↑xu : F) ^ (p : ℕ)
        • Pcoef s (↑yu : F) (↑zu : F) AI AO Scom p)
      = msm a s.gs + msm b (vinv (powers (↑yu : F) n) ⊙ s.hs) + μ • s.h := by
  simp only [arithOut, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [P_repackage s (↑yu : F) (↑zu : F) (↑xu : F) AI AO Scom] at h
  exact h.2

/-- Scatter the densely-transmitted coefficient commitments `{T_i}` back onto the full degree
range `0 … 2n'+2`: degree `tIdx i` carries `T i`; the unsent degrees (`0 … c`, and the special
`n'`) carry `0`. Proof apparatus only — the wire message stays dense. -/
def tScatter {c : ℕ} (T : Fin (3 * c + 5) → G) (r : Fin (2 * nPrime c + 3)) : G :=
  ∑ i : Fin (3 * c + 5), if tIdx i = r then T i else 0

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier's `eq1` right-hand side is the polynomial `∑ᵣ xʳ·Tcoef'ᵣ` over the **full**
degree range: the special `n'`-coefficient `special = (δ−w_c)·g − ⟨w_V, V⟩` at the gap, and the
scattered dense message `tScatter T` elsewhere (`0` at the unsent degrees `0 … c`). Reindexes
the dense sum by `tIdx_inj`/`tIdx_ne`, so the `x`-Vandermonde extraction over all `2n'+3`
coefficients applies unchanged. -/
lemma eq1_RHS_repackage {c : ℕ} (x : F) (special : G) (T : Fin (3 * c + 5) → G) :
    x ^ nPrime c • special
        + (∑ i : Fin (3 * c + 5), x ^ (tIdx i : ℕ) • T i)
      = ∑ r : Fin (2 * nPrime c + 3), x ^ (r : ℕ)
          • (if (r : ℕ) = nPrime c then special else tScatter T r) := by
  have hnp : nPrime c < 2 * nPrime c + 3 := by omega
  have hsc : (∑ i : Fin (3 * c + 5), x ^ (tIdx i : ℕ) • T i)
      = ∑ r : Fin (2 * nPrime c + 3), x ^ (r : ℕ) • tScatter T r := by
    simp only [tScatter, Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  rw [hsc, ← sum_pow_smul_ite x (nPrime c) hnp special, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : (r : ℕ) = nPrime c
  · have h0 : tScatter T r = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg fun h => tIdx_ne i (by rw [h]; exact hr)
    rw [if_pos hr, if_pos hr, h0, smul_zero, add_zero]
  · rw [if_neg hr, if_neg hr, smul_zero, zero_add]

set_option maxHeartbeats 1600000 in
/-- The verifier's first check (`eq1`), restated as `⟨a,b⟩·g + τₓ·h = ∑ᵣ xʳ·Tcoef'ᵣ` with the
special `n'`-coefficient `(δ−w_c)·g − ⟨w_V,V⟩` and the dense `{T_i}` scattered onto the full
degree range (`eq1_RHS_repackage`). -/
lemma arithVerify_eq1 {n q m c : ℕ} (s : Statement F G n q m c)
    (AI AO Scom : G) (yu zu xu : Fˣ) (T : Fin (3 * c + 5) → G)
    (τx μ : F) (a b : Fin n → F)
    (h : (relArith F G n).rel (arithOut s ((AI, AO, Scom), yu, zu, T, xu, PUnit.unit))
      (τx, μ, a, b) = true) :
    ip a b • s.g + τx • s.h
      = ∑ r : Fin (2 * nPrime c + 3), (↑xu : F) ^ (r : ℕ) • (if (r : ℕ) = nPrime c then
          ((ip (hadamard (vinv (powers (↑yu : F) n)) ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WR)))
                ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WL))
              - (↑zu : F) * ip (powers (↑zu : F) q) s.cc) • s.g
            - msm ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WV)) s.V)
          else tScatter T r) := by
  simp only [arithOut, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [eq1_RHS_repackage (↑xu : F)
      ((ip (hadamard (vinv (powers (↑yu : F) n)) ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WR)))
                ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WL))
              - (↑zu : F) * ip (powers (↑zu : F) q) s.cc) • s.g
            - msm ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WV)) s.V) T] at h
  exact h.1

/-- The honest sparse `f_L` coefficient family (degree index `p : Fin (n'+2)`), built from the
extracted wires `aL, aO, aC` and mask `sL`. (Named form of `tcoeff_expand`'s inline `f_L`.) -/
def honestFL {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aO sL : Fin n → F) (aC : Fin c → Fin n → F) (p : Fin (nPrime c + 2)) : Fin n → F :=
  (((if (p : ℕ) = c + 1 then
        fun i => aL i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i
      else 0) +
      ∑ k : Fin c, if (p : ℕ) = nPrime c - ((k : ℕ) + 1) then aC k else 0) +
    if (p : ℕ) = nPrime c then aO else 0) +
  if (p : ℕ) = nPrime c + 1 then sL else 0

/-- The honest sparse `f_R` coefficient family, built from `aR, aux` and mask `sR`. -/
def honestFR {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aR sR : Fin n → F) (aux : Fin c → Fin n → F) (ℓ : Fin (nPrime c + 2)) : Fin n → F :=
  ((((if (ℓ : ℕ) = 0 then
          fun i => ((↑zu : F) • powers (↑zu) q ᵥ* s.WO) i - powers (↑yu) n i else 0) +
        ∑ x : Fin c, if (ℓ : ℕ) = (x : ℕ) + 1 then (↑zu : F) • powers (↑zu) q ᵥ* s.WC x else 0) +
      if (ℓ : ℕ) = c + 1 then
        fun i => powers (↑yu) n i * aR i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WL) i else 0) +
    ∑ k : Fin c, if (ℓ : ℕ) = nPrime c - ((k : ℕ) + 1) then
      fun i => powers (↑yu) n i * aux k i else 0) +
  if (ℓ : ℕ) = nPrime c + 1 then fun i => powers (↑yu) n i * sR i else 0

set_option maxHeartbeats 1600000 in
omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Step 2 (constraint-free `t`-polynomial expansion).** The `n'`-coefficient of `⟨f_L, f_R⟩`,
for the honest sparse polynomials built from the extracted wires `aL, aR, aO, aC, aux, sL, sR`,
expands *without using any R1CS/Hadamard constraint* into `δ + ⟨linear R1CS terms⟩ +
∑ᵢ yⁱ(aL_i·aR_i − aO_i)`. (The soundness counterpart of `tcoeff_eq`: it stops *before* the
constraints are applied, keeping the Hadamard term explicit so Step 3 can recover the constraints
by deaggregation.) -/
lemma tcoeff_expand {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aR aO sL sR : Fin n → F) (aC aux : Fin c → Fin n → F) :
    (∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
        if (p : ℕ) + (ℓ : ℕ) = nPrime c then
          ip ((((if (p : ℕ) = c + 1 then
                    fun i => aL i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i
                  else 0) +
                  ∑ k : Fin c, if (p : ℕ) = nPrime c - ((k : ℕ) + 1) then aC k else 0) +
                if (p : ℕ) = nPrime c then aO else 0) +
              if (p : ℕ) = nPrime c + 1 then sL else 0)
            (((((if (ℓ : ℕ) = 0 then
                      fun i => ((↑zu : F) • powers (↑zu) q ᵥ* s.WO) i - powers (↑yu) n i else 0) +
                    ∑ x : Fin c, if (ℓ : ℕ) = (x : ℕ) + 1 then (↑zu : F) • powers (↑zu) q ᵥ* s.WC x else 0) +
                  if (ℓ : ℕ) = c + 1 then
                    fun i => powers (↑yu) n i * aR i + ((↑zu : F) • powers (↑zu) q ᵥ* s.WL) i else 0) +
                ∑ k : Fin c, if (ℓ : ℕ) = nPrime c - ((k : ℕ) + 1) then
                  fun i => powers (↑yu) n i * aux k i else 0) +
              if (ℓ : ℕ) = nPrime c + 1 then fun i => powers (↑yu) n i * sR i else 0)
        else 0)
      = ip (hadamard (vinv (powers (↑yu) n)) ((↑zu : F) • powers (↑zu) q ᵥ* s.WR))
            ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
          + ip aL ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
          + ip aR ((↑zu : F) • powers (↑zu) q ᵥ* s.WR)
          + ip aO ((↑zu : F) • powers (↑zu) q ᵥ* s.WO)
          + (∑ k, ip (aC k) ((↑zu : F) • powers (↑zu) q ᵥ* s.WC k))
          + ∑ i, powers (↑yu) n i * (aL i * aR i - aO i) := by
  simp only [ip_add_left, ip_sum_left, ip_ite_left, ite_zero_add, ite_zero_sum,
    ite_ite_zero, Finset.sum_add_distrib]
  rw [double_sum_collapse (c + 1) (nPrime c) (by simp only [nPrime]; omega)
        (by simp only [nPrime]; omega) (by omega),
    double_sum_collapse (nPrime c) (nPrime c) (by omega) (le_refl _) (by omega),
    double_sum_zero (nPrime c + 1) (nPrime c) (by omega),
    family_collapse (fun k => nPrime c - ((k : ℕ) + 1)) (nPrime c)
      (fun k => by dsimp only; omega) (fun k => by dsimp only; omega)
      (fun k => by dsimp only; omega)]
  have hidx1 : nPrime c - (c + 1) = c + 1 := by simp only [nPrime]; omega
  have hidx3 : nPrime c - nPrime c = 0 := by omega
  have hidx2 : ∀ k : Fin c, nPrime c - (nPrime c - ((k : ℕ) + 1)) = (k : ℕ) + 1 :=
    fun k => by have := k.isLt; simp only [nPrime]; omega
  simp only [hidx1, hidx3, hidx2, ip_add_right, ip_sum_right, ip_ite_right]
  simp only [if_true]
  rw [if_neg (show ¬(c + 1 = 0) by omega),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬(c + 1 = (x : ℕ) + 1) by
      have := x.isLt; omega)),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬(c + 1 = nPrime c - ((x : ℕ) + 1)) by
      have := x.isLt; simp only [nPrime]; omega)),
    if_neg (show ¬(c + 1 = nPrime c + 1) by simp only [nPrime]; omega),
    if_neg (show ¬((0 : ℕ) = c + 1) by omega),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬((0 : ℕ) = (x : ℕ) + 1) by omega)),
    Finset.sum_eq_zero (fun (x : Fin c) _ => if_neg (show ¬((0 : ℕ) = nPrime c - ((x : ℕ) + 1)) by
      have := x.isLt; simp only [nPrime]; omega)),
    if_neg (show ¬((0 : ℕ) = nPrime c + 1) by simp only [nPrime]; omega)]
  have e0 : ∀ x : Fin c, ((x : ℕ) + 1 = 0) = False := fun x => eq_false (by omega)
  have eM : ∀ x : Fin c, ((x : ℕ) + 1 = c + 1) = False := fun x => eq_false (by have := x.isLt; omega)
  have eN : ∀ x : Fin c, ((x : ℕ) + 1 = nPrime c + 1) = False :=
    fun x => eq_false (by simp only [nPrime]; omega)
  have eH : ∀ x x_1 : Fin c, ((x : ℕ) + 1 = nPrime c - ((x_1 : ℕ) + 1)) = False :=
    fun x x_1 => eq_false (by have := x.isLt; have := x_1.isLt; simp only [nPrime]; omega)
  have eD : ∀ x x_1 : Fin c, ((x : ℕ) + 1 = (x_1 : ℕ) + 1) = (x_1 = x) :=
    fun x x_1 => by rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  simp only [e0, eM, eN, eH, eD, if_false, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, add_zero, zero_add]
  have hvyinv := powers_mul_vinv yu n
  have hI_nc : ip (fun i => aL i + (↑zu • powers (↑zu) q ᵥ* s.WR) i * vinv (powers (↑yu) n) i)
          (fun i => powers (↑yu) n i * aR i + (↑zu • powers (↑zu) q ᵥ* s.WL) i)
        + ip aO (fun i => (↑zu • powers (↑zu) q ᵥ* s.WO) i - powers (↑yu) n i)
      = ip (hadamard (vinv (powers (↑yu) n)) (↑zu • powers (↑zu) q ᵥ* s.WR))
            (↑zu • powers (↑zu) q ᵥ* s.WL)
        + ip aL ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
        + ip aR ((↑zu : F) • powers (↑zu) q ᵥ* s.WR)
        + ip aO ((↑zu : F) • powers (↑zu) q ᵥ* s.WO)
        + ∑ i, powers (↑yu) n i * (aL i * aR i - aO i) := by
    simp only [ip, hadamard]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination ((↑zu • powers (↑zu) q ᵥ* s.WR) i * aR i) * (hvyinv i)
  linear_combination hI_nc

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- `tcoeff_expand` in named `honestFL`/`honestFR` form (for composing with `tcoeff_recover`). -/
lemma tcoeff_expand' {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aR aO sL sR : Fin n → F) (aC aux : Fin c → Fin n → F) :
    (∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
        if (p : ℕ) + (ℓ : ℕ) = nPrime c then
          ip (honestFL s yu zu aL aO sL aC p) (honestFR s yu zu aR sR aux ℓ) else 0)
      = ip (hadamard (vinv (powers (↑yu) n)) ((↑zu : F) • powers (↑zu) q ᵥ* s.WR))
            ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
          + ip aL ((↑zu : F) • powers (↑zu) q ᵥ* s.WL)
          + ip aR ((↑zu : F) • powers (↑zu) q ᵥ* s.WR)
          + ip aO ((↑zu : F) • powers (↑zu) q ᵥ* s.WO)
          + (∑ k, ip (aC k) ((↑zu : F) • powers (↑zu) q ᵥ* s.WC k))
          + ∑ i, powers (↑yu) n i * (aL i * aR i - aO i) := by
  simp only [honestFL, honestFR]
  exact tcoeff_expand s yu zu aL aR aO sL sR aC aux

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Step 3 (`z`-deaggregation).** A relation `had + ∑_q z^{ℓ+1}·rows_q = 0` holding at `q+1`
distinct `z` forces the constant part `had` and every row `rows_q` to vanish (a degree-`q`
Vandermonde system in `z`). Applied to `(★)`, this splits off the `R1CS` rows. -/
lemma star_deaggregate_z {q : ℕ} (z : Fin (q + 1) → F) (hz : Function.Injective z)
    (had : F) (rows : Fin q → F)
    (h : ∀ j, had + ∑ ℓ : Fin q, (z j) ^ ((ℓ : ℕ) + 1) * rows ℓ = 0) :
    had = 0 ∧ ∀ ℓ, rows ℓ = 0 := by
  have hd : (Fin.cons had rows : Fin (q + 1) → F) = 0 := by
    apply vandermonde_kernel z hz
    intro j
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_eq_mul, Fin.val_succ, Fin.val_zero, pow_zero,
      one_mul]
    exact h j
  refine ⟨by simpa using congrFun hd 0, fun ℓ => by simpa using congrFun hd ℓ.succ⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **Step 3 (`y`-deaggregation, Hadamard).** A relation `∑_i y^i·c_i = 0` holding at `n` distinct
`y` forces every `c_i` to vanish (a degree-`(n-1)` Vandermonde in `y`). Applied once the `R1CS`
rows are gone, this splits off the Hadamard clause `aL∘aR − aO = 0`. -/
lemma hadamard_deaggregate {n : ℕ} (y : Fin n → F) (hy : Function.Injective y)
    (c : Fin n → F) (h : ∀ a, ∑ i : Fin n, (y a) ^ (i : ℕ) * c i = 0) (i : Fin n) : c i = 0 :=
  congrFun (vandermonde_kernel y hy c fun a => by simpa [smul_eq_mul] using h a) i

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier coefficient family vanishes above degree `n'+1`. -/
lemma Pcoef_high_zero {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G)
    (p : Fin (2 * nPrime c + 3)) (hp : nPrime c + 2 ≤ (p : ℕ)) :
    Pcoef s y z AI AO Scom p = 0 := by
  have hk : ∀ k : Fin c, ((p : ℕ) = (k : ℕ) + 1) = False := fun k =>
    eq_false (by have := k.isLt; simp only [nPrime] at hp; omega)
  have hac : ∀ k : Fin c, ((p : ℕ) = nPrime c - ((k : ℕ) + 1)) = False := fun k =>
    eq_false (by simp only [nPrime] at hp ⊢; omega)
  simp only [Pcoef, show ((p : ℕ) = 0) = False from eq_false (by omega),
    show ((p : ℕ) = c + 1) = False from eq_false (by simp only [nPrime] at hp; omega),
    show ((p : ℕ) = nPrime c) = False from eq_false (by omega),
    show ((p : ℕ) = nPrime c + 1) = False from eq_false (by omega),
    hk, hac, if_false, Finset.sum_const_zero, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier coefficient at degree `n'−(k+1)` is exactly the vector commitment `A_C k`. -/
lemma Pcoef_AC {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G) (k : Fin c) :
    Pcoef s y z AI AO Scom
        ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩ = s.AC k := by
  have hk := k.isLt
  have hwc : ∀ x : Fin c, (nPrime c - ((k : ℕ) + 1) = (x : ℕ) + 1) = False := fun x =>
    eq_false (by have := x.isLt; simp only [nPrime]; omega)
  have hac : ∀ x : Fin c, (nPrime c - ((k : ℕ) + 1) = nPrime c - ((x : ℕ) + 1)) = (x = k) := fun x =>
    by rw [eq_iff_iff]; constructor
       · intro h; have := x.isLt; exact Fin.ext (by simp only [nPrime] at h; omega)
       · intro h; rw [h]
  simp only [Pcoef,
    show (nPrime c - ((k : ℕ) + 1) = 0) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c - ((k : ℕ) + 1) = c + 1) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c - ((k : ℕ) + 1) = nPrime c) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c - ((k : ℕ) + 1) = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    hwc, hac, if_false, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier coefficient at degree `0` is the public `WtO` opening (pure `h'`-part). -/
lemma Pcoef_WtO {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G) :
    Pcoef s y z AI AO Scom ⟨0, by simp only [nPrime]; omega⟩
      = msm (z • (powers z q ᵥ* s.WO) - powers y n) (vinv (powers y n) ⊙ s.hs) := by
  have hwc : ∀ k : Fin c, ((0 : ℕ) = (k : ℕ) + 1) = False := fun k => eq_false (by omega)
  have hac : ∀ k : Fin c, ((0 : ℕ) = nPrime c - ((k : ℕ) + 1)) = False :=
    fun k => eq_false (by have := k.isLt; simp only [nPrime]; omega)
  simp only [Pcoef,
    show ((0 : ℕ) = c + 1) = False from eq_false (by omega),
    show ((0 : ℕ) = nPrime c) = False from eq_false (by simp only [nPrime]; omega),
    show ((0 : ℕ) = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    hwc, hac, if_true, if_false, Finset.sum_const_zero, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier coefficient at degree `k+1` is the public `Wtk` opening (pure `h'`-part). -/
lemma Pcoef_Wtk {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G) (k : Fin c) :
    Pcoef s y z AI AO Scom ⟨(k : ℕ) + 1, by have := k.isLt; simp only [nPrime]; omega⟩
      = msm (z • (powers z q ᵥ* s.WC k)) (vinv (powers y n) ⊙ s.hs) := by
  have hk := k.isLt
  have hwc : ∀ x : Fin c, ((k : ℕ) + 1 = (x : ℕ) + 1) = (x = k) := fun x =>
    by rw [eq_iff_iff]; exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  have hac : ∀ x : Fin c, ((k : ℕ) + 1 = nPrime c - ((x : ℕ) + 1)) = False :=
    fun x => eq_false (by have := x.isLt; simp only [nPrime]; omega)
  simp only [Pcoef,
    show ((k : ℕ) + 1 = 0) = False from eq_false (by omega),
    show ((k : ℕ) + 1 = c + 1) = False from eq_false (by omega),
    show ((k : ℕ) + 1 = nPrime c) = False from eq_false (by simp only [nPrime]; omega),
    show ((k : ℕ) + 1 = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    hwc, hac, if_true, if_false, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    add_zero, zero_add]

omit [DecidableEq F] [DecidableEq G] in
/-- **The coupling.** The `n'`-coefficient `∑ₗ V⁻¹[n',l]·⟨aₗ,bₗ⟩` of the inner products of the
prover's sent vectors (with `aₗ = ∑ₚ xₗᵖ·fLₚ`, `bₗ = ∑ᵩ xₗᵠ·fRᵩ` of degree `n'+1`) equals the
convolution coefficient `∑_{p+ℓ=n'} ⟨fLₚ, fRᵩ⟩` — the LHS of `tcoeff_expand`. -/
lemma tcoeff_recover {n np : ℕ} (x : Fin (2 * np + 3) → F) (hx : Function.Injective x)
    (fL fR : Fin (np + 2) → (Fin n → F)) (hnp : np < 2 * np + 3) :
    (∑ l : Fin (2 * np + 3), (Matrix.vandermonde x)⁻¹ ⟨np, hnp⟩ l
        • ip (fun i => ∑ p : Fin (np + 2), x l ^ (p : ℕ) * fL p i)
             (fun i => ∑ ℓ : Fin (np + 2), x l ^ (ℓ : ℕ) * fR ℓ i))
      = ∑ p : Fin (np + 2), ∑ ℓ : Fin (np + 2),
          if (p : ℕ) + (ℓ : ℕ) = np then ip (fL p) (fR ℓ) else 0 := by
  have hu : IsUnit (Matrix.vandermonde x).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hx)
  have key := matrix_one_smul_recover (Matrix.vandermonde x)⁻¹ (Matrix.vandermonde x)
    (Matrix.nonsing_inv_mul _ hu)
    (fun d : Fin (2 * np + 3) => ∑ p : Fin (np + 2), ∑ ℓ : Fin (np + 2),
      if (p : ℕ) + (ℓ : ℕ) = (d : ℕ) then ip (fL p) (fR ℓ) else 0) ⟨np, hnp⟩
  rw [← key]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ip_xpoly_conv (M := 2 * np + 3) (x l) fL fR
      (fun p ℓ => by have := p.isLt; have := ℓ.isLt; omega)]
  simp only [Matrix.vandermonde_apply, smul_eq_mul]

omit [DecidableEq F] [DecidableEq G] in
/-- **Step 4 (`z`-level `V`-recovery, clause 4).** With `W_V` left-invertible (`M`) and the
aggregate `msm wV V = A_j·g + C_j·h` holding at `q+1` distinct `z`, invert the Vandermonde in `z`
to read off each `∑_k (W_V)_{ℓ,k} V_k`, then apply `M` to recover each scalar-commitment opening
`V_k = v_k·g + γ_k·h`. -/
lemma V_recover {n q m c : ℕ} (s : Statement F G n q m c) (z : Fin (q + 1) → F)
    (hz : Function.Injective z) (Mmat : Matrix (Fin m) (Fin q) F) (hM : Mmat * s.WV = 1)
    (A C : Fin (q + 1) → F)
    (hI : ∀ j, msm (z j • (powers (z j) q ᵥ* s.WV)) s.V = A j • s.g + C j • s.h) :
    ∀ k, s.V k = (∑ ℓ, Mmat k ℓ * (∑ j, (Matrix.vandermonde z)⁻¹ ℓ.succ j * A j)) • s.g
      + (∑ ℓ, Mmat k ℓ * (∑ j, (Matrix.vandermonde z)⁻¹ ℓ.succ j * C j)) • s.h := by
  set U : Fin q → G := fun ℓ => ∑ k, s.WV ℓ k • s.V k with hUdef
  -- `msm wV V` is the polynomial `∑_q z^{ℓ+1}·U_q`
  have hexp : ∀ j, msm (z j • (powers (z j) q ᵥ* s.WV)) s.V
      = ∑ ℓ : Fin q, (z j) ^ ((ℓ : ℕ) + 1) • U ℓ := by
    intro j
    have hk : ∀ k, (z j • (powers (z j) q ᵥ* s.WV)) k
        = ∑ ℓ : Fin q, (z j) ^ ((ℓ : ℕ) + 1) * s.WV ℓ k := by
      intro k
      simp only [Pi.smul_apply, Matrix.vecMul, dotProduct, powers, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    simp only [msm, hk, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [hUdef, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_smul]
  -- samples = the polynomial values, with `Fin.cons 0 U` the coefficients
  have hsmp : ∀ j, ∑ i : Fin (q + 1), (z j) ^ (i : ℕ) • (Fin.cons (0 : G) U) i = A j • s.g + C j • s.h := by
    intro j
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, smul_zero, zero_add,
      Fin.val_succ]
    rw [← hexp j, hI j]
  -- recover each `U_q` as a `(g, h)`-combination
  have hUq : ∀ ℓ : Fin q, U ℓ
      = (∑ j, (Matrix.vandermonde z)⁻¹ ℓ.succ j * A j) • s.g
        + (∑ j, (Matrix.vandermonde z)⁻¹ ℓ.succ j * C j) • s.h := by
    intro ℓ
    have hc := vandermonde_coeff z hz (Fin.cons (0 : G) U) _ hsmp ℓ.succ
    rw [Fin.cons_succ] at hc
    rw [hc]
    simp only [smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul]
  -- apply the left inverse
  intro k
  have hrec := leftInverse_recover s.WV Mmat hM s.V U (fun ℓ => rfl) k
  rw [hrec]
  simp only [hUq, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]
