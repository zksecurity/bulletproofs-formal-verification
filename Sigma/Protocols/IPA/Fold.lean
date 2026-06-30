/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Utils.Vec
import Sigma.Protocols.IPA.Relation

namespace Sigma.Protocols.IPA

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## Halving and folding -/

/-- The lower half of a length-`2^(t+1)` vector, as a length-`2^t` vector. -/
def splitL {α : Type*} {t : ℕ} (v : Fin (2 ^ (t + 1)) → α) : Fin (2 ^ t) → α :=
  fun i => v (Fin.cast (by rw [pow_succ]; omega) (i.castAdd (2 ^ t)))

/-- The upper half of a length-`2^(t+1)` vector, as a length-`2^t` vector. -/
def splitR {α : Type*} {t : ℕ} (v : Fin (2 ^ (t + 1)) → α) : Fin (2 ^ t) → α :=
  fun i => v (Fin.cast (by rw [pow_succ]; omega) (Fin.natAdd (2 ^ t) i))

/-- Fold the `𝐠` generators: `gᵢ' = ξ⁻¹·gᵢᴸ + ξ·gᵢᴿ`. -/
def foldG {m : ℕ} (ξ : F) (gL gR : Fin m → G) : Fin m → G := fun i => ξ⁻¹ • gL i + ξ • gR i

/-- Fold the `𝐡` generators: `hᵢ' = ξ·hᵢᴸ + ξ⁻¹·hᵢᴿ`. -/
def foldH {m : ℕ} (ξ : F) (hL hR : Fin m → G) : Fin m → G := fun i => ξ • hL i + ξ⁻¹ • hR i

/-- Fold the `a` witness: `aᵢ' = ξ·aᵢᴸ + ξ⁻¹·aᵢᴿ`. -/
def foldA {m : ℕ} (ξ : F) (aL aR : Fin m → F) : Fin m → F := fun i => ξ * aL i + ξ⁻¹ * aR i

/-- Fold the `b` witness: `bᵢ' = ξ⁻¹·bᵢᴸ + ξ·bᵢᴿ`. -/
def foldB {m : ℕ} (ξ : F) (bL bR : Fin m → F) : Fin m → F := fun i => ξ⁻¹ * bL i + ξ * bR i

/-! ## Splitting sums, `msm`, and `ip` into lower/upper halves -/

/-- Split a sum over `Fin (2^(t+1))` into the lower and upper halves used by `splitL`/`splitR`. -/
lemma sum_split {α : Type*} [AddCommMonoid α] {t : ℕ}
    (hpow : 2 ^ t + 2 ^ t = 2 ^ (t + 1)) (f : Fin (2 ^ (t + 1)) → α) :
    ∑ j, f j = (∑ i, f (Fin.cast hpow (Fin.castAdd (2 ^ t) i)))
             + (∑ i, f (Fin.cast hpow (Fin.natAdd (2 ^ t) i))) := by
  rw [← Equiv.sum_comp (finCongr hpow) f, Fin.sum_univ_add]
  simp only [finCongr_apply]

/-- `msm` splits as the sum over the lower and upper halves. -/
lemma msm_split {t : ℕ} (a : Fin (2 ^ (t + 1)) → F) (gs : Fin (2 ^ (t + 1)) → G) :
    msm a gs = msm (splitL a) (splitL gs) + msm (splitR a) (splitR gs) := by
  simp only [msm]
  rw [sum_split (by rw [pow_succ]; omega) (fun j => a j • gs j)]
  rfl

/-- `ip` splits as the sum over the lower and upper halves. -/
lemma ip_split {t : ℕ} (a b : Fin (2 ^ (t + 1)) → F) :
    ip a b = ip (splitL a) (splitL b) + ip (splitR a) (splitR b) := by
  simp only [ip]
  rw [sum_split (by rw [pow_succ]; omega) (fun j => a j * b j)]
  rfl

/-! ## One folding round expansions -/

-- `match_scalars` can leave a per-atom goal that `field_simp` discharges outright, so the
-- trailing `<;> ring` legitimately runs on possibly-zero goals; silence the false positive.
set_option linter.unnecessarySeqFocus false in
/-- Expansion of the folded `⟨a', 𝐠'⟩`. -/
lemma expand_aG {t : ℕ} (ξ : F) (hξ : ξ ≠ 0)
    (aL aR : Fin (2 ^ t) → F) (gL gR : Fin (2 ^ t) → G) :
    msm (foldA ξ aL aR) (foldG ξ gL gR)
      = msm aL gL + msm aR gR + ξ ^ 2 • msm aL gR + (ξ⁻¹) ^ 2 • msm aR gL := by
  simp only [msm, foldA, foldG]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  match_scalars <;> field_simp <;> ring

set_option linter.unnecessarySeqFocus false in
/-- Expansion of the folded `⟨b', 𝐡'⟩`. -/
lemma expand_bH {t : ℕ} (ξ : F) (hξ : ξ ≠ 0)
    (bL bR : Fin (2 ^ t) → F) (hL hR : Fin (2 ^ t) → G) :
    msm (foldB ξ bL bR) (foldH ξ hL hR)
      = msm bL hL + msm bR hR + (ξ⁻¹) ^ 2 • msm bL hR + ξ ^ 2 • msm bR hL := by
  simp only [msm, foldB, foldH]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  match_scalars <;> field_simp <;> ring

/-- Expansion of the folded `⟨a', b'⟩`. -/
lemma expand_ab {t : ℕ} (ξ : F) (hξ : ξ ≠ 0) (aL aR bL bR : Fin (2 ^ t) → F) :
    ip (foldA ξ aL aR) (foldB ξ bL bR)
      = ip aL bL + ip aR bR + ξ ^ 2 * ip aL bR + (ξ⁻¹) ^ 2 * ip aR bL := by
  simp only [ip, foldA, foldB]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  ring

/-! ## The round invariant -/

/-- The folding round invariant: if `P` opens the inner-product relation for `(a, b)` on
generators `(𝐠, 𝐡)`, then the updated commitment `P + ξ²·L + ξ⁻²·R` (with the prover's
cross-terms `L, R`) opens the relation for the folded `(a', b')` on the folded generators. -/
lemma fold_relation {t : ℕ} (ξ : F) (hξ : ξ ≠ 0)
    (gs hs : Fin (2 ^ (t + 1)) → G) (u : G) (a b : Fin (2 ^ (t + 1)) → F) (P : G)
    (hP : P = msm a gs + msm b hs + ip a b • u) :
    P + (ξ ^ 2 • (msm (splitL a) (splitR gs) + msm (splitR b) (splitL hs)
                    + (ip (splitL a) (splitR b)) • u)
          + (ξ⁻¹) ^ 2 • (msm (splitR a) (splitL gs) + msm (splitL b) (splitR hs)
                    + (ip (splitR a) (splitL b)) • u))
      = msm (foldA ξ (splitL a) (splitR a)) (foldG ξ (splitL gs) (splitR gs))
        + msm (foldB ξ (splitL b) (splitR b)) (foldH ξ (splitL hs) (splitR hs))
        + ip (foldA ξ (splitL a) (splitR a)) (foldB ξ (splitL b) (splitR b)) • u := by
  rw [hP, msm_split a gs, msm_split b hs, ip_split a b,
    expand_aG ξ hξ (splitL a) (splitR a) (splitL gs) (splitR gs),
    expand_bH ξ hξ (splitL b) (splitR b) (splitL hs) (splitR hs),
    expand_ab ξ hξ (splitL a) (splitR a) (splitL b) (splitR b)]
  module

/-! ## The singleton base case -/

/-- A multi-scalar multiplication over the singleton index `Fin (2^0)`. -/
lemma msm_pow_zero (c : Fin (2 ^ 0) → F) (g : Fin (2 ^ 0) → G) : msm c g = c 0 • g 0 := by
  show (∑ i : Fin 1, c i • g i) = c 0 • g 0
  rw [Fin.sum_univ_one]

/-- An inner product over the singleton index `Fin (2^0)`. -/
lemma ip_pow_zero (a b : Fin (2 ^ 0) → F) : ip a b = a 0 * b 0 := by
  show (∑ i : Fin 1, a i * b i) = a 0 * b 0
  rw [Fin.sum_univ_one]

end Sigma.Protocols.IPA
