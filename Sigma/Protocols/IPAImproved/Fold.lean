/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.IPA.Fold

namespace Sigma.Protocols.IPAImproved

open Sigma.Protocols.IPA (splitL splitR msm_split ip_split)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## The polynomial fold -/

/-- Fold the `𝐠` generators: `gᵢ' = gᵢᴸ + ξ·gᵢᴿ`. -/
def foldG {m : ℕ} (ξ : F) (gL gR : Fin m → G) : Fin m → G := fun i => gL i + ξ • gR i

/-- Fold the `𝐡` generators: `hᵢ' = ξ·hᵢᴸ + hᵢᴿ`. -/
def foldH {m : ℕ} (ξ : F) (hL hR : Fin m → G) : Fin m → G := fun i => ξ • hL i + hR i

/-- Fold the `a` witness: `aᵢ' = ξ·aᵢᴸ + aᵢᴿ`. -/
def foldA {m : ℕ} (ξ : F) (aL aR : Fin m → F) : Fin m → F := fun i => ξ * aL i + aR i

/-- Fold the `b` witness: `bᵢ' = bᵢᴸ + ξ·bᵢᴿ`. -/
def foldB {m : ℕ} (ξ : F) (bL bR : Fin m → F) : Fin m → F := fun i => bL i + ξ * bR i

/-! ## One folding round expansions -/

/-- Expansion of the folded `⟨a', 𝐠'⟩`. -/
lemma expand_aG {t : ℕ} (ξ : F)
    (aL aR : Fin (2 ^ t) → F) (gL gR : Fin (2 ^ t) → G) :
    msm (foldA ξ aL aR) (foldG ξ gL gR)
      = ξ • msm aL gL + ξ • msm aR gR + ξ ^ 2 • msm aL gR + msm aR gL := by
  simp only [msm, foldA, foldG]
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  match_scalars <;> ring

/-- Expansion of the folded `⟨b', 𝐡'⟩`. -/
lemma expand_bH {t : ℕ} (ξ : F)
    (bL bR : Fin (2 ^ t) → F) (hL hR : Fin (2 ^ t) → G) :
    msm (foldB ξ bL bR) (foldH ξ hL hR)
      = ξ • msm bL hL + ξ • msm bR hR + ξ ^ 2 • msm bR hL + msm bL hR := by
  simp only [msm, foldB, foldH]
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  match_scalars <;> ring

/-- Expansion of the folded `⟨a', b'⟩`. -/
lemma expand_ab {t : ℕ} (ξ : F) (aL aR bL bR : Fin (2 ^ t) → F) :
    ip (foldA ξ aL aR) (foldB ξ bL bR)
      = ξ * ip aL bL + ξ * ip aR bR + ξ ^ 2 * ip aL bR + ip aR bL := by
  simp only [ip, foldA, foldB]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## The round invariant -/

/-- The folding round invariant: if `P` opens the inner-product relation for `(a, b)` on
generators `(𝐠, 𝐡)`, then the updated commitment `ξ²·L + ξ·P + R` (with the prover's
cross-terms `L, R`) opens the relation for the folded `(a', b')` on the folded generators. -/
lemma fold_relation {t : ℕ} (ξ : F)
    (gs hs : Fin (2 ^ (t + 1)) → G) (u : G) (a b : Fin (2 ^ (t + 1)) → F) (P : G)
    (hP : P = msm a gs + msm b hs + ip a b • u) :
    ξ ^ 2 • (msm (splitL a) (splitR gs) + msm (splitR b) (splitL hs)
                    + (ip (splitL a) (splitR b)) • u)
          + ξ • P
          + (msm (splitR a) (splitL gs) + msm (splitL b) (splitR hs)
                    + (ip (splitR a) (splitL b)) • u)
      = msm (foldA ξ (splitL a) (splitR a)) (foldG ξ (splitL gs) (splitR gs))
        + msm (foldB ξ (splitL b) (splitR b)) (foldH ξ (splitL hs) (splitR hs))
        + ip (foldA ξ (splitL a) (splitR a)) (foldB ξ (splitL b) (splitR b)) • u := by
  rw [hP, msm_split a gs, msm_split b hs, ip_split a b,
    expand_aG ξ (splitL a) (splitR a) (splitL gs) (splitR gs),
    expand_bH ξ (splitL b) (splitR b) (splitL hs) (splitR hs),
    expand_ab ξ (splitL a) (splitR a) (splitL b) (splitR b)]
  module

end Sigma.Protocols.IPAImproved
