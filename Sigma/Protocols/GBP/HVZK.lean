/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBP.Reductions
import Sigma.Protocols.GBP.ArithmetizationHVZK

/-!
# Perfect HVZK of the whole logarithmic Generalized Bulletproofs protocol

The arithmetization is the only step carrying a zero-knowledge obligation; the reveal-fold
and the inner-product tower contribute just their honest provers (reused verbatim from the
completeness proof `Sigma.Protocols.GBP.gbpRed_complete`). So perfect HVZK of the whole tower
is `Sigma.Reduction.compose_hvzk_perfect` applied once at the outer seam, with
`Sigma.Protocols.GBP.arithRed_hvzk`.
-/

namespace Sigma.Protocols.GBP

open OracleComp OracleSpec
open Sigma.Protocols.IPA (ipaRed soundTower towerHonest)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
  [Fintype F] [Fintype G] [SampleableType F] [SampleableType Fˣ] [SampleableType G]

local instance (k : ℕ) : Inhabited ((ipaRed F G k).In.Stmt) :=
  ⟨Rel.castStmt (soundTower F G k).hIn.symm default⟩

local instance (k : ℕ) : Inhabited (innerRed (F := F) (G := G) k).In.Stmt :=
  ⟨⟨0, 0, 0, 0, fun _ => 0, fun _ => 0⟩⟩

/-- **Perfect HVZK of the whole logarithmic Generalized Bulletproofs protocol**, assuming each
arithmetization statement's blinding base `h` is perfectly hiding. The honest prover is the
one from `gbpRed_complete`; the simulator runs `arithSim` and then the inner honest prover. -/
theorem gbpRed_hvzk (k q m c : ℕ)
    (hHide : ∀ x : (arithRed (F := F) (G := G) (2 ^ (k + 1)) q m c).In.Stmt,
      Function.Bijective (· • x.h : F → G)) :
    (gbpRed (F := F) (G := G) k q m c).PerfectHVZK
      (Reduction.composeHonest (arithRed (2 ^ (k + 1)) q m c) (innerRed k) rfl
        arithRedHonest
        (Reduction.composeHonest (revealFold k) (ipaRed F G k)
          (soundTower F G k).hIn (revealFoldHonest k) (towerHonest F G k)))
      (Reduction.composeSim (arithRed (2 ^ (k + 1)) q m c) (innerRed k) rfl
        arithSim
        (Reduction.composeHonest (revealFold k) (ipaRed F G k)
          (soundTower F G k).hIn (revealFoldHonest k) (towerHonest F G k))) :=
  Reduction.compose_hvzk_perfect (arithRed (2 ^ (k + 1)) q m c) (innerRed k) rfl
    arithRedHonest _ arithSim (arithRed_hvzk hHide)

end Sigma.Protocols.GBP
