/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.GBPImproved.Reductions
import Sigma.Protocols.GBPImproved.ArithmetizationHVZK

/-!
# Perfect HVZK of the whole improved logarithmic Generalized Bulletproofs protocol

The arithmetization is the only step carrying a zero-knowledge obligation; the `t̂`-reveal and
the polynomial-fold inner-product tower contribute just their honest provers (reused verbatim
from `Sigma.Protocols.GBPImproved.gbpRed'_complete`). So perfect HVZK of the whole tower is
`Sigma.Reduction.compose_hvzk_perfect` applied once at the outer seam, with
`Sigma.Protocols.GBPImproved.arithRed'_hvzk`.
-/

namespace Sigma.Protocols.GBPImproved

open OracleComp OracleSpec
open Sigma.Protocols.IPAImproved (ipaRed soundTower towerHonest)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
  [Fintype F] [Fintype G] [SampleableType F] [SampleableType Fˣ] [SampleableType G]

local instance (k : ℕ) : Inhabited ((ipaRed F G k).In.Stmt) :=
  ⟨Rel.castStmt (soundTower F G k).hIn.symm default⟩

local instance (k : ℕ) : Inhabited (innerRed' (F := F) (G := G) k).In.Stmt :=
  ⟨⟨0, 0, 0, 0, fun _ => 0, fun _ => 0⟩⟩

/-- **Perfect HVZK of the whole improved logarithmic Generalized Bulletproofs protocol**,
assuming each arithmetization statement's blinding base `h` is perfectly hiding. The honest
prover is the one from `gbpRed'_complete`; the simulator runs `arithSim'` and then the inner
honest prover. -/
theorem gbpRed'_hvzk (k q m c : ℕ)
    (hHide : ∀ x : (arithRed' (F := F) (G := G) (2 ^ (k + 1)) q m c).In.Stmt,
      Function.Bijective (· • x.h : F → G)) :
    (gbpRed' (F := F) (G := G) k q m c).PerfectHVZK
      (Reduction.composeHonest (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl
        arithHonest'
        (Reduction.composeHonest (revealT k) (ipaRed F G k)
          (soundTower F G k).hIn (revealTHonest k) (towerHonest F G k)))
      (Reduction.composeSim (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl
        arithSim'
        (Reduction.composeHonest (revealT k) (ipaRed F G k)
          (soundTower F G k).hIn (revealTHonest k) (towerHonest F G k))) :=
  Reduction.compose_hvzk_perfect (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl
    arithHonest' _ arithSim' (arithRed'_hvzk hHide)

end Sigma.Protocols.GBPImproved
