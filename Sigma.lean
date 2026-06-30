/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
-- Framework: definitions
import Sigma.Definitions.Reduction
import Sigma.Definitions.ReductionTree
-- Framework: constructions
import Sigma.Constructions.ReductionCompose
-- Framework: theorems
import Sigma.Theorems.ReductionCompose
-- Utilities
import Sigma.Utils.Vec
import Sigma.Utils.Algebra
import Sigma.Utils.Vandermonde
import Sigma.Utils.LeftInverse
import Sigma.Utils.Binding
-- Examples
import Sigma.Examples.NestedSchnorr
-- Protocol: inner-product argument
import Sigma.Protocols.IPA.Relation
import Sigma.Protocols.IPA.Fold
import Sigma.Protocols.IPA.Extract
import Sigma.Protocols.IPA.NodeExtract
import Sigma.Protocols.IPA.ValueFold
import Sigma.Protocols.IPA.Reductions
-- Protocol: improved inner-product argument (polynomial fold)
import Sigma.Protocols.IPAImproved.Fold
import Sigma.Protocols.IPAImproved.Extract
import Sigma.Protocols.IPAImproved.NodeExtract
import Sigma.Protocols.IPAImproved.Reductions
-- Protocol: Generalized Bulletproofs
import Sigma.Protocols.GBP.Relation
import Sigma.Protocols.GBP.Arithmetization
import Sigma.Protocols.GBP.ArithmetizationComplete
import Sigma.Protocols.GBP.ArithmetizationSound
import Sigma.Protocols.GBP.Reductions
import Sigma.Protocols.GBP.ArithmetizationHVZK
import Sigma.Protocols.GBP.HVZK
-- Protocol: improved Generalized Bulletproofs (R_GBP')
import Sigma.Protocols.GBPImproved.Relation
import Sigma.Protocols.GBPImproved.Arithmetization
import Sigma.Protocols.GBPImproved.ArithmetizationPreR
import Sigma.Protocols.GBPImproved.ArithmetizationComplete
import Sigma.Protocols.GBPImproved.ArithmetizationSound
import Sigma.Protocols.GBPImproved.Reductions
import Sigma.Protocols.GBPImproved.ArithmetizationHVZK
import Sigma.Protocols.GBPImproved.HVZK

/-!
# Sigma

Reductions of knowledge for public-coin interactive arguments, built on the `VCV-io`
verified-cryptography library, together with protocol instances built on top: the
Bulletproofs inner-product argument (and its improved polynomial-fold variant) and the
Generalized Bulletproofs protocol (and its improved variant `R_GBP'`).

## The framework (`Sigma.Reduction`) — one interface for every protocol

Every protocol is a `Sigma.Reduction` between two relations (`Sigma.Rel`, a
statement/witness/predicate triple) — see [docs/reductions.md](docs/reductions.md). The
conversation is a free list of `Sigma.Move`s (no distinguished first message or trailing
challenge, no dummy rounds between adjacent challenges), there is no separate verifier —
one map `reduce : In.Stmt → Conversation → Option Out.Stmt` rejects or derives the output
statement — and the final message (a witness for `Out`) is **never sent**. Composition
(`Sigma.Reduction.compose`, [docs/composition.md](docs/composition.md)) is concatenation
plus statement plumbing; closing a tower is composition with the trivial proof of knowledge
`Sigma.Rel.send`; classical completeness and `(k₁,…,kₙ)`-special soundness are the
`Out = Rel.trivial` instances of the reduction-level predicates.

* `Sigma.Definitions.Reduction` — `Rel`, `Move`, `Conversation`, `rounds` (direction
  transitions), `Reduction`, `Closed`, `Accepting`, `Complete`, `HVZK`.
* `Sigma.Definitions.ReductionTree` — arity-annotated moves, decorated conversation trees
  (`TreeK`), and knowledge soundness (`Sigma.Reduction.Sound`, witness-or-break).
* `Sigma.Constructions.ReductionCompose` — `Reduction.compose`, `Rel.send`,
  `Reduction.close`, the stitched honest prover/simulator, and the composite extractor.
* `Sigma.Theorems.ReductionCompose` — completeness, knowledge soundness (arities
  concatenate), and HVZK all compose, with no per-instance bridge obligations; the trivial
  PoK is complete and perfectly sound.
* `Sigma.Examples.NestedSchnorr` — a worked 2-round `(2,2)`-special-sound example.

## Utilities (`Sigma.Utils`)
* `Sigma.Utils.Vec` — vector helpers (`ip`, `msm`, `hadamard`, `powers`).
* `Sigma.Utils.Algebra` — generic `ip`/`msm`/sum linearity lemmas shared by the completeness proofs.
* `Sigma.Utils.Vandermonde` — module-valued Vandermonde / left-inverse recovery, and the
  efficient Lagrange-form Vandermonde inverse (`vandInv`) the extractors compute with.
* `Sigma.Utils.LeftInverse` — a computable, polynomial-time left inverse of a
  full-column-rank matrix by verified Gaussian elimination (`gaussLeftInv`).
* `Sigma.Utils.Binding` — a non-trivial generator relation `⟨v, Γ⟩ = 0` reduces to discrete log
  (the "break" branch of computational knowledge soundness).

## Protocols (`Sigma.Protocols`)

### `Sigma.Protocols.IPA` — the inner-product argument (reused by both GBP variants)
* `Relation` — the inner-product relation `relIP` and the value-explicit `relIPV` (`R_IP`).
* `Fold` — the halving/folding maps and the round invariant `fold_relation`.
* `Extract` — the single-round 1066 reconstruction (witness or discrete-log relation).
* `NodeExtract` — the per-node extractor `nodeExtractData` (pigeonhole selection of four
  challenges with distinct squares out of eight; witness/break packaging).
* `ValueFold` — the "folding in the value" adaptor: `vfCombine` recovers an `R_IP` witness
  from openings at two distinct challenges (the reveal rounds of both GBP variants).
* `Reductions` — **the argument as a tower of reductions**: one fold round is
  `foldRed : relIP (k+1) → relIP k`; the tower `ipaRed` is `(8,…,8)`-special sound and
  complete by the composition theorems alone; `ipaProto = ipaRed.close` is the wire
  protocol — only the final scalar witness is ever transmitted.

### `Sigma.Protocols.IPAImproved` — the improved inner-product argument (polynomial fold)
Same statement, relation, message schedule, and communication as the Bulletproofs argument,
but the fold is *polynomial* in the challenge (Attema–Cramer eprint 2020/152 style:
`a' = ξ·aᴸ + aᴿ`, `𝐠' = 𝐠ᴸ + ξ·𝐠ᴿ`, `P ↦ ξ²·L + ξ·P + R`), so the challenges are *plain
field elements* (zero allowed, no inversions anywhere — the Bulletproofs argument requires
units `Fˣ`), the per-round extractor needs only pairwise-distinct challenges — no distinct
squares, no nonzeroness — and the special-soundness arity drops from 8 to 4.
* `Fold` — the polynomial folding maps and their round invariant.
* `Extract` — the single-round reconstruction (plain Vandermonde and degree-`≤3`
  consistency; witness or discrete-log relation).
* `NodeExtract` — the arity-4 per-node extractor (no selection step).
* `Reductions` — the `(4,…,4)` tower `ipaRed` and its closure `ipaProto`, over the same
  `SoundTower` bundle as the Bulletproofs tower.

### `Sigma.Protocols.GBP` — Generalized Bulletproofs
* `Relation` — the GB `Statement`, `Witness`, and `rel`.
* `Arithmetization` / `ArithmetizationComplete` / `ArithmetizationSound` — the
  arithmetization as a reduction `arithRed : R_GBP → relArith` (output relation = the two
  verifier equations on the never-sent vector opening), its completeness, and its
  `(n, Q+1, 2n'+3)`-knowledge soundness (witness or discrete-log relation).
* `Reductions` — the reveal-fold reduction `revealFold : relArith → relIP` (sends
  `(τx, μ, t̂)`, folds in the value at `ξ`), the full tower
  `gbpRed = arithRed ∘ revealFold ∘ ipaRed`, and the wire protocol `gbpProto`, with
  `(n, Q+1, 2n'+3, 2, 8, …, 8)`-knowledge soundness and completeness assembled from the
  parts by the composition theorems alone.

### `Sigma.Protocols.GBPImproved` — the improved protocol (`R_GBP'`, no auxiliary openings)
* `Relation` / `Arithmetization` / `ArithmetizationComplete` — the tighter relation and its
  arithmetization `arithRed'` (the binding challenge `r` recombines the split commitments;
  the mask slot of `f_L` carries the binding offset `z^{Q+1}·𝟙`; the output relation is the
  folded two-equation check on the never-sent opening) with completeness.
* `ArithmetizationSound` — **`arithRed'_sound`**: `(n, Q+2, 2m+5, 3)`-knowledge soundness
  of the protocol of record for `R_GBP'` (the `Offset.*` modules: three-child
  `r`-quadrants, the `t̂`-quadratic, and the binding-offset elimination argument forcing every
  `𝐆`-side `𝐇`-stray to zero).
* `ArithmetizationPreR` — the pre-`r`-ordering variant (opening sent before `r`, as a
  *closed* reduction) and its `(n, Q+1, 2m+5, 2)`-soundness for `R_GBP'`
  (`arithRedPreR_sound`): the formal record that the ordering alone — with no offset —
  pins the split openings exactly.
* `Reductions` — the `t̂`-reveal reduction `revealT : relArith' → relIP`, the full tower
  `gbpRed' = arithRed' ∘ revealT ∘ ipaRed` over the improved (arity-4) inner-product
  tower, and the wire protocol `gbpProto'`, with
  `(n, Q+2, 2m+5, 3, 2, 4, …, 4)`-knowledge soundness and completeness assembled by the
  composition theorems alone.
-/
