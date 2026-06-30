/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Theorems.ReductionCompose
import Sigma.Protocols.GBPImproved.ArithmetizationSound
import Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetSound
import Sigma.Protocols.GBPImproved.ArithmetizationComplete
import Sigma.Protocols.IPA.ValueFold
import Sigma.Protocols.IPAImproved.Reductions

/-!
# The improved logarithmic Generalized Bulletproofs protocol, as a tower of reductions

The improved protocol is the three-layer sequential composition

* `Sigma.Protocols.GBPImproved.arithRed'` — the improved arithmetization (split
  commitments, binding challenge `r`, binding offset), reducing `R_GBP'` to knowledge of
  the opening vectors (`Sigma.Protocols.GBPImproved.relArith'`);
* `Sigma.Protocols.GBPImproved.revealT` — the prover reveals **the scalar openings
  `(τ_x, μ, t̂)`** (its first message; nothing was revealed by the arithmetization, whose
  output witness carries them), the verifier checks the `t`-polynomial equation and folds
  the value in at `ξ` (`u := ξ·G`, `P' := P − μ·H + t̂·u`), reducing the claim to the
  inner-product relation;
* `Sigma.Protocols.IPAImproved.ipaRed` — the polynomial-fold inner-product tower
  (`(4,…,4)`-sound, plain field challenges), reducing to the scalar relation.

`Sigma.Protocols.GBPImproved.gbpRed'` is the composite and `gbpProto'` its closure — only
the final scalar pair is ever transmitted. Knowledge soundness (`gbpRed'_sound`) is
`Sigma.Reduction.compose_sound` at each seam — `arithRed'_sound` (the binding-offset
analysis), `revealT_sound` (two `ξ`-branches pin `t̂ = ⟨a, b⟩` via
`Sigma.Protocols.IPA.vfCombine_valid`), and `ipaRed_sound` — with arity vector
`(n, q+2, 2c+5, 3, 2, 4, …, 4)`. Completeness is `compose_complete` at each seam.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.TreeK
open Sigma.Protocols.GBP (gens)
open Sigma.Protocols.IPA (relIPRel relIPScalar IPStatement IPStatementV relIP foldStmt
  vfCombine vfCombine_valid ipGens mem_paths_msg_chal_leaf)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## The `t̂`-reveal reduction `relArith' → relIP` -/

/-- Package the improved arithmetization output statement and the revealed scalar openings
`(τ_x, μ, t̂)` into the value-explicit inner-product statement. -/
def toV' {k : ℕ} (s : ArithOpen' F G (2 ^ (k + 1))) (o : F × F × F) : IPStatementV F G k where
  P := s.P
  gs := s.gs
  hs := s.hs
  hgen := s.h
  ggen := s.g
  mu := o.2.1
  tHat := o.2.2
  tauX := o.1

/-- **The scalar-openings reveal reduction.** The prover reveals `(τ_x, μ, t̂)`; the
verifier checks the `t`-polynomial equation `t̂·g + τ_x·h = Tx` (rejecting otherwise) and,
on the challenge `ξ`, folds the value in: `u := ξ·g`, `P' := P − μ·h + t̂·u`. The claim is
reduced to the inner-product relation on the folded statement; the vectors are never
sent. -/
def revealT (k : ℕ) : Reduction where
  In := relArith' F G (2 ^ (k + 1))
  Out := relIPRel F G k
  moves := [.msg (F × F × F), .chal Fˣ]
  reduce := fun s c =>
    if c.1.2.2 • s.g + c.1.1 • s.h = s.Tx then
      some (foldStmt (toV' s c.1) (c.2.1 : F))
    else none

/-- The `t̂`-reveal break predicate: a non-trivial discrete-log relation among
`𝐆 ⧺ 𝐡'' ⧺ [g]`. -/
def vtBrk (k : ℕ) (s : ArithOpen' F G (2 ^ (k + 1)))
    (v : Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F) : Prop :=
  IsNontrivialDLRel (ipGens (⟨0, s.gs, s.hs, s.g⟩ : IPStatement F G k)) v

/-- The reveal extractor: read `(τ_x, μ, t̂)` off the conversation, run
`Sigma.Protocols.IPA.vfCombine` on the two decorated branches, and recombine the recovered
vectors with the revealed scalars into the `relArith'` opening `(τ_x, μ, a, b)`. -/
def revealTExtract (k : ℕ) (s : (relArith' F G (2 ^ (k + 1))).Stmt)
    (T : TreeK [.msg (F × F × F), .chal Fˣ 2] (relIPRel F G k).Wit) :
    (relArith' F G (2 ^ (k + 1))).Wit ⊕ (Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F) :=
  Sum.map (fun ab => (T.msgVal.1, T.msgVal.2.1, ab.1, ab.2)) id
    (vfCombine (toV' s T.msgVal) ((T.msgSub.chalVal 0 : Fˣ) : F)
      ((T.msgSub.chalVal 1 : Fˣ) : F)
      ((T.msgSub.chalSub 0).leafVal) ((T.msgSub.chalSub 1).leafVal))

/-- **The reveal is knowledge sound** (arity `2`): two accepting branches at distinct `ξ`
pin `t̂ = ⟨a, b⟩` and the opening (`Sigma.Protocols.IPA.vfCombine_valid`); together with the
reduce map's `t`-polynomial check, the revealed scalars and the recovered vectors satisfy
`relArith'` — or the collision is a non-trivial discrete-log relation. -/
theorem revealT_sound (k : ℕ) :
    (revealT (F := F) (G := G) k).Sound (mk := [.msg (F × F × F), .chal Fˣ 2]) rfl
      (vtBrk k) (revealTExtract k) := by
  intro s T hacc
  have hpath : ∀ i : Fin 2,
      ∃ st, (revealT (F := F) (G := G) k).reduce s
          (T.msgVal, T.msgSub.chalVal i, PUnit.unit) = some st ∧
        relIP st ((T.msgSub.chalSub i).leafVal) = true :=
    fun i => hacc _ (mem_paths_msg_chal_leaf T i)
  obtain ⟨st₀, hst₀, _⟩ := hpath 0
  have hcheck : T.msgVal.2.2 • s.g + T.msgVal.1 • s.h = s.Tx := by
    by_contra hc
    replace hst₀ : (if T.msgVal.2.2 • s.g + T.msgVal.1 • s.h = s.Tx then
        some (foldStmt (toV' s T.msgVal) ((T.msgSub.chalVal 0 : Fˣ) : F)) else none)
        = some st₀ := hst₀
    rw [if_neg hc] at hst₀
    simp at hst₀
  have hrel : ∀ i : Fin 2,
      relIP (foldStmt (toV' s T.msgVal) ((T.msgSub.chalVal i : Fˣ) : F))
        ((T.msgSub.chalSub i).leafVal) = true := by
    intro i
    obtain ⟨st, hst, hr⟩ := hpath i
    replace hst : (if T.msgVal.2.2 • s.g + T.msgVal.1 • s.h = s.Tx then
        some (foldStmt (toV' s T.msgVal) ((T.msgSub.chalVal i : Fˣ) : F)) else none)
        = some st := hst
    rw [if_pos hcheck] at hst
    obtain rfl := Option.some.inj hst
    exact hr
  have hdist : ((T.msgSub.chalVal 0 : Fˣ) : F) ≠ ((T.msgSub.chalVal 1 : Fˣ) : F) := fun h =>
    absurd (T.msgSub.chalInj (Units.ext h)) (by decide)
  obtain ⟨hwit, hbrk⟩ := vfCombine_valid (toV' s T.msgVal) _ _ hdist
    ((T.msgSub.chalSub 0).leafVal) ((T.msgSub.chalSub 1).leafVal) (hrel 0) (hrel 1)
  have hext : revealTExtract k s T
      = Sum.map (fun ab => (T.msgVal.1, T.msgVal.2.1, ab.1, ab.2)) id
        (vfCombine (toV' s T.msgVal) ((T.msgSub.chalVal 0 : Fˣ) : F)
          ((T.msgSub.chalVal 1 : Fˣ) : F)
          ((T.msgSub.chalSub 0).leafVal) ((T.msgSub.chalSub 1).leafVal)) := rfl
  rcases hvc : vfCombine (toV' s T.msgVal) ((T.msgSub.chalVal 0 : Fˣ) : F)
      ((T.msgSub.chalVal 1 : Fˣ) : F)
      ((T.msgSub.chalSub 0).leafVal) ((T.msgSub.chalSub 1).leafVal) with ab | v
  · refine ⟨fun w hw => ?_, fun b hb => ?_⟩
    · rw [hext, hvc, Sum.map_inl] at hw
      obtain rfl := Sum.inl.inj hw
      have hV := hwit ab hvc
      simp only [Sigma.Protocols.IPA.relIPV, toV', decide_eq_true_eq] at hV
      obtain ⟨hP, hthat⟩ := hV
      show (relArith' F G (2 ^ (k + 1))).rel s _ = true
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [← hthat]; exact hcheck, hP⟩
    · rw [hext, hvc, Sum.map_inl] at hb
      cases hb
  · refine ⟨fun w hw => ?_, fun b hb => ?_⟩
    · rw [hext, hvc, Sum.map_inr] at hw
      cases hw
    · rw [hext, hvc, Sum.map_inr] at hb
      obtain rfl := Sum.inr.inj hb
      exact hbrk v hvc

/-! ## The full improved logarithmic protocol -/

/-- The inner composite: `t̂`-reveal, then the polynomial-fold inner-product tower. -/
def innerRed' (k : ℕ) : Reduction :=
  (revealT (F := F) (G := G) k).compose (Sigma.Protocols.IPAImproved.ipaRed F G k)
    (Sigma.Protocols.IPAImproved.soundTower F G k).hIn

/-- **The improved logarithmic Generalized Bulletproofs protocol as a reduction**: the
improved arithmetization composed with the `t̂`-reveal and the polynomial-fold
inner-product tower. -/
def gbpRed' (k q m c : ℕ) : Reduction :=
  (arithRed' (F := F) (G := G) (2 ^ (k + 1)) q m c).compose (innerRed' k) rfl

/-- **The wire protocol**: close the tower — only the final scalar pair is transmitted. -/
def gbpProto' (k q m c : ℕ) : Reduction := (gbpRed' (F := F) (G := G) k q m c).close

theorem gbpProto'_closed (k q m c : ℕ) : (gbpProto' (F := F) (G := G) k q m c).Closed :=
  Reduction.close_closed _

/-! ## Knowledge soundness of the whole protocol -/

section Soundness

instance gbpInhabitedIPWit' (k : ℕ) :
    Inhabited (Sigma.Protocols.IPAImproved.ipaRed F G k).In.Wit :=
  (Sigma.Protocols.IPAImproved.soundTower F G k).instWit

instance gbpInhabitedInnerWit' (k : ℕ) :
    Inhabited (innerRed' (F := F) (G := G) k).In.Wit :=
  ⟨(0, 0, fun _ => 0, fun _ => 0)⟩

/-- The annotated tree shape of the inner composite. -/
@[reducible] def innerMK' (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (k : ℕ) : List MoveK :=
  [.msg (F × F × F), .chal Fˣ 2] ++ (Sigma.Protocols.IPAImproved.soundTower F G k).mks

/-- **Knowledge soundness of the inner composite** (`t̂`-reveal ∘ improved IPA tower). -/
theorem innerRed'_sound (k : ℕ) :
    (innerRed' (F := F) (G := G) k).Sound (mk := innerMK' F G k)
      (by rw [stripMoves_append, (Sigma.Protocols.IPAImproved.soundTower F G k).hmk]; rfl)
      (Reduction.composeBrk (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
        (Sigma.Protocols.IPAImproved.soundTower F G k).hIn (vtBrk k)
        (Sigma.Protocols.IPAImproved.soundTower F G k).brk)
      (Reduction.composeExtract (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
        (Sigma.Protocols.IPAImproved.soundTower F G k).hIn rfl (revealTExtract k)
        (Sigma.Protocols.IPAImproved.soundTower F G k).e) :=
  Reduction.compose_sound (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
    (Sigma.Protocols.IPAImproved.soundTower F G k).hIn rfl
    (Sigma.Protocols.IPAImproved.soundTower F G k).hmk
    (fun S => TreeK.paths_ne_nil S (Sigma.Protocols.IPAImproved.soundTower F G k).hpos)
    (revealT_sound k) (Sigma.Protocols.IPAImproved.soundTower F G k).sound

/-- The annotated tree shape of the whole improved protocol:
`(n, q+2, 2c+5, 3)` for the arithmetization, `2` for the `t̂`-reveal, `(4,…,4)` for the
polynomial-fold inner-product tower. -/
@[reducible] def gbpMK' (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (k q c : ℕ) : List MoveK :=
  Offset.arithMK' F G (2 ^ (k + 1)) q c ++ innerMK' F G k

/-- **Knowledge soundness of the whole improved logarithmic protocol**: `compose_sound` at
the outer seam, with `arithRed'_sound` (the binding-offset analysis) and
`innerRed'_sound`. -/
theorem gbpRed'_sound (k q m c : ℕ) :
    (gbpRed' (F := F) (G := G) k q m c).Sound (mk := gbpMK' F G k q c)
      (by rw [stripMoves_append, stripMoves_append,
            (Sigma.Protocols.IPAImproved.soundTower F G k).hmk]; rfl)
      (Reduction.composeBrk (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl
        (fun s v => IsNontrivialDLRel (gens s) v)
        (Reduction.composeBrk (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
          (Sigma.Protocols.IPAImproved.soundTower F G k).hIn (vtBrk k)
          (Sigma.Protocols.IPAImproved.soundTower F G k).brk))
      (Reduction.composeExtract (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl
        rfl Offset.arithExtractData
        (Reduction.composeExtract (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
          (Sigma.Protocols.IPAImproved.soundTower F G k).hIn rfl (revealTExtract k)
          (Sigma.Protocols.IPAImproved.soundTower F G k).e)) :=
  Reduction.compose_sound (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl rfl
    (by rw [stripMoves_append, (Sigma.Protocols.IPAImproved.soundTower F G k).hmk]; rfl)
    (fun S => TreeK.paths_ne_nil S (by
      rw [chalArities_append]
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · simp only [chalArities_msg_cons, chalArities_chal_cons, chalArities_nil,
          List.mem_singleton] at h
        omega
      · exact (Sigma.Protocols.IPAImproved.soundTower F G k).hpos a h))
    (arithRed'_sound (Nat.two_pow_pos _))
    (innerRed'_sound k)

end Soundness

/-! ## Completeness of the whole protocol -/

section Completeness

open OracleComp OracleSpec
open Sigma.Protocols.IPAImproved (towerHonest ipaRed_complete)

variable [SampleableType F] [SampleableType Fˣ]

/-- Honest prover for the reveal: send the witness scalars `(τ_x, μ)` and `t̂ = ⟨f_L, f_R⟩`,
and carry `(f_L, f_R)` as the output witness. -/
def revealTHonest (k : ℕ) (_s : (revealT (F := F) (G := G) k).In.Stmt)
    (w : (revealT (F := F) (G := G) k).In.Wit) :
    ProbComp (Conversation (revealT (F := F) (G := G) k).moves
      × (revealT (F := F) (G := G) k).Out.Wit) := do
  let ξu ← uniformSample Fˣ
  pure (((w.1, w.2.1, ip w.2.2.1 w.2.2.2), ξu, PUnit.unit), (w.2.2.1, w.2.2.2))

omit [SampleableType F] in
/-- **The reveal is complete**: the `t`-polynomial check passes by `eq1`, and the carried
vectors satisfy the folded inner-product relation by `eq2`. -/
theorem revealT_complete (k : ℕ) :
    (revealT (F := F) (G := G) k).Complete (revealTHonest k) := by
  intro s w hrel p hp
  simp only [revealTHonest, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hp
  obtain ⟨ξu, rfl⟩ := hp
  have hrel' : (relArith' F G (2 ^ (k + 1))).rel s w = true := hrel
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrel'
  obtain ⟨heq1, heq2⟩ := hrel'
  refine ⟨foldStmt (toV' s (w.1, w.2.1, ip w.2.2.1 w.2.2.2)) ((ξu : Fˣ) : F), ?_, ?_⟩
  · show (if ip w.2.2.1 w.2.2.2 • s.g + w.1 • s.h = s.Tx then
        some (foldStmt (toV' s (w.1, w.2.1, ip w.2.2.1 w.2.2.2)) ((ξu : Fˣ) : F)) else none)
      = _
    rw [if_pos heq1]
    rfl
  · show relIP (foldStmt (toV' s (w.1, w.2.1, ip w.2.2.1 w.2.2.2)) ((ξu : Fˣ) : F))
      (w.2.2.1, w.2.2.2) = true
    simp only [relIP, foldStmt, toV', decide_eq_true_eq]
    linear_combination (norm := module) heq2

local instance (k : ℕ) : Inhabited (Sigma.Protocols.IPAImproved.ipaRed F G k).In.Stmt :=
  ⟨Rel.castStmt (Sigma.Protocols.IPAImproved.soundTower F G k).hIn.symm default⟩

local instance (k : ℕ) : Inhabited (innerRed' (F := F) (G := G) k).In.Stmt :=
  ⟨⟨0, 0, 0, 0, fun _ => 0, fun _ => 0⟩⟩

/-- **Completeness of the inner composite.** -/
theorem innerRed'_complete (k : ℕ) :
    (innerRed' (F := F) (G := G) k).Complete
      (Reduction.composeHonest (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
        (Sigma.Protocols.IPAImproved.soundTower F G k).hIn (revealTHonest k)
        (towerHonest F G k)) :=
  Reduction.compose_complete (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
    (Sigma.Protocols.IPAImproved.soundTower F G k).hIn (revealTHonest k)
    (towerHonest F G k) (revealT_complete k) (ipaRed_complete F G k)

/-- **Completeness of the whole improved logarithmic protocol.** -/
theorem gbpRed'_complete (k q m c : ℕ) :
    (gbpRed' (F := F) (G := G) k q m c).Complete
      (Reduction.composeHonest (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl
        arithHonest'
        (Reduction.composeHonest (revealT k) (Sigma.Protocols.IPAImproved.ipaRed F G k)
          (Sigma.Protocols.IPAImproved.soundTower F G k).hIn (revealTHonest k)
          (towerHonest F G k))) :=
  Reduction.compose_complete (arithRed' (2 ^ (k + 1)) q m c) (innerRed' k) rfl
    arithHonest' _ arithRed'_complete (innerRed'_complete k)

end Completeness

end Sigma.Protocols.GBPImproved
