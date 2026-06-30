/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Theorems.ReductionCompose
import Sigma.Protocols.IPAImproved.NodeExtract
import Sigma.Protocols.IPA.Reductions

/-!
# The improved inner-product argument as a tower of reductions of knowledge

The polynomial-fold inner-product argument (Attema–Cramer eprint 2020/152 style) on the
`Sigma.Reduction` interface, mirroring `Sigma.Protocols.IPA.Reductions`: one folding round
is the reduction `relIP (k+1) → relIP k` with the *polynomial* fold
(`𝐠' = 𝐠ᴸ + ξ·𝐠ᴿ`, commitment `ξ²·L + ξ·P + R` — no inversion, `ξ = 0` allowed, plain
field challenges), the tower `Sigma.Protocols.IPAImproved.ipaRed` is the `(k+1)`-fold
composition, and `ipaProto` its closure. The per-round extractor
(`Sigma.Protocols.IPAImproved.nodeExtractData_valid`) needs only **four** pairwise-distinct
challenges, so the arity vector is `(4,…,4)` (`ipaRed_arities`); knowledge soundness of the
tower is again `Sigma.Reduction.compose_sound` applied per level, and completeness is
`Sigma.Reduction.compose_complete` over the per-fold `fold_relation`.

The relations (`relIPRel`, `relIPScalar`), the cross-terms (`foldCross`), and the
`SoundTower` bundle are shared with the Bulletproofs tower — only the fold and the arity
differ.
-/

namespace Sigma.Protocols.IPAImproved

open Sigma.TreeK
open Sigma.Protocols.IPA (IPStatement relIP splitL splitR ipGens relIPRel relIPScalar
  foldCross mem_paths_msg_chal_leaf msm_pow_zero ip_pow_zero SoundTower)

variable (F G : Type) [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## One polynomial folding round as a reduction -/

/-- **One improved folding round**, as a reduction `relIP (k+1) → relIP k`: the prover
sends the cross-terms `(L, R)`, the verifier sends a plain field challenge `ξ`, and the
claim is reduced to the polynomially folded statement (`foldG ξ`/`foldH ξ` generators,
commitment `ξ²·L + ξ·P + R`). The folded witness is never sent. -/
def foldRed (k : ℕ) : Reduction where
  In := relIPRel F G (k + 1)
  Out := relIPRel F G k
  moves := [.msg (G × G), .chal F]
  reduce := fun x c => some
    { P := c.2.1 ^ 2 • c.1.1 + c.2.1 • x.P + c.1.2
      gs := foldG c.2.1 (splitL x.gs) (splitR x.gs)
      hs := foldH c.2.1 (splitL x.hs) (splitR x.hs)
      u := x.u }

/-- **The last improved folding round**, reducing the length-two relation to the scalar
relation. -/
def foldRedBase : Reduction where
  In := relIPRel F G 0
  Out := relIPScalar F G
  moves := [.msg (G × G), .chal F]
  reduce := fun x c => some
    (c.2.1 ^ 2 • c.1.1 + c.2.1 • x.P + c.1.2,
      foldG c.2.1 (splitL x.gs) (splitR x.gs) 0,
      foldH c.2.1 (splitL x.hs) (splitR x.hs) 0,
      x.u)

/-- The arity-`4` tree annotation of one improved folding round: the polynomial-fold
extractor needs only four pairwise-distinct challenges. -/
@[reducible] def foldMK : List MoveK := [.msg (G × G), .chal F 4]

/-! ## Per-fold knowledge soundness -/

/-- The per-fold extractor: the plain-Vandermonde reconstruction core `nodeExtractData` on
the four decorated branches. -/
def foldRedExtract (k : ℕ) (_x : (relIPRel F G (k + 1)).Stmt)
    (T : TreeK (foldMK F G) (relIPRel F G k).Wit) :
    (relIPRel F G (k + 1)).Wit ⊕ (Fin (2 ^ (k + 1 + 1) + 2 ^ (k + 1 + 1) + 1) → F) :=
  nodeExtractData (T.msgSub.chalVal)
    (fun i => ((T.msgSub.chalSub i).leafVal).1) (fun i => ((T.msgSub.chalSub i).leafVal).2)

/-- The base-case extractor, with the scalar decorations as one-dimensional vectors. -/
def foldBaseExtract (_x : (relIPRel F G 0).Stmt)
    (T : TreeK (foldMK F G) (relIPScalar F G).Wit) :
    (relIPRel F G 0).Wit ⊕ (Fin (2 ^ (0 + 1) + 2 ^ (0 + 1) + 1) → F) :=
  nodeExtractData (T.msgSub.chalVal)
    (fun i _ => ((T.msgSub.chalSub i).leafVal).1)
    (fun i _ => ((T.msgSub.chalSub i).leafVal).2)

/-- **One improved folding round is knowledge sound** (arity `4`): from four accepting
decorated branches with pairwise-distinct challenges, recover a parent witness or a
non-trivial discrete-log relation. -/
theorem foldRed_sound (k : ℕ) :
    (foldRed F G k).Sound (mk := foldMK F G) rfl
      (fun x v => IsNontrivialDLRel (ipGens x) v) (foldRedExtract F G k) := by
  intro x T hacc
  have hC : ∀ i : Fin 4,
      T.msgSub.chalVal i ^ 2 • T.msgVal.1 + T.msgSub.chalVal i • x.P + T.msgVal.2
      = msm ((T.msgSub.chalSub i).leafVal.1)
          (foldG (T.msgSub.chalVal i) (splitL x.gs) (splitR x.gs))
        + msm ((T.msgSub.chalSub i).leafVal.2)
          (foldH (T.msgSub.chalVal i) (splitL x.hs) (splitR x.hs))
        + ip ((T.msgSub.chalSub i).leafVal.1) ((T.msgSub.chalSub i).leafVal.2) • x.u := by
    intro i
    obtain ⟨s, hs, hrel⟩ := hacc _ (mem_paths_msg_chal_leaf T i)
    simp only [foldRed] at hs
    obtain rfl := Option.some.inj hs
    simp only [foldRed, relIP, decide_eq_true_eq] at hrel
    exact hrel
  exact nodeExtractData_valid x T.msgSub.chalVal T.msgSub.chalInj T.msgVal.1 T.msgVal.2
    (fun i => ((T.msgSub.chalSub i).leafVal).1) (fun i => ((T.msgSub.chalSub i).leafVal).2)
    hC

/-- **The last improved folding round is knowledge sound** (arity `4`). -/
theorem foldRedBase_sound :
    (foldRedBase F G).Sound (mk := foldMK F G) rfl
      (fun x v => IsNontrivialDLRel (ipGens x) v) (foldBaseExtract F G) := by
  intro x T hacc
  have hC : ∀ i : Fin 4,
      T.msgSub.chalVal i ^ 2 • T.msgVal.1 + T.msgSub.chalVal i • x.P + T.msgVal.2
      = msm (fun _ : Fin (2 ^ 0) => ((T.msgSub.chalSub i).leafVal).1)
          (foldG (T.msgSub.chalVal i) (splitL x.gs) (splitR x.gs))
        + msm (fun _ : Fin (2 ^ 0) => ((T.msgSub.chalSub i).leafVal).2)
          (foldH (T.msgSub.chalVal i) (splitL x.hs) (splitR x.hs))
        + ip (fun _ : Fin (2 ^ 0) => ((T.msgSub.chalSub i).leafVal).1)
            (fun _ : Fin (2 ^ 0) => ((T.msgSub.chalSub i).leafVal).2) • x.u := by
    intro i
    obtain ⟨s, hs, hrel⟩ := hacc _ (mem_paths_msg_chal_leaf T i)
    simp only [foldRedBase] at hs
    obtain rfl := Option.some.inj hs
    simp only [foldRedBase, relIPScalar, decide_eq_true_eq] at hrel
    rw [msm_pow_zero, msm_pow_zero, ip_pow_zero]
    exact hrel
  exact nodeExtractData_valid x T.msgSub.chalVal T.msgSub.chalInj T.msgVal.1 T.msgVal.2
    (fun i _ => ((T.msgSub.chalSub i).leafVal).1)
    (fun i _ => ((T.msgSub.chalSub i).leafVal).2) hC

/-! ## The sound tower -/

/-- The sound improved-IPA tower, by recursion on the number of folding rounds — the
`(4,…,4)` twin of `Sigma.Protocols.IPA.soundTower`, over the same `SoundTower` bundle. -/
def soundTower : (k : ℕ) → SoundTower F G k
  | 0 =>
    { R := foldRedBase F G
      hIn := rfl
      hOut := rfl
      mks := foldMK F G
      hmk := rfl
      hpos := by intro a ha; simp only [foldMK, chalArities_msg_cons, chalArities_chal_cons,
        chalArities_nil, List.mem_singleton] at ha; omega
      B := Fin (2 ^ (0 + 1) + 2 ^ (0 + 1) + 1) → F
      brk := fun x v => IsNontrivialDLRel (ipGens x) v
      e := foldBaseExtract F G
      sound := foldRedBase_sound F G
      instWit := ⟨(fun _ => 0, fun _ => 0)⟩ }
  | k + 1 =>
    let prev := soundTower k
    letI : Inhabited prev.R.In.Wit := prev.instWit
    { R := (foldRed F G k).compose prev.R prev.hIn
      hIn := rfl
      hOut := prev.hOut
      mks := foldMK F G ++ prev.mks
      hmk := by rw [stripMoves_append, prev.hmk]; rfl
      hpos := by
        rw [chalArities_append]
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · simp only [foldMK, chalArities_msg_cons, chalArities_chal_cons, chalArities_nil,
            List.mem_singleton] at h
          omega
        · exact prev.hpos a h
      B := (Fin (2 ^ (k + 1 + 1) + 2 ^ (k + 1 + 1) + 1) → F) ⊕ prev.B
      brk := Reduction.composeBrk (foldRed F G k) prev.R prev.hIn
        (fun x v => IsNontrivialDLRel (ipGens x) v) prev.brk
      e := Reduction.composeExtract (foldRed F G k) prev.R prev.hIn rfl
        (foldRedExtract F G k) prev.e
      sound := Reduction.compose_sound (foldRed F G k) prev.R prev.hIn rfl prev.hmk
        (fun S => TreeK.paths_ne_nil S prev.hpos) (foldRed_sound F G k) prev.sound
      instWit := ⟨(fun _ => 0, fun _ => 0)⟩ }

/-! ## The headline objects and theorems -/

/-- **The improved inner-product argument as a reduction of knowledge**
`relIP k → scalar`. -/
def ipaRed (k : ℕ) : Reduction := (soundTower F G k).R

lemma ipaRed_In (k : ℕ) : (ipaRed F G k).In = relIPRel F G k := (soundTower F G k).hIn

lemma ipaRed_Out (k : ℕ) : (ipaRed F G k).Out = relIPScalar F G := (soundTower F G k).hOut

/-- **Knowledge soundness of the improved IPA tower**, assembled from the per-fold
soundness by `Sigma.Reduction.compose_sound` alone. -/
theorem ipaRed_sound (k : ℕ) :
    (ipaRed F G k).Sound (soundTower F G k).hmk (soundTower F G k).brk
      (soundTower F G k).e :=
  (soundTower F G k).sound

/-- **The improved IPA tower is `(4,…,4)`-special sound**: one arity-`4` branching per
folding challenge, in order. -/
theorem ipaRed_arities (k : ℕ) :
    chalArities (soundTower F G k).mks = List.replicate (k + 1) 4 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show chalArities (foldMK F G ++ (soundTower F G k).mks) = _
      rw [chalArities_append, ih]
      rfl

/-! ## The closed protocol -/

instance ipaRedOutWitInhabited (k : ℕ) : Inhabited (ipaRed F G k).Out.Wit :=
  ⟨Rel.castWit (soundTower F G k).hOut.symm ((0 : F), (0 : F))⟩

/-- **The wire protocol**: close the tower — only the final, scalar-sized witness is ever
sent. -/
def ipaProto (k : ℕ) : Reduction := (ipaRed F G k).close

/-- The wire protocol is a complete protocol: nothing remains to be proven. -/
theorem ipaProto_closed (k : ℕ) : (ipaProto F G k).Closed :=
  Reduction.close_closed _

/-- **Knowledge soundness of the wire protocol**: closing preserves the tower's soundness
and its `(4,…,4)` arities. -/
theorem ipaProto_sound (k : ℕ) :
    (ipaProto F G k).Sound
      (mk := (soundTower F G k).mks ++ [.msg (ipaRed F G k).Out.Wit])
      (by rw [stripMoves_append, (soundTower F G k).hmk]; rfl)
      (Reduction.composeBrk (ipaRed F G k) (Rel.send (ipaRed F G k).Out) rfl
        (soundTower F G k).brk (fun _ b => b.elim))
      (Reduction.composeExtract (ipaRed F G k) (Rel.send (ipaRed F G k).Out) rfl
        (soundTower F G k).hmk (soundTower F G k).e (Rel.sendExtract (ipaRed F G k).Out)) :=
  Reduction.close_sound (ipaRed F G k) (soundTower F G k).hmk (soundTower F G k).sound

/-! ## Completeness -/

section Completeness

open OracleComp OracleSpec
open Sigma.Protocols.IPA (foldCross)

variable [SampleableType F]

/-- Honest prover for one improved folding round: emit the cross-terms, receive `ξ`, carry
the polynomially folded `(a', b')`. -/
def foldRedHonest (k : ℕ) (x : (foldRed F G k).In.Stmt) (w : (foldRed F G k).In.Wit) :
    ProbComp (Conversation (foldRed F G k).moves × (foldRed F G k).Out.Wit) := do
  let ξ ← uniformSample F
  pure ((foldCross F G x.gs x.hs x.u w.1 w.2, ξ, PUnit.unit),
    (foldA ξ (splitL w.1) (splitR w.1), foldB ξ (splitL w.2) (splitR w.2)))

omit [DecidableEq F] in
/-- **One improved folding round is complete** — exactly `fold_relation` (no challenge
needs to be invertible). -/
theorem foldRed_complete (k : ℕ) :
    (foldRed F G k).Complete (foldRedHonest F G k) := by
  intro x w hrel p hp
  simp only [foldRedHonest, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hp
  obtain ⟨ξ, rfl⟩ := hp
  have hP : x.P = msm w.1 x.gs + msm w.2 x.hs + ip w.1 w.2 • x.u := by
    simpa [foldRed, relIP] using hrel
  refine ⟨_, rfl, ?_⟩
  simp only [foldRed, relIP, decide_eq_true_eq, foldCross]
  have hfr := fold_relation ξ x.gs x.hs x.u w.1 w.2 x.P hP
  linear_combination (norm := module) hfr

/-- Honest prover for the last improved folding round. -/
def foldRedBaseHonest (x : (foldRedBase F G).In.Stmt) (w : (foldRedBase F G).In.Wit) :
    ProbComp (Conversation (foldRedBase F G).moves × (foldRedBase F G).Out.Wit) := do
  let ξ ← uniformSample F
  pure ((foldCross F G x.gs x.hs x.u w.1 w.2, ξ, PUnit.unit),
    (foldA ξ (splitL w.1) (splitR w.1) 0, foldB ξ (splitL w.2) (splitR w.2) 0))

omit [DecidableEq F] in
/-- **The last improved folding round is complete**. -/
theorem foldRedBase_complete : (foldRedBase F G).Complete (foldRedBaseHonest F G) := by
  intro x w hrel p hp
  simp only [foldRedBaseHonest, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hp
  obtain ⟨ξ, rfl⟩ := hp
  have hP : x.P = msm w.1 x.gs + msm w.2 x.hs + ip w.1 w.2 • x.u := by
    simpa [foldRedBase, relIP] using hrel
  refine ⟨_, rfl, ?_⟩
  simp only [foldRedBase, relIPScalar, decide_eq_true_eq, foldCross, msm_pow_zero,
    ip_pow_zero]
  have hfr := fold_relation ξ x.gs x.hs x.u w.1 w.2 x.P hP
  simp only [msm_pow_zero, ip_pow_zero] at hfr
  linear_combination (norm := module) hfr

/-- The honest prover of the improved tower. -/
def towerHonest : (k : ℕ) → (ipaRed F G k).In.Stmt → (ipaRed F G k).In.Wit →
    ProbComp (Conversation (ipaRed F G k).moves × (ipaRed F G k).Out.Wit)
  | 0 => foldRedBaseHonest F G
  | k + 1 =>
      letI : Inhabited (soundTower F G k).R.In.Stmt :=
        ⟨Rel.castStmt (soundTower F G k).hIn.symm default⟩
      Reduction.composeHonest (foldRed F G k) (soundTower F G k).R (soundTower F G k).hIn
        (foldRedHonest F G k) (towerHonest k)

/-- **Completeness of the improved IPA tower**, by `Sigma.Reduction.compose_complete` per
level. -/
theorem ipaRed_complete : ∀ k : ℕ, (ipaRed F G k).Complete (towerHonest F G k)
  | 0 => foldRedBase_complete F G
  | k + 1 => by
      letI : Inhabited (soundTower F G k).R.In.Stmt :=
        ⟨Rel.castStmt (soundTower F G k).hIn.symm default⟩
      exact Reduction.compose_complete (foldRed F G k) (soundTower F G k).R
        (soundTower F G k).hIn (foldRedHonest F G k) (towerHonest F G k)
        (foldRed_complete F G k) (ipaRed_complete k)

instance ipaRedOutStmtInhabited (k : ℕ) : Inhabited (ipaRed F G k).Out.Stmt :=
  ⟨Rel.castStmt (soundTower F G k).hOut.symm ((0 : G), (0 : G), (0 : G), (0 : G))⟩

/-- **Completeness of the wire protocol**. -/
theorem ipaProto_complete (k : ℕ) :
    (ipaProto F G k).Complete
      (Reduction.composeHonest (ipaRed F G k) (Rel.send (ipaRed F G k).Out) rfl
        (towerHonest F G k) (Rel.sendHonest (ipaRed F G k).Out)) :=
  Reduction.close_complete (ipaRed F G k) (towerHonest F G k) (ipaRed_complete F G k)

end Completeness

end Sigma.Protocols.IPAImproved
