/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Theorems.ReductionCompose
import Sigma.Protocols.IPA.NodeExtract

/-!
# The inner-product argument as a tower of reductions of knowledge

The Bulletproofs inner-product argument, rebuilt on the `Sigma.Reduction` interface: one
folding round is a reduction `relIP (k+1) → relIP k` (`Sigma.Protocols.IPA.foldRed`) whose
(virtual) final message — the folded witness — is never sent; the full argument
`Sigma.Protocols.IPA.ipaRed` is the `(k+1)`-fold sequential composition of folding rounds
(bottoming out at the scalar relation), and the wire protocol
`Sigma.Protocols.IPA.ipaProto` is its closure — only the last, scalar-sized witness is ever
transmitted, by the trivial proof of knowledge.

Knowledge soundness of the whole tower (`Sigma.Protocols.IPA.ipaRed_sound`,
`ipaProto_sound`) is assembled from a *single* per-fold fact
(`Sigma.Protocols.IPA.foldRed_sound`, the 1066 reconstruction core
`Sigma.Protocols.IPA.nodeExtractData_valid`) by `Sigma.Reduction.compose_sound` alone —
there are no per-instance bridge obligations at the seams. The arity vector is `(8,…,8)`, one `8` per
folding challenge (`Sigma.Protocols.IPA.ipaRed_arities`), and closing contributes no
challenge move.

The data of each tower level is packaged in `Sigma.Protocols.IPA.SoundTower` (the
reduction, its tree shape, extractor, break predicate, and soundness proof together), so
the recursion over `k` carries everything it needs without casts.
-/

namespace Sigma.Protocols.IPA

open Sigma.TreeK

/-- The single decorated path of a `[message, k'-fold challenge]`-shaped tree along branch
`i`. -/
lemma mem_paths_msg_chal_leaf {M C : Type} {k' : ℕ} {L : Type}
    (T : TreeK [.msg M, .chal C k'] L) (i : Fin k') :
    ((T.msgVal, (T.msgSub.chalVal i, PUnit.unit)), (T.msgSub.chalSub i).leafVal)
      ∈ T.paths := by
  rw [TreeK.paths_eq_msg, TreeK.paths_eq_chal]
  refine List.mem_map.2
    ⟨((T.msgSub.chalVal i, PUnit.unit), (T.msgSub.chalSub i).leafVal), ?_, rfl⟩
  refine List.mem_flatMap.2 ⟨i, List.mem_finRange i, ?_⟩
  refine List.mem_map.2 ⟨(PUnit.unit, (T.msgSub.chalSub i).leafVal), ?_, rfl⟩
  rw [TreeK.paths_eq_leaf]
  exact List.mem_singleton.mpr rfl

variable (F G : Type) [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## The relations of the tower -/

/-- The inner-product relation on length-`2^(k+1)` vectors, as a relation triple:
`P = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩ + ⟨a, b⟩·u`. -/
@[reducible] def relIPRel (k : ℕ) : Rel where
  Stmt := IPStatement F G k
  Wit := (Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F)
  rel := relIP

/-- The scalar inner-product relation after the last fold: statement
`(P, g, h, u)`, witness `(a, b)`, relation `P = a·g + b·h + (a·b)·u`. -/
@[reducible] def relIPScalar : Rel where
  Stmt := G × G × G × G
  Wit := F × F
  rel := fun s ab => decide (s.1 = ab.1 • s.2.1 + ab.2 • s.2.2.1 + (ab.1 * ab.2) • s.2.2.2)

/-! ## One folding round as a reduction -/

/-- **One folding round** of the inner-product argument, as a reduction
`relIP (k+1) → relIP k`: the prover sends the cross-terms `(L, R)`, the verifier sends
`ξ`, and the claim is reduced to the folded statement (`foldG ξ`/`foldH ξ` generators,
commitment `P + ξ²·L + ξ⁻²·R`). The folded witness — the final message — is never sent. -/
def foldRed (k : ℕ) : Reduction where
  In := relIPRel F G (k + 1)
  Out := relIPRel F G k
  moves := [.msg (G × G), .chal Fˣ]
  reduce := fun x c => some
    { P := x.P + ((c.2.1 : F)) ^ 2 • c.1.1 + (((c.2.1 : F))⁻¹) ^ 2 • c.1.2
      gs := foldG (c.2.1 : F) (splitL x.gs) (splitR x.gs)
      hs := foldH (c.2.1 : F) (splitL x.hs) (splitR x.hs)
      u := x.u }

/-- **The last folding round**, reducing the length-two inner-product relation to the
scalar relation. -/
def foldRedBase : Reduction where
  In := relIPRel F G 0
  Out := relIPScalar F G
  moves := [.msg (G × G), .chal Fˣ]
  reduce := fun x c => some
    (x.P + ((c.2.1 : F)) ^ 2 • c.1.1 + (((c.2.1 : F))⁻¹) ^ 2 • c.1.2,
      foldG (c.2.1 : F) (splitL x.gs) (splitR x.gs) 0,
      foldH (c.2.1 : F) (splitL x.hs) (splitR x.hs) 0,
      x.u)

/-- The arity-`8` tree annotation of one folding round: the 1066 extractor needs four
challenges with pairwise distinct squares, and any `8` distinct challenges contain them. -/
@[reducible] def foldMK : List MoveK := [.msg (G × G), .chal Fˣ 8]

/-! ## Per-fold knowledge soundness -/

/-- The per-fold extractor: the 1066 reconstruction core `nodeExtractData` on the eight
decorated branches. -/
def foldRedExtract (k : ℕ) (_x : (relIPRel F G (k + 1)).Stmt)
    (T : TreeK (foldMK F G) (relIPRel F G k).Wit) :
    (relIPRel F G (k + 1)).Wit ⊕ (Fin (2 ^ (k + 1 + 1) + 2 ^ (k + 1 + 1) + 1) → F) :=
  nodeExtractData (fun i => ((T.msgSub.chalVal i : Fˣ) : F))
    (fun i => ((T.msgSub.chalSub i).leafVal).1) (fun i => ((T.msgSub.chalSub i).leafVal).2)

/-- The base-case extractor: as `foldRedExtract`, with the scalar decorations as
one-dimensional vectors. -/
def foldBaseExtract (_x : (relIPRel F G 0).Stmt)
    (T : TreeK (foldMK F G) (relIPScalar F G).Wit) :
    (relIPRel F G 0).Wit ⊕ (Fin (2 ^ (0 + 1) + 2 ^ (0 + 1) + 1) → F) :=
  nodeExtractData (fun i => ((T.msgSub.chalVal i : Fˣ) : F))
    (fun i _ => ((T.msgSub.chalSub i).leafVal).1)
    (fun i _ => ((T.msgSub.chalSub i).leafVal).2)

/-- **One folding round is knowledge sound** (arity `8`): from eight accepting decorated
branches, recover a parent witness or a non-trivial discrete-log relation among the parent
generators. -/
theorem foldRed_sound (k : ℕ) :
    (foldRed F G k).Sound (mk := foldMK F G) rfl
      (fun x v => IsNontrivialDLRel (ipGens x) v) (foldRedExtract F G k) := by
  intro x T hacc
  have hC : ∀ i : Fin 8,
      x.P + ((T.msgSub.chalVal i : F)) ^ 2 • T.msgVal.1
        + (((T.msgSub.chalVal i : F))⁻¹) ^ 2 • T.msgVal.2
      = msm ((T.msgSub.chalSub i).leafVal.1)
          (foldG (T.msgSub.chalVal i : F) (splitL x.gs) (splitR x.gs))
        + msm ((T.msgSub.chalSub i).leafVal.2)
          (foldH (T.msgSub.chalVal i : F) (splitL x.hs) (splitR x.hs))
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

/-- **The last folding round is knowledge sound** (arity `8`). -/
theorem foldRedBase_sound :
    (foldRedBase F G).Sound (mk := foldMK F G) rfl
      (fun x v => IsNontrivialDLRel (ipGens x) v) (foldBaseExtract F G) := by
  intro x T hacc
  have hC : ∀ i : Fin 8,
      x.P + ((T.msgSub.chalVal i : F)) ^ 2 • T.msgVal.1
        + (((T.msgSub.chalVal i : F))⁻¹) ^ 2 • T.msgVal.2
      = msm (fun _ : Fin (2 ^ 0) => ((T.msgSub.chalSub i).leafVal).1)
          (foldG (T.msgSub.chalVal i : F) (splitL x.gs) (splitR x.gs))
        + msm (fun _ : Fin (2 ^ 0) => ((T.msgSub.chalSub i).leafVal).2)
          (foldH (T.msgSub.chalVal i : F) (splitL x.hs) (splitR x.hs))
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

/-- One level of the sound IPA reduction tower: the reduction together with its tree
shape, extractor, break predicate, soundness proof, and the typing facts the recursion
needs. Carrying everything in one bundle keeps the recursion over `k` cast-free. -/
structure SoundTower (k : ℕ) where
  /-- The reduction at this level (the `(k+1)`-fold tower). -/
  R : Reduction
  /-- Its input relation is the inner-product relation at size `2^(k+1)`. -/
  hIn : R.In = relIPRel F G k
  /-- Its output relation is the scalar relation. -/
  hOut : R.Out = relIPScalar F G
  /-- The annotated tree shape. -/
  mks : List MoveK
  /-- The tree shape matches the reduction's moves. -/
  hmk : stripMoves mks = R.moves
  /-- All arities are positive (they are all `8`). -/
  hpos : ∀ a ∈ chalArities mks, 0 < a
  /-- The break type. -/
  B : Type
  /-- The break predicate (a tower of discrete-log relations). -/
  brk : R.In.Stmt → B → Prop
  /-- The extractor. -/
  e : R.In.Stmt → TreeK mks R.Out.Wit → R.In.Wit ⊕ B
  /-- Knowledge soundness at this level. -/
  sound : R.Sound hmk brk e
  /-- The input witness type is inhabited (needed by the composite extractor). -/
  instWit : Inhabited R.In.Wit

/-- The sound IPA tower, by recursion on the number of folding rounds: the base is the
last folding round, and each level is `foldRed k` composed with the previous level —
soundness by `Sigma.Reduction.compose_sound` and `foldRed_sound` alone. -/
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

/-- **The inner-product argument as a reduction of knowledge** `relIP k → scalar`: the
`(k+1)`-fold tower of folding rounds. No witness is ever sent. -/
def ipaRed (k : ℕ) : Reduction := (soundTower F G k).R

lemma ipaRed_In (k : ℕ) : (ipaRed F G k).In = relIPRel F G k := (soundTower F G k).hIn

lemma ipaRed_Out (k : ℕ) : (ipaRed F G k).Out = relIPScalar F G := (soundTower F G k).hOut

/-- **Knowledge soundness of the IPA tower**, assembled from the per-fold soundness by
`Sigma.Reduction.compose_sound` alone. -/
theorem ipaRed_sound (k : ℕ) :
    (ipaRed F G k).Sound (soundTower F G k).hmk (soundTower F G k).brk
      (soundTower F G k).e :=
  (soundTower F G k).sound

/-- **The IPA tower is `(8,…,8)`-special sound**: one arity-`8` branching per folding
challenge, in order. -/
theorem ipaRed_arities (k : ℕ) :
    chalArities (soundTower F G k).mks = List.replicate (k + 1) 8 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show chalArities (foldMK F G ++ (soundTower F G k).mks) = _
      rw [chalArities_append, ih]
      rfl

/-! ## The closed protocol -/

instance ipaRedOutWitInhabited (k : ℕ) : Inhabited (ipaRed F G k).Out.Wit :=
  ⟨Rel.castWit (soundTower F G k).hOut.symm ((0 : F), (0 : F))⟩

/-- **The wire protocol**: close the tower — send the final, scalar-sized witness by the
trivial proof of knowledge. -/
def ipaProto (k : ℕ) : Reduction := (ipaRed F G k).close

/-- The wire protocol is a complete protocol: nothing remains to be proven. -/
theorem ipaProto_closed (k : ℕ) : (ipaProto F G k).Closed :=
  Reduction.close_closed _

/-- **Knowledge soundness of the wire protocol**: closing preserves the tower's soundness
and its `(8,…,8)` arities (the final message contributes no challenge move). -/
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

/-- The deterministic cross-terms `(L, R)` of one folding round on witness `(a, b)`. -/
def foldCross {k : ℕ} (gs hs : Fin (2 ^ (k + 1)) → G) (u : G)
    (a b : Fin (2 ^ (k + 1)) → F) : G × G :=
  (msm (splitL a) (splitR gs) + msm (splitR b) (splitL hs) + (ip (splitL a) (splitR b)) • u,
   msm (splitR a) (splitL gs) + msm (splitL b) (splitR hs) + (ip (splitR a) (splitL b)) • u)

instance instInhabitedIPStatement (k : ℕ) : Inhabited (IPStatement F G k) :=
  ⟨⟨0, fun _ => 0, fun _ => 0, 0⟩⟩

section Completeness

open OracleComp OracleSpec

variable [SampleableType Fˣ]

/-- Honest prover for one folding round: emit the cross-terms, receive `ξ`, and carry the
folded `(a', b')` as the output witness — nothing else is sent. -/
def foldRedHonest (k : ℕ) (x : (foldRed F G k).In.Stmt) (w : (foldRed F G k).In.Wit) :
    ProbComp (Conversation (foldRed F G k).moves × (foldRed F G k).Out.Wit) := do
  let ξu ← uniformSample Fˣ
  pure ((foldCross F G x.gs x.hs x.u w.1 w.2, ξu, PUnit.unit),
    (foldA (ξu : F) (splitL w.1) (splitR w.1), foldB (ξu : F) (splitL w.2) (splitR w.2)))

omit [DecidableEq F] in
/-- **One folding round is complete**: the folded witness satisfies the folded relation —
exactly `fold_relation`. -/
theorem foldRed_complete (k : ℕ) :
    (foldRed F G k).Complete (foldRedHonest F G k) := by
  intro x w hrel p hp
  simp only [foldRedHonest, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hp
  obtain ⟨ξu, rfl⟩ := hp
  have hP : x.P = msm w.1 x.gs + msm w.2 x.hs + ip w.1 w.2 • x.u := by
    simpa [foldRed, relIP] using hrel
  refine ⟨_, rfl, ?_⟩
  simp only [foldRed, relIP, decide_eq_true_eq, foldCross]
  have hfr := fold_relation (ξu : F) (Units.ne_zero ξu) x.gs x.hs x.u w.1 w.2 x.P hP
  linear_combination (norm := module) hfr

/-- Honest prover for the last folding round: as `foldRedHonest`, with the scalar output
witness. -/
def foldRedBaseHonest (x : (foldRedBase F G).In.Stmt) (w : (foldRedBase F G).In.Wit) :
    ProbComp (Conversation (foldRedBase F G).moves × (foldRedBase F G).Out.Wit) := do
  let ξu ← uniformSample Fˣ
  pure ((foldCross F G x.gs x.hs x.u w.1 w.2, ξu, PUnit.unit),
    (foldA (ξu : F) (splitL w.1) (splitR w.1) 0, foldB (ξu : F) (splitL w.2) (splitR w.2) 0))

omit [DecidableEq F] in
/-- **The last folding round is complete**. -/
theorem foldRedBase_complete : (foldRedBase F G).Complete (foldRedBaseHonest F G) := by
  intro x w hrel p hp
  simp only [foldRedBaseHonest, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hp
  obtain ⟨ξu, rfl⟩ := hp
  have hP : x.P = msm w.1 x.gs + msm w.2 x.hs + ip w.1 w.2 • x.u := by
    simpa [foldRedBase, relIP] using hrel
  refine ⟨_, rfl, ?_⟩
  simp only [foldRedBase, relIPScalar, decide_eq_true_eq, foldCross, msm_pow_zero, ip_pow_zero]
  have hfr := fold_relation (ξu : F) (Units.ne_zero ξu) x.gs x.hs x.u w.1 w.2 x.P hP
  simp only [msm_pow_zero, ip_pow_zero] at hfr
  linear_combination (norm := module) hfr

/-- The honest prover of the tower: at each level, run the fold round's prover and hand the
folded witness to the rest. -/
def towerHonest : (k : ℕ) → (ipaRed F G k).In.Stmt → (ipaRed F G k).In.Wit →
    ProbComp (Conversation (ipaRed F G k).moves × (ipaRed F G k).Out.Wit)
  | 0 => foldRedBaseHonest F G
  | k + 1 =>
      letI : Inhabited (soundTower F G k).R.In.Stmt :=
        ⟨Rel.castStmt (soundTower F G k).hIn.symm default⟩
      Reduction.composeHonest (foldRed F G k) (soundTower F G k).R (soundTower F G k).hIn
        (foldRedHonest F G k) (towerHonest k)

/-- **Completeness of the IPA tower**, assembled from the per-fold completeness by
`Sigma.Reduction.compose_complete` alone (no junction conditions exist). -/
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

/-- **Completeness of the wire protocol**: run the tower's prover and send the final
scalar witness. -/
theorem ipaProto_complete (k : ℕ) :
    (ipaProto F G k).Complete
      (Reduction.composeHonest (ipaRed F G k) (Rel.send (ipaRed F G k).Out) rfl
        (towerHonest F G k) (Rel.sendHonest (ipaRed F G k).Out)) :=
  Reduction.close_complete (ipaRed F G k) (towerHonest F G k) (ipaRed_complete F G k)

end Completeness

end Sigma.Protocols.IPA
