/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Constructions.ReductionCompose

/-!
# Composition theorems for reductions of knowledge

The three security properties of a `Sigma.Reduction` each *compose* along
`Sigma.Reduction.compose`, and the trivial proof of knowledge `Sigma.Rel.send` carries all
of them — so towers built by `compose` and terminated by `Sigma.Reduction.close` are secure
by construction.

## Main results

* `Sigma.Reduction.compose_complete` — completeness composes: a satisfied input relation
  yields a satisfied middle relation (by `R₁`), whose witness drives `R₂`'s honest prover.
  There is no junction side condition of any kind.
* `Sigma.Reduction.compose_sound` — knowledge soundness composes, with the arity
  vectors concatenated (`Sigma.chalArities` of `mk₁ ++ mk₂`).
* `Sigma.Reduction.compose_hvzk` / `compose_hvzk_perfect` — honest-verifier zero-knowledge
  composes; only the outer reduction carries a simulator obligation.
* `Sigma.Rel.send_complete` / `send_sound` — the trivial PoK is complete and *perfectly*
  knowledge-sound (the witness is read off the conversation; the break type is `Empty`),
  and it has no challenge moves, so closing never changes the arity vector.
* `Sigma.Reduction.close_complete` / `close_sound` — the corollaries for `close`.

## The soundness-composition proof, step by step

Steps 1, 3–5 live as constructions in `Sigma.Constructions.ReductionCompose`; the
correctness argument is `compose_sound` below.

* Step 1 — *split the composite tree*: `Sigma.TreeK.splitTree`, with the path factoring
  `Sigma.TreeK.paths_splitTree`.
* Step 2 — *factor the accepting condition*: `Sigma.Reduction.compose_reduce_joinCK`; along
  every composite path the outer reduce succeeds with some middle statement, and the inner
  path is accepting for it (`hfact`/`hsome`/`hsub` in the proof).
* Step 3 — *per-leaf inner extraction*: `Sigma.Reduction.composeRes` with `R₂`'s soundness;
  each leaf yields a valid middle witness or an inner break, at a derivable statement
  (`hres`).
* Step 4 — *break short-circuit*: the first inner break is a composite break
  (`Sigma.Reduction.composeBrk`).
* Step 5 — *re-decorate and conclude*: `Sigma.TreeK.mapLeaves` replaces each leaf's subtree
  by its extracted middle witness; the resulting outer tree is accepting **by definition**
  of `Sigma.Reduction.Accepting` — a shared-junction composition would need bridge
  hypotheses here; this framework needs nothing — and `R₁`'s extractor
  finishes.
-/

namespace Sigma

namespace Reduction

variable {B₁ B₂ : Type}

/-- **Completeness composes.** If `R₁` and `R₂` are complete, the stitched composite
prover is complete for `R₁.compose R₂`: `R₁`'s prover yields an accepting outer
conversation together with a valid middle witness, which is exactly what `R₂`'s prover
needs at the plumbed statement. -/
theorem compose_complete (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) [Inhabited R₂.In.Stmt]
    (H₁ : R₁.In.Stmt → R₁.In.Wit → ProbComp (Conversation R₁.moves × R₁.Out.Wit))
    (H₂ : R₂.In.Stmt → R₂.In.Wit → ProbComp (Conversation R₂.moves × R₂.Out.Wit))
    (hc₁ : R₁.Complete H₁) (hc₂ : R₂.Complete H₂) :
    (R₁.compose R₂ h).Complete (composeHonest R₁ R₂ h H₁ H₂) := by
  intro x w hrel p hp
  replace hp : p ∈ support (H₁ x w >>= composeCont R₁ R₂ h H₂ x) := hp
  rw [support_bind] at hp
  obtain ⟨p₁, hp₁, hp⟩ := Set.mem_iUnion₂.mp hp
  replace hp : p ∈ support
      (H₂ ((R₁.reduce x p₁.1).elim default (Rel.castStmt h.symm)) (Rel.castWit h.symm p₁.2)
        >>= fun p₂ => pure (Conversation.append p₁.1 p₂.1, p₂.2)) := hp
  rw [support_bind] at hp
  obtain ⟨p₂, hp₂, hp⟩ := Set.mem_iUnion₂.mp hp
  rw [support_pure] at hp
  replace hp : p = (Conversation.append p₁.1 p₂.1, p₂.2) := hp
  subst hp
  obtain ⟨s₁, hs₁, hz₁⟩ := hc₁ x w hrel p₁ hp₁
  rw [hs₁] at hp₂
  have hzin : R₂.In.rel (Rel.castStmt h.symm s₁) (Rel.castWit h.symm p₁.2) = true := by
    rw [Rel.rel_castStmt_castWit h.symm]
    exact hz₁
  obtain ⟨s₂, hs₂, hz₂⟩ := hc₂ _ _ hzin p₂ hp₂
  refine ⟨s₂, ?_, hz₂⟩
  rw [compose_reduce_append, hs₁]
  exact hs₂

/-- **Knowledge soundness composes**, with the arity vectors concatenated. Given the two
reductions' extractors, the composite extractor (`Sigma.Reduction.composeExtract`) is sound
for the composite, with the composite break (`Sigma.Reduction.composeBrk`): an outer break,
or an inner break at a derivable statement. Steps 1–5 per the module header: factor the
accepting condition through the split (Steps 1–2), extract per leaf (Step 3), short-circuit
on a break (Step 4), otherwise re-decorate and run the outer extractor (Step 5). -/
theorem compose_sound (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out)
    {mk₁ mk₂ : List MoveK} (hm₁ : stripMoves mk₁ = R₁.moves) (hm₂ : stripMoves mk₂ = R₂.moves)
    (hne : ∀ S : TreeK mk₂ R₂.Out.Wit, S.paths ≠ []) [Inhabited R₂.In.Wit]
    {brk₁ : R₁.In.Stmt → B₁ → Prop}
    {e₁ : R₁.In.Stmt → TreeK mk₁ R₁.Out.Wit → R₁.In.Wit ⊕ B₁}
    (h₁ : R₁.Sound hm₁ brk₁ e₁)
    {brk₂ : R₂.In.Stmt → B₂ → Prop}
    {e₂ : R₂.In.Stmt → TreeK mk₂ R₂.Out.Wit → R₂.In.Wit ⊕ B₂}
    (h₂ : R₂.Sound hm₂ brk₂ e₂) :
    (R₁.compose R₂ h).Sound (mk := mk₁ ++ mk₂)
      (by rw [stripMoves_append, hm₁, hm₂]; rfl)
      (composeBrk R₁ R₂ h brk₁ brk₂)
      (composeExtract R₁ R₂ h hm₁ e₁ e₂) := by
  intro x T hacc
  -- Step 2: along every outer leaf-path the outer reduce succeeds, and every inner path
  -- through it is accepting for the derived statement.
  have hfact : ∀ pS ∈ (TreeK.splitTree mk₁ T).paths, ∀ qz ∈ pS.2.paths,
      ∃ s₁, R₁.reduce x (hm₁ ▸ pS.1) = some s₁ ∧
        R₂.Accepting (Rel.castStmt h.symm s₁) (hm₂ ▸ qz.1) qz.2 := by
    intro pS hpS qz hqz
    have hmem : (joinCK mk₁ pS.1 qz.1, qz.2) ∈ T.paths := by
      rw [TreeK.paths_splitTree mk₁ T]
      exact List.mem_flatMap.2 ⟨pS, hpS, List.mem_map.2 ⟨qz, hqz, rfl⟩⟩
    obtain ⟨sO, hred, hrel⟩ := hacc _ hmem
    dsimp only at hred hrel
    rw [compose_reduce_joinCK R₁ R₂ h hm₁ hm₂
      (by rw [stripMoves_append, hm₁, hm₂]; rfl) x pS.1 qz.1] at hred
    obtain ⟨s₁, hs₁, hs₂⟩ := Option.bind_eq_some_iff.mp hred
    exact ⟨s₁, hs₁, sO, hs₂, hrel⟩
  -- Step 2 (corollaries): every outer leaf-path admits a derived statement (inner trees
  -- are nonempty), and each hanging subtree is accepting for it.
  have hsome : ∀ pS ∈ (TreeK.splitTree mk₁ T).paths,
      ∃ s₁, R₁.reduce x (hm₁ ▸ pS.1) = some s₁ := by
    intro pS hpS
    obtain ⟨qz, hqz⟩ := List.exists_mem_of_ne_nil _ (hne pS.2)
    obtain ⟨s₁, hs₁, _⟩ := hfact pS hpS qz hqz
    exact ⟨s₁, hs₁⟩
  have hsub : ∀ pS ∈ (TreeK.splitTree mk₁ T).paths, ∀ s₁,
      R₁.reduce x (hm₁ ▸ pS.1) = some s₁ →
      R₂.AcceptingTree hm₂ (Rel.castStmt h.symm s₁) pS.2 := by
    intro pS hpS s₁ hs₁ qz hqz
    obtain ⟨s₁', hs₁', hAcc⟩ := hfact pS hpS qz hqz
    rw [hs₁] at hs₁'
    obtain rfl := Option.some.inj hs₁'
    exact hAcc
  -- Step 3: the per-leaf extraction is sound — a valid middle witness or a genuine inner
  -- break, in both cases at a derivable statement.
  have hres : ∀ pS ∈ (TreeK.splitTree mk₁ T).paths,
      (∀ w₂, composeRes R₁ R₂ h hm₁ e₂ x pS.1 pS.2 = Sum.inl w₂ →
        ∃ s₁, R₁.reduce x (hm₁ ▸ pS.1) = some s₁ ∧
          R₂.In.rel (Rel.castStmt h.symm s₁) w₂ = true) ∧
      (∀ b₂, composeRes R₁ R₂ h hm₁ e₂ x pS.1 pS.2 = Sum.inr b₂ →
        ∃ s₁, R₁.reduce x (hm₁ ▸ pS.1) = some s₁ ∧
          brk₂ (Rel.castStmt h.symm s₁) b₂) := by
    intro pS hpS
    obtain ⟨s₁, hs₁⟩ := hsome pS hpS
    have hr : composeRes R₁ R₂ h hm₁ e₂ x pS.1 pS.2
        = e₂ (Rel.castStmt h.symm s₁) pS.2 := by
      simp only [composeRes, hs₁]
    have hsound := h₂ (Rel.castStmt h.symm s₁) pS.2 (hsub pS hpS s₁ hs₁)
    refine ⟨fun w₂ hw => ?_, fun b₂ hb => ?_⟩
    · rw [hr] at hw
      exact ⟨s₁, hs₁, hsound.1 w₂ hw⟩
    · rw [hr] at hb
      exact ⟨s₁, hs₁, hsound.2 b₂ hb⟩
  -- Case analysis on the composite extractor.
  rw [composeExtract]
  split
  · -- Step 4: some leaf reported an inner break.
    rename_i b₂ hfs
    obtain ⟨pS, hpS, hpS2⟩ := List.exists_of_findSome?_eq_some hfs
    refine ⟨fun w hw => by simp at hw, fun b hb => ?_⟩
    obtain rfl : Sum.inr b₂ = b := by simpa using hb
    rw [Sum.getRight?_eq_some_iff] at hpS2
    obtain ⟨s₁, hs₁, hbrk⟩ := (hres pS hpS).2 b₂ hpS2
    exact ⟨hm₁ ▸ pS.1, s₁, hs₁, hbrk⟩
  · -- Step 5: no leaf breaks — the re-decorated outer tree is accepting by definition,
    -- so `R₁`'s extractor finishes.
    rename_i hfs
    rw [List.findSome?_eq_none_iff] at hfs
    have hT₁acc : R₁.AcceptingTree hm₁ x
        ((TreeK.splitTree mk₁ T).mapLeaves fun c S =>
          Rel.castWit h ((composeRes R₁ R₂ h hm₁ e₂ x c S).getLeft?.getD default)) := by
      intro p hp
      rw [TreeK.paths_mapLeaves] at hp
      obtain ⟨pS, hpS, rfl⟩ := List.mem_map.mp hp
      obtain ⟨w₂, hw₂⟩ : ∃ w₂, composeRes R₁ R₂ h hm₁ e₂ x pS.1 pS.2 = Sum.inl w₂ := by
        rcases hcr : composeRes R₁ R₂ h hm₁ e₂ x pS.1 pS.2 with w₂ | b₂
        · exact ⟨w₂, rfl⟩
        · have := hfs _ hpS
          rw [hcr] at this
          simp at this
      obtain ⟨s₁, hs₁, hrel₂⟩ := (hres pS hpS).1 w₂ hw₂
      refine ⟨s₁, hs₁, ?_⟩
      rw [hw₂]
      simp only [Sum.getLeft?_inl, Option.getD_some]
      rw [Rel.rel_castWit h]
      exact hrel₂
    obtain ⟨hwit, hbrk⟩ := h₁ x _ hT₁acc
    refine ⟨fun w hw => ?_, fun b hb => ?_⟩
    · rcases hw' : e₁ x _ with w' | b'
      · rw [hw'] at hw
        obtain rfl := Sum.inl.inj hw
        exact hwit w' hw'
      · rw [hw'] at hw
        simp at hw
    · rcases hb' : e₁ x _ with w' | b'
      · rw [hb'] at hb
        simp at hb
      · rw [hb'] at hb
        obtain rfl := Sum.inr.inj hb
        exact hbrk b' hb'

/-- **HVZK composes (quantitative).** If the outer reduction is `ζ`-HVZK, so is the
composite — the honest prover and the simulator share the continuation that derives the
statement, runs `R₂`'s honest prover, and concatenates; only the first bind differs. The
inner reduction needs no zero-knowledge property of its own. -/
theorem compose_hvzk (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out) [Inhabited R₂.In.Stmt]
    (H₁ : R₁.In.Stmt → R₁.In.Wit → ProbComp (Conversation R₁.moves × R₁.Out.Wit))
    (H₂ : R₂.In.Stmt → R₂.In.Wit → ProbComp (Conversation R₂.moves × R₂.Out.Wit))
    (S₁ : R₁.In.Stmt → ProbComp (Conversation R₁.moves × R₁.Out.Wit))
    {ζ : ℝ} (hzk : R₁.HVZK H₁ S₁ ζ) :
    (R₁.compose R₂ h).HVZK (composeHonest R₁ R₂ h H₁ H₂) (composeSim R₁ R₂ h S₁ H₂) ζ := by
  intro x w hrel
  simp only [composeHonest, composeSim]
  exact le_trans (tvDist_bind_right_le _ (H₁ x w) (S₁ x)) (hzk x w hrel)

/-- **Perfect HVZK composes** — the `ζ = 0` specialization of
`Sigma.Reduction.compose_hvzk`. -/
theorem compose_hvzk_perfect (R₁ R₂ : Reduction) (h : R₂.In = R₁.Out)
    [Inhabited R₂.In.Stmt]
    (H₁ : R₁.In.Stmt → R₁.In.Wit → ProbComp (Conversation R₁.moves × R₁.Out.Wit))
    (H₂ : R₂.In.Stmt → R₂.In.Wit → ProbComp (Conversation R₂.moves × R₂.Out.Wit))
    (S₁ : R₁.In.Stmt → ProbComp (Conversation R₁.moves × R₁.Out.Wit))
    (hzk : R₁.PerfectHVZK H₁ S₁) :
    (R₁.compose R₂ h).PerfectHVZK (composeHonest R₁ R₂ h H₁ H₂)
      (composeSim R₁ R₂ h S₁ H₂) := by
  rw [perfectHVZK_iff_hvzk_zero]
  exact compose_hvzk R₁ R₂ h H₁ H₂ S₁
    ((perfectHVZK_iff_hvzk_zero R₁ H₁ S₁).mp hzk)

end Reduction

/-! ## The trivial proof of knowledge is complete and perfectly sound -/

namespace Rel

/-- The honest prover of the trivial PoK: send the witness. -/
def sendHonest (R : Rel) :
    R.Stmt → R.Wit → ProbComp (Conversation [Move.msg R.Wit] × PUnit) :=
  fun _x w => pure ((w, PUnit.unit), PUnit.unit)

/-- The trivial proof of knowledge is complete. -/
theorem send_complete (R : Rel) : (Rel.send R).Complete R.sendHonest := by
  intro x w hrel p hp
  have hrel' : R.rel x w = true := hrel
  simp only [sendHonest] at hp
  replace hp : p = ((w, PUnit.unit), PUnit.unit) := hp
  subst hp
  exact ⟨PUnit.unit, by simp [Rel.send, hrel'], rfl⟩

/-- The trivial PoK's extractor: read the witness off the conversation. -/
def sendExtract (R : Rel) (_x : R.Stmt) (T : TreeK [.msg R.Wit] PUnit) : R.Wit ⊕ Empty :=
  Sum.inl T.msgVal

/-- The trivial proof of knowledge is **perfectly** knowledge sound: an accepting
conversation contains the witness, and no break is ever needed (`Empty`). It has no
challenge moves, so it contributes nothing to the arity vector. -/
theorem send_sound (R : Rel) :
    (Rel.send R).Sound (mk := [.msg R.Wit]) rfl (fun _ b => b.elim) R.sendExtract := by
  intro x T hacc
  refine ⟨fun w hw => ?_, fun b hb => ?_⟩
  · obtain rfl := Sum.inl.inj hw
    have hmem : ((T.msgVal, PUnit.unit), PUnit.unit) ∈ T.paths := by
      rw [TreeK.paths_eq_msg, TreeK.paths_eq_leaf]
      exact List.mem_singleton.mpr rfl
    obtain ⟨s, hs, _⟩ := hacc _ hmem
    show R.rel x T.msgVal = true
    by_contra hrel
    simp [Rel.send, hrel] at hs
  · simp [sendExtract] at hb

end Rel

/-! ## Closing preserves completeness and knowledge soundness -/

namespace Reduction

/-- **Closing preserves completeness**: the closed protocol's honest prover runs the
reduction's prover and sends the final witness. -/
theorem close_complete (R : Reduction) [Inhabited R.Out.Stmt]
    (H : R.In.Stmt → R.In.Wit → ProbComp (Conversation R.moves × R.Out.Wit))
    (hc : R.Complete H) :
    R.close.Complete (composeHonest R (Rel.send R.Out) rfl H (Rel.sendHonest R.Out)) :=
  compose_complete R (Rel.send R.Out) rfl H (Rel.sendHonest R.Out) hc
    (Rel.send_complete R.Out)

/-- **Closing preserves knowledge soundness**, with the same arity vector: the appended
final message contributes no challenge move, and the appended extractor merely reads the
final witness off the conversation. -/
theorem close_sound (R : Reduction) {mk : List MoveK} (hm : stripMoves mk = R.moves)
    {B : Type} [Inhabited R.Out.Wit]
    {brk : R.In.Stmt → B → Prop} {e : R.In.Stmt → TreeK mk R.Out.Wit → R.In.Wit ⊕ B}
    (hs : R.Sound hm brk e) :
    R.close.Sound (mk := mk ++ [.msg R.Out.Wit])
      (by rw [stripMoves_append, hm]; rfl)
      (composeBrk R (Rel.send R.Out) rfl brk (fun _ b => b.elim))
      (composeExtract R (Rel.send R.Out) rfl hm e (Rel.sendExtract R.Out)) :=
  compose_sound R (Rel.send R.Out) rfl hm rfl
    (fun S => TreeK.paths_ne_nil S (by simp)) hs (Rel.send_sound R.Out)

end Reduction

end Sigma
