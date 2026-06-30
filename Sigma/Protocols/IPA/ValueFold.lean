/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.Protocols.IPA.Relation
import Sigma.Protocols.IPA.NodeExtract

/-!
# The value-folding adaptor

The arithmetization reduces the GB relation to the *inner-product relation with the value made
explicit* (report `R_IP`):
`P = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩ + μ·H  ∧  t̂ = ⟨a, b⟩`,
with `μ, t̂` carried as statement components. The inner-product towers
(`Sigma.Protocols.IPA.ipaRed`, `Sigma.Protocols.IPAImproved.ipaRed`) instead prove the
*folded* relation `relIP : P' = ⟨a, 𝐠⟩ + ⟨b, 𝐡⟩ + ⟨a, b⟩·u`.

The bridge between them is the report's **"Folding in the Value"** round: sample `ξ ∈ Fˣ`, set
`u := ξ·G` and `P' := P − μ·H + t̂·u` (`foldStmt`), then run an inner-product argument on the
folded statement. This file proves the *soundness* of that one round: from inner-product
witnesses at **two distinct** challenges `ξ ≠ ξ'`, the extractor `vfCombine` recovers a witness
for `R_IP` (i.e. `t̂ = ⟨a,b⟩` is forced) *or* a non-trivial discrete-log relation among
`𝐠 ⧺ 𝐡 ⧺ [G]` (`vfCombine_valid`).

This is the local, per-leaf binding of `t̂` to `⟨a,b⟩`: the `ξ`-randomized `u` separates the
value `t̂` from any stray `G`-component, so the round needs only arity 2. It is the per-round
soundness content of the reveal reductions `Sigma.Protocols.GBP.revealFold` and
`Sigma.Protocols.GBPImproved.revealT` that link the arithmetizations to the inner-product
towers.
-/

namespace Sigma.Protocols.IPA

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-! ## The `R_IP` statement and relation

The statement `IPStatementV` and relation `relIPV` are defined in `Sigma.Protocols.IPA.Relation`. -/

/-- **Folding in the value** at challenge `ξ`: `u := ξ·G`, `P' := P − μ·H + t̂·u`. The result is
the folded inner-product statement the argument runs on. -/
def foldStmt {k : ℕ} (x : IPStatementV F G k) (ξ : F) : IPStatement F G k where
  P := x.P - x.mu • x.hgen + x.tHat • (ξ • x.ggen)
  gs := x.gs
  hs := x.hs
  u := ξ • x.ggen

/-! ## Break generators and the implied opening -/

/-- Auxiliary inner-product statement carrying `(𝐠, 𝐡, G)` as `(gs, hs, u)`; only its generator
family is used. -/
def vAux {k : ℕ} (x : IPStatementV F G k) : IPStatement F G k := ⟨0, x.gs, x.hs, x.ggen⟩

/-- The break generator family for the value-fold: `𝐠 ⧺ 𝐡 ⧺ [G]`. -/
def vGens {k : ℕ} (x : IPStatementV F G k) : Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → G :=
  ipGens (vAux x)

/-- The break predicate: a non-trivial discrete-log relation among `vGens x`. -/
def brkV {k : ℕ} (x : IPStatementV F G k) (v : Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F) : Prop :=
  IsNontrivialDLRel (vGens x) v

omit [DecidableEq F] [DecidableEq G] in
@[simp] lemma msm_vGens {k : ℕ} (x : IPStatementV F G k) (vg vh : Fin (2 ^ (k + 1)) → F) (vu : F) :
    msm (ipRelVec vg vh vu) (vGens x) = msm vg x.gs + msm vh x.hs + vu • x.ggen := by
  rw [vGens, msm_ipRelVec]; rfl

/-- The opening of `P − μ·H` against `vGens x` that a folded-relation witness `(a,b)` at challenge
`ξ` implies: coefficients `a` on `𝐠`, `b` on `𝐡`, and `(⟨a,b⟩ − t̂)·ξ` on `G`. -/
def vOpen {k : ℕ} (x : IPStatementV F G k) (a b : Fin (2 ^ (k + 1)) → F) (ξ : F) :
    Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F :=
  ipRelVec a b ((ip a b - x.tHat) * ξ)

omit [DecidableEq F] in
/-- A folded-relation witness at `ξ` is exactly an opening of `P − μ·H` against `vGens x` by
`vOpen x a b ξ`. -/
lemma relIP_foldStmt_iff {k : ℕ} (x : IPStatementV F G k) (a b : Fin (2 ^ (k + 1)) → F) (ξ : F) :
    relIP (foldStmt x ξ) (a, b) = true ↔
      msm (vOpen x a b ξ) (vGens x) = x.P - x.mu • x.hgen := by
  simp only [relIP, foldStmt, vOpen, msm_vGens, decide_eq_true_eq]
  constructor
  · intro h; linear_combination (norm := module) -h
  · intro h; linear_combination (norm := module) -h

/-! ## Injectivity of `ipRelVec` (to read back the three blocks) -/

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq F] in
lemma ipRelVec_inj {k : ℕ} {vg vg' vh vh' : Fin (2 ^ (k + 1)) → F} {vu vu' : F}
    (h : ipRelVec vg vh vu = ipRelVec vg' vh' vu') : vg = vg' ∧ vh = vh' ∧ vu = vu' := by
  refine ⟨funext fun i => ?_, funext fun i => ?_, ?_⟩
  · have := congrFun h (Fin.castAdd 1 (Fin.castAdd (2 ^ (k + 1)) i))
    simpa only [ipRelVec, Fin.append_left] using this
  · have := congrFun h (Fin.castAdd 1 (Fin.natAdd (2 ^ (k + 1)) i))
    simpa only [ipRelVec, Fin.append_left, Fin.append_right] using this
  · have := congrFun h (Fin.natAdd (2 ^ (k + 1) + 2 ^ (k + 1)) 0)
    simpa only [ipRelVec, Fin.append_right, Matrix.cons_val_fin_one] using this

/-! ## The value-fold combination -/

/-- **The value-fold extractor.** From two folded-relation witnesses at distinct challenges
`ξ ≠ ξ'`, compare the implied openings: if they agree, the common witness satisfies `R_IP`
(forcing `t̂ = ⟨a,b⟩`); otherwise their difference is a non-trivial generator relation. -/
def vfCombine {k : ℕ} (x : IPStatementV F G k) (ξ ξ' : F)
    (ab ab' : (Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F)) :
    ((Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F)) ⊕
      (Fin (2 ^ (k + 1) + 2 ^ (k + 1) + 1) → F) :=
  let c := vOpen x ab.1 ab.2 ξ
  let c' := vOpen x ab'.1 ab'.2 ξ'
  if c = c' then Sum.inl ab else Sum.inr (c - c')

/-- **Soundness of the value-fold.** From folded-relation witnesses at two distinct challenges, the
extractor outputs either an `R_IP` witness or a non-trivial discrete-log relation among
`𝐠 ⧺ 𝐡 ⧺ [G]`. The `t̂ = ⟨a,b⟩` binding falls out from the `ξ`-randomization: the implied
`G`-coefficient `(⟨a,b⟩ − t̂)·ξ` agreeing across `ξ ≠ ξ'` forces `⟨a,b⟩ = t̂`. -/
lemma vfCombine_valid {k : ℕ} (x : IPStatementV F G k) (ξ ξ' : F) (hξξ' : ξ ≠ ξ')
    (ab ab' : (Fin (2 ^ (k + 1)) → F) × (Fin (2 ^ (k + 1)) → F))
    (hξ : relIP (foldStmt x ξ) ab = true) (hξ' : relIP (foldStmt x ξ') ab' = true) :
    (∀ w, vfCombine x ξ ξ' ab ab' = Sum.inl w → relIPV x w = true) ∧
    (∀ v, vfCombine x ξ ξ' ab ab' = Sum.inr v → brkV x v) := by
  have hc : msm (vOpen x ab.1 ab.2 ξ) (vGens x) = x.P - x.mu • x.hgen :=
    (relIP_foldStmt_iff x ab.1 ab.2 ξ).mp hξ
  have hc' : msm (vOpen x ab'.1 ab'.2 ξ') (vGens x) = x.P - x.mu • x.hgen :=
    (relIP_foldStmt_iff x ab'.1 ab'.2 ξ').mp hξ'
  have hcoll : msm (vOpen x ab.1 ab.2 ξ) (vGens x) = msm (vOpen x ab'.1 ab'.2 ξ') (vGens x) :=
    hc.trans hc'.symm
  by_cases hcc : vOpen x ab.1 ab.2 ξ = vOpen x ab'.1 ab'.2 ξ'
  · -- Openings agree: the common witness satisfies `R_IP`.
    have hvf : vfCombine x ξ ξ' ab ab' = Sum.inl ab := by
      simp only [vfCombine]; rw [if_pos hcc]
    rw [hvf]
    refine ⟨fun w hw => ?_, fun v hv => by simp at hv⟩
    obtain rfl : ab = w := by simpa using hw
    -- Read off the three blocks of `c = c'`.
    simp only [vOpen] at hcc
    obtain ⟨ha, hb, hu⟩ := ipRelVec_inj hcc
    have hipeq : ip ab.1 ab.2 = ip ab'.1 ab'.2 := by rw [ha, hb]
    -- The `ξ`-randomized `G`-coefficient agreeing across `ξ ≠ ξ'` forces `⟨a,b⟩ = t̂`.
    have hthat : ip ab.1 ab.2 = x.tHat := by
      have hmul : (ip ab.1 ab.2 - x.tHat) * ξ = (ip ab.1 ab.2 - x.tHat) * ξ' := by
        rw [hu, hipeq]
      have hz : (ip ab.1 ab.2 - x.tHat) * (ξ - ξ') = 0 := by linear_combination hmul
      rcases mul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h) hξξ'
    -- With `⟨a,b⟩ = t̂` the `G`-coefficient vanishes, leaving the bare commitment opening.
    have hcoeff : (ip ab.1 ab.2 - x.tHat) * ξ = 0 := by rw [hthat]; ring
    have hopen : msm ab.1 x.gs + msm ab.2 x.hs = x.P - x.mu • x.hgen := by
      have h := hc
      rw [vOpen, hcoeff, msm_vGens] at h
      simpa using h
    have hgoal : x.P = msm ab.1 x.gs + msm ab.2 x.hs + x.mu • x.hgen ∧ x.tHat = ip ab.1 ab.2 :=
      ⟨by rw [hopen]; abel, hthat.symm⟩
    simpa only [relIPV, decide_eq_true_eq] using hgoal
  · -- Openings differ: their difference is a non-trivial relation.
    have hvf : vfCombine x ξ ξ' ab ab'
        = Sum.inr (vOpen x ab.1 ab.2 ξ - vOpen x ab'.1 ab'.2 ξ') := by
      simp only [vfCombine]; rw [if_neg hcc]
    rw [hvf]
    refine ⟨fun w hw => by simp at hw, fun v hv => ?_⟩
    obtain rfl : vOpen x ab.1 ab.2 ξ - vOpen x ab'.1 ab'.2 ξ' = v := by simpa using hv
    exact isNontrivialDLRel_sub_of_openings hcc hcoll

end Sigma.Protocols.IPA
