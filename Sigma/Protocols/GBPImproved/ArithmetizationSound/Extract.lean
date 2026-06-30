/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.Pcoef

/-!
# Improved-arithmetization soundness: the tree, the openings, and the candidate witness

The `(n, q+1, 2c+5, 2)`-tree shape of the improved arithmetization (`arithRoundsK'`) with its
path/distinct-challenge lemmas (`mem_paths'`, `chalY/Z/X_inj'`, `path_verify'`); the **binding
interpolation applied to the tree** (`node_open`: the two `r`-children of every `(y,z,x)` node
pin `P_L(x)` to a pure `(𝐆, H)`-opening and `P_R(x)` to a pure `(𝐲⁻¹⊙𝐇, H)`-opening); the
per-bundle inverse-Vandermonde opening coefficients (`bcoefL`/`bcoefR`, via the efficient `vandInv`)
with their correctness (`bundle_openL/R`); the `eq1` recoveries at target `c+1`
(`eqDj'/eqAj'/eqCj'`, `eq1_open'`); the **candidate witness** `candWitness'` (no `aux` fields);
and the unconditional witness clauses 3 and 4 (`clause3_holds'`, `clause4_holds'`).

Note `clause3_holds'`: the *tight* vector-commitment opening `A_C⁽ᵏ⁾ = ⟨a_C⁽ᵏ⁾,𝐆⟩ + γ_C⁽ᵏ⁾·H`
— with **no `𝐇`-component** — holds under acceptance alone, because `node_open` already forced
the `𝐇`-mass of every `P_L`-coefficient to zero. This is exactly where the improved protocol's
tighter relation `R_GBP'` is earned.
-/

namespace Sigma.Protocols.GBPImproved

open Sigma.Protocols.GBP
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The arity-annotated move list of the `(n, q+1, 2c+5, 2)`-tree of the pre-`r` variant.
Stripping the arities recovers `arithMovesPreR F G n c`; the final challenge is the binding
challenge `r`, of arity `2`, on which the conversation ends. -/
@[reducible] def arithMKPreR (F G : Type) [Monoid F] (n q c : ℕ) : List MoveK :=
  [ .msg (G × G × G × G × G), .chal Fˣ n, .chal Fˣ (q + 1),
    .msg (Fin (2 * c + 5) → G), .chal Fˣ (2 * c + 5),
    .msg (F × F × F × (Fin n → F) × (Fin n → F)), .chal Fˣ 2 ]

/-- The `(n, q+1, 2c+5, 2)`-tree of the pre-`r` variant: a closed reduction, so the leaf
decorations are trivial. -/
abbrev ArithTreePreR (F G : Type) [Field F] (n q c : ℕ) :=
  TreeK (arithMKPreR F G n q c) PUnit

section PreRAccessors

variable {n q c : ℕ}

/-- The root message `(A_L, A_R, A_O, S_L, S_R)`. -/
@[reducible] def rootP (T : ArithTreePreR F G n q c) : G × G × G × G × G := T.msgVal

/-- The `y`-challenges. -/
@[reducible] def chalYP (T : ArithTreePreR F G n q c) : Fin n → Fˣ := T.msgSub.chalVal

/-- The `z`-challenges below the `i`-th `y`-branch. -/
@[reducible] def chalZP (T : ArithTreePreR F G n q c) (i : Fin n) : Fin (q + 1) → Fˣ :=
  (T.msgSub.chalSub i).chalVal

/-- The `{T_i}` message below the `(i, j)`-th branch. -/
@[reducible] def tcomP (T : ArithTreePreR F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    Fin (2 * c + 5) → G :=
  ((T.msgSub.chalSub i).chalSub j).msgVal

/-- The `x`-challenges below the `(i, j)`-th branch. -/
@[reducible] def chalXP (T : ArithTreePreR F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    Fin (2 * c + 5) → Fˣ :=
  ((T.msgSub.chalSub i).chalSub j).msgSub.chalVal

/-- The pre-`r` opening `(τ_x, μ_L, μ_R, a, b)` below the `(i, j, l)`-th branch. -/
@[reducible] def openP (T : ArithTreePreR F G n q c) (i : Fin n) (j : Fin (q + 1))
    (l : Fin (2 * c + 5)) : F × F × F × (Fin n → F) × (Fin n → F) :=
  (((T.msgSub.chalSub i).chalSub j).msgSub.chalSub l).msgVal

/-- The binding challenges below the `(i, j, l)`-th branch. -/
@[reducible] def chalRP (T : ArithTreePreR F G n q c) (i : Fin n) (j : Fin (q + 1))
    (l : Fin (2 * c + 5)) : Fin 2 → Fˣ :=
  (((T.msgSub.chalSub i).chalSub j).msgSub.chalSub l).msgSub.chalVal

end PreRAccessors

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `(i, j, l, e)`-th decorated root-to-leaf conversation of an `(n, q+1, 2c+5, 2)`-tree
is one of the tree's `paths`. -/
lemma mem_paths' {n q c : ℕ}
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (l : Fin (2 * c + 5)) (e : Fin 2) :
    ((rootP tree, chalYP tree i, chalZP tree i j, tcomP tree i j, chalXP tree i j l,
      openP tree i j l, chalRP tree i j l e, PUnit.unit), PUnit.unit) ∈ tree.paths := by
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((chalYP tree i, chalZP tree i j, tcomP tree i j, chalXP tree i j l,
    openP tree i j l, chalRP tree i j l e, PUnit.unit), PUnit.unit), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨i, by simp, List.mem_map.2 ⟨((chalZP tree i j, tcomP tree i j,
    chalXP tree i j l, openP tree i j l, chalRP tree i j l e, PUnit.unit),
    PUnit.unit), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨j, by simp, List.mem_map.2 ⟨((tcomP tree i j, chalXP tree i j l,
    openP tree i j l, chalRP tree i j l e, PUnit.unit), PUnit.unit), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((chalXP tree i j l, openP tree i j l, chalRP tree i j l e,
    PUnit.unit), PUnit.unit), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨l, by simp, List.mem_map.2 ⟨((openP tree i j l,
    chalRP tree i j l e, PUnit.unit), PUnit.unit), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((chalRP tree i j l e, PUnit.unit), PUnit.unit), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨e, by simp, List.mem_map.2 ⟨(PUnit.unit, PUnit.unit), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_leaf]
  exact List.mem_singleton.2 rfl

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `y`-challenges of the root, coerced to `F`, are pairwise distinct. -/
lemma chalY_inj' {n q c : ℕ} (tree : ArithTreePreR F G n q c) :
    Function.Injective (fun i => ((chalYP tree i : Fˣ) : F)) :=
  Units.val_injective.comp tree.msgSub.chalInj

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `z`-challenges below a fixed `y`-branch, coerced to `F`, are pairwise distinct. -/
lemma chalZ_inj' {n q c : ℕ} (tree : ArithTreePreR F G n q c) (i : Fin n) :
    Function.Injective (fun j => ((chalZP tree i j : Fˣ) : F)) :=
  Units.val_injective.comp (tree.msgSub.chalSub i).chalInj

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `x`-challenges below a fixed `(y, z)`-branch, coerced to `F`, are pairwise
distinct. -/
lemma chalX_inj' {n q c : ℕ} (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) :
    Function.Injective (fun l => ((chalXP tree i j l : Fˣ) : F)) :=
  Units.val_injective.comp ((tree.msgSub.chalSub i).chalSub j).msgSub.chalInj

/-- Every decorated root-to-leaf conversation of an accepting tree passes the verifier:
the `(i, j, l, e)` path satisfies `arithVerifyPreR s · = true`. -/
lemma path_verify' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (l : Fin (2 * c + 5)) (e : Fin 2) :
    arithVerifyPreR s (rootP tree, chalYP tree i, chalZP tree i j, tcomP tree i j,
      chalXP tree i j l, openP tree i j l, chalRP tree i j l e, PUnit.unit) = true := by
  obtain ⟨st, hst, _⟩ := hacc _ (mem_paths' tree i j l e)
  by_contra hc
  replace hst : (if arithVerifyPreR s (rootP tree, chalYP tree i, chalZP tree i j,
      tcomP tree i j, chalXP tree i j l, openP tree i j l, chalRP tree i j l e,
      PUnit.unit) = true then some PUnit.unit else none) = some st := hst
  rw [if_neg hc] at hst
  simp at hst

/-! ## The binding interpolation applied to the tree -/

/-- **Per-node split openings.** At every `(y, z, x)` node of an accepting tree, the two
`r`-children share the node's pre-`r` message `(τ_x, μ_L, μ_R, a, b)`; the `eq2` identities at
the two distinct `r`'s interpolate (`r_interpolate`) to *exact* split openings:
`P_L(x) = ⟨a, 𝐆⟩ + μ_L·H` (no `𝐇`-component) and `P_R(x) = ⟨b, 𝐲⁻¹⊙𝐇⟩ + μ_R·H` (no
`𝐆`-component). -/
lemma node_open {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (l : Fin (2 * c + 5)) :
    (∑ p : Fin (2 * c + 5), ((chalXP tree i j l : Fˣ) : F) ^ (p : ℕ)
        • PcoefL' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
            (rootP tree).1 (rootP tree).2.2.1 (rootP tree).2.2.2.1 p)
      = msm (openP tree i j l).2.2.2.1 s.gs
        + (openP tree i j l).2.1 • s.h
    ∧ (∑ ℓ : Fin (2 * c + 5), ((chalXP tree i j l : Fˣ) : F) ^ (ℓ : ℕ)
        • PcoefR' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
            (rootP tree).2.1 (rootP tree).2.2.2.2 ℓ)
      = msm (openP tree i j l).2.2.2.2
          (vinv (powers ((chalYP tree i : Fˣ) : F) n) ⊙ s.hs)
        + (openP tree i j l).2.2.1 • s.h := by
  have h0 := arithVerifyPreR_eq2 s (rootP tree).1 (rootP tree).2.1 (rootP tree).2.2.1
    (rootP tree).2.2.2.1 (rootP tree).2.2.2.2 (chalYP tree i) (chalZP tree i j)
    (chalXP tree i j l)
    (chalRP tree i j l 0)
    (tcomP tree i j) _ _ _ _ _ (path_verify' s tree hacc i j l 0)
  have h1 := arithVerifyPreR_eq2 s (rootP tree).1 (rootP tree).2.1 (rootP tree).2.2.1
    (rootP tree).2.2.2.1 (rootP tree).2.2.2.2 (chalYP tree i) (chalZP tree i j)
    (chalXP tree i j l)
    (chalRP tree i j l 1)
    (tcomP tree i j) _ _ _ _ _ (path_verify' s tree hacc i j l 1)
  have hne : ((chalRP tree i j l 0 : Fˣ) : F)
      ≠ ((chalRP tree i j l 1 : Fˣ) : F) := fun hcontra =>
    absurd ((((tree.msgSub.chalSub i).chalSub j).msgSub.chalSub l).msgSub.chalInj
      (Units.ext hcontra)) (by decide)
  exact r_interpolate hne h0 h1

/-! ## The per-bundle opening coefficients -/

/-- The opening coefficients (in the `(𝐆, h)` basis) of the `𝐆`-side verifier coefficient
`PcoefL' p`, inverse-Vandermonde-extracted from the `x`-children's pre-`r` messages at the
`(i, j)` bundle: the `a`-vectors and the `μ_L`-blinders. -/
def bcoefL {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * c + 5)) : (Fin n → F) × F :=
  let vinvm := vandInv (fun l => ((chalXP tree i j l : Fˣ) : F)) p
  (∑ l, vinvm l • (openP tree i j l).2.2.2.1,
   ∑ l, vinvm l • (openP tree i j l).2.1)

/-- The opening coefficients (in the `(𝐲⁻¹⊙𝐇, h)` basis) of the `𝐇`-side verifier coefficient
`PcoefR' ℓ`: the `b`-vectors and the `μ_R`-blinders, inverse-Vandermonde-extracted. -/
def bcoefR {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (ℓ : Fin (2 * c + 5)) : (Fin n → F) × F :=
  let vinvm := vandInv (fun l => ((chalXP tree i j l : Fˣ) : F)) ℓ
  (∑ l, vinvm l • (openP tree i j l).2.2.2.2,
   ∑ l, vinvm l • (openP tree i j l).2.2.1)

/-- **`𝐆`-side extraction correctness.** Under acceptance, `bcoefL i j p` is a genuine opening
of `PcoefL' p` in the `(𝐆, h)` basis — with no `𝐇`-component at all. -/
lemma bundle_openL {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * c + 5)) :
    PcoefL' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
        (rootP tree).1 (rootP tree).2.2.1 (rootP tree).2.2.2.1 p
      = msm (bcoefL s tree i j p).1 s.gs + (bcoefL s tree i j p).2 • s.h := by
  have hext := coeff_open s.gs s.h
    (PcoefL' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
      (rootP tree).1 (rootP tree).2.2.1 (rootP tree).2.2.2.1)
    (fun l => ((chalXP tree i j l : Fˣ) : F)) (chalX_inj' tree i j)
    (fun l => (openP tree i j l).2.2.2.1)
    (fun l => (openP tree i j l).2.1)
    (fun l => (node_open s tree hacc i j l).1) p
  rw [hext]; simp only [bcoefL, vandInv_eq (chalX_inj' tree i j)]

/-- **`𝐇`-side extraction correctness.** Under acceptance, `bcoefR i j ℓ` is a genuine opening
of `PcoefR' ℓ` in the `(𝐲⁻¹⊙𝐇, h)` basis — with no `𝐆`-component at all. -/
lemma bundle_openR {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (ℓ : Fin (2 * c + 5)) :
    PcoefR' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
        (rootP tree).2.1 (rootP tree).2.2.2.2 ℓ
      = msm (bcoefR s tree i j ℓ).1 (vinv (powers ((chalYP tree i : Fˣ) : F) n) ⊙ s.hs)
        + (bcoefR s tree i j ℓ).2 • s.h := by
  have hext := coeff_open (vinv (powers ((chalYP tree i : Fˣ) : F) n) ⊙ s.hs) s.h
    (PcoefR' s ((chalYP tree i : Fˣ) : F) ((chalZP tree i j : Fˣ) : F)
      (rootP tree).2.1 (rootP tree).2.2.2.2)
    (fun l => ((chalXP tree i j l : Fˣ) : F)) (chalX_inj' tree i j)
    (fun l => (openP tree i j l).2.2.2.2)
    (fun l => (openP tree i j l).2.2.1)
    (fun l => (node_open s tree hacc i j l).2) ℓ
  rw [hext]; simp only [bcoefR, vandInv_eq (chalX_inj' tree i j)]

/-! ## `eq1` recoveries at target `c+1` -/

/-- The `eq1` special degree-`(c+1)` coefficient `D` (the public `g`-part `δ − w_c`) at bundle
`(i, j)`. -/
def eqDj' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : F :=
  ip (hadamard (vinv (powers ((chalYP tree i : Fˣ) : F) n))
        (((chalZP tree i j : Fˣ) : F)
          • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WR)))
      (((chalZP tree i j : Fˣ) : F)
        • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WL))
    - ((chalZP tree i j : Fˣ) : F)
        * ip (powers ((chalZP tree i j : Fˣ) : F) q) s.cc

/-- The recovered `eq1` `g`-coefficient of `⟨w_V, V⟩` at bundle `(i, j)`: `D` minus the
inverse-Vandermonde of the node inner products `⟨a, b⟩`. -/
def eqAj' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : F :=
  eqDj' s tree i j - ∑ l, vandInv (fun l => ((chalXP tree i j l : Fˣ) : F)) ⟨c + 1, by omega⟩ l
    * ip (openP tree i j l).2.2.2.1
        (openP tree i j l).2.2.2.2

/-- The recovered `eq1` `h`-coefficient of `⟨w_V, V⟩` at bundle `(i, j)` (inverse-Vandermonde
of the node blinders `τ_x`). -/
def eqCj' {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (i : Fin n) (j : Fin (q + 1)) : F :=
  -∑ l, vandInv (fun l => ((chalXP tree i j l : Fˣ) : F)) ⟨c + 1, by omega⟩ l
    * (openP tree i j l).1

/-- **eq1 opening at an arbitrary bundle.** The aggregate `msm (z·(𝐳·W_V)) V` is the
`(g, h)`-combination `eqAj'·g + eqCj'·h` recovered from the bundle's `x`-children. -/
lemma eq1_open' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) :
    msm (((chalZP tree i j : Fˣ) : F)
        • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV)) s.V
      = eqAj' s tree i j • s.g + eqCj' s tree i j • s.h := by
  have heq1 := fun (l : Fin (2 * c + 5)) =>
    arithVerifyPreR_eq1 s (rootP tree).1 (rootP tree).2.1 (rootP tree).2.2.1
      (rootP tree).2.2.2.1 (rootP tree).2.2.2.2 (chalYP tree i)
      (chalZP tree i j) (chalXP tree i j l)
      (chalRP tree i j l 0)
      (tcomP tree i j) _ _ _ _ _ (path_verify' s tree hacc i j l 0)
  rw [eqAj', eqCj', eqDj']
  simp only [vandInv_eq (chalX_inj' tree i j)]
  exact eq1_special_extract' (by omega) s.g s.h
    (msm (((chalZP tree i j : Fˣ) : F)
      • (powers ((chalZP tree i j : Fˣ) : F) q ᵥ* s.WV)) s.V) _
    (fun l => ((chalXP tree i j l : Fˣ) : F)) (chalX_inj' tree i j)
    _ _ _ heq1

/-! ## The candidate witness -/

/-- **The candidate witness, recovered (computably) from the transcript tree.** Every field is a
fixed inverse-Vandermonde combination of the pre-`r` node data of the `y`-branch `⟨0, hn⟩` (the
prover's vectors `a, b` and blinders `μ_L, μ_R, τ_x`), plus the computed left inverse of `W_V`
for the `v, γ` openings. No discrete-log computation and no `Classical.choice` — a
polynomial-time linear-algebraic function of the tree (interpolation by the Lagrange-form
`Sigma.vandInv`; `W_V` inverted by Gaussian elimination, `Sigma.gaussLeftInv`). For `n = 0` the
tree is path-free, so the witness is irrelevant and set to `0`.

* `aL` reads off the `bcoefL` slot `0` minus the public `w_R∘y⁻¹`;
* `aR` reads off the `bcoefR` slot `c+1` minus the public `w_L`, rescaled by `y⁻¹`;
* `aO`, `aC⁽ᵏ⁾`, `γ_C⁽ᵏ⁾` read off the `bcoefL` slots `1` and `k+2` (`𝐆`- and `h`-parts);
* `v, γ` come from the `eq1` `(c+1)`-coefficients across the `q+1` `z`-children,
  `z`-interpolated and hit with the `W_V` left inverse. -/
def candWitness' {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c) :
    Witness F n m c :=
  if hn : 0 < n then
    let yinv : Fin n → F := vinv (powers ((chalYP tree ⟨0, hn⟩ : Fˣ) : F) n)
    let zch : Fin (q + 1) → F := fun j => ((chalZP tree ⟨0, hn⟩ j : Fˣ) : F)
    let wR' : Fin n → F := zch 0 • (powers (zch 0) q ᵥ* s.WR)
    let wL' : Fin n → F := zch 0 • (powers (zch 0) q ᵥ* s.WL)
    let cL : Fin (2 * c + 5) → (Fin n → F) × F := fun p => bcoefL s tree ⟨0, hn⟩ 0 p
    let cR : Fin (2 * c + 5) → (Fin n → F) × F := fun p => bcoefR s tree ⟨0, hn⟩ 0 p
    let pAC : Fin c → Fin (2 * c + 5) := fun k => ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩
    let Aj : Fin (q + 1) → F := fun j => eqAj' s tree ⟨0, hn⟩ j
    let Cj : Fin (q + 1) → F := fun j => eqCj' s tree ⟨0, hn⟩ j
    let Mmat : Matrix (Fin m) (Fin q) F := gaussLeftInv s.WV
    ⟨fun t => (cL ⟨0, by omega⟩).1 t - wR' t * yinv t,
     fun t => ((cR ⟨c + 1, by omega⟩).1 t - wL' t) * yinv t,
     (cL ⟨1, by omega⟩).1,
     fun k => ∑ ℓ : Fin q, Mmat k ℓ * (∑ j, vandInv zch ℓ.succ j * Aj j),
     fun k => ∑ ℓ : Fin q, Mmat k ℓ * (∑ j, vandInv zch ℓ.succ j * Cj j),
     fun k => (cL (pAC k)).1,
     fun k => (cL (pAC k)).2⟩
  else ⟨0, 0, 0, 0, 0, 0, 0⟩

/-! ## Witness clauses 3 and 4 hold under acceptance -/

/-- **Clause 3 holds under acceptance — in the tight, `aux`-free form.** The vector-commitment
opening `A_C⁽ᵏ⁾ = ⟨a_C⁽ᵏ⁾, 𝐆⟩ + γ_C⁽ᵏ⁾·H` is satisfied by the recovered `candWitness'`
fields: they are the `(0,0)`-bundle `bcoefL` opening of `PcoefL' (k+2) = A_C⁽ᵏ⁾`
(`bundle_openL` + `PcoefL'_AC`), which the binding interpolation already stripped of any
`𝐇`-component. -/
lemma clause3_holds' {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree) (k : Fin c) :
    s.AC k = msm ((candWitness' s tree).aC k) s.gs + (candWitness' s tree).γC k • s.h := by
  have hp := bundle_openL s tree hacc ⟨0, hn⟩ 0 ⟨(k : ℕ) + 2, by have := k.isLt; omega⟩
  rw [PcoefL'_AC] at hp
  simp only [candWitness', dif_pos hn]
  exact hp

/-- **Clause 4 holds under acceptance** (with `W_V` full column rank). The scalar-commitment
opening `V_k = v_k·g + γ_k·h` is satisfied by the recovered `candWitness'` fields: the `eq1`
`(c+1)`-coefficients give `msm w_V V = eqAj'·g + eqCj'·h` at each `z`-child (`eq1_open'`), and
`V_recover` (with the Gaussian-elimination left inverse `gaussLeftInv s.WV`) inverts the
`z`-Vandermonde and `W_V` to the per-`k` opening. -/
lemma clause4_holds' {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTreePreR F G n q c)
    (hacc : (arithRedPreR (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMKPreR F G n q c) rfl s tree) (k : Fin m) :
    s.V k = (candWitness' s tree).v k • s.g + (candWitness' s tree).γ k • s.h := by
  have hI : ∀ j, msm (((chalZP tree ⟨0, hn⟩ j : Fˣ) : F)
        • (powers ((chalZP tree ⟨0, hn⟩ j : Fˣ) : F) q ᵥ* s.WV)) s.V
      = eqAj' s tree ⟨0, hn⟩ j • s.g + eqCj' s tree ⟨0, hn⟩ j • s.h :=
    fun j => eq1_open' s tree hacc ⟨0, hn⟩ j
  have hV := V_recover s (fun j => ((chalZP tree ⟨0, hn⟩ j : Fˣ) : F))
    (chalZ_inj' tree ⟨0, hn⟩) (gaussLeftInv s.WV) (gaussLeftInv_correct s.WV s.hWV)
    (fun j => eqAj' s tree ⟨0, hn⟩ j) (fun j => eqCj' s tree ⟨0, hn⟩ j) hI k
  simp only [candWitness', dif_pos hn, vandInv_eq (chalZ_inj' tree ⟨0, hn⟩)]
  exact hV

end Sigma.Protocols.GBPImproved
