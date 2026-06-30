/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBP.ArithmetizationSound.Pcoef
import Sigma.Utils.LeftInverse

/-!
# Arithmetization soundness: the extractor data and the per-bundle `(★)`

The `(n, q+1, 2n'+3)`-tree shape (`arithMK`) and its distinct-challenge lemmas
(`chalX/Y/Z_inj`, `path_verify`); the explicitly-extracted opening coefficients and candidate
witness (`bcoef`, `eqDj/eqAj/eqCj`, `candWitness` — interpolating with the efficient
`Sigma.vandInv` and inverting `W_V` by Gaussian elimination, `Sigma.gaussLeftInv`); and the
per-bundle relation `(★)` assembled from the combined `tcoeff`/`eq1` identity
(`star_at_bundle`, `conv_eq`).
-/

namespace Sigma.Protocols.GBP

open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The arity-annotated move list of the `(n, q+1, 2·nPrime c+3)`-tree. Stripping the
arities recovers `arithMoves F G c`; the adjacent `y, z` challenges need no separating
message. -/
@[reducible] def arithMK (F G : Type) [Monoid F] (n q c : ℕ) : List MoveK :=
  [ .msg (G × G × G), .chal Fˣ n, .chal Fˣ (q + 1),
    .msg (Fin (3 * c + 5) → G), .chal Fˣ (2 * nPrime c + 3) ]

/-- The decorated `(n, q+1, 2·nPrime c+3)`-tree of the arithmetization reduction:
conversations over `arithMoves`, decorated with the (never sent) openings. -/
abbrev ArithTree (F G : Type) [Field F] (n q c : ℕ) :=
  TreeK (arithMK F G n q c) (Opening F n)

section Accessors

variable {n q c : ℕ}

omit [Field F] in
/-- The root message `(A_I, A_O, S)`. -/
@[reducible] def rootT [Field F] (T : ArithTree F G n q c) : G × G × G := T.msgVal

/-- The `y`-challenges. -/
@[reducible] def chalY (T : ArithTree F G n q c) : Fin n → Fˣ := T.msgSub.chalVal

/-- The `z`-challenges below the `i`-th `y`-branch. -/
@[reducible] def chalZ (T : ArithTree F G n q c) (i : Fin n) : Fin (q + 1) → Fˣ :=
  (T.msgSub.chalSub i).chalVal

/-- The dense `{T_i}` message below the `(i, j)`-th `(y, z)`-branch. -/
@[reducible] def tcomT (T : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    Fin (3 * c + 5) → G :=
  ((T.msgSub.chalSub i).chalSub j).msgVal

/-- The `x`-challenges below the `(i, j)`-th branch. -/
@[reducible] def chalX (T : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) :
    Fin (2 * nPrime c + 3) → Fˣ :=
  ((T.msgSub.chalSub i).chalSub j).msgSub.chalVal

/-- The opening decorating the `(i, j, l)`-th leaf. -/
@[reducible] def leafO (T : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (l : Fin (2 * nPrime c + 3)) : Opening F n :=
  (((T.msgSub.chalSub i).chalSub j).msgSub.chalSub l).leafVal

/-- The `(i, j, l)`-th conversation of the tree. -/
@[reducible] def pathConv (T : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1))
    (l : Fin (2 * nPrime c + 3)) : Conversation (arithMoves F G c) :=
  (rootT T, chalY T i, chalZ T i j, tcomT T i j, chalX T i j l, PUnit.unit)

end Accessors

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `(i, j, l)`-th decorated root-to-leaf conversation of an `(n, q+1, 2·nPrime c+3)`-tree,
written via the accessors, is one of the tree's `paths`. -/
lemma mem_paths {n q c : ℕ} (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (l : Fin (2 * nPrime c + 3)) :
    (pathConv tree i j l, leafO tree i j l) ∈ tree.paths := by
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((chalY tree i, chalZ tree i j, tcomT tree i j, chalX tree i j l,
    PUnit.unit), leafO tree i j l), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨i, by simp, List.mem_map.2 ⟨((chalZ tree i j, tcomT tree i j,
    chalX tree i j l, PUnit.unit), leafO tree i j l), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨j, by simp, List.mem_map.2 ⟨((tcomT tree i j, chalX tree i j l,
    PUnit.unit), leafO tree i j l), ?_, rfl⟩⟩
  rw [TreeK.paths_eq_msg]
  refine List.mem_map.2 ⟨((chalX tree i j l, PUnit.unit), leafO tree i j l), ?_, rfl⟩
  rw [TreeK.paths_eq_chal]
  refine List.mem_flatMap.2 ⟨l, by simp, List.mem_map.2 ⟨(PUnit.unit, leafO tree i j l),
    ?_, rfl⟩⟩
  rw [TreeK.paths_eq_leaf]
  exact List.mem_singleton.2 rfl

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `y`-challenges of the root, coerced to `F`, are pairwise distinct. -/
lemma chalY_inj {n q c : ℕ} (tree : ArithTree F G n q c) :
    Function.Injective (fun i => ((chalY tree i : Fˣ) : F)) :=
  Units.val_injective.comp tree.msgSub.chalInj

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `z`-challenges below a fixed `y`-branch, coerced to `F`, are pairwise distinct. -/
lemma chalZ_inj {n q c : ℕ} (tree : ArithTree F G n q c) (i : Fin n) :
    Function.Injective (fun j => ((chalZ tree i j : Fˣ) : F)) :=
  Units.val_injective.comp (tree.msgSub.chalSub i).chalInj

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The `x`-challenges below a fixed `(y, z)`-branch, coerced to `F`, are pairwise distinct. -/
lemma chalX_inj {n q c : ℕ} (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) :
    Function.Injective (fun l => ((chalX tree i j l : Fˣ) : F)) :=
  Units.val_injective.comp ((tree.msgSub.chalSub i).chalSub j).msgSub.chalInj

/-- Every decorated root-to-leaf conversation of an accepting tree is accepting: the
`(i, j, l)` opening satisfies both verifier equations at the derived statement. -/
lemma path_verify {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (hacc : (arithRed (F := F) (G := G) n q m c).AcceptingTree
      (mk := arithMK F G n q c) rfl s tree)
    (i : Fin n) (j : Fin (q + 1)) (l : Fin (2 * nPrime c + 3)) :
    (relArith F G n).rel (arithOut s (pathConv tree i j l)) (leafO tree i j l) = true := by
  obtain ⟨st, hst, hrel⟩ := hacc _ (mem_paths tree i j l)
  simp only [arithRed] at hst
  obtain rfl := Option.some.inj hst
  exact hrel

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier coefficient at degree `n'+1` is the masking commitment `S`. -/
lemma Pcoef_S {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G) :
    Pcoef s y z AI AO Scom ⟨nPrime c + 1, by omega⟩ = Scom := by
  have hwc : ∀ k : Fin c, (nPrime c + 1 = (k : ℕ) + 1) = False := fun k =>
    eq_false (by have := k.isLt; simp only [nPrime]; omega)
  have hac : ∀ k : Fin c, (nPrime c + 1 = nPrime c - ((k : ℕ) + 1)) = False := fun k =>
    eq_false (by have := k.isLt; simp only [nPrime]; omega)
  simp only [Pcoef,
    show (nPrime c + 1 = 0) = False from eq_false (by omega),
    show (nPrime c + 1 = c + 1) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c + 1 = nPrime c) = False from eq_false (by omega),
    hwc, hac, if_false, Finset.sum_const_zero, if_true, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- `msm` against the rescaled generators `b ⊙ gs` folds the scaling into the coefficients. -/
lemma msm_vsmul {ι : Type*} [Fintype ι] (a b : ι → F) (gs : ι → G) :
    msm a (b ⊙ gs) = msm (fun i => a i * b i) gs := by
  simp only [msm, vsmul, smul_smul]

omit [DecidableEq F] [DecidableEq G] in
/-- **Opening a commitment from its `Pcoef`-form** (`A_I` case): if `C + WtL + WtR` opens in the
`(𝐆, h', h)` basis, then `C` itself opens in the `(𝐆, 𝐇, h)` basis. -/
lemma commit_open {n q m c : ℕ} (s : Statement F G n q m c) (C : G) (Lp Rp : Fin n → F) (Mp : F)
    (yinv wL wR' : Fin n → F)
    (hp : C + msm wL (yinv ⊙ s.hs) + msm wR' s.gs
        = msm Lp s.gs + msm Rp (yinv ⊙ s.hs) + Mp • s.h) :
    ∃ aL aR : Fin n → F, ∃ α : F, C = msm aL s.gs + msm aR s.hs + α • s.h := by
  refine ⟨Lp - wR', (fun i => Rp i * yinv i) - (fun i => wL i * yinv i), Mp, ?_⟩
  have hC : C = msm Lp s.gs + msm Rp (yinv ⊙ s.hs) + Mp • s.h
              - msm wL (yinv ⊙ s.hs) - msm wR' s.gs := by rw [← hp]; abel
  rw [hC]; simp only [msm_vsmul, msm_sub_left]; module

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier coefficient at degree `n'` is the output commitment `A_O`. -/
lemma Pcoef_AO {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G) :
    Pcoef s y z AI AO Scom ⟨nPrime c, by omega⟩ = AO := by
  have hwc : ∀ k : Fin c, (nPrime c = (k : ℕ) + 1) = False := fun k =>
    eq_false (by have := k.isLt; simp only [nPrime]; omega)
  have hac : ∀ k : Fin c, (nPrime c = nPrime c - ((k : ℕ) + 1)) = False := fun k =>
    eq_false (by have := k.isLt; simp only [nPrime]; omega)
  simp only [Pcoef,
    show (nPrime c = 0) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c = c + 1) = False from eq_false (by simp only [nPrime]; omega),
    show (nPrime c = nPrime c + 1) = False from eq_false (by omega),
    hwc, hac, if_false, Finset.sum_const_zero, if_true, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- The verifier coefficient at degree `c+1` is `A_I + WtL + WtR`. -/
lemma Pcoef_AI {n q m c : ℕ} (s : Statement F G n q m c) (y z : F) (AI AO Scom : G) :
    Pcoef s y z AI AO Scom ⟨c + 1, by simp only [nPrime]; omega⟩
      = AI + msm (z • (powers z q ᵥ* s.WL)) (vinv (powers y n) ⊙ s.hs)
          + msm (hadamard (vinv (powers y n)) (z • (powers z q ᵥ* s.WR))) s.gs := by
  have hwc : ∀ k : Fin c, (c + 1 = (k : ℕ) + 1) = False := fun k =>
    eq_false (by have := k.isLt; omega)
  have hac : ∀ k : Fin c, (c + 1 = nPrime c - ((k : ℕ) + 1)) = False := fun k =>
    eq_false (by have := k.isLt; simp only [nPrime]; omega)
  simp only [Pcoef,
    show (c + 1 = 0) = False from eq_false (by omega),
    show (c + 1 = nPrime c) = False from eq_false (by simp only [nPrime]; omega),
    show (c + 1 = nPrime c + 1) = False from eq_false (by simp only [nPrime]; omega),
    hwc, hac, if_false, Finset.sum_const_zero, if_true, zero_add, add_zero]

omit [DecidableEq F] [DecidableEq G] in
/-- **eq1 `n'`-coefficient.** From the `eq1` family at distinct `x`, the aggregate `msm wV V`
(appearing in the special `n'`-coefficient `D·g − msm wV V`) is a `(g, h)`-combination. -/
lemma eq1_special_extract {n q m c : ℕ} (s : Statement F G n q m c) (D : F) (wV : Fin m → F)
    (x : Fin (2 * nPrime c + 3) → F) (hx : Function.Injective x)
    (a b : Fin (2 * nPrime c + 3) → (Fin n → F)) (τx : Fin (2 * nPrime c + 3) → F)
    (T : Fin (2 * nPrime c + 3) → G)
    (heq : ∀ l, ip (a l) (b l) • s.g + τx l • s.h
        = ∑ r : Fin (2 * nPrime c + 3), (x l) ^ (r : ℕ)
            • (if (r : ℕ) = nPrime c then (D • s.g - msm wV s.V) else T r)) :
    msm wV s.V
      = (D - ∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, by omega⟩ l * ip (a l) (b l)) • s.g
        + (-∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, by omega⟩ l * τx l) • s.h := by
  have hnp : nPrime c < 2 * nPrime c + 3 := by omega
  have hco := vandermonde_coeff x hx _ _ (fun l => (heq l).symm) ⟨nPrime c, hnp⟩
  rw [if_pos rfl] at hco
  simp only [smul_add, Finset.sum_add_distrib, smul_smul, ← Finset.sum_smul] at hco
  have h2 : msm wV s.V
      = D • s.g - ((∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, hnp⟩ l * ip (a l) (b l)) • s.g
          + (∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, hnp⟩ l * τx l) • s.h) := by
    rw [← hco]; abel
  rw [h2]; module

/-- The opening coefficients (in the `(𝐆, h', h)` basis) of the verifier commitment `Pcoef p`,
inverse-Vandermonde-extracted from the `x`-leaves of the `(i, j)` bundle. -/
def bcoef {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree F G n q c)
    (i : Fin n) (j : Fin (q + 1)) (p : Fin (2 * nPrime c + 3)) :
    (Fin n → F) × (Fin n → F) × F :=
  let vinvm := vandInv (fun l => ((chalX tree i j l : Fˣ) : F)) p
  let lf := fun l => leafO tree i j l
  (∑ l, vinvm l • (lf l).2.2.1, ∑ l, vinvm l • (lf l).2.2.2, ∑ l, vinvm l • (lf l).2.1)

/-- The `eq1` special degree-`n'` coefficient `D` (the public `g`-part `δ − wc`) at bundle `(i,j)`. -/
def eqDj {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) : F :=
  ip (hadamard (vinv (powers ((chalY tree i : Fˣ) : F) n))
        (((chalZ tree i j : Fˣ) : F)
          • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WR)))
      (((chalZ tree i j : Fˣ) : F)
        • (powers ((chalZ tree i j : Fˣ) : F) q ᵥ* s.WL))
    - ((chalZ tree i j : Fˣ) : F)
        * ip (powers ((chalZ tree i j : Fˣ) : F) q) s.cc

/-- The recovered `eq1` `g`-coefficient of `msm wV V` at bundle `(i,j)`: `D` minus the
inverse-Vandermonde of the leaf inner products `⟨a,b⟩`. -/
def eqAj {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) : F :=
  eqDj s tree i j - ∑ l, vandInv (fun l => ((chalX tree i j l : Fˣ) : F)) ⟨nPrime c, by omega⟩ l
    * ip (leafO tree i j l).2.2.1
        (leafO tree i j l).2.2.2

/-- The recovered `eq1` `h`-coefficient of `msm wV V` at bundle `(i,j)` (inverse-Vandermonde of the
leaf blinders `τₓ`). -/
def eqCj {n q m c : ℕ} (_s : Statement F G n q m c)
    (tree : ArithTree F G n q c) (i : Fin n) (j : Fin (q + 1)) : F :=
  -∑ l, vandInv (fun l => ((chalX tree i j l : Fˣ) : F)) ⟨nPrime c, by omega⟩ l
    * (leafO tree i j l).1

/-- **Step 5 (the candidate witness), recovered (computably) from the transcript tree.** Every field
is a fixed inverse-Vandermonde combination of the *scalar* leaf data of the `y`-branch `⟨0, hn⟩` (the
prover's sent vectors `a, b`, blinders `μ, τₓ`), plus the computed left inverse of `W_V` for the
`v, γ` openings. There is **no discrete-log computation and no `Classical.choice`**: it is a
genuine `def` — a polynomial-time linear-algebraic function of the tree (interpolation by the
Lagrange-form `Sigma.vandInv`, not the `d!`-permutation `det⁻¹ • adjugate`; `W_V` inverted by
Gaussian elimination, `Sigma.gaussLeftInv`, not by minor search). For `n = 0` the tree is
path-free, so the witness is irrelevant and set to `0`.

* `A_C⁽ᵏ⁾`, `A_O` open directly off the `(0,0)`-bundle `eq2` coefficients (`Pcoef_AC`, `Pcoef_AO`);
* `A_I` needs the public `WtL/WtR` subtraction (`commit_open` / `Pcoef_AI`);
* `v, γ` come from the `eq1` `n'`-coefficients across the `q+1` `z`-children, `z`-interpolated and
  hit with the `W_V` left inverse (`eq1_special_extract` + `V_recover`). -/
def candWitness {n q m c : ℕ} (s : Statement F G n q m c)
    (tree : ArithTree F G n q c) : Witness F n m c :=
  if hn : 0 < n then
    let y₀ : F := ((chalY tree ⟨0, hn⟩ : Fˣ) : F)
    let yinv : Fin n → F := vinv (powers y₀ n)
    let xch : Fin (q + 1) → Fin (2 * nPrime c + 3) → F :=
      fun j l => ((chalX tree ⟨0, hn⟩ j l : Fˣ) : F)
    let lf : Fin (q + 1) → Fin (2 * nPrime c + 3) → F × F × (Fin n → F) × (Fin n → F) :=
      fun j l => leafO tree ⟨0, hn⟩ j l
    let zch : Fin (q + 1) → F := fun j => ((chalZ tree ⟨0, hn⟩ j : Fˣ) : F)
    -- `(0,0)`-bundle opening coefficients of the verifier commitment `Pcoef p`
    let cG : Fin (2 * nPrime c + 3) → (Fin n → F) := fun p => (bcoef s tree ⟨0, hn⟩ 0 p).1
    let cH : Fin (2 * nPrime c + 3) → (Fin n → F) := fun p => (bcoef s tree ⟨0, hn⟩ 0 p).2.1
    let ch : Fin (2 * nPrime c + 3) → F := fun p => (bcoef s tree ⟨0, hn⟩ 0 p).2.2
    -- public `WtL/WtR` parts at `z = z₀`
    let wL : Fin n → F := zch 0 • (powers (zch 0) q ᵥ* s.WL)
    let wR' : Fin n → F := hadamard yinv (zch 0 • (powers (zch 0) q ᵥ* s.WR))
    let pAI : Fin (2 * nPrime c + 3) := ⟨c + 1, by simp only [nPrime]; omega⟩
    let pAO : Fin (2 * nPrime c + 3) := ⟨nPrime c, by omega⟩
    let pAC : Fin c → Fin (2 * nPrime c + 3) :=
      fun k => ⟨nPrime c - ((k : ℕ) + 1), by have := k.isLt; simp only [nPrime]; omega⟩
    -- `eq1` `g`/`h`-coefficients of `msm wV V` at bundle `(0, j)`, then `z`-interpolated
    let Aj : Fin (q + 1) → F := fun j => eqAj s tree ⟨0, hn⟩ j
    let Cj : Fin (q + 1) → F := fun j => eqCj s tree ⟨0, hn⟩ j
    let Mmat : Matrix (Fin m) (Fin q) F := gaussLeftInv s.WV
    ⟨cG pAI - wR',
     (fun i => cH pAI i * yinv i) - (fun i => wL i * yinv i),
     cG pAO,
     fun k => ∑ ℓ : Fin q, Mmat k ℓ * (∑ j, vandInv zch ℓ.succ j * Aj j),
     fun k => ∑ ℓ : Fin q, Mmat k ℓ * (∑ j, vandInv zch ℓ.succ j * Cj j),
     fun k => cG (pAC k),
     fun k => hadamard (cH (pAC k)) yinv,
     fun k => ch (pAC k)⟩
  else ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- An opening `(a, b, c)` in the `(𝐆, 𝐇, h)` basis, written as a coefficient vector against
`gens s = 𝐆 ++ 𝐇 ++ [g, h]` (the `g`-coordinate is `0`). -/
def gvec {n : ℕ} (a b : Fin n → F) (c : F) : Fin (n + n + 2) → F :=
  Fin.append (Fin.append a b) ![0, c]


-- `relCand` / `relCandList` are defined below (after the `pubVec`/`ghCand`/read-off helpers).

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
omit [DecidableEq F] in
/-- **Assembling `(★)` from the combined `tcoeff`/`eq1` identity.** After the `δ`-terms cancel, the
residual identity `Had + R1CS_lin + wc + ⟨wV, v⟩ = 0` (each summand an `ip` against the `z`-aggregated
weight rows) is exactly the per-bundle relation `Had + ∑_q z^{ℓ+1}·(R1CS row ℓ) = 0`, via
`ip_smul_vecMul` (`⟨a, z·(𝐳·W)⟩ = z·⟨𝐳, W·a⟩`) turning each `ip` into its `z`-polynomial. -/
lemma star_from_combine {n q m c : ℕ} (s : Statement F G n q m c)
    (aL aR aO : Fin n → F) (aC : Fin c → Fin n → F) (v : Fin m → F) (z Had : F)
    (hcombine : Had + (ip aL (z • (powers z q ᵥ* s.WL)) + ip aR (z • (powers z q ᵥ* s.WR))
          + ip aO (z • (powers z q ᵥ* s.WO)) + ∑ k, ip (aC k) (z • (powers z q ᵥ* s.WC k)))
        + z * ip (powers z q) s.cc + ip (z • (powers z q ᵥ* s.WV)) v = 0) :
    Had + ∑ ℓ : Fin q, z ^ ((ℓ : ℕ) + 1)
        * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k) + s.WV *ᵥ v + s.cc) ℓ = 0 := by
  have key : ∀ {p : ℕ} (W : Matrix (Fin q) (Fin p) F) (a : Fin p → F),
      ip a (z • (powers z q ᵥ* W)) = ∑ ℓ : Fin q, z ^ ((ℓ : ℕ) + 1) * (W *ᵥ a) ℓ := fun W a => by
    rw [ip_smul_vecMul]; simp only [ip]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by simp only [powers]; ring
  have keyc : z * ip (powers z q) s.cc = ∑ ℓ : Fin q, z ^ ((ℓ : ℕ) + 1) * s.cc ℓ := by
    simp only [ip]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by simp only [powers]; ring
  have keyV : ip (z • (powers z q ᵥ* s.WV)) v
      = ∑ ℓ : Fin q, z ^ ((ℓ : ℕ) + 1) * (s.WV *ᵥ v) ℓ := by rw [ip_comm]; exact key s.WV v
  have keyC : (∑ k, ip (aC k) (z • (powers z q ᵥ* s.WC k)))
      = ∑ ℓ : Fin q, z ^ ((ℓ : ℕ) + 1) * (∑ k, s.WC k *ᵥ aC k) ℓ := by
    simp only [key]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_apply, Finset.mul_sum]
  have hconv : (ip aL (z • (powers z q ᵥ* s.WL)) + ip aR (z • (powers z q ᵥ* s.WR))
          + ip aO (z • (powers z q ᵥ* s.WO)) + ∑ k, ip (aC k) (z • (powers z q ᵥ* s.WC k)))
        + z * ip (powers z q) s.cc + ip (z • (powers z q ᵥ* s.WV)) v
      = ∑ ℓ : Fin q, z ^ ((ℓ : ℕ) + 1)
          * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k) + s.WV *ᵥ v + s.cc) ℓ := by
    rw [key s.WL aL, key s.WR aR, key s.WO aO, keyc, keyV, keyC]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [Pi.add_apply]; ring
  rw [← hconv]; linear_combination hcombine

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The per-bundle relation `(★)`.** From the consistency that the leaf data are the honest
polynomials (`Hla`/`Hlb`) and the `eq1` `n'`-coefficient identity (`Heq`: `= δ − wc − ⟨wV,v⟩`), the
tcoeff side (`tcoeff_recover`+`tcoeff_expand'`) gives `δ + R1CS_lin + Had`; equating and cancelling
`δ` yields `Had + ∑_q z^{ℓ+1}·(R1CS row ℓ) = 0` (`star_from_combine`). -/
lemma star_at_bundle {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aR aO sL sR : Fin n → F) (aC aux : Fin c → Fin n → F) (v : Fin m → F)
    (x : Fin (2 * nPrime c + 3) → F) (hx : Function.Injective x)
    (la lb : Fin (2 * nPrime c + 3) → (Fin n → F))
    (Hla : ∀ l, la l = fun i => ∑ p : Fin (nPrime c + 2),
      (x l) ^ (p : ℕ) * honestFL s yu zu aL aO sL aC p i)
    (fR : Fin (nPrime c + 2) → (Fin n → F))
    (Hlb : ∀ l, lb l = fun i => ∑ ℓ : Fin (nPrime c + 2), (x l) ^ (ℓ : ℕ) * fR ℓ i)
    (Hconv : (∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
          if (p : ℕ) + (ℓ : ℕ) = nPrime c then ip (honestFL s yu zu aL aO sL aC p) (fR ℓ) else 0)
        = ∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
          if (p : ℕ) + (ℓ : ℕ) = nPrime c then
            ip (honestFL s yu zu aL aO sL aC p) (honestFR s yu zu aR sR aux ℓ) else 0)
    (Heq : (∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, by omega⟩ l • ip (la l) (lb l))
      = (ip (hadamard (vinv (powers (↑yu : F) n)) ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WR))
            ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WL)
          - (↑zu : F) * ip (powers (↑zu : F) q) s.cc)
        - ip ((↑zu : F) • (powers (↑zu : F) q ᵥ* s.WV)) v) :
    (∑ i, powers (↑yu : F) n i * (aL i * aR i - aO i))
      + ∑ ℓ : Fin q, (↑zu : F) ^ ((ℓ : ℕ) + 1)
          * (s.WL *ᵥ aL + s.WR *ᵥ aR + s.WO *ᵥ aO + (∑ k, s.WC k *ᵥ aC k)
              + s.WV *ᵥ v + s.cc) ℓ = 0 := by
  have htc : (∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, by omega⟩ l • ip (la l) (lb l))
      = ip (hadamard (vinv (powers (↑yu : F) n)) ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WR))
            ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WL)
          + ip aL ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WL)
          + ip aR ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WR)
          + ip aO ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WO)
          + (∑ k, ip (aC k) ((↑zu : F) • powers (↑zu : F) q ᵥ* s.WC k))
          + ∑ i, powers (↑yu : F) n i * (aL i * aR i - aO i) := by
    rw [show (∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, by omega⟩ l • ip (la l) (lb l))
        = ∑ l, (Matrix.vandermonde x)⁻¹ ⟨nPrime c, by omega⟩ l
            • ip (fun i => ∑ p : Fin (nPrime c + 2), (x l) ^ (p : ℕ) * honestFL s yu zu aL aO sL aC p i)
                 (fun i => ∑ ℓ : Fin (nPrime c + 2), (x l) ^ (ℓ : ℕ) * fR ℓ i)
        from by simp only [Hla, Hlb]]
    rw [tcoeff_recover x hx (honestFL s yu zu aL aO sL aC) fR (by omega), Hconv]
    exact tcoeff_expand' s yu zu aL aR aO sL sR aC aux
  exact star_from_combine s aL aR aO aC v (↑zu : F)
    (∑ i, powers (↑yu : F) n i * (aL i * aR i - aO i)) (by linear_combination htc.symm.trans Heq)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The convolution equality `Hconv`** holds once the extracted `f_R` agrees with `honestFR` at
every coefficient *except* possibly `ℓ = n'` (the `A_O` `𝐇`-part): at `ℓ = n'` the convolution
partner is `honestFL` at degree `0`, which is `0`, so that term vanishes on both sides. -/
lemma conv_eq {n q m c : ℕ} (s : Statement F G n q m c) (yu zu : Fˣ)
    (aL aR aO sL sR : Fin n → F) (aC aux : Fin c → Fin n → F)
    (fR : Fin (nPrime c + 2) → (Fin n → F))
    (Hq : ∀ ℓ : Fin (nPrime c + 2), (ℓ : ℕ) ≠ nPrime c → fR ℓ = honestFR s yu zu aR sR aux ℓ) :
    (∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
        if (p : ℕ) + (ℓ : ℕ) = nPrime c then ip (honestFL s yu zu aL aO sL aC p) (fR ℓ) else 0)
      = ∑ p : Fin (nPrime c + 2), ∑ ℓ : Fin (nPrime c + 2),
        if (p : ℕ) + (ℓ : ℕ) = nPrime c then
          ip (honestFL s yu zu aL aO sL aC p) (honestFR s yu zu aR sR aux ℓ) else 0 := by
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hpq : (p : ℕ) + (ℓ : ℕ) = nPrime c
  · simp only [if_pos hpq]
    by_cases hq : (ℓ : ℕ) = nPrime c
    · have hfl0 : honestFL s yu zu aL aO sL aC p = 0 := by
        have hp0 : (p : ℕ) = 0 := by omega
        simp only [honestFL, hp0]
        rw [if_neg (show ¬((0 : ℕ) = c + 1) by omega),
          if_neg (show ¬((0 : ℕ) = nPrime c) by simp only [nPrime]; omega),
          if_neg (show ¬((0 : ℕ) = nPrime c + 1) by simp only [nPrime]; omega),
          Finset.sum_eq_zero (fun (k : Fin c) _ => if_neg (show ¬((0 : ℕ) = nPrime c - ((k : ℕ) + 1)) by
            have := k.isLt; simp only [nPrime]; omega))]
        abel
      rw [hfl0]; simp only [ip, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    · rw [Hq ℓ hq]
  · simp only [if_neg hpq]
