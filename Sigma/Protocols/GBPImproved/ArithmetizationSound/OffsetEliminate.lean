/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Sigma.Protocols.GBPImproved.ArithmetizationSound.OffsetPin

/-!
# Offset elimination: every `P_L`-stray vanishes

The central step in the offset protocol's tightness. Per accepting bundle, the per-node identity
`⟨a*(x), β(x)⟩ = 0` (from the `t̂`-quadratic, `node_facts`) interpolates across the `2c+5`
`x`-children into the vanishing of every convolution coefficient of the two truncated
coefficient families (`conv_vanish`). A **descending induction over the stray slots** then
forces them to zero one at a time, from the top `x`-degree down (`strayW_zero`): at degree
`ℓ₀ + c + 2` all higher-slot strays are already zero, so the convolution collapses to the single
pairing of the mask slot — the `s_L`-component **plus the binding offset** `z^{q+1}·𝟙` — against
`strayW ℓ₀`:

  `⟨u_{S_L}, 𝐲∘w⟩ + z^{q+1} · Σ_t w_t·y^t = 0`.

The fresh `z`-degree isolates the offset term over the `q+2` `z`-children (`isolate_fresh_degree`),
and the `y`-Vandermonde over the `n` `y`-branches forces `w` to zero coordinate-wise (the reused
base `hadamard_deaggregate`). Consequently the `β`-quadrant vanishes at every node (`betaF_zero`)
and each child's inner product is exactly `⟨a*, b*⟩` (`tHat_eq_quad`) — the inputs the `(★)`
extraction and the tight clause 3 need.
-/

namespace Sigma.Protocols.GBPImproved.Offset

open Sigma.Protocols.GBP Sigma.Protocols.GBPImproved
open OracleComp Sigma.TreeK
open scoped Matrix Classical

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- **The fresh-degree isolation.** A polynomial of the shape `D + z^{q+1}·B` vanishing at
`q+2` distinct points has `B = 0` (Vandermonde at full degree; pairwise differences would not
suffice, since distinct points can share a `(q+1)`-th power). -/
lemma isolate_fresh_degree {q : ℕ} (z : Fin (q + 2) → F) (hz : Function.Injective z) (D B : F)
    (h : ∀ j, D + z j ^ (q + 1) * B = 0) : B = 0 := by
  have hker := vandermonde_kernel (G := F) z hz
    (fun κ => (if (κ : ℕ) = 0 then D else 0) + (if (κ : ℕ) = q + 1 then B else 0))
    (fun j => by
      have hsum : (∑ κ : Fin (q + 2), z j ^ (κ : ℕ)
          • ((if (κ : ℕ) = 0 then D else 0) + (if (κ : ℕ) = q + 1 then B else 0)))
          = D + z j ^ (q + 1) * B := by
        simp only [smul_add, Finset.sum_add_distrib]
        rw [sum_pow_smul_ite (z j) 0 (by omega) D, sum_pow_smul_ite (z j) (q + 1) (by omega) B]
        simp only [pow_zero, smul_eq_mul, one_mul]
      rw [hsum]; exact h j)
  have hb := congrFun hker ⟨q + 1, by omega⟩
  simpa using hb

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Inner product against a constant vector. -/
lemma ip_const_left {nn : ℕ} (c : F) (v : Fin nn → F) :
    ip (fun _ => c) v = c * ∑ t, v t := by
  simp only [ip, Finset.mul_sum]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **The convolution coefficients of `⟨a*(x), β(x)⟩` vanish.** Truncating both quadrant
polynomials to degree `c+2` (high slots zero by the candidates), the per-node identity
`⟨a*(x_l), β(x_l)⟩ = 0` at the `2c+5` distinct `x`-children forces every Cauchy coefficient to zero. -/
lemma conv_vanish {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (hnode : ∀ l : Fin (2 * c + 5), ip (aStarF tree i j l) (betaF tree i j l) = 0)
    (d : Fin (2 * c + 5)) :
    (∑ p : Fin (c + 3), ∑ ℓ : Fin (c + 3),
        if (p : ℕ) + (ℓ : ℕ) = (d : ℕ) then
          ip ((bcoefL s tree i j ⟨(p : ℕ), by omega⟩).1)
             ((bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1)
        else 0) = 0 := by
  have hval : ∀ l : Fin (2 * c + 5),
      (∑ dd : Fin (2 * c + 5),
        (chalXO tree i j l) ^ (dd : ℕ)
          • (∑ p : Fin (c + 3), ∑ ℓ : Fin (c + 3),
              if (p : ℕ) + (ℓ : ℕ) = (dd : ℕ) then
                ip ((bcoefL s tree i j ⟨(p : ℕ), by omega⟩).1)
                   ((bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1)
              else 0)) = 0 := by
    intro l
    have hA : aStarF tree i j l
        = fun t => ∑ p : Fin (c + 3),
            (chalXO tree i j l) ^ (p : ℕ)
              * (bcoefL s tree i j ⟨(p : ℕ), by omega⟩).1 t := by
      rw [leafAStar_recover s tree i j l,
        sum_truncate' (chalXO tree i j l)
          (fun p => (bcoefL s tree i j p).1)
          (fun ℓ => (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).1)
          (fun ℓ => rfl)
          (fun p hp => (bcoefL_high_zero hn s tree i j hbz p hp).1)]
      funext t; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hB : betaF tree i j l
        = fun t => ∑ ℓ : Fin (c + 3),
            (chalXO tree i j l) ^ (ℓ : ℕ)
              * (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1 t := by
      rw [leafBeta_recover s tree i j l,
        sum_truncate' (chalXO tree i j l)
          (fun p => (bcoefL s tree i j p).2.1)
          (fun ℓ => (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1)
          (fun ℓ => rfl)
          (fun p hp => (bcoefL_high_zero hn s tree i j hbz p hp).2)]
      funext t; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h0 := hnode l
    rw [hA, hB, ip_xpoly_conv (M := 2 * c + 5)
      (chalXO tree i j l) _ _
      (fun p ℓ => by have := p.isLt; have := ℓ.isLt; omega)] at h0
    simpa [smul_eq_mul] using h0
  have hker := vandermonde_kernel (G := F)
    (fun l => (chalXO tree i j l)) (chalX_inj tree i j)
    (fun dd => ∑ p : Fin (c + 3), ∑ ℓ : Fin (c + 3),
      if (p : ℕ) + (ℓ : ℕ) = (dd : ℕ) then
        ip ((bcoefL s tree i j ⟨(p : ℕ), by omega⟩).1)
           ((bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1)
      else 0)
    hval
  exact congrFun hker d

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 4 (the descending stray elimination, one step).** Step 2 gives `⟨a*(x), β(x)⟩ = 0` at every
node, hence every convolution coefficient of the two degree-`(c+2)` quadrant polynomials vanishes.
At convolution degree `ℓ₀+c+2`, with the higher-slot strays zero by the induction hypothesis, the
sum collapses to the mask slot `c+2` paired against `strayW ℓ₀`. The mask carries `u + z^{q+1}·𝟙`,
so the coefficient is `⟨u, 𝐲∘w⟩ + z^{q+1} ∑_t y^t w_t`; the fresh `z^{q+1}` power isolates
`∑_t y^t w_t` under a full-degree `z`-Vandermonde (`q+2` points), and the `y`-Vandermonde then
forces `strayW ℓ₀ = w = 0` coordinate-wise. -/
lemma stray_step {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hbzAll : ∀ (i : Fin n) (j : Fin (q + 2)), ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (hnodeAll : ∀ (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)),
      ip (aStarF tree i j l) (betaF tree i j l) = 0)
    (q0 : Fin (c + 3))
    (IH : ∀ ℓ : Fin (c + 3), (q0 : ℕ) < (ℓ : ℕ) → strayW s tree hn ℓ = 0) :
    strayW s tree hn q0 = 0 := by
  -- Step 1: per bundle, the collapsed identity `⟨cG(c+2), cH(ℓ₀)⟩ = 0`.
  have hpair : ∀ (i : Fin n) (j : Fin (q + 2)),
      ip ((bcoefL s tree i j ⟨c + 2, by omega⟩).1)
         ((bcoefL s tree i j ⟨(q0 : ℕ), by omega⟩).2.1) = 0 := by
    intro i j
    have hconv := conv_vanish hn s tree i j (hbzAll i j) (hnodeAll i j)
      ⟨(q0 : ℕ) + c + 2, by have := q0.isLt; omega⟩
    rw [Finset.sum_eq_single (⟨c + 2, by omega⟩ : Fin (c + 3))] at hconv
    · rw [Finset.sum_eq_single q0] at hconv
      · rwa [if_pos (by simp only; omega)] at hconv
      · intro ℓ _ hq
        rw [if_neg]
        simp only
        intro hcontra
        exact hq (Fin.ext (by omega))
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro p _ hp
      refine Finset.sum_eq_zero fun ℓ _ => ?_
      by_cases hg : (p : ℕ) + (ℓ : ℕ) = (q0 : ℕ) + c + 2
      · rw [if_pos hg]
        have hple : (p : ℕ) < c + 2 := by
          have h1 := p.isLt
          have h2 : (p : ℕ) ≠ c + 2 := fun h => hp (Fin.ext h)
          omega
        have hq_gt : (q0 : ℕ) < (ℓ : ℕ) := by omega
        have hzq : (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1 = 0 := by
          have hpin : (bcoefL s tree i j ⟨(ℓ : ℕ), by omega⟩).2.1
              = hadamard (powers ((chalYO tree i : Fˣ) : F) n) (strayW s tree hn ℓ) :=
            strayW_pin hn s tree i j (hbzAll i j) ℓ
          rw [hpin, IH ℓ hq_gt]
          funext t; simp [hadamard]
        rw [hzq, ip_zero_right]
      · rw [if_neg hg]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Step 2: rewrite the pairing through the read-offs and isolate the fresh `z`-degree.
  have hyB : ∀ i : Fin n,
      (∑ t, powers ((chalYO tree i : Fˣ) : F) n t * strayW s tree hn q0 t) = 0 := by
    intro i
    refine isolate_fresh_degree (q := q)
      (fun j => (chalZO tree i j)) (chalZ_inj tree i)
      (ip (fun t => (bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1 t
          - (chalZO tree ⟨0, hn⟩ 0) ^ (q + 1))
        (hadamard (powers ((chalYO tree i : Fˣ) : F) n) (strayW s tree hn q0)))
      (∑ t, powers ((chalYO tree i : Fˣ) : F) n t * strayW s tree hn q0 t)
      (fun j => ?_)
    have hG : (bcoefL s tree i j ⟨c + 2, by omega⟩).1
        = fun t => ((bcoefL s tree ⟨0, hn⟩ 0 ⟨c + 2, by omega⟩).1 t
              - (chalZO tree ⟨0, hn⟩ 0) ^ (q + 1))
            + (chalZO tree i j) ^ (q + 1) :=
      (slCand_readoff hn s tree i j (hbzAll i j _ (by
        rw [bundleCands]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).1
    have hH : (bcoefL s tree i j ⟨(q0 : ℕ), by omega⟩).2.1
        = hadamard (powers ((chalYO tree i : Fˣ) : F) n) (strayW s tree hn q0) :=
      strayW_pin hn s tree i j (hbzAll i j) q0
    have hp := hpair i j
    rw [hG, hH] at hp
    rw [ip_add_left'] at hp
    rw [ip_const_left] at hp
    have hsum : (∑ t, hadamard (powers ((chalYO tree i : Fˣ) : F) n)
          (strayW s tree hn q0) t)
        = ∑ t, powers ((chalYO tree i : Fˣ) : F) n t * strayW s tree hn q0 t := by
      refine Finset.sum_congr rfl fun t _ => ?_
      simp [hadamard]
    rw [hsum] at hp
    exact hp
  -- Step 3: the `y`-Vandermonde forces the stray to zero coordinate-wise.
  funext t
  have := hadamard_deaggregate (fun i => ((chalYO tree i : Fˣ) : F)) (chalY_inj tree)
    (strayW s tree hn q0) (fun i => by simpa [powers] using hyB i) t
  simpa using this

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- **Step 4 (offset elimination).** Every residual stray vanishes: `strayW ℓ = 0` for all `ℓ`,
by descending induction from the top `x`-degree (`stray_step`). This is the slack the after-`r`
ordering alone cannot remove, and which the binding offset `z^{q+1}·𝟙` eliminates. -/
lemma strayW_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (hbzAll : ∀ (i : Fin n) (j : Fin (q + 2)), ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (hnodeAll : ∀ (i : Fin n) (j : Fin (q + 2)) (l : Fin (2 * c + 5)),
      ip (aStarF tree i j l) (betaF tree i j l) = 0) :
    ∀ ℓ : Fin (c + 3), strayW s tree hn ℓ = 0 := by
  suffices h : ∀ k : ℕ, ∀ ℓ : Fin (c + 3), c + 2 - (ℓ : ℕ) ≤ k → strayW s tree hn ℓ = 0 by
    intro ℓ
    exact h (c + 2) ℓ (by omega)
  intro k
  induction k with
  | zero =>
    intro ℓ hq
    exact stray_step hn s tree hbzAll hnodeAll ℓ
      (fun ℓ' hq' => absurd ℓ'.isLt (by omega))
  | succ k ih =>
    intro ℓ hq
    exact stray_step hn s tree hbzAll hnodeAll ℓ
      (fun ℓ' hq' => ih ℓ' (by omega))

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- With every stray zero, the `β`-quadrant vanishes at every node. -/
lemma betaF_zero {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (hstray : ∀ ℓ : Fin (c + 3), strayW s tree hn ℓ = 0)
    (l : Fin (2 * c + 5)) :
    betaF tree i j l = 0 := by
  rw [leafBeta_recover s tree i j l]
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases lt_or_ge (p : ℕ) (c + 3) with hlt | hge
  · have hpin : (bcoefL s tree i j p).2.1
        = hadamard (powers ((chalYO tree i : Fˣ) : F) n) (strayW s tree hn ⟨(p : ℕ), hlt⟩) :=
      strayW_pin hn s tree i j hbz ⟨(p : ℕ), hlt⟩
    rw [hpin, hstray ⟨(p : ℕ), hlt⟩]
    have : hadamard (powers ((chalYO tree i : Fˣ) : F) n) (0 : Fin n → F) = 0 := by
      funext t; simp [hadamard]
    rw [this, smul_zero]
  · rw [(bcoefL_high_zero hn s tree i j hbz p hge).2, smul_zero]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- With the strays zero, each child's inner product is exactly the quadrant convolution
`⟨a*, b*⟩` — the value the `(★)` extraction consumes. -/
lemma tHat_eq_quad {n q m c : ℕ} (hn : 0 < n) (s : Statement F G n q m c)
    (tree : ArithTree' F G n q c)
    (i : Fin n) (j : Fin (q + 2))
    (hbz : ∀ rc ∈ bundleCands s tree hn i j, rc = 0)
    (hstray : ∀ ℓ : Fin (c + 3), strayW s tree hn ℓ = 0)
    (l : Fin (2 * c + 5)) :
    ip (leafA tree i j l 0) (leafB tree i j l 0)
      = ip (aStarF tree i j l) (bStarF tree i j l) := by
  have hfacts := node_facts hn s tree i j hbz l
  have hb0 := betaF_zero hn s tree i j hbz hstray l
  rw [(hfacts.2.2 0), hb0, ip_zero_right, add_zero]

end Sigma.Protocols.GBPImproved.Offset
