/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Radon
import Mathlib.Tactic.Rify
import BoundingSphere.Basic

/-!
# Upper bounds on the radius of the minimal bounding sphere

In this file we prove some upper bounds on the radius of the minimal bounding sphere
of a nonempty bounded set in a finite dimensional euclidean space.

## Main results

- `BoundingSphere.center_mem_convexHull_sphere_of_finite`:
  The center of the minimal bounding sphere of a non empty finite set `s`
  is contained in the convex hull of the points of `s` that lie on the sphere.
- `BoundingSphere.radius_le_sqrt_of_finite`:
  An upper bound on the radius of the minimal bounding sphere of a finite set.
- `BoundingSphere.radius_le_sqrt_of_isBounded`:
  An upper bound on the radius of the minimal bounding sphere of a bounded set.
  This result was originally proved by H. Jung in 1901.
-/

section

open Bornology ENNReal Metric InnerProductSpace Pointwise Finset Module

variable {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {X : Set V}

namespace BoundingSphere

/-- The center of the minimal bounding sphere of a non empty finite set `s`
is contained in the convex hull of the points of `s` that lie on the sphere. -/
theorem center_mem_convexHull_sphere_of_finite (hX1 : X.Finite) (hX2 : X.Nonempty) :
    center X ∈ convexHull ℝ (X ∩ sphere (center X) (radius X)) := by
  set c := center X
  set r := radius X
  -- Denote `Y` the points of `X` that lie on the sphere
  set Y := X ∩ sphere c r
  have hX3 := hX1.fintype
  have hY1 := Fintype.ofFinite Y
  have hY2 : Y ⊆ X := by simp [Y]
  -- By contradiction, assume that the center `c` is not in the convex hull of `Y`
  by_contra! h1
  -- There exists a vector `v` separating `c` from the convex hull of `Y`
  obtain ⟨v, hv, h2⟩ : ∃ v, v ≠ 0 ∧ ∀ x ∈ convexHull ℝ Y, ⟪v, x - c⟫_ℝ > 0 := by
    set s : Set V := {0}
    have hs1 : Convex ℝ s := convex_singleton _
    have hs2 : IsCompact s := isCompact_singleton
    set t := (· - c) '' convexHull ℝ Y
    have ht1 : Convex ℝ t := by
      let f := AffineMap.id ℝ _ - AffineMap.const ℝ _ c
      apply Convex.affine_image f
      apply convex_convexHull
    have ht2 : IsCompact t := IsCompact.image
      (hX1.subset hY2).isCompact_convexHull (continuous_sub_right c)
    have ht3 : IsClosed t := IsCompact.isClosed ht2
    have ht4 : Y.Nonempty := nonempty_sphere_of_finite hX1 hX2
    have ht5 : t.Nonempty := Set.image_nonempty.mpr ht4.convexHull
    have hst : Disjoint s t := by
      simp [s, t]
      intro x hx
      contrapose! h1
      convert hx using 1
      apply_fun (· + c) at h1
      simpa using h1.symm
    obtain ⟨f, u, w, hu, huw, hw⟩ := geometric_hahn_banach_compact_closed hs1 hs2 ht1 ht3 hst
    replace hu : u > 0 := by simpa [s] using hu
    let v := (InnerProductSpace.toDual ℝ V).symm f
    have hf x : f x = ⟪v, x⟫_ℝ := by simp [v]
    refine ⟨v, ?_, ?_⟩
    · by_contra! hv
      specialize hw ht5.choose ht5.choose_spec
      simp [hf, hv] at hw
      linarith only [hu, huw, hw]
    · intro x hx
      specialize hw (x - c) (by simp [t, hx])
      simp [hf] at hw
      linarith only [hu, huw, hw]
  -- Perturb the center `c` a bit in the direction of `v`
  let c' (ε : ℝ) := c + ε • v
  -- For a small enough perturbation, all points of `Y` are in the interior of the ball
  obtain ⟨δY, hδY, hcY⟩ : ∃ δY > 0, ∀ ε, ε > 0 → ε < δY → ∀ x ∈ Y, ‖x - c' ε‖ ^ 2 < r ^ 2 := by
    let δ x := ⟪v, x - c⟫_ℝ
    have hY3 : Y.toFinset.Nonempty := Set.toFinset_nonempty.mpr (nonempty_sphere_of_finite hX1 hX2)
    let d := Y.toFinset.inf' hY3 δ
    have hd1 xi (hxi : xi ∈ Y) : d ≤ δ xi := Y.toFinset.inf'_le δ (by simpa using hxi)
    have hd2 : ∃ xi ∈ Y, δ xi = d := by
      convert Y.toFinset.exists_mem_eq_inf' hY3 δ using 2 with xi; simp [d]; tauto
    have hd3 : d > 0 := by
      obtain ⟨x0, hx0, hd⟩ := hd2
      rw [←hd]
      apply h2 x0
      exact mem_convexHull_iff.mpr fun _ a _ => a hx0
    use 2 * d / ‖v‖ ^ 2, by field_simp; nlinarith only [hd3]
    intro ε hε1 hε2 xi hxi
    calc
      ‖xi - c' ε‖ ^ 2 = ‖(xi - c) - ε • v‖ ^ 2 := by congr 2; module
      _ = ‖xi - c‖ ^ 2 - 2 * ε * ⟪v, xi - c⟫_ℝ + ‖ε • v‖ ^ 2 := by
        rw [norm_sub_sq_real, real_inner_comm, real_inner_smul_left]
        ring
      _ = ‖xi - c‖ ^ 2 - 2 * ε * ⟪v, xi - c⟫_ℝ + ε ^ 2 * ‖v‖ ^ 2 := by
        congr 1
        rw [norm_smul, mul_pow, Real.norm_of_nonneg]
        exact hε1.le
      _ ≤ ‖xi - c‖ ^ 2 - 2 * ε * d + ε ^ 2 * ‖v‖ ^ 2 := by gcongr 3; exact hd1 xi hxi
      _ = ‖xi - c‖ ^ 2 + (-2 * ε * d + ε ^ 2 * ‖v‖ ^ 2) := by ring
      _ < ‖xi - c‖ ^ 2 + 0 := by
        gcongr 1
        calc
          -2 * ε * d + ε ^ 2 * ‖v‖ ^ 2 = ε * (-2 * d + ε * ‖v‖ ^ 2) := by ring
          _ < ε * 0 := by
            gcongr 1
            calc
              _ < -2 * d + (2 * d / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by gcongr 2
              _ = -2 * d + 2 * d := by congr 1; field_simp
              _ = _ := by ring
          _ = _ := by ring
      _ = _ := by simp [Y] at hxi; simp [hxi]
  -- For a small enough perturbation, all points of `X \ Y` are also in the interior of the ball
  let Z := X \ Y
  obtain ⟨δZ, hδZ, hcZ⟩ : ∃ δZ > 0, ∀ ε, ε > 0 → ε < δZ → ∀ x ∈ Z, ‖x - c' ε‖ ^ 2 < r ^ 2 := by
    have hZ0 := Fintype.ofFinite Z
    by_cases hZ1 : Z = ∅
    · simp [hZ1]; use 1; norm_num
    replace hZ1 := Set.toFinset_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hZ1)
    let f ε := Z.toFinset.sup' hZ1 (fun x => ‖x - c' ε‖ ^ 2)
    have hf : Continuous f := by apply Continuous.finset_sup'_apply; fun_prop
    replace hf : ContinuousAt f 0 := by apply hf.continuousAt
    rw [Metric.continuousAt_iff] at hf
    have f0_lt : f 0 < r ^ 2 := by
      unfold f
      rw [Finset.sup'_lt_iff]
      intro x hx
      suffices dist x c ^ 2 < r ^ 2 by simpa [c', ←dist_eq_norm] using this
      rw [sq_lt_sq₀]
      · simp [Z] at hx
        apply lt_of_le_of_ne
        · exact subset hX1.isBounded hx.left
        · have := hx.right
          contrapose! this
          simp [Y, hx.left, ←dist_eq_norm, this]
      · apply dist_nonneg
      · apply radius_nonneg
    replace ⟨δ, hδ, hf⟩ := hf (r ^ 2 - f 0) (by linarith only [f0_lt])
    use δ, hδ
    intro ε hε1 hε2
    simp only [dist_eq_norm] at hf
    have hεδ : ‖ε - 0‖ < δ := by
      rw [Real.norm_of_nonneg]
      · linarith only [hε2]
      · linarith only [hε1]
    specialize hf hεδ
    intro x hx
    calc
      _ ≤ f ε := by
        unfold f
        rw [Finset.le_sup'_iff]
        use x, by simpa using hx
      _ = (f ε - f 0) + f 0 := by ring
      _ ≤ ‖f ε - f 0‖ + f 0 := by gcongr 1; apply Real.le_norm_self
      _ < r ^ 2 := by linarith only [hf]
  -- Thus perturbing the center by a small amout yields a smaller ball still enclosing all of `X`,
  obtain ⟨δX, hδX, hcX⟩ : ∃ δX > 0, ∀ ε, ε > 0 → ε < δX → ∀ x ∈ X, ‖x - c' ε‖ ^ 2 < r ^ 2 := by
    use δY ⊓ δZ, lt_min hδY hδZ
    intro ε hε1 hε2 x hx
    obtain h | h : x ∈ Y ∨ x ∈ Z := by simp [Y, Z, hx]; tauto
    · exact hcY ε hε1 (lt_of_lt_of_le hε2 inf_le_left) x h
    · exact hcZ ε hε1 (lt_of_lt_of_le hε2 inf_le_right) x h
  -- Contradicting the minimality of the original ball.
  let δ0 := δX / 2
  obtain ⟨x, hx, hr0⟩ := X.toFinset.exists_mem_eq_sup' (Set.toFinset_nonempty.mpr hX2) (‖· - c' δ0‖)
  set r0 := X.toFinset.sup' (Set.toFinset_nonempty.mpr hX2) (‖· - c' δ0‖)
  have h3 : X ⊆ closedBall (c' δ0) r0 := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_eq_norm, r0]
    rw [Finset.le_sup'_iff]
    use x, by simpa using hx
  have h4 : r ≤ r0 := radius_le hX2 hX1.isBounded (c' δ0) r0 h3
  have h5 := calc
    r0 = √(r0 ^ 2) := by
      rw [Real.sqrt_sq]
      rw [Finset.le_sup'_iff]
      use hX2.choose, by simpa using hX2.choose_spec
      apply norm_nonneg
    _ < √(r ^ 2) := by
      apply Real.sqrt_lt_sqrt
      · apply sq_nonneg
      rw [hr0]
      apply hcX δ0
      · unfold δ0; linarith only [hδX]
      · unfold δ0; linarith only [hδX]
      · simpa using hx
    _ = r := by
      rw [Real.sqrt_sq]
      apply radius_nonneg
  linarith only [h4, h5]

/-- A finite set with at least two points has at least two points on the boundary
of its minimal bounding sphere. -/
theorem encard_sphere_ge_two_of_finite (hX1 : X.encard ≥ 2) (hX2 : X.Finite) :
    (X ∩ sphere (center X) (radius X)).encard ≥ 2 := by
  have hX3 := hX2.isBounded
  have hX4 : X.Nonempty := by
    apply Set.encard_ne_zero.mp
    by_contra! h0
    simp [h0] at hX1
  set c := center X
  set r := radius X
  set Y := X ∩ sphere c r
  obtain hY1 | hY1 : ¬Y.Finite ∨ Y.Finite := by tauto
  · rw [Set.encard_eq_top]
    · simp
    · simpa using hY1
  obtain hY2 | hY2 | hY2 : Y.encard = 0 ∨ Y.encard = 1 ∨ Y.encard ≥ 2 := by
    have := hY1.fintype
    unfold Set.encard
    rw [ENat.card_eq_coe_natCard]
    norm_cast
    omega
  · exfalso
    rw [Set.encard_eq_zero] at hY2
    have hY3 := nonempty_sphere_of_finite hX2 hX4
    contrapose! hY3
    exact hY2
  · exfalso
    rw [Set.encard_eq_one] at hY2
    obtain ⟨x, hx⟩ := hY2
    have hx1 : x ∈ Y := by simp [hx]
    have hx2 : x ∈ X := hx1.left
    have hx3 := hx1.right
    have h1 : c ∈ convexHull ℝ Y := center_mem_convexHull_sphere_of_finite hX2 hX4
    replace h1 : c = x := by simpa [hx] using h1
    have h2 : r = 0 := by simpa [sphere, c, h1] using hx3.symm
    have h3 : r > 0 := radius_pos hX3 hX1
    linarith only [h2, h3]
  · exact hY2

/-- An upper bound on the radius of the minimal bounding sphere of a finite set. -/
theorem radius_le_sqrt_of_finite {d : ℕ} (hX1 : X.Finite) (hXd : X.ncard ≤ d + 1) :
    radius X ≤ √(d / (2 * d + 2) : ℝ) * diam X := by
  -- Handle cases where `X` has 0 or 1 point first to avoid later divisions by a diameter of zero.
  classical
  obtain hX2 | hX2 | hX2 : X.ncard = 0 ∨ X.ncard = 1 ∨ X.ncard ≥ 2 := by omega
  · rw [Set.ncard_eq_zero hX1] at hX2
    simp [hX2]
  · have ⟨a, ha⟩ := Set.ncard_eq_one.mp hX2
    simp [ha, radius_singleton]
  have hX3 : X.Nonempty := by by_contra! h; simp [h] at hX2
  -- Without loss of generality, translate `X` so that its center is at the origin.
  wlog hc : center X = 0
  · let T := -center X +ᵥ X
    have hT : T.ncard = X.ncard := Set.ncard_image_of_injective _ (add_right_injective _)
    specialize this (X := T) (d := d)
    specialize this hX1.vadd_set
    specialize this (by simpa [hT] using hXd)
    specialize this (by simpa [hT] using hX2)
    specialize this (by simpa [T] using hX3)
    specialize this (by simp [T, center_vadd hX3 hX1.isBounded (-center X)])
    convert this using 1 <;> simp [T]
  have hX0 := hX1.fintype
  have hX4 : diam X > 0 := by
    let a : Fin (Fintype.card X) ↪ X := hX0.equivFin.symm.toEmbedding
    let b : Fin 2 ↪ Fin (Fintype.card X) := Fin.castLEEmb (by
      simpa [←Set.toFinset_card, X.ncard_eq_toFinset_card'.symm] using hX2)
    let x0 := a (b ⟨0, by simp⟩)
    let x1 := a (b ⟨1, by simp⟩)
    calc
      0 < dist x0 x1 := dist_pos.mpr ((a.injective.comp b.injective).ne (by simp))
      _ ≤ diam X := dist_le_diam_of_mem hX1.isBounded x0.2 x1.2
  -- Denote `Y` the points of `X` that lie on the sphere, and let `n` be their number.
  set r := radius X
  have hY0 := Fintype.ofFinite (X ∩ sphere 0 r : Set V)
  let Y := (X ∩ sphere 0 r).toFinset
  have hY1 : Y.Nonempty := by simpa [Y, hc] using nonempty_sphere_of_finite hX1 hX3
  have hY2 : Y ⊆ X.toFinset := by simp [Y]
  let n := #Y
  have hn : n ≠ 0 := by
    by_contra! hn
    rw [card_eq_zero] at hn
    simp [hn] at hY1
  -- As the center is in the convex hull of `Y`, rewrite it as a convex combination.
  -- `c = ∑ xi ∈ Y, l xi • xi` with `∑ x i ∈ Y, l xi = 1` and `l xi ≥ 0`
  have hcY : center X ∈ convexHull ℝ Y := by
    simpa [Y, hc] using center_mem_convexHull_sphere_of_finite hX1 hX3
  obtain ⟨l, hl1, hl2, hl3⟩ := mem_convexHull'.mp hcY
  -- First, derive a lower bound on `1 - l xi` for `xi ∈ Y`.
  have ineq xi (hi : xi ∈ Y) := calc
    1 - l xi = ∑ xk ∈ Y, l xk - l xi := by rw [hl2]
    _ = ∑ xk ∈ Y \ {xi}, l xk + l xi - l xi := by simp [←sum_sdiff (singleton_subset_iff.mpr hi)]
    _ = ∑ xk ∈ Y \ {xi}, l xk * 1 := by ring_nf
    _ ≥ ∑ xk ∈ Y \ {xi}, l xk * (‖xk - xi‖ ^ 2 / diam X ^ 2) := by
      gcongr 2 with xk hk
      · simp at hk
        exact hl1 xk hk.left
      · simp at hk
        suffices dist xk xi ^ 2 ≤ diam X ^ 2 by
          field_simp
          simpa [dist_eq_norm] using this
        gcongr 1
        apply dist_le_diam_of_mem hX1.isBounded
        · exact Set.mem_toFinset.mp (hY2 hk.left)
        · exact Set.mem_toFinset.mp (hY2 hi)
    _ = (1 / diam X ^ 2) * ∑ xk ∈ Y \ {xi}, l xk * ‖xk - xi‖ ^ 2 := by rw [mul_sum]; field_simp
    _ = (1 / diam X ^ 2) * ∑ xk ∈ Y, l xk * ‖xk - xi‖ ^ 2 := by
      simp [←sum_sdiff (singleton_subset_iff.mpr hi)]
    _ = (1 / diam X ^ 2) * ∑ xk ∈ Y,
          (l xk * ‖xk‖ ^ 2 + l xk * ‖xi‖ ^ 2 - 2 * (l xk * ⟪xk, xi⟫_ℝ)) := by
      congr! 2 with xk hk
      rw [norm_sub_sq_real]
      ring
    _ = (1 / diam X ^ 2) *
          (∑ xk ∈ Y, l xk * ‖xk‖ ^ 2 + ∑ xk ∈ Y, l xk * ‖xi‖ ^ 2 -
          2 * ∑ xk ∈ Y, l xk * ⟪xk, xi⟫_ℝ) := by
      congr 1
      conv_lhs => rw [sum_sub_distrib, sum_add_distrib]
      congr 2
      rw [mul_sum]
    _ = (1 / diam X ^ 2) *
          (∑ xk ∈ Y, l xk * r ^ 2 + ∑ xk ∈ Y, l xk * r ^ 2 - 2 * ∑ xk ∈ Y, l xk * ⟪xk, xi⟫_ℝ) := by
      congr! 6 with xk hk
      · simp [Y] at hk
        simp [hk]
      · simp [Y] at hi
        simp [hi]
    _ = (1 / diam X ^ 2) *
          (r ^ 2 * ∑ xk ∈ Y, l xk + r ^ 2 * ∑ xk ∈ Y, l xk - 2 * ∑ xk ∈ Y, l xk * ⟪xk, xi⟫_ℝ) := by
      congr 3
      all_goals
      · rw [mul_sum]
        congr! 1 with xk hk
        ring
    _ = (1 / diam X ^ 2) * (2 * r ^ 2 - 2 * (∑ xk ∈ Y, l xk * ⟪xk, xi⟫_ℝ)) := by
      congr 2
      rw [hl2]
      ring
    _ = (1 / diam X ^ 2) * (2 * r ^ 2 - 2 * (∑ xk ∈ Y, ⟪l xk • xk, xi⟫_ℝ)) := by
      congr! 4 with xk hk
      rw [real_inner_smul_left]
    _ = (1 / diam X ^ 2) * (2 * r ^ 2 - 2 * (⟪∑ xk ∈ Y, l xk • xk, xi⟫_ℝ)) := by
      congr! 4 with xk hk
      rw [sum_inner]
    _ = (1 / diam X ^ 2) * (2 * r ^ 2) := by simp [hl3, hc]
    _ = 2 * r ^ 2 / diam X ^ 2 := by field_simp
  -- Now, sum this inequality over all `xi ∈ Y` to get an inequality involving `n` and `r`.
  replace ineq := calc
    n - 1 = ∑ xi ∈ Y, 1 - ∑ i ∈ Y, l i := by simp [hl2, n]
    _ = ∑ xi ∈ Y, (1 - l xi) := by rw [sum_sub_distrib]
    _ ≥ ∑ xi ∈ Y, (2 * r ^ 2 / diam X ^ 2) := by gcongr 2 with xi hi; exact ineq xi hi
    _ = n * (2 * r ^ 2 / diam X ^ 2) := by simp [sum_const, n]
    _ = 2 * n * r ^ 2 / diam X ^ 2 := by ring
  -- Rearranging this inequality yields the desired result.
  exact calc
    r = √(r ^ 2) := by
      rw [Real.sqrt_sq]
      calc
        0 ≤ _ := dist_nonneg
        _ ≤ r := subset hX1.isBounded hX3.choose_spec
    _ ≤ √(((n - 1) / (2 * n)) * diam X ^ 2) := by gcongr 1; field_simp at ineq ⊢; simpa using ineq
    _ = √((n - 1) / (2 * n)) * √(diam X ^ 2) := by rw [Real.sqrt_mul]; field_simp; simp; omega
    _ = √((n - 1) / (2 * n)) * diam X := by congr 1; apply Real.sqrt_sq; apply diam_nonneg
    _ ≤ √(d / (2 * d + 2)) * diam X := by
      gcongr 2
      have := calc
        n ≤ #X.toFinset := Finset.card_le_card hY2
        _ = X.ncard := X.ncard_eq_toFinset_card'.symm
        _ ≤ d + 1 := hXd
      field_simp
      rify at this
      nlinarith only [this]

/-- Jung's theorem. An upper bound on the radius of the minimal bounding sphere of a bounded set. -/
theorem radius_le_sqrt_of_isBounded (hX1 : IsBounded X) :
    radius X ≤ (√(finrank ℝ V / (2 * finrank ℝ V + 2) : ℝ) * diam X) := by
  set d := finrank ℝ V
  obtain hX2 | hX2 : X.encard ≤ d + 1 ∨ X.encard ≥ d + 1 := by apply le_total
  · apply radius_le_sqrt_of_finite (Set.finite_of_encard_le_coe hX2)
    apply ENat.coe_le_coe.mp
    convert hX2 using 1
    simp [Set.ncard, Set.finite_of_encard_le_coe hX2]
  · let f (x : V) := closedBall x (√(d / (2 * d + 2) : ℝ) * diam X)
    let F (x : X) := f x.val
    suffices (⋂ i, F i).Nonempty by
      refine radius_le ?_ hX1 this.choose _ ?_
      · apply Set.encard_ne_zero.mp; by_contra! h1; simp [h1] at hX2
      · simpa [F, f, mem_closedBall, dist_comm] using this.choose_spec
    apply Convex.helly_theorem_compact (𝕜 := ℝ)
    · simpa using hX2
    · intro ⟨i, hi⟩
      apply convex_closedBall
    · intro ⟨i, hi⟩
      apply isCompact_closedBall
    · intro I hI
      let K := Subtype.val '' SetLike.coe I
      have hK : K.ncard = d + 1 := by
        simpa [K, Set.ncard_image_of_injOn Set.injOn_subtype_val] using hI
      suffices (⋂ k ∈ K, f k).Nonempty by
        obtain ⟨c, hc⟩ := this
        use c
        simp only [Set.mem_iInter] at hc
        simp only [Set.iInter_coe_set, Set.mem_iInter]
        intro i hi hj
        simpa using hc i ⟨⟨i, hi⟩, hj, rfl⟩
      have hK2 : K.Finite := Set.finite_of_ncard_ne_zero (by omega)
      have hK3 : K ⊆ X := by simp [K]
      use center K
      simp only [Set.mem_iInter]
      intro i hi
      have hc := (subset (hX1.subset hK3) hi).trans (radius_le_sqrt_of_finite hK2 hK.le)
      rw [dist_comm] at hc
      apply le_trans hc
      gcongr 1
      exact diam_mono hK3 hX1

end BoundingSphere

end
