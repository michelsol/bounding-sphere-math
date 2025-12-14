/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import BoundingSphere.SupDistance

/-!
# Minimal bounding sphere

In this file we develop a basic theory of the minimal bounding sphere in a finite dimensional
euclidean affine space.
In such a space, the minimal bounding sphere of a nonempty bounded set exists and is unique.
Most results are about the radius and center of the sphere, rather than the sphere itself.

## Main definitions

- `BoundingSphere.radius`: The radius of the minimal bounding sphere.
- `BoundingSphere.center`: The center of the minimal bounding sphere.

## Main results

- `BoundingSphere.radius_mem_range`: Key lemma used to define the center.
- `BoundingSphere.radius_le`: The radius of the minimal bounding sphere is less than or equal to
  that of any other ball containing the set.
- `BoundingSphere.subset`: The minimal bounding sphere contains the set.
- `BoundingSphere.radius_eq_radius_of_IsMinimal` and
  `BoundingSphere.center_eq_center_of_IsMinimal`: Uniqueness of the minimal bounding sphere.

-/
section

open Bornology ENNReal Metric EMetric InnerProductSpace Pointwise

variable {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable {P} [MetricSpace P] [NormedAddTorsor V P] {s t : Set P}

namespace BoundingSphere

/-- The radius of the minimal bounding sphere of a set, defined as the infimum of the supremal
distance from a point to the set. -/
noncomputable def radius
    {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {P} [MetricSpace P] [NormedAddTorsor V P] (s : Set P) :=
  (⨅ x, supEdist x s).toReal

/-- The radius of the minimal bounding sphere is non negative. -/
theorem radius_nonneg : radius s ≥ 0 := by simp [radius]

/-- The radius of the minimal bounding sphere of the empty set is `0`. -/
@[simp]
theorem radius_empty : radius (∅ : Set V) = 0 := by simp [radius]

theorem radius_eq_zero_of_not_isBounded (h1 : ¬IsBounded s) : radius s = 0 := by
  simp [radius, EMetric.supEdist_eq_top_of_not_isBounded h1]

/-- The radius of the minimal bounding sphere of a bounded set `s` is less than or equal to
that of any other ball containing `s`. -/
theorem radius_le (h0 : s.Nonempty) (h1 : IsBounded s) :
    ∀ c', ∀ r', s ⊆ Metric.closedBall c' r' → radius s ≤ r' := by
  intro c' r' h2
  have hr' := calc
    r' ≥ dist h0.choose c' := h2 h0.choose_spec
    _ ≥ 0 := dist_nonneg
  unfold radius
  rw [←le_ofReal_iff_toReal_le _ hr', iInf_le_iff]
  · intro x hx
    specialize hx c'
    rw [supEdist, le_iSup_iff] at hx
    apply hx
    intro y
    rw [iSup_le_iff]
    intro hy
    rw [edist_le_ofReal hr', dist_comm]
    exact h2 hy
  · simp [EMetric.supEdist_ne_top_of_isBounded h1]

/-- The radius of the minimal bounding sphere of a singleton is `0`. -/
@[simp]
theorem radius_singleton (a : V) : radius {a} = 0 := by
  have := radius_le (Set.singleton_nonempty a) isBounded_singleton a 0 (by simp)
  exact le_antisymm this radius_nonneg

/-- Translating a set does not change the radius of
its minimal bounding sphere. -/
@[simp]
theorem radius_vadd (s : Set P) (v : V) : radius (v +ᵥ s) = radius s := by
  unfold radius
  rw [(AffineIsometryEquiv.constVAdd ℝ P (-v)).toEquiv.iInf_congr]
  simpa using fun x => EMetric.supEdist_vadd (-v) x (v +ᵥ s)

/-- The radius of the minimal bounding sphere is attained as a supremal distance
from some point to the set. -/
theorem radius_mem_range (s : Set P) : radius s ∈ Set.range (supDist · s) := by
  obtain h0 | h0 := s.eq_empty_or_nonempty
  · simp [radius, h0]
  obtain h1 | h1 := em' (IsBounded s)
  · simp [radius_eq_zero_of_not_isBounded h1, supDist_eq_zero_of_not_isBounded h1]
  unfold radius
  suffices ⨅ x, supEdist x s ∈ Set.range (supEdist · s) by
    simp only [Set.mem_range] at this
    simp only [supDist, Set.mem_range]
    obtain ⟨y, hy⟩ := this
    use y
    congr 1
  let s0 := h0.choose
  have hs0 : s0 ∈ s := h0.choose_spec
  let K := EMetric.closedBall s0 (2 * supEdist s0 s)
  suffices ⨅ x ∈ K, supEdist x s ∈ (supEdist · s) '' K by
    apply Set.mem_range_of_mem_image _ K
    convert this using 1
    apply csInf_eq_csInf_of_forall_exists_le
    · intro _ ⟨c, hc⟩
      subst hc
      by_cases hc2 : c ∈ K
      · use supEdist c s
        exact ⟨by use c; exact (iInf_pos hc2), by simp⟩
      · use supEdist s0 s
        split_ands
        · use s0, by simp [K]
        · calc
            supEdist s0 s ≤ supEdist s0 s + supEdist s0 s := le_add_self
            _ = 2 * supEdist s0 s := by rw [two_mul]
            _ ≤ edist c s0 := le_of_lt (by simpa [K] using hc2)
            _ ≤ _ := edist_le_supEdist_of_mem hs0
    · intro _ ⟨y, hy⟩
      subst hy
      use supEdist y s
      simp
  have hK : IsCompact K := by
    unfold K
    let f := (AffineIsometryEquiv.constVSub ℝ s0).symm.toIsometryEquiv
    let K' := Metric.closedBall (0 : V) (2 * supDist s0 s)
    convert_to IsCompact (f '' K') using 1
    · rw [f.image_closedBall, ←emetric_closedBall]
      · congr 1
        · simp [f]
        · simp [supEdist_eq_supDist_of_isBounded h1]
      · simp [supDist_nonneg]
    exact (isCompact_closedBall _ _).image_of_continuousOn f.continuous.continuousOn
  rw [←sInf_image]
  apply IsCompact.sInf_mem
  · exact hK.image_of_continuousOn continuous_supEdist.continuousOn
  · use supEdist s0 s, s0, by simp [K]

open Classical in
/-- The center of the minimal bounding sphere of a non empty bounded set -/
noncomputable def center
    {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {P} [MetricSpace P] [NormedAddTorsor V P] (s : Set P) :=
  (radius_mem_range s).choose

/-- The radius of the minimal bounding sphere of a set is the supremal distance
from its center to the set. -/
theorem radius_eq_supDist_center : radius s = supDist (center s) s :=
  (radius_mem_range s).choose_spec.symm

/-- The minimal bouding ball of a bounded set contains it. -/
theorem subset (h1 : IsBounded s) : s ⊆ Metric.closedBall (center s) (radius s) := by
  by_cases h0 : s.Nonempty
  · intro p hp
    rw [Metric.mem_closedBall, radius_eq_supDist_center, dist_comm]
    exact dist_le_supDist_of_mem h1 hp
  · simp [Set.not_nonempty_iff_eq_empty.mp h0]

/-- A set `s` is minimally enclosed by a closed ball with center `c` and radius `r`
if `s` is contained in the closed ball and any closed ball containing `s` has radius at least
`r`. -/
def IsMinimal {α} [PseudoMetricSpace α] (s : Set α) c r :=
  s ⊆ Metric.closedBall c r ∧ ∀ c', ∀ r', s ⊆ Metric.closedBall c' r' → r ≤ r'

theorem IsMinimal.of_isBounded (h0 : s.Nonempty) (h1 : IsBounded s) :
    IsMinimal s (center s) (radius s) := ⟨subset h1, radius_le h0 h1⟩

/-- The radius of a minimal bounding sphere is unique. -/
theorem radius_eq_radius_of_IsMinimal [PseudoMetricSpace α] {s : Set α} {x r1 y r2}
    (h1 : IsMinimal s x r1) (h2 : IsMinimal s y r2) : r1 = r2 :=
  le_antisymm (h1.right y r2 h2.left) (h2.right x r1 h1.left)

/-- The center of a minimal bounding sphere is unique.
Thus the minimal bounding sphere is unique. -/
theorem center_eq_center_of_IsMinimal
    {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {P} [MetricSpace P] [NormedAddTorsor V P] {s : Set P}
    (h0 : s.Nonempty) {x y : P} {r1 r2 : ℝ}
    (h1 : IsMinimal s x r1) (h2 : IsMinimal s y r2) : x = y := by
  have := radius_eq_radius_of_IsMinimal h1 h2
  subst this
  let s0 := h0.choose
  have hs0 : s0 ∈ s := h0.choose_spec
  have hr1 := calc
      r1 ≥ dist s0 y := h2.left hs0
      _ ≥ 0 := dist_nonneg
  let r0 := dist x y / 2
  let c := midpoint ℝ x y
  set B1 := closedBall x r1
  set B2 := closedBall y r1
  have h3 z (hz1 : z ∈ B1) (hz2 : z ∈ B2) : dist z c ^ 2 ≤ r1 ^ 2 - r0 ^ 2 :=
    let a := x -ᵥ z
    let b := y -ᵥ z
    calc
    dist z c ^ 2 = ‖c -ᵥ z‖ ^ 2 := by rw [dist_comm, dist_eq_norm_vsub]
    _ = (1 / 4 : ℝ) * ‖a + b‖ ^ 2  := by
      unfold a b
      rw [midpoint_vsub, ←smul_add, norm_smul, mul_pow]
      norm_num
    _ = (1 / 4 : ℝ) * (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 - ‖a - b‖ ^ 2) := by
      rw [norm_add_sq_real a b, norm_sub_sq_real a b]
      ring
    _ = (1 / 4 : ℝ) * (2 * ‖x -ᵥ z‖ ^ 2 + 2 * ‖y -ᵥ z‖ ^ 2 - ‖y -ᵥ x‖ ^ 2) := by
      congr 3
      rw [norm_sub_rev]
      simp [a, b]
    _ = (1 / 2 : ℝ) * ‖x -ᵥ z‖ ^ 2 + (1 / 2 : ℝ) * ‖y -ᵥ z‖ ^ 2 - (1 / 4 : ℝ) * ‖y -ᵥ x‖ ^ 2 := by
      ring
    _ ≤ (1 / 2 : ℝ) * r1 ^ 2 + (1 / 2 : ℝ) * r1 ^ 2 - (1 / 4 : ℝ) * (2 * r0) ^ 2 := by
      gcongr 4
      · simpa [B1, dist_comm, dist_eq_norm_vsub] using hz1
      · simpa [B2, dist_comm, dist_eq_norm_vsub] using hz2
      · apply le_of_eq
        rw [←dist_eq_norm_vsub, dist_comm]
        ring
    _ = r1 ^ 2 - r0 ^ 2 := by ring
  have h4 : s ⊆ closedBall c √(r1 ^ 2 - r0 ^ 2) := by
    intro z hz
    rw [Metric.mem_closedBall]
    calc
      _ = √(dist z c ^ 2) := by
        symm
        apply Real.sqrt_sq
        apply dist_nonneg
      _ ≤ √(r1 ^ 2 - r0 ^ 2) := Real.sqrt_le_sqrt (h3 z (h1.left hz) (h2.left hz))
  have := h1.right c (√(r1 ^ 2 - r0 ^ 2)) h4
  replace := calc
    r1 ^ 2 ≤ √(r1 ^ 2 - r0 ^ 2) ^ 2 := by gcongr 1
    _ = r1 ^ 2 - r0 ^ 2 := by
      apply Real.sq_sqrt
      calc
        0 ≤ dist s0 c ^ 2 := by apply sq_nonneg
        _ ≤ _ := h3 s0 (h1.left hs0) (h2.left hs0)
  replace : r0 = 0 := by nlinarith only [this]
  unfold r0 at this
  replace : dist x y = 0 := by linarith only [this]
  simpa [dist_eq_zero] using this

/-- Translating a set translates the center of its minimal bounding sphere accordingly. -/
theorem center_vadd (h1 : s.Nonempty) (h2 : IsBounded s) (v : V) :
    center (v +ᵥ s) = v +ᵥ center s := by
  have h1' : (v +ᵥ s).Nonempty := h1.image _
  have h2' : IsBounded (v +ᵥ s) := h2.vadd v
  have h3 := IsMinimal.of_isBounded h1' h2'
  have h4 : IsMinimal (v +ᵥ s) (v +ᵥ center s) (radius s) := by
    split_ands
    · rw [←Metric.vadd_closedBall]
      exact Set.vadd_set_mono (subset h2)
    · intro c' r' h
      simpa using radius_le h1' h2' c' _ h
  exact center_eq_center_of_IsMinimal h1' h3 h4

/-- The radius of the minimal bounding sphere of a bounded set with at least two points
is strictly positive. -/
theorem radius_pos (h1 : IsBounded s) (h2 : s.encard ≥ 2) : radius s > 0 := by
  obtain ⟨x0, hx0, x1, hx1, h3⟩ : ∃ x0 ∈ s, ∃ x1 ∈ s, x0 ≠ x1 := by
    have f : Fin 2 ↪ s := by
      by_cases h3 : s.Finite
      · have := h3.fintype
        let a : Fin (Fintype.card s) ↪ s := this.equivFin.symm.toEmbedding
        let b : Fin 2 ↪ Fin (Fintype.card s) :=
          Fin.castLEEmb (by apply ENat.coe_le_coe.mp; simp [h2])
        exact b.trans a
      · let a : ℕ ↪ s := Set.Infinite.natEmbedding s h3
        let b : Fin 2 ↪ ℕ := Fin.valEmbedding
        exact b.trans a
    let x0 := f ⟨0, by simp⟩
    let x1 := f ⟨1, by simp⟩
    use x0.1, x0.2, x1.1, x1.2
    rw [Subtype.coe_inj.ne]
    apply f.injective.ne
    simp
  set r := radius s
  set c := center s
  calc
    r = (r + r) / 2 := by ring
    _ ≥ (dist x0 c + dist c x1) / 2 := by
      gcongr 2
      · simpa using subset h1 hx0
      · simpa [dist_comm] using subset h1 hx1
    _ ≥ dist x0 x1 / 2 := by gcongr 1; apply dist_triangle
    _ > 0 / 2 := by gcongr 1; exact dist_pos.mpr h3
    _ = 0 := by simp

/-- The minimal bounding sphere of a finite set hits some point of the set. -/
theorem nonempty_sphere_of_finite (h1 : s.Finite) (h2 : s.Nonempty) :
    (s ∩ sphere (center s) (radius s)).Nonempty := by
  have hc := subset h1.isBounded
  set c := center s
  set r := radius s
  obtain ⟨y0, hy0, hy0'⟩ := supDist_mem_of_isFinite h1 h2 c
  rw [dist_comm] at hy0'
  set r' := supDist c s
  have h3 : r ≤ r' := by
    apply radius_le h2 h1.isBounded c r'
    intro z hz
    simpa [dist_comm] using dist_le_supDist_of_mem h1.isBounded hz
  have h4 : r' ≤ r := by simpa [hy0'] using hc hy0
  replace h2 : r = r' := le_antisymm h3 h4
  have h5 : y0 ∈ s ∩ sphere c r := by simp [sphere, hy0, hy0', h2]
  use y0

end BoundingSphere

end
