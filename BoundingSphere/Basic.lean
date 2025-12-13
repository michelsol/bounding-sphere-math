/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/
import Mathlib

/-!
# Supremal extended distance to a set


## Main results


## Tags
metric space
-/

noncomputable section

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v

variable {α : Type u} {β : Type v}

namespace EMetric

section SupEdist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

/-! ### Supremal distance of a point to a set as a function into `ℝ≥0∞`. -/

/-- The supremal edistance of a point to a set -/
noncomputable def supEdist (x : α) (s : Set α) : ℝ≥0∞ := ⨆ y ∈ s, edist x y

@[simp]
theorem supEdist_empty : supEdist x ∅ = 0 := iSup_emptyset

theorem supEdist_le {d} : supEdist x s ≤ d ↔ ∀ y ∈ s, edist x y ≤ d := by
  simp only [supEdist, iSup_le_iff]

/-- The supEdist to a union is the maximum of the supEdist -/
@[simp]
theorem supEdist_union : supEdist x (s ∪ t) = supEdist x s ⊔ supEdist x t := iSup_union

@[simp]
theorem supEdist_iUnion (f : ι → Set α) (x : α) : supEdist x (⋃ i, f i) = ⨆ i, supEdist x (f i) :=
  iSup_iUnion f _

lemma supEdist_biUnion {ι : Type*} (f : ι → Set α) (I : Set ι) (x : α) :
    supEdist x (⋃ i ∈ I, f i) = ⨆ i ∈ I, supEdist x (f i) := by simp only [supEdist_iUnion]

/-- The supEdist to a singleton is the edistance to the single point of this singleton -/
@[simp]
theorem supEdist_singleton : supEdist x {y} = edist x y := iSup_singleton

/-- The supEdist to a set is bounded below by the edist to any of its points -/
theorem edist_le_supEdist_of_mem (h : y ∈ s) : edist x y ≤ supEdist x s := by
  convert le_iSup₂ y h using 1
  rfl

/-- If a point `x` belongs to `s`, then its supEdist to `s` is less than or equal to the
diameter of `s` -/
theorem supEdist_le_diam_of_mem (h : x ∈ s) : supEdist x s ≤ diam s :=
  iSup₂_le fun _ hy => edist_le_diam_of_mem h hy

/-- The supEdist is monotone with respect to inclusion. -/
@[gcongr]
theorem supEdist_mono (h : s ⊆ t) : supEdist x s ≤ supEdist x t :=
  iSup_le_iSup_of_subset h

/-- The supEdist to a set is `> r` iff there exists a point in the set at edistance `> r` -/
theorem lt_supEdist_iff {r : ℝ≥0∞} : r < supEdist x s ↔ ∃ y ∈ s, r < edist x y := by
  simp_rw [supEdist, lt_iSup_iff, exists_prop]

/-- The supEdist of `x` to `s` is bounded by the sum of the supEdist of `y` to `s` and
the edist from `x` to `y` -/
theorem supEdist_le_supEdist_add_edist [Nonempty α] : supEdist x s ≤ supEdist y s + edist x y := by
  unfold supEdist
  rw [ENNReal.iSup_add]
  refine iSup_mono fun i ↦ ?_
  obtain hi | hi := em' (i ∈ s)
  · simp [hi]
  have := Nonempty.intro hi
  rw [ENNReal.iSup_add]
  refine iSup_mono fun j ↦ ?_
  rw [add_comm]
  apply edist_triangle

/-- The supEdist to a set depends continuously on the point -/
@[continuity, fun_prop]
theorem continuous_supEdist [Nonempty α] : Continuous fun x => supEdist x s :=
  continuous_of_le_add_edist 1 (by simp) <| by
    simp only [one_mul, supEdist_le_supEdist_add_edist, forall₂_true_iff]

/-- The supremum edistance is invariant under isometries -/
theorem supEdist_image (hΦ : Isometry Φ) : supEdist (Φ x) (Φ '' t) = supEdist x t := by
  simp only [supEdist, iSup_image, hΦ.edist_eq]

@[to_additive (attr := simp)]
theorem supEdist_smul {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Set α) :
    supEdist (c • x) (c • s) = supEdist x s :=
  supEdist_image (isometry_smul _ _)

theorem supEdist_eq_sSup : supEdist x s = sSup (edist x '' s) := sSup_image.symm

theorem supEdist_mem_of_isCompact (h1 : IsCompact s) (h2 : s.Nonempty) x :
    supEdist x s ∈ edist x '' s := by
  rw [supEdist_eq_sSup]
  apply IsCompact.sSup_mem
  · exact h1.image (continuous_const.edist continuous_id')
  · simp [h2]

theorem supEdist_mem_of_isFinite (h1 : s.Finite) (h2 : s.Nonempty) x :
    supEdist x s ∈ edist x '' s := supEdist_mem_of_isCompact h1.isCompact h2 _

theorem supEdist_ne_top_of_isBounded {α} [PseudoMetricSpace α] {s : Set α} (h1 : IsBounded s) x :
    supEdist x s ≠ ⊤ := by
  obtain h2 | h2 := s.eq_empty_or_nonempty
  · simp [h2]
  let t0 := h2.choose
  rw [Metric.isBounded_iff_ediam_ne_top] at h1
  apply ne_top_of_le_ne_top (add_ne_top.mpr ⟨h1, edist_ne_top t0 x⟩)
  rw [supEdist_eq_sSup, sSup_le_iff]
  intro _ ⟨t, ht1, ht2⟩
  subst ht2
  rw [edist_comm]
  apply le_trans (edist_triangle t t0 x)
  exact add_le_add_right (edist_le_diam_of_mem ht1 h2.choose_spec) (edist t0 x)

theorem supEdist_eq_top_of_not_isBounded {α} [PseudoMetricSpace α]
    {s : Set α} (h1 : ¬IsBounded s) x : supEdist x s = ⊤ := by
  rw [supEdist_eq_sSup]
  contrapose! h1
  rw [Metric.isBounded_iff_ediam_ne_top, EMetric.diam_eq_sSup]
  contrapose! h1
  rw [sSup_eq_top] at h1 ⊢
  contrapose! h1
  obtain ⟨b, hb1, hb2⟩ := h1
  replace hb2 : ∀ t ∈ s, edist x t ≤ b := by simpa using hb2
  use b + b, add_lt_top.mpr ⟨hb1, hb1⟩
  intro _ ⟨t, ht, r, hr, hxy⟩
  subst hxy
  apply le_trans (edist_triangle t x r)
  rw [edist_comm]
  exact add_le_add (hb2 t ht) (hb2 r hr)

end SupEdist

end EMetric



/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`sInf` and `sSup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/

namespace Metric

section SupDist

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t : Set α} {x y : α} {Φ : α → β}

open EMetric

/-! ### Supremal distance of a point to a set as a function into `ℝ`. -/

/-- The supremal distance of a point to a set -/
def supDist (x : α) (s : Set α) : ℝ :=
  ENNReal.toReal (supEdist x s)

theorem supDist_eq_iSup : supDist x s = ⨆ y : s, dist x y := by
  rw [supDist, supEdist, iSup_subtype', ENNReal.toReal_iSup]
  · simp only [dist_edist]
  · finiteness

/-- The supremal distance is always nonnegative -/
theorem supDist_nonneg : 0 ≤ supDist x s := toReal_nonneg

/-- The supremal distance to the empty set is 0 -/
@[simp]
theorem supDist_empty : supDist x ∅ = 0 := by simp [supDist]

/-- The supremal distance to an unbounded set is `0`. -/
theorem supDist_eq_zero_of_not_isBounded (h1 : ¬IsBounded s) : supDist x s = 0 := by
  simp [supDist, supEdist_eq_top_of_not_isBounded h1, toReal_top]

/-- The supremal distance to a bounded set coincides with the supremal edistance. -/
theorem supEdist_eq_supDist_of_isBounded (h1 : IsBounded s) x :
    supEdist x s = ENNReal.ofReal (supDist x s) := by
  rw [supDist, ofReal_toReal]
  exact supEdist_ne_top_of_isBounded h1 x

theorem supDist_le_diam_of_mem (hs : IsBounded s) (h : x ∈ s) : supDist x s ≤ diam s :=
  toReal_mono (isBounded_iff_ediam_ne_top.mp hs) (supEdist_le_diam_of_mem h)

/-- The supremal distance to a singleton is the distance to the unique point in this singleton. -/
@[simp]
theorem supDist_singleton : supDist x {y} = dist x y := by simp [supDist, dist_edist]

/-- The supremal distance to a set is ≥ to the distance to any point in this set. -/
theorem dist_le_supDist_of_mem (hs : IsBounded s) (h : y ∈ s) : dist x y ≤ supDist x s := by
  rw [dist_edist, supDist]
  exact toReal_mono (supEdist_ne_top_of_isBounded hs _) (edist_le_supEdist_of_mem h)

lemma isLUB_supDist (hs : s.Nonempty) (hs' : IsBounded s) :
    IsLUB ((dist x ·) '' s) (supDist x s) := by
  simpa [supDist_eq_iSup, sSup_image']
    using isLUB_csSup (hs.image _) ⟨supDist x s, by
      simpa [upperBounds] using fun _ => dist_le_supDist_of_mem hs'⟩

/-- The supremal distance is monotone with respect to inclusion. -/
theorem supDist_mono (h : s ⊆ t) (ht : IsBounded t) : supDist x s ≤ supDist x t :=
  toReal_mono (supEdist_ne_top_of_isBounded ht _) (supEdist_mono h)

lemma supDist_le {r : ℝ} (hr : r ≥ 0) (hs : IsBounded s) :
    supDist x s ≤ r ↔ ∀ y ∈ s, dist x y ≤ r := by
  rw [supDist, ←le_ofReal_iff_toReal_le (supEdist_ne_top_of_isBounded hs x) hr, supEdist_le]
  constructor <;> intro h y hy <;> specialize h y hy <;>
    simpa [dist_edist, le_ofReal_iff_toReal_le (edist_ne_top x y) hr] using h

/-- The supDist to a set is `> r` iff there exists a point in the set at distance `> r` -/
theorem lt_supDist_iff {r : ℝ} (hr : r ≥ 0) (hs : IsBounded s) :
    r < supDist x s ↔ ∃ y ∈ s, r < dist x y := by
  simpa using not_congr (supDist_le hr hs)

/-- The supDist of `x` to `s` is bounded by the sum of the supDist of `y` to `s` and
the distance from `x` to `y` -/
theorem supDist_le_supDist_add_dist [Nonempty α] : supDist x s ≤ supDist y s + dist x y := by
  by_cases hs : IsBounded s
  · unfold supDist
    rw [dist_edist, ←toReal_add (supEdist_ne_top_of_isBounded hs y) (edist_ne_top x y)]
    apply toReal_mono
    · exact add_ne_top.mpr ⟨supEdist_ne_top_of_isBounded hs y, edist_ne_top x y⟩
    · exact supEdist_le_supEdist_add_edist
  · simp [supDist_eq_zero_of_not_isBounded hs]

/-- The supremal distance to a set is Lipschitz in point with constant 1 -/
theorem lipschitz_supDist_pt [Nonempty α] (s : Set α) : LipschitzWith 1 (supDist · s) :=
  LipschitzWith.of_le_add fun _ _ => supDist_le_supDist_add_dist

/-- The supremal distance to a set is uniformly continuous in point -/
theorem uniformContinuous_supDist_pt [Nonempty α] (s : Set α) : UniformContinuous (supDist · s) :=
  (lipschitz_supDist_pt s).uniformContinuous

/-- The minimal distance to a set is continuous in point -/
@[continuity, fun_prop]
theorem continuous_supDist_pt [Nonempty α] (s : Set α) : Continuous (supDist · s) :=
  (uniformContinuous_supDist_pt s).continuous

/-- The supremum distance is invariant under isometries. -/
theorem supDist_image (hΦ : Isometry Φ) : supDist (Φ x) (Φ '' t) = supDist x t := by
  simp [supDist, supEdist_image hΦ]

@[to_additive (attr := simp)]
theorem supDist_smul {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Set α) :
    supDist (c • x) (c • s) = supDist x s :=
  supDist_image (isometry_smul _ _)

theorem supDist_eq_sSup x : supDist x s = sSup (dist x '' s) := by
  rw [supDist, supEdist_eq_sSup, toReal_sSup]
  · congr 1
    ext x
    simp [edist_dist, dist_nonneg, toReal_ofReal]
  · simp [edist_ne_top]

theorem supDist_mem_of_isCompact (h1 : IsCompact s) (h2 : s.Nonempty) x :
    supDist x s ∈ dist x '' s := by
  rw [supDist_eq_sSup]
  apply IsCompact.sSup_mem
  · exact h1.image (continuous_const.dist continuous_id')
  · simp [h2]

theorem supDist_mem_of_isFinite (h1 : s.Finite) (h2 : s.Nonempty) x :
    supDist x s ∈ dist x '' s := supDist_mem_of_isCompact h1.isCompact h2 _

end SupDist

end Metric

end




/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/

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

namespace BoundingSphere

open Bornology ENNReal Metric EMetric InnerProductSpace Pointwise

variable {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {P} [MetricSpace P] [NormedAddTorsor V P] {s t : Set P}

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




/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/

/-!
# Upper bounds on the radius of the minimal bounding sphere

In this file we prove some upper bounds on the radius of the minimal bounding sphere
of a nonempty bounded set in a proper inner product space.

## Main results

- `BoundingSphere.center_mem_convexHull_sphere_of_finite`:
  The center of the minimal bounding sphere of a non empty finite set `X`
  is contained in the convex hull of the points of `X` that lie on the sphere.
- `BoundingSphere.radius_le_sqrt_of_finite`:
  An upper bound on the radius of the minimal bounding sphere of a finite set.
- `BoundingSphere.radius_le_sqrt_of_isBounded`:
  An upper bound on the radius of the minimal bounding sphere of a bounded set.
  This result was originally proved by H. Jung in 1901.
-/

namespace BoundingSphere

open Bornology ENNReal Metric InnerProductSpace Pointwise Finset Module

variable {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {X : Set V}

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
theorem radius_le_sqrt_of_finite [DecidableEq V] {d : ℕ} (hX1 : X.Finite) (hXd : X.ncard ≤ d + 1) :
    radius X ≤ √(d / (2 * d + 2) : ℝ) * diam X := by
  -- Handle cases where `X` has 0 or 1 point first to avoid later divisions by a diameter of zero.
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
theorem radius_le_sqrt_of_isBounded [DecidableEq V] (hX1 : IsBounded X) :
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
