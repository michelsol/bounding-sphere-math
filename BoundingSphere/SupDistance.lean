/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic.Finiteness

/-!
# Supremal extended distance to a set


## Main results


## Tags
metric space
-/

section SupEdist

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v

variable {α : Type u} {β : Type v}

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

namespace EMetric

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

end EMetric

end SupEdist

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`sInf` and `sSup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/

section SupDist

open NNReal ENNReal Topology Set Filter Pointwise Bornology EMetric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t : Set α} {x y : α} {Φ : α → β}

namespace Metric

/-! ### Supremal distance of a point to a set as a function into `ℝ`. -/

/-- The supremal distance of a point to a set -/
noncomputable def supDist (x : α) (s : Set α) : ℝ :=
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

end Metric

end SupDist
