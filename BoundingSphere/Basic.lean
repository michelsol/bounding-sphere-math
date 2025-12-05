/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/
import Mathlib

section
open Bornology ENNReal Metric
variable [PseudoMetricSpace α] {X : Set α}

/-- The supremal distance from a point `c` to a set `X`,
which is equal to `⊤` if `X` is unbounded. -/
noncomputable def supEDist {α} [EDist α] (X : Set α) c := sSup {edist s c | s ∈ X}

/-- If `X` is bounded, then the supremal distance from `X` to `c` is not `⊤`. -/
theorem supEDist_ne_top_of_isBounded (h1 : IsBounded X) c : supEDist X c ≠ ⊤ := by
  unfold supEDist
  obtain h2 | h2 := X.eq_empty_or_nonempty
  · simp [h2]
  · let s0 := h2.choose
    rw [isBounded_iff_ediam_ne_top] at h1
    have := add_ne_top.mpr ⟨h1, edist_ne_top s0 c⟩
    apply ne_top_of_le_ne_top this
    rw [sSup_le_iff]
    intro _ ⟨s, hs1, hs2⟩
    subst hs2
    apply le_trans (edist_triangle s s0 c)
    gcongr 1
    exact EMetric.edist_le_diam_of_mem hs1 h2.choose_spec

/-- If `X` is unbounded, then the supremal distance from `X` to `c` is `⊤`. -/
theorem supEDist_eq_top_of_not_isBounded (h1 : ¬IsBounded X) c : supEDist X c = ⊤ := by
  unfold supEDist
  contrapose! h1
  rw [isBounded_iff_ediam_ne_top, EMetric.diam_eq_sSup]
  contrapose! h1
  rw [sSup_eq_top] at h1 ⊢
  contrapose! h1
  obtain ⟨b, hb1, hb2⟩ := h1
  replace hb2 : ∀ s ∈ X, edist s c ≤ b := by simpa using hb2
  use b + b, add_lt_top.mpr ⟨hb1, hb1⟩
  intro _ ⟨x, hx, y, hy, hxy⟩
  subst hxy
  apply le_trans (edist_triangle x c y)
  gcongr 2
  · simpa using hb2 x hx
  · simpa [edist_comm] using hb2 y hy

/-- If `X` is finite, then the supremal distance from `X` to `c` is attained. -/
theorem supEDist_mem_of_isFinite (h1 : X.Finite) (h2 : X.Nonempty) c :
    supEDist X c ∈ (edist · c) '' X := by
  have h1' := h1.fintype
  convert_to sSup ((edist · c) '' X.toFinset) ∈ (edist · c) '' X using 1
  · rw [Set.coe_toFinset]
    rfl
  rw [←X.toFinset.sup'_eq_csSup_image (by simpa using h2)]
  apply Finset.sup'_mem
  · grind
  · intro s hs
    use s, by simpa using hs

/-- If `X` is compact, then the supremal distance from `X` to `c` is attained. -/
theorem supEDist_mem_of_isCompact (h1 : IsCompact X) (h2 : X.Nonempty) c :
    supEDist X c ∈ (edist · c) '' X := by
  apply IsCompact.sSup_mem
  · apply h1.image
    fun_prop
  · simp [h2]

theorem edist_le_supEDist c {y} (hy : y ∈ X) : edist y c ≤ supEDist X c := by
  unfold supEDist
  rw [le_sSup_iff]
  intro b hb
  simp [upperBounds] at hb
  exact hb y hy

theorem supEDist_image_add_right [AddGroup α] [IsIsometricVAdd αᵃᵒᵖ α] (X : Set α) c a :
    supEDist ((· + a) '' X) c = supEDist X (c - a) := by
  apply csSup_eq_csSup_of_forall_exists_le
  · intro _ ⟨x, hx, hx2⟩
    subst hx2
    simp only [Set.mem_setOf_eq, exists_exists_and_eq_and]
    use x - a, by simpa [←sub_eq_add_neg] using hx, by rw [edist_sub_right]
  · intro _ ⟨y, hy, hy2⟩
    subst hy2
    simp only [Set.mem_setOf_eq, exists_exists_and_eq_and]
    use y + a, by simpa using hy
    calc
      _ = edist (y + a - a) (c - a) := by congr 1; simp
      _ ≤ _ := by rw [edist_sub_right]

theorem supEDist_image_sub_right [AddGroup α] [IsIsometricVAdd αᵃᵒᵖ α] (X : Set α) c a :
    supEDist ((· - a) '' X) c = supEDist X (c + a) := by
  convert supEDist_image_add_right X c (-a) using 2
  · simp [sub_eq_add_neg]
  · simp


/-- The supremal distance from a point `c` to a set `X`, as a real number,
which is equal to `0` if `X` is unbounded. -/
noncomputable def supDist (X : Set α) c := (supEDist X c).toReal

theorem supDist_eq c : supDist X c = sSup {dist s c | s ∈ X} := by
  unfold supDist supEDist
  rw [toReal_sSup]
  · congr 1
    ext x
    simp [edist_dist, dist_nonneg, toReal_ofReal]
  · simp [edist_ne_top]

/-- If `X` is unbounded, then the supremal distance from `X` to `c` is `0`. -/
theorem supDist_eq_zero_of_not_isBounded (h1 : ¬IsBounded X) c : supDist X c = 0 := by
  unfold supDist
  simp [supEDist_eq_top_of_not_isBounded h1, toReal_top]

theorem supEDist_eq_supDist_of_isBounded (h1 : IsBounded X) c :
    supEDist X c = ENNReal.ofReal (supDist X c) := by
  unfold supDist
  rw [ofReal_toReal]
  exact supEDist_ne_top_of_isBounded h1 c

/-- If `X` is finite, then the supremal distance from `X` to `c` is attained. -/
theorem supDist_mem_of_isFinite c (h1 : X.Finite) (h2 : X.Nonempty) :
    supDist X c ∈ (dist · c) '' X := by
  unfold supDist
  obtain ⟨x, hx1, hx2⟩ := supEDist_mem_of_isFinite h1 h2 c
  rw [←hx2]
  use x, hx1
  simp [dist_edist]

/-- If `X` is compact, then the supremal distance from `X` to `c` is attained. -/
theorem supDist_mem_of_isCompact (h1 : IsCompact X) (h2 : X.Nonempty) c :
    supDist X c ∈ (dist · c) '' X := by
  rw [supDist_eq]
  apply IsCompact.sSup_mem
  · apply h1.image
    fun_prop
  · simp [h2]

theorem dist_le_supDist (h1 : IsBounded X) c {y} (hy : y ∈ X) : dist y c ≤ supDist X c := by
  unfold supDist
  apply (edist_le_ofReal (by simp)).mp
  change edist y c ≤ ENNReal.ofReal (supDist X c)
  rw [←supEDist_eq_supDist_of_isBounded h1 c]
  apply edist_le_supEDist c hy

theorem supDist_image_add_right [AddGroup α] [IsIsometricVAdd αᵃᵒᵖ α] (X : Set α) c a :
    supDist ((· + a) '' X) c = supDist X (c - a) := by
  unfold supDist
  rw [supEDist_image_add_right]

theorem supDist_image_sub_right [AddGroup α] [IsIsometricVAdd αᵃᵒᵖ α] (X : Set α) c a :
    supDist ((· - a) '' X) c = supDist X (c + a) := by
  unfold supDist
  rw [supEDist_image_sub_right]

end












namespace BoundingSphere
open Bornology ENNReal Metric InnerProductSpace

section
variable {α} {X : Set α} [PseudoMetricSpace α]

/-- The radius of the minimal bounding sphere of a set `X`, defined as the infimum of the supremal
distance from a point to the set. -/
noncomputable def radius (X : Set α) := sInf (Set.range (supDist X))

/-- The radius of the minimal bounding sphere is non negative. -/
theorem radius_nonneg : radius X ≥ 0 := by
  apply Real.sInf_nonneg ?_
  intro _ ⟨x, hx⟩
  subst hx
  simp [supDist]

/-- The radius of the minimal bounding sphere of the empty set is `0`. -/
@[simp]
theorem radius_empty [Inhabited α] : radius (∅ : Set α) = 0 := by
  unfold radius supDist supEDist
  simp

theorem ofReal_radius_eq_of_isBounded [Inhabited α] (h1 : IsBounded X) :
    ENNReal.ofReal (radius X) = sInf (Set.range (supEDist X)) := by
  unfold radius
  obtain h0 | h0 := X.eq_empty_or_nonempty
  · unfold supDist supEDist
    simp [h0]
  symm
  calc
  _ = ENNReal.ofReal (sInf (Set.range (supEDist X))).toReal := by
    rw [ofReal_toReal]
    by_contra! h2
    rw [sInf_eq_top] at h2
    contrapose! h2
    let s0 := h0.choose
    use supEDist X s0, by simp, supEDist_ne_top_of_isBounded h1 s0
  _ = ENNReal.ofReal (sInf (ENNReal.toReal '' Set.range (supEDist X))) := by
    rw [toReal_sInf]
    intro _ ⟨x, hx⟩
    subst hx
    exact supEDist_ne_top_of_isBounded h1 x
  _ = ENNReal.ofReal (sInf (Set.range (ENNReal.toReal ∘ supEDist X))) := by rw [Set.range_comp]

/-- The radius of the minimal bounding sphere of a bounded set `X` is less than or equal to
that of any other ball containing `X`. -/
theorem radius_le [Inhabited α] (h1 : IsBounded X) (h0 : X.Nonempty) :
    ∀ c', ∀ r', X ⊆ closedBall c' r' → radius X ≤ r' := by
  intro c' r' h2
  have hr' := calc
      r' ≥ dist h0.choose c' := h2 h0.choose_spec
      _ ≥ 0 := dist_nonneg
  rw [←ofReal_le_ofReal_iff hr', ofReal_radius_eq_of_isBounded h1, sInf_le_iff]
  intro s hs
  replace hs : ∀ x, s ≤ supEDist X x := by simpa [lowerBounds] using hs
  specialize hs c'
  rw [supEDist, le_sSup_iff] at hs
  apply hs
  intro _ ⟨a, ha, ha2⟩
  subst ha2
  rw [edist_le_ofReal hr']
  exact h2 ha

/-- The radius of the minimal bounding sphere of a singleton is `0`. -/
@[simp]
theorem radius_singleton [Inhabited α] (a : α) : radius {a} = 0 := by
  suffices radius {a} ≤ 0 by
    apply le_antisymm this
    apply radius_nonneg
  apply radius_le isBounded_singleton (Set.singleton_nonempty a) a 0
  simp

end

section
variable {α} {X : Set α} [PseudoMetricSpace α] [AddGroup α] [IsIsometricVAdd αᵃᵒᵖ α]

/-- Translating a set `X` does not change the radius of its minimal bounding sphere. -/
theorem radius_image_add_right (X : Set α) a :
    radius ((· + a) '' X) = radius X := by
  unfold radius
  convert_to sInf (Set.range (supDist X ∘ (· - a))) = _ using 3
  · ext c
    rw [supDist_image_add_right, Function.comp_apply]
  congr 1
  apply Function.Surjective.range_comp
  simpa [sub_eq_add_neg] using add_right_surjective (-a)

/-- Translating a set `X` does not change the radius of its minimal bounding sphere. -/
theorem radius_image_sub_right (X : Set α) a :
    radius ((· - a) '' X) = radius X := by
  simpa [sub_eq_add_neg] using radius_image_add_right X (-a)

end

section
variable {α} {X : Set α} [PseudoMetricSpace α] [Inhabited α] [ProperSpace α]

/-- If `X` is bounded, then the radius is attained
as the supremal distance from some point in `X`. -/
theorem radius_mem_of_isBounded (h1 : IsBounded X) : radius X ∈ Set.range (supDist X) := by
  unfold radius
  obtain h0 | h0 := X.eq_empty_or_nonempty
  · unfold supDist supEDist
    simp [h0]

  let s0 := h0.choose
  have hs0 : s0 ∈ X := h0.choose_spec
  let K := closedBall s0 (2 * supDist X s0)
  suffices sInf (supDist X '' K) ∈ supDist X '' K by
    apply Set.mem_range_of_mem_image (supDist X) K
    convert this using 1
    apply csInf_eq_csInf_of_forall_exists_le
    · intro _ ⟨c, hc⟩
      subst hc
      by_cases hc2 : c ∈ K
      · use supDist X c
        split_ands
        · use c
        · simp
      · replace hc2 : dist c s0 > 2 * supDist X s0 := by simpa [K] using hc2
        use supDist X s0
        split_ands
        · use s0; simp [K, supDist]
        · calc
            supDist X c = (supEDist X c).toReal := rfl
            _ ≥ (edist s0 c - supEDist X s0).toReal := by
              gcongr 1
              · exact supEDist_ne_top_of_isBounded h1 c
              · erw [le_sSup_iff]
                intro b hb
                simp [upperBounds] at hb
                calc
                  _ ≤ edist s0 c := by apply tsub_le_self
                  _ ≤ b := hb s0 hs0
            _ = (edist c s0).toReal - (supEDist X s0).toReal := by
              rw [toReal_sub_of_le]
              · rw [edist_comm]
              · suffices supDist X s0 ≤ dist s0 c by
                  rw [←toReal_le_toReal (supEDist_ne_top_of_isBounded h1 s0) (edist_ne_top _ _)]
                  rw [edist_dist, toReal_ofReal dist_nonneg]
                  simpa using this
                rw [dist_comm]
                have : supDist X s0 ≥ 0 := by unfold supDist; simp
                linarith only [hc2, this]
              · apply edist_ne_top
            _ = dist c s0 - supDist X s0 := by congr 1; simp [edist_dist]
            _ ≥ _ := by linarith only [hc2]
    · intro _ ⟨y, hy1, hy2⟩
      subst hy2
      use supDist X y
      simp

  apply IsCompact.sInf_mem
  · apply IsCompact.image_of_continuousOn
    · apply isCompact_closedBall
    · apply Continuous.continuousOn
      apply UniformContinuous.continuous
      apply LipschitzWith.uniformContinuous (K := (1 : ℝ).toNNReal)
      apply LipschitzWith.of_dist_le'
      suffices ∀ x y, supDist X x - supDist X y ≤ dist x y by
        intro x y
        change |_| ≤ _
        rw [abs_le]
        split_ands
        · rw [dist_comm]
          linarith only [this y x]
        · simpa using this x y
      intro x y
      suffices supDist X x ≤ supDist X y + dist x y by linarith only [this]
      calc
        supDist X x = (supEDist X x).toReal := rfl
        _ ≤ (supEDist X y + edist x y).toReal := by
          gcongr 1
          · exact add_ne_top.mpr ⟨supEDist_ne_top_of_isBounded h1 y, by apply edist_ne_top⟩
          calc
            supEDist X x = sSup {edist s x | s ∈ X} := by rfl
            _ ≤ sSup {edist s y | s ∈ X} + edist x y := by
              rw [sSup_le_iff]
              intro _ ⟨s, hs, hs2⟩; subst hs2
              calc
                edist s x ≤ edist s y + edist y x := by apply edist_triangle
                _ = edist s y + edist x y := by congr 1; rw [edist_comm]
                _ ≤ _ := by
                  gcongr 1
                  rw [le_sSup_iff]
                  intro t ht
                  simp [upperBounds] at ht
                  exact ht s hs
            _ = supEDist X y + edist x y := rfl
        _ = (supEDist X y).toReal + (edist x y).toReal :=
          toReal_add (supEDist_ne_top_of_isBounded h1 y) (by apply edist_ne_top)
        _ = _ := by congr 1; simp [edist_dist]
  · use supDist X s0, s0, by simp [K, supDist]

open Classical in
/-- The center of the minimal bounding sphere of a bounded set `X`,
defined as a point where the radius is attained. -/
noncomputable def center (X : Set α) :=
  if h1 : IsBounded X then (radius_mem_of_isBounded h1).choose else default

theorem radius_eq_supDist_center_of_isBounded (h1 : IsBounded X) :
    radius X = supDist X (center X) := by
  unfold center
  split_ifs
  exact (radius_mem_of_isBounded h1).choose_spec.symm

/-- The minimal bounding ball of a bounded set `X` contains the set `X`. -/
theorem subset (h1 : IsBounded X) : X ⊆ closedBall (center X) (radius X) := by
  by_cases h0 : X.Nonempty
  · intro s hs
    rw [mem_closedBall, radius_eq_supDist_center_of_isBounded h1]
    exact dist_le_supDist h1 (center X) hs
  · simp [Set.not_nonempty_iff_eq_empty.mp h0]

end


section
variable {α} {X : Set α}

/-- A set `X` is minimally enclosed by a closed ball with center `c` and radius `r`
if `X` is contained in the closed ball and any closed ball containing `X` has radius at least
`r`. -/
def IsMinimal [PseudoMetricSpace α] (X : Set α) c r :=
  X ⊆ closedBall c r ∧ ∀ c', ∀ r', X ⊆ closedBall c' r' → r ≤ r'

theorem IsMinimal.of_isBounded [PseudoMetricSpace α] [Inhabited α] [ProperSpace α]
    (h1 : IsBounded X) (h0 : X.Nonempty) :
    IsMinimal X (center X) (radius X) := ⟨subset h1, radius_le h1 h0⟩


/-- The radius of a minimal bounding sphere is unique. -/
theorem radius_eq_radius_of_IsMinimal [PseudoMetricSpace α]
    {x r1 y r2} (h1 : IsMinimal X x r1) (h2 : IsMinimal X y r2) : r1 = r2 :=
  le_antisymm (h1.right y r2 h2.left) (h2.right x r1 h1.left)

/-- The center of a minimal bounding sphere is unique.
Thus the minimal bounding sphere is unique. -/
theorem center_eq_center_of_IsMinimal
    [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    (h0 : X.Nonempty)
    {x r1 y r2} (h1 : IsMinimal X x r1) (h2 : IsMinimal X y r2) : x = y := by
  have h := radius_eq_radius_of_IsMinimal h1 h2
  subst h
  let s0 := h0.choose
  have hs0 : s0 ∈ X := h0.choose_spec
  have hr1 := calc
      r1 ≥ dist s0 y := h2.left hs0
      _ ≥ 0 := dist_nonneg
  let r0 := dist x y / 2
  let c := (1 / 2 : ℝ) • (x + y)
  set B1 := closedBall x r1
  set B2 := closedBall y r1
  have h5 z (hz1 : z ∈ B1) (hz2 : z ∈ B2) : dist z c ^ 2 ≤ r1 ^ 2 - r0 ^ 2 := calc
    dist z c ^ 2 = _ := by rw [dist_eq_norm]
    ‖z - c‖ ^ 2 = ‖(1 / 2 : ℝ) • (z - x + (z - y))‖ ^ 2 := by
      congr 2
      module
    _ = ‖(1 / 2 : ℝ)‖ ^ 2 * ‖(z - x + (z - y))‖ ^ 2 := by
      rw [norm_smul]
      ring
    _ = (1 / 4 : ℝ) * ‖(z - x + (z - y))‖ ^ 2 := by congr 1; norm_num
    _ = (1 / 4 : ℝ) * (2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 - ‖x - y‖ ^ 2) := by
      congr 1
      set a := z - x
      set b := z - y
      convert_to ‖a + b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 - ‖a - b‖ ^ 2 using 3
      · rw [norm_sub_rev]
        congr 1
        module
      generalize a = a, b = b
      rw [norm_add_sq_real, norm_sub_sq_real]
      ring
    _ = (1 / 2 : ℝ) * ‖z - x‖ ^ 2 + (1 / 2 : ℝ) * ‖z - y‖ ^ 2 - (1 / 4 : ℝ) * ‖x - y‖ ^ 2 := by ring
    _ ≤ (1 / 2 : ℝ) * r1 ^ 2 + (1 / 2 : ℝ) * r1 ^ 2 - (1 / 4 : ℝ) * (2 * r0) ^ 2 := by
      gcongr 4
      · simpa [B1, dist_eq_norm] using hz1
      · simpa [B2, dist_eq_norm] using hz2
      · apply le_of_eq
        calc
          _ = dist x y := by ring
          _ = ‖x - y‖ := by rw [dist_eq_norm]
    _ = r1 ^ 2 - r0 ^ 2 := by ring
  have h6 : X ⊆ closedBall c √(r1 ^ 2 - r0 ^ 2) := by
    intro s hs
    rw [mem_closedBall]
    calc
      _ = √(dist s c ^ 2) := by
        symm
        apply Real.sqrt_sq
        apply dist_nonneg
      _ ≤ √(r1 ^ 2 - r0 ^ 2) := Real.sqrt_le_sqrt (h5 s (h1.left hs) (h2.left hs))
  have h3 := h1.right c (√(r1 ^ 2 - r0 ^ 2)) h6
  replace h3 := calc
    r1 ^ 2 ≤ √(r1 ^ 2 - r0 ^ 2) ^ 2 := by gcongr 1
    _ = r1 ^ 2 - r0 ^ 2 := by
      apply Real.sq_sqrt
      calc
        0 ≤ dist s0 c ^ 2 := by apply sq_nonneg
        _ ≤ _ := h5 s0 (h1.left hs0) (h2.left hs0)
  replace h3 : r0 = 0 := by nlinarith only [h3]
  unfold r0 at h3
  replace h3 : dist x y = 0 := by linarith only [h3]
  simpa [dist_eq_zero] using h3

end

section
variable {α} {X : Set α}
variable [NormedAddCommGroup α] [InnerProductSpace ℝ α]
variable [Inhabited α] [ProperSpace α]

/-- Translating a bounded set `X` by `a`
translates the center of its minimal bounding sphere by `a`. -/
theorem center_image_add_right (h1 : IsBounded X) (h2 : X.Nonempty) a :
    center ((· + a) '' X) = center X + a := by
  set T := ((· + a) '' X)
  have h1' : IsBounded T := by
    apply isBounded_image_iff.mpr
    use diam X
    intro x hx y hy
    simpa using dist_le_diam_of_mem h1 hx hy
  have h2' : T.Nonempty := by apply h2.image
  have h3 := IsMinimal.of_isBounded h1' h2'
  have h4 : IsMinimal T (center X + a) (radius X) := by
    split_ands
    · simp only [T, Set.image_subset_iff, preimage_add_right_closedBall, add_sub_cancel_right]
      exact subset h1
    · intro c' r' h
      simp only [T, Set.image_subset_iff, preimage_add_right_closedBall] at h
      exact radius_le h1 h2 (c' - a) r' h
  exact center_eq_center_of_IsMinimal h2' h3 h4

/-- Translating a bounded set `X` by `-a`
translates the center of its minimal bounding sphere by `-a`. -/
theorem center_image_sub_right (h1 : IsBounded X) (h2 : X.Nonempty) a :
    center ((· - a) '' X) = center X - a := by
  simpa [sub_eq_add_neg] using center_image_add_right h1 h2 (-a)

end

section
variable {α} {X : Set α}

/-- The radius of the minimal bounding sphere of a bounded set `X` with at least two points
is strictly positive. -/
theorem radius_pos [MetricSpace α] [Inhabited α] [ProperSpace α]
    (h1 : IsBounded X) (h2 : X.encard ≥ 2) : radius X > 0 := by
  obtain ⟨x0, hx0, x1, hx1, h3⟩ : ∃ x0 ∈ X, ∃ x1 ∈ X, x0 ≠ x1 := by
    have f : Fin 2 ↪ X := by
      by_cases h3 : X.Finite
      · have := h3.fintype
        let a : Fin (Fintype.card X) ↪ X := this.equivFin.symm.toEmbedding
        let b : Fin 2 ↪ Fin (Fintype.card X) :=
          Fin.castLEEmb (by apply ENat.coe_le_coe.mp; simp [h2])
        exact b.trans a
      · let a : ℕ ↪ X := Set.Infinite.natEmbedding X h3
        let b : Fin 2 ↪ ℕ := Fin.valEmbedding
        exact b.trans a
    let x0 := f ⟨0, by simp⟩
    let x1 := f ⟨1, by simp⟩
    use x0.1, x0.2, x1.1, x1.2
    rw [Subtype.coe_inj.ne]
    apply f.injective.ne
    simp
  set r := radius X
  set c := center X
  calc
    r = (r + r) / 2 := by ring
    _ ≥ (dist x0 c + dist c x1) / 2 := by
      gcongr 2
      · simpa using subset h1 hx0
      · simpa [dist_comm] using subset h1 hx1
    _ ≥ dist x0 x1 / 2 := by gcongr 1; apply dist_triangle
    _ > 0 / 2 := by gcongr 1; exact dist_pos.mpr h3
    _ = 0 := by simp


/-- The minimal bounding sphere of a finite set `X` hits some point in `X`. -/
theorem nonempty_sphere_of_finite
    [PseudoMetricSpace α] [Inhabited α] [ProperSpace α]
    (h1 : X.Finite) (h2 : X.Nonempty) :
    (X ∩ sphere (center X) (radius X)).Nonempty := by
  have hc := subset h1.isBounded
  set c := center X
  set r := radius X
  obtain ⟨y0, hy0, hy0'⟩ := supDist_mem_of_isFinite c h1 h2
  dsimp at hy0'
  set r' := supDist X c
  have h3 : r ≤ r' := by
    apply radius_le h1.isBounded h2 c r'
    intro s hs
    exact dist_le_supDist h1.isBounded c hs
  have h4 : r' ≤ r := by simpa [hy0'] using hc hy0
  replace h2 : r = r' := by linarith only [h3, h4]
  have h5 : y0 ∈ X ∩ sphere c r := by simp [sphere, hy0, hy0', h2]
  use y0

/-- The center of the minimal bounding sphere of a non empty finite set `X`
is contained in the convex hull of the points of `X` that lie on the sphere. -/
theorem center_mem_convexHull_sphere_of_finite
    [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    [Inhabited α] [ProperSpace α]
    (hX1 : X.Finite) (hX2 : X.Nonempty) :
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
  obtain ⟨v, hv, h2⟩ : ∃ v : α, v ≠ 0 ∧ ∀ x ∈ convexHull ℝ Y, ⟪v, x - c⟫_ℝ > 0 := by
    set s : Set α := {0}
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
    let v := (InnerProductSpace.toDual ℝ α).symm f
    have hf (x : α) : f x = ⟪v, x⟫_ℝ := by simp [v]
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
    simp only [mem_closedBall, dist_eq_norm, r0]
    rw [Finset.le_sup'_iff]
    use x, by simpa using hx
  have h4 : r ≤ r0 := radius_le hX1.isBounded hX2 (c' δ0) r0 h3
  have h5 := calc
    r0 = √(r0 ^ 2) := by
      rw [Real.sqrt_sq]
      unfold r0
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
theorem encard_sphere_ge_two_of_finite
    [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    [Inhabited α] [ProperSpace α]
    (h : X.encard ≥ 2) (h' : X.Finite) :
    (X ∩ sphere (center X) (radius X)).encard ≥ 2 := by
  have hX : IsBounded X := h'.isBounded
  have hX2 : X.Nonempty := by
    apply Set.encard_ne_zero.mp
    by_contra! h0
    simp [h0] at h
  have hr := radius_le hX hX2
  have hc := subset hX
  set c := center X
  set r := radius X
  let hit := X ∩ sphere (center X) (radius X)
  change hit.encard ≥ 2
  obtain h0 | h0 : ¬hit.Finite ∨ hit.Finite := by tauto
  · rw [Set.encard_eq_top]
    · simp
    · simpa using h0
  obtain h1 | h1 | h1 : hit.encard = 0 ∨ hit.encard = 1 ∨ hit.encard ≥ 2 := by
    have := h0.fintype
    unfold Set.encard
    rw [ENat.card_eq_coe_natCard]
    norm_cast
    omega
  · exfalso
    rw [Set.encard_eq_zero] at h1
    have h2 := nonempty_sphere_of_finite h' hX2
    contrapose! h2
    exact h1
  · exfalso
    rw [Set.encard_eq_one] at h1
    obtain ⟨x, hx⟩ := h1
    have hx1 : x ∈ hit := by simp [hx]
    have hx2 : x ∈ X := hx1.left
    have hx3 := hx1.right
    have h1 : c ∈ convexHull ℝ hit := center_mem_convexHull_sphere_of_finite h' hX2
    replace h1 : c = x := by simpa [hx] using h1
    have h2 : r = 0 := by simpa [sphere, c, h1] using hx3.symm
    have h3 : r > 0 := radius_pos hX h
    linarith only [h2, h3]
  · exact h1


open Finset in
/-- An upper bound on the radius of the minimal bounding sphere of a finite set `X` -/
theorem radius_le_sqrt_of_finite
    [NormedAddCommGroup α] [InnerProductSpace ℝ α] [Inhabited α] [ProperSpace α] [DecidableEq α]
    (hX2 : X.Finite) :
    let d := X.ncard - 1
    radius X ≤ √(d / (2 * d + 2) : ℝ) * diam X := by

  intro d
  obtain hX3 | hX3 | hX3 : X.ncard = 0 ∨ X.ncard = 1 ∨ X.ncard ≥ 2 := by omega
  · rw [Set.ncard_eq_zero hX2] at hX3
    simp [hX3]
  · have ⟨a, ha⟩ := Set.ncard_eq_one.mp hX3
    simp [ha, radius_singleton]

  have hX4 : X.Nonempty := by
    by_contra! h
    rw [←Set.ncard_eq_zero (Set.finite_of_ncard_ne_zero (by linarith only [hX3]))] at h
    omega

  wlog hc : center X = 0
  · let T := (· - center X) '' X
    have hT : T.ncard = X.ncard := Set.ncard_image_of_injective _ sub_left_injective
    specialize this (X := T)
    specialize this (Set.Finite.image (· - center X) hX2)
    specialize this (by simpa [hT] using hX3)
    specialize this (by simpa [T] using hX4)
    specialize this (by simp [T, center_image_sub_right hX2.isBounded hX4])
    convert this using 1
    · simp [T, radius_image_sub_right]
    · congr 1
      · rw [hT]
      · unfold diam
        congr 1
        iterate 2 rw [EMetric.diam_eq_sSup]
        congr 1
        ext x
        simp [T]

  have hX : IsBounded X := hX2.isBounded
  set r := radius X
  let h3 := subset hX

  have h1' := hX2.fintype
  have h1 : X.toFinset.card ≥ 2 := by
    convert hX3 using 1
    exact Eq.symm (Set.ncard_eq_toFinset_card' X)

  have := Fintype.ofFinite (X ∩ sphere 0 r : Set α)
  let X' : Finset α := (X ∩ sphere 0 r : Set α).toFinset
  have hX'1 : X'.Nonempty := by simpa [X', hc] using nonempty_sphere_of_finite h1'.finite hX4
  have hS' : X' ⊆ X.toFinset := by simp [X']

  let n := #X'
  have hn : n ≠ 0 := by
    by_contra! hn
    rw [card_eq_zero] at hn
    simp [hn] at hX'1

  have h5 : center X ∈ convexHull ℝ X' := by
    simpa [X', hc] using center_mem_convexHull_sphere_of_finite hX2 hX4

  obtain ⟨l, h6, h7, h8⟩ : ∃ (l : α → ℝ),
      (∀ k ∈ X', l k ≥ 0) ∧ ∑ x ∈ X', l x = 1 ∧ center X = ∑ x ∈ X', l x • x := by
    rw [mem_convexHull'] at h5
    obtain ⟨w, g1, g2, g3⟩ := h5
    use w
    exact ⟨fun k hk => g1 k (by simpa using hk), g2, g3.symm⟩

  have h8' : diam X > 0 := by
    let a : Fin (Fintype.card X) ↪ X := h1'.equivFin.symm.toEmbedding
    let b : Fin 2 ↪ Fin (Fintype.card X) := Fin.castLEEmb (by simpa [←Set.toFinset_card] using h1)
    let x0 := a (b ⟨0, by simp⟩)
    let x1 := a (b ⟨1, by simp⟩)
    have x : x0 ≠ x1 := (a.injective.comp b.injective).ne (by simp)
    calc
      0 < dist x0 x1 := by apply dist_pos.mpr; exact x
      _ ≤ diam X := dist_le_diam_of_mem hX x0.2 x1.2

  have h9 (i : α) (hi : i ∈ X') := calc
    1 - l i = ∑ k ∈ X', l k - l i := by rw [h7]
    _ = ∑ k ∈ X' \ {i}, l k + l i - l i := by
      have h : {i} ⊆ X' := by simpa using hi
      simp [←sum_sdiff h]
    _ = ∑ k ∈ X' \ {i}, l k * 1 := by ring_nf
    _ ≥ ∑ k ∈ X' \ {i}, l k * (‖k - i‖ ^ 2 / diam X ^ 2) := by
      gcongr 2 with k hk
      · simp at hk
        exact h6 k (by simp [hk])
      · simp at hk
        suffices dist k i ^ 2 ≤ diam X ^ 2 by
          field_simp
          simpa [dist_eq_norm] using this
        gcongr 1
        apply dist_le_diam_of_mem hX
        · exact Set.mem_toFinset.mp (hS' hk.left)
        · exact Set.mem_toFinset.mp (hS' hi)
    _ = (1 / diam X ^ 2) * ∑ k ∈ X' \ {i}, l k * ‖k - i‖ ^ 2 := by
      rw [mul_sum]
      congr! 1 with k hk
      field_simp
    _ = (1 / diam X ^ 2) * ∑ k ∈ X', l k * ‖k - i‖ ^ 2 := by
      congr 1
      have h : {i} ⊆ X' := by simpa using hi
      simp [←sum_sdiff h]
    _ = (1 / diam X ^ 2) * ∑ k ∈ X',
          (l k * ‖k‖ ^ 2 + l k * ‖i‖ ^ 2 - 2 * (l k * ⟪k, i⟫_ℝ)) := by
      congr! 2 with k hk
      rw [norm_sub_sq_real]
      ring
    _ = (1 / diam X ^ 2) * (
          ∑ k ∈ X', l k * ‖k‖ ^ 2 + ∑ k ∈ X', l k * ‖i‖ ^ 2 -
          2 * ∑ k ∈ X', l k * ⟪k, i⟫_ℝ) := by
      congr 1
      conv_lhs => rw [sum_sub_distrib, sum_add_distrib]
      congr 2
      rw [mul_sum]
    _ = (1 / diam X ^ 2) * (
          ∑ k ∈ X', l k * r ^ 2 + ∑ k ∈ X', l k * r ^ 2 -
          2 * ∑ k ∈ X', l k * ⟪k, i⟫_ℝ) := by
      congr! 6 with k hk
      · simp [X'] at hk
        simp [hk]
      · simp [X'] at hi
        simp [hi]
    _ = (1 / diam X ^ 2) * (
          r ^ 2 * ∑ k ∈ X', l k + r ^ 2 * ∑ k ∈ X', l k -
          2 * ∑ k ∈ X', l k * ⟪k, i⟫_ℝ) := by
      congr 3
      all_goals
      · rw [mul_sum]
        congr! 1 with k hk
        ring
    _ = (1 / diam X ^ 2) * (2 * r ^ 2 - 2 * ∑ k ∈ X', l k * ⟪k, i⟫_ℝ) := by
      congr 2
      rw [h7]
      ring
    _ = (1 / diam X ^ 2) * (2 * r ^ 2 - 2 * (∑ k ∈ X', l k * ⟪k, i⟫_ℝ)) := by
      ring
    _ = (1 / diam X ^ 2) * (2 * r ^ 2 - 2 * (∑ k ∈ X', ⟪l k • k, i⟫_ℝ)) := by
      congr! 4 with k hk
      rw [real_inner_smul_left]
    _ = (1 / diam X ^ 2) * (2 * r ^ 2 - 2 * (⟪∑ k ∈ X', l k • k, i⟫_ℝ)) := by
      congr! 4 with k hk
      rw [sum_inner]
    _ = (1 / diam X ^ 2) * (2 * r ^ 2) := by simp [←h8, hc]
    _ = 2 * r ^ 2 / diam X ^ 2 := by field_simp

  have h10 := calc
    n - 1 = ∑ i ∈ X', 1 - ∑ i ∈ X', l i := by simp [h7, n]
    _ = ∑ i ∈ X', (1 - l i) := by rw [sum_sub_distrib]
    _ ≥ ∑ i ∈ X', (2 * r ^ 2 / diam X ^ 2) := by
      gcongr 2 with i hi
      exact h9 i hi
    _ = n * (2 * r ^ 2 / diam X ^ 2) := by simp [sum_const, n]
    _ = 2 * n * r ^ 2 / diam X ^ 2 := by ring

  exact calc
    r = √(r ^ 2) := by
      symm
      apply Real.sqrt_sq
      calc
        0 ≤ _ := by apply dist_nonneg
        _ ≤ r := h3 hX4.choose_spec
    _ ≤ √(((n - 1) / (2 * n)) * diam X ^ 2) := by
      apply Real.sqrt_le_sqrt
      field_simp at h10 ⊢
      simpa using h10
    _ = √((n - 1) / (2 * n)) * √(diam X ^ 2) := by
      rw [Real.sqrt_mul]
      field_simp
      simp
      omega
    _ = √((n - 1) / (2 * n)) * diam X := by
      congr 1
      apply Real.sqrt_sq
      apply diam_nonneg
    _ ≤ √(d / (2 * d + 2)) * diam X := by
      gcongr 2
      field_simp
      have : n ≤ d + 1 := calc
        #X' ≤ #X.toFinset := Finset.card_le_card hS'
        _ = X.ncard := Eq.symm (Set.ncard_eq_toFinset_card' X)
        _ = d + 1 := by omega
      rify at this
      nlinarith only [this]

open Finset in
/-- An upper bound on the radius of the minimal bounding sphere of a bounded set `X`
with cardinality greater than the dimension of the ambient space -/
theorem radius_le_sqrt_of_encard_gt_finrank
    [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    [Inhabited α] [ProperSpace α] [DecidableEq α]
    [FiniteDimensional ℝ α]
    (hX : IsBounded X) (hX2 : X.encard ≥ Module.finrank ℝ α + 1) :
    let d := Module.finrank ℝ α
    radius X ≤ (√(d / (2 * d + 2) : ℝ) * diam X) := by
  intro d

  have hX3 : X.Nonempty := by
    apply Set.encard_ne_zero.mp
    by_contra! h1
    simp [h1] at hX2

  suffices ∃ c, X ⊆ closedBall c (√(d / (2 * d + 2) : ℝ) * diam X) by
    obtain ⟨c, hc⟩ := this
    apply radius_le hX hX3 c _ hc

  let F (x : X) := closedBall x.val (√(d / (2 * d + 2) : ℝ) * diam X)

  suffices (⋂ i, F i).Nonempty by
    let c := this.choose
    have hc : c ∈ (⋂ y : X, F y) := this.choose_spec
    simp [F] at hc
    use c
    simpa [mem_closedBall, dist_comm] using hc

  apply Convex.helly_theorem_compact (𝕜 := ℝ)
  · simpa using hX2
  · intro ⟨i, hi⟩
    apply convex_closedBall
  · intro ⟨i, hi⟩
    apply isCompact_closedBall
  · intro I hI
    let I' := SetLike.coe I
    replace hI : #I = d + 1 := by simpa using hI
    simp only [Set.iInter_coe_set, Set.nonempty_iInter, Set.mem_iInter]
    set c := center (Subtype.val '' I')
    have hI' := calc
      (Subtype.val '' I').ncard = I'.ncard := Set.ncard_image_of_injOn Set.injOn_subtype_val
      _ = d + 1 := by simpa [I'] using hI
    have hc : radius (Subtype.val '' I') ≤ _ := radius_le_sqrt_of_finite (Set.toFinite _)
    rw [hI'] at hc
    have hc' := subset (IsBounded.subset hX (Subtype.coe_image_subset X I))
    rw [Set.image_subset_iff] at hc'
    use c
    intro i hi hi2
    specialize hc' hi2
    suffices dist c i ≤ √(d / (2 * d + 2) : ℝ) * diam (X) by simpa [F] using this
    replace hc : dist c i ≤ √(d / (2 * d + 2) : ℝ) * diam (Subtype.val '' I') := by
      simpa [dist_comm] using hc'.trans hc
    apply le_trans hc
    gcongr 1
    exact diam_mono (Subtype.coe_image_subset X I) hX

/-- An upper bound on the radius of the minimal bounding sphere of a bounded set `X` -/
theorem radius_le_sqrt_of_isBounded
    [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    [Inhabited α] [ProperSpace α] [DecidableEq α]
    [FiniteDimensional ℝ α]
    (hX : IsBounded X) :
    let d := Module.finrank ℝ α
    radius X ≤ (√(d / (2 * d + 2) : ℝ) * diam X) := by
  intro d
  obtain h2 | h2 : X.encard ≤ d + 1 ∨ X.encard ≥ d + 1 := by apply le_total
  · apply le_trans (radius_le_sqrt_of_finite (Set.finite_of_encard_le_coe h2))
    gcongr 2
    replace h2 : X.ncard ≤ d + 1 := by
      apply ENat.coe_le_coe.mp
      convert h2 using 1
      simp [Set.ncard, Set.finite_of_encard_le_coe h2]
    replace h2 : X.ncard - 1 ≤ d := by omega
    rify at h2
    field_simp
    nlinarith only [h2]
  · exact radius_le_sqrt_of_encard_gt_finrank hX h2

/-- Jung's theorem. A bounded set `X` is contained in a closed ball of radius
at most `√(d / (2 * d + 2)) * diam X`, where `d` is the dimension of the ambient space. -/
theorem jung_theorem
    [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    [Inhabited α] [ProperSpace α] [DecidableEq α]
    [FiniteDimensional ℝ α]
    (hX : IsBounded X) :
    let d := Module.finrank ℝ α
    ∃ c, X ⊆ closedBall c (√(d / (2 * d + 2) : ℝ) * diam X) := by
  use center X
  apply (subset hX).trans
  apply closedBall_subset_closedBall
  exact radius_le_sqrt_of_isBounded hX

end

end BoundingSphere
