import Mathlib

section
open Bornology ENNReal Metric
variable {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))

noncomputable def supEDist c := sSup {edist s c | s ∈ S}

noncomputable def supDist c := (supEDist S c).toReal

theorem supEDist_ne_top_of_isBounded c (h1 : IsBounded S) : supEDist S c ≠ ⊤ := by
  unfold supEDist
  obtain h2 | h2 := S.eq_empty_or_nonempty
  · simp [h2]
  by_contra! h3
  rw [sSup_eq_top] at h3
  contrapose! h3
  let s0 := h2.choose
  use EMetric.diam S + edist s0 c
  use by
    apply add_lt_top.mpr
    split_ands
    · simpa [lt_top_iff_ne_top, ←isBounded_iff_ediam_ne_top] using h1
    · apply edist_lt_top
  intro t ⟨s, hs, hs2⟩
  subst hs2
  calc
    edist s c ≤ edist s s0 + edist s0 c := by apply edist_triangle
    _ ≤ _ := by gcongr 1; exact EMetric.edist_le_diam_of_mem hs h2.choose_spec

theorem supEDist_eq_top_of_not_isBounded c (h1 : ¬IsBounded S) : supEDist S c = ⊤ := by
  unfold supEDist
  rw [sSup_eq_top]
  contrapose! h1
  obtain ⟨b, h1, h2⟩ := h1
  simp at h2
  rw [isBounded_iff_ediam_ne_top]
  rw [EMetric.diam_eq_sSup]
  by_contra! h3
  rw [sSup_eq_top] at h3
  contrapose! h3
  use b + b, add_lt_top.mpr ⟨h1, h1⟩
  intro _ ⟨x, hx, y, hy, hxy⟩
  subst hxy
  calc
    edist x y ≤ edist x c + edist c y := by apply edist_triangle
    _ ≤ b + b := by
      gcongr 2
      · simpa using h2 x hx
      · simpa [edist_comm] using h2 y hy

theorem supEDist_eq_supDist_of_isBounded c (h1 : IsBounded S) :
    supEDist S c = ENNReal.ofReal (supDist S c) := by
  unfold supDist
  rw [ofReal_toReal]
  exact supEDist_ne_top_of_isBounded S c h1

theorem supEDist_mem_of_isFinite c (h1 : S.Finite) (h0 : S.Nonempty) :
    supEDist S c ∈ ((edist · c) '' S) := by
  have := h1.fintype
  change sSup ((edist · c) '' S) ∈ _
  convert_to sSup ((edist · c) '' S.toFinset) ∈ _ using 3
  · exact Eq.symm (Set.coe_toFinset S)
  rw [←Finset.sup'_eq_csSup_image S.toFinset (by simpa using h0)]
  apply Finset.sup'_mem
  · intro _ ⟨x, hx, hx2⟩ _ ⟨y, hy, hy2⟩
    subst hx2 hy2
    simp
    grind
  · intro s hs; use s, by simpa using hs

theorem supDist_mem_of_isFinite c (h1 : S.Finite) (h0 : S.Nonempty) :
    supDist S c ∈ (dist · c) '' S := by
  unfold supDist
  obtain ⟨x, hx1, hx2⟩ := supEDist_mem_of_isFinite S c h1 h0
  rw [←hx2]
  use x, hx1
  simp [dist_edist]

theorem edist_le_supEDist c y (hy : y ∈ S) : edist y c ≤ supEDist S c := by
  unfold supEDist
  rw [le_sSup_iff]
  intro b hb
  simp [upperBounds] at hb
  exact hb y hy

theorem dist_le_supDist (h1 : IsBounded S) c y (hy : y ∈ S) : dist y c ≤ supDist S c := by
  unfold supDist
  apply (edist_le_ofReal (by simp)).mp
  change edist y c ≤ ENNReal.ofReal (supDist S c)
  rw [←supEDist_eq_supDist_of_isBounded S c h1]
  apply edist_le_supEDist S c y hy

theorem supEDist_image_add_right c a :
    supEDist ((· + a) '' S) c = supEDist S (c - a) := by
  apply csSup_eq_csSup_of_forall_exists_le
  · intro _ ⟨x, hx, hx2⟩
    subst hx2
    simp at hx
    suffices ∃ y ∈ S, edist x c ≤ edist y (c - a) by simpa using this
    use x - a, by simpa using hx, by rw [edist_sub_right]
  · intro _ ⟨y, hy, hy2⟩
    subst hy2
    simp only [Set.image_add_right, Set.mem_preimage, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use y + a, by simpa using hy
    calc
      _ = edist (y + a - a) (c - a) := by congr 1; simp
      _ ≤ _ := by rw [edist_sub_right]

theorem supEDist_image_sub_right c a :
    supEDist ((· - a) '' S) c = supEDist S (c + a) := by
  convert supEDist_image_add_right S c (-a) using 2; simp

theorem supDist_image_add_right c a :
    supDist ((· + a) '' S) c = supDist S (c - a) := by
  unfold supDist
  rw [supEDist_image_add_right]

theorem supDist_image_sub_right c a :
    supDist ((· - a) '' S) c = supDist S (c + a) := by
  unfold supDist
  rw [supEDist_image_sub_right]

end













namespace BoundingSphere
open Bornology ENNReal Metric
variable {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))

noncomputable def eradius := sInf (Set.range (supEDist S))

noncomputable def radius := sInf (Set.range (supDist S))

theorem radius_empty : radius (∅ : Set (EuclideanSpace ℝ (Fin d))) = 0 := by
  unfold radius supDist supEDist
  simp

theorem eradius_eq_radius_of_isBounded (h1 : IsBounded S) :
    eradius S = ENNReal.ofReal (radius S) := by
  unfold eradius radius
  obtain h0 | h0 := S.eq_empty_or_nonempty
  · unfold supDist supEDist
    simp [h0]
  calc
  _ = ENNReal.ofReal (sInf (Set.range (supEDist S))).toReal := by
    rw [ofReal_toReal]
    by_contra! h2
    rw [sInf_eq_top] at h2
    contrapose! h2
    let s0 := h0.choose
    use supEDist S s0, by simp, supEDist_ne_top_of_isBounded S s0 h1
  _ = ENNReal.ofReal (sInf (ENNReal.toReal '' Set.range (supEDist S))) := by
    rw [toReal_sInf]
    intro y ⟨x, hx⟩
    subst hx
    apply supEDist_ne_top_of_isBounded S x h1
  _ = ENNReal.ofReal (sInf (Set.range (ENNReal.toReal ∘ supEDist S))) := by rw [Set.range_comp]

theorem eradius_eq_top_of_not_isBounded (h1 : ¬IsBounded S) : eradius S = ⊤ := by
  unfold eradius
  rw [sInf_eq_top]
  intro _ ⟨x, hx⟩
  subst hx
  exact supEDist_eq_top_of_not_isBounded S x h1

theorem radius_mem_of_isBounded (h1 : IsBounded S) :
    radius S ∈ Set.range (supDist S) := by
  unfold radius
  obtain h0 | h0 := S.eq_empty_or_nonempty
  · unfold supDist supEDist
    simp [h0]

  let s0 := h0.choose
  have hs0 : s0 ∈ S := h0.choose_spec

  let K := closedBall s0 (2 * supDist S s0)
  suffices sInf (supDist S '' K) ∈ supDist S '' K by
    apply Set.mem_range_of_mem_image (supDist S) K
    convert this using 1
    refine csInf_eq_csInf_of_forall_exists_le ?_ ?_
    swap
    · intro _ ⟨y, hy1, hy2⟩
      subst hy2
      use supDist S y
      simp
    · intro _ ⟨c, hc⟩
      subst hc
      by_cases hc2 : c ∈ K
      · use supDist S c
        split_ands
        · use c
        · simp
      · replace hc2 : dist c s0 > 2 * supDist S s0 := by simpa [K] using hc2
        use supDist S s0
        split_ands
        · use s0
          split_ands
          · simp [K]
            apply toReal_nonneg
          · simp
        · calc
            supDist S c = (supEDist S c).toReal := rfl
            _ ≥ (edist s0 c - supEDist S s0).toReal := by
              gcongr 1
              · exact supEDist_ne_top_of_isBounded S c h1
              change _ ≤ sSup _
              rw [le_sSup_iff]
              intro b hb
              simp [upperBounds] at hb
              calc
                _ ≤ edist s0 c := by apply tsub_le_self
                _ ≤ b := hb s0 hs0
            _ = (edist c s0).toReal - (supEDist S s0).toReal := by
              rw [toReal_sub_of_le]
              · rw [edist_comm]
              · suffices supDist S s0 ≤ dist s0 c by
                  rw [←toReal_le_toReal (supEDist_ne_top_of_isBounded S s0 h1) (edist_ne_top _ _)]
                  rw [edist_dist, toReal_ofReal (by apply dist_nonneg)]
                  simpa using this
                rw [dist_comm]
                have : supDist S s0 ≥ 0 := by unfold supDist; simp
                linarith
              · apply edist_ne_top
            _ = dist c s0 - supDist S s0 := by
              congr 1
              simp [edist_dist]
            _ ≥ _ := by linarith

  apply IsCompact.sInf_mem
  · apply IsCompact.image_of_continuousOn
    · apply isCompact_closedBall
    · apply Continuous.continuousOn
      apply UniformContinuous.continuous
      apply LipschitzWith.uniformContinuous (K := (1 : ℝ).toNNReal)
      apply LipschitzWith.of_dist_le'
      intro x y
      calc
        |supDist S x - supDist S y| ≤ dist x y := by
          revert x y
          suffices ∀ x y, supDist S x - supDist S y ≤ dist x y by
            intro x y
            rw [abs_le]
            split_ands
            · specialize this y x
              rw [dist_comm]
              linarith
            · exact this x y
          intro x y
          suffices supDist S x ≤ supDist S y + dist x y by linarith
          calc
            supDist S x = (supEDist S x).toReal := rfl
            _ ≤ (supEDist S y + edist x y).toReal := by
              gcongr 1
              · exact add_ne_top.mpr ⟨supEDist_ne_top_of_isBounded S y h1, by apply edist_ne_top⟩
              calc
                supEDist S x = sSup {edist s x | s ∈ S} := by rfl
                _ ≤ sSup {edist s y | s ∈ S} + edist x y := by
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
                _ = supEDist S y + edist x y := rfl
            _ = (supEDist S y).toReal + (edist x y).toReal :=
              toReal_add (supEDist_ne_top_of_isBounded S y h1) (by apply edist_ne_top)
            _ = _ := by congr 1; simp [edist_dist]
        _ = _ := by simp
  · use supDist S s0, s0, by simp [K, supDist]

open Classical in
noncomputable def center := if h1 : IsBounded S then (radius_mem_of_isBounded S h1).choose else 0

theorem radius_eq_supDist_center_of_isBounded (h1 : IsBounded S) :
    radius S = supDist S (center S) := by
  unfold center
  split_ifs
  exact (radius_mem_of_isBounded S h1).choose_spec.symm

theorem radius_nonneg : radius S ≥ 0 := by
  apply Real.sInf_nonneg ?_
  intro _ ⟨x, hx⟩
  subst hx
  simp [supDist]

theorem eradius_eq_supEDist_center : eradius S = supEDist S (center S) := by
  by_cases h1 : IsBounded S
  · rw [supEDist_eq_supDist_of_isBounded S _ h1]
    rw [eradius_eq_radius_of_isBounded S h1]
    rw [radius_eq_supDist_center_of_isBounded S h1]
  · rw [eradius_eq_top_of_not_isBounded S h1]
    rw [supEDist_eq_top_of_not_isBounded S _ h1]

theorem subset_of_isBounded (h1 : IsBounded S) : S ⊆ closedBall (center S) (radius S) := by
  intro s hs
  rw [mem_closedBall]
  rw [←edist_le_ofReal (radius_nonneg S)]
  rw [←eradius_eq_radius_of_isBounded S h1]
  rw [eradius_eq_supEDist_center]
  unfold supEDist
  rw [le_sSup_iff]
  intro b hb
  simp [upperBounds] at hb
  exact hb s hs

def IsMinimal c r := S ⊆ closedBall c r ∧ ∀ c', ∀ r', S ⊆ closedBall c' r' → r ≤ r'

theorem IsMinimal.of_isBounded_nonempty (h1 : IsBounded S) (h0 : S.Nonempty) :
    IsMinimal S (center S) (radius S) := by
  split_ands
  · apply subset_of_isBounded S h1
  · intro c' r' h2
    have hr' := calc
        r' ≥ dist h0.choose c' := by simpa [mem_closedBall] using h2 h0.choose_spec
        _ ≥ 0 := by apply dist_nonneg
    rw [←ofReal_le_ofReal_iff hr']
    rw [←eradius_eq_radius_of_isBounded S h1]
    unfold eradius
    rw [sInf_le_iff]
    intro s hs
    replace hs : ∀ x, s ≤ supEDist S x := by simpa [lowerBounds] using hs
    specialize hs c'
    rw [supEDist, le_sSup_iff] at hs
    apply hs
    intro _ ⟨a, ha, ha2⟩
    subst ha2
    rw [edist_le_ofReal hr']
    exact h2 ha

theorem radius_isMinimal (h1 : IsBounded S) (h0 : S.Nonempty) :
    ∀ c', ∀ r', S ⊆ closedBall c' r' → radius S ≤ r' :=
  (IsMinimal.of_isBounded_nonempty S h1 h0).right

theorem radius_pos (hS : IsBounded S) (hS2 : S.encard ≥ 2) :
    radius S > 0 := by
  have h1 := subset_of_isBounded S hS
  have f : Fin 2 ↪ S := by
    by_cases hS4 : S.Finite
    · have := hS4.fintype
      let a : Fin (Fintype.card S) ↪ S := this.equivFin.symm.toEmbedding
      let b : Fin 2 ↪ Fin (Fintype.card S) :=
        Fin.castLEEmb (by apply ENat.coe_le_coe.mp; simp [hS2])
      exact b.trans a
    · let a : ℕ ↪ S := Set.Infinite.natEmbedding S hS4
      let b : Fin 2 ↪ ℕ := Fin.valEmbedding
      exact b.trans a
  obtain ⟨x0, hx0, x1, hx1, h⟩ : ∃ x0 ∈ S, ∃ x1 ∈ S, x0 ≠ x1 := by
    let x0 := f ⟨0, by simp⟩
    let x1 := f ⟨1, by simp⟩
    use x0.1, x0.2, x1.1, x1.2
    rw [Subtype.coe_inj.ne]
    apply f.injective.ne
    simp
  set r := radius S
  set c := center S
  calc
    r = (r + r) / 2 := by ring
    _ ≥ (dist x0 c + dist c x1) / 2 := by
      gcongr 2
      · simpa using h1 hx0
      · simpa [dist_comm] using h1 hx1
    _ ≥ dist x0 x1 / 2 := by gcongr 1; apply dist_triangle
    _ > 0 / 2 := by gcongr 1; exact dist_pos.mpr h
    _ = 0 := by simp


theorem eradius_image_add_right a : eradius ((· + a) '' S) = eradius S := by
  unfold eradius
  convert_to sInf (Set.range (supEDist S ∘ (· - a))) = _ using 3
  · ext c
    rw [supEDist_image_add_right, Function.comp_apply]
  congr 1
  apply Function.Surjective.range_comp
  apply add_right_surjective (-a)

theorem eradius_image_sub_right a : eradius ((· - a) '' S) = eradius S := by
  convert eradius_image_add_right S (-a) using 1

theorem radius_image_add_right a : radius ((· + a) '' S) = radius S := by
  unfold radius
  convert_to sInf (Set.range (supDist S ∘ (· - a))) = _ using 3
  · ext c
    rw [supDist_image_add_right, Function.comp_apply]
  congr 1
  apply Function.Surjective.range_comp
  apply add_right_surjective (-a)

theorem radius_image_sub_right a : radius ((· - a) '' S) = radius S := by
  convert radius_image_add_right S (-a) using 1


theorem radius_eq_radius_of_IsMinimal
    {x r1 y r2} (h1 : IsMinimal S x r1) (h2 : IsMinimal S y r2) : r1 = r2 :=
  le_antisymm (h1.right y r2 h2.left) (h2.right x r1 h1.left)

theorem center_eq_center_of_IsMinimal
    (h0 : S.Nonempty)
    {x r1 y r2} (h1 : IsMinimal S x r1) (h2 : IsMinimal S y r2) : x = y := by
  have h := radius_eq_radius_of_IsMinimal S h1 h2
  subst h

  let s0 := h0.choose
  have hs0 : s0 ∈ S := h0.choose_spec
  have hr1 := calc
      r1 ≥ dist s0 y := by simpa [mem_closedBall] using h2.left hs0
      _ ≥ 0 := by apply dist_nonneg

  let α := dist x y / 2
  let c := (1 / 2 : ℝ) • (x + y)
  set B1 := closedBall x r1
  set B2 := closedBall y r1

  have h5 z (hz1 : z ∈ B1) (hz2 : z ∈ B2) : dist z c ^ 2 ≤ r1 ^ 2 - α ^ 2 := calc
    ‖z - c‖ ^ 2 = ‖(1 / 2 : ℝ) • (z - x + (z - y))‖ ^ 2 := by congr 2; module
    _ = ‖(1 / 2 : ℝ)‖ ^ 2 * ‖(z - x + (z - y))‖ ^ 2 := by rw [norm_smul]; ring
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
    _ ≤ (1 / 2 : ℝ) * r1 ^ 2 + (1 / 2 : ℝ) * r1 ^ 2 - (1 / 4 : ℝ) * (2 * α) ^ 2 := by
      gcongr 4
      · simpa [mem_closedBall] using hz1
      · simpa [mem_closedBall] using hz2
      · apply le_of_eq
        calc
          _ = dist x y := by ring
          _ = ‖x - y‖ := rfl
    _ = r1 ^ 2 - α ^ 2 := by ring

  have h6 : S ⊆ closedBall c √(r1 ^ 2 - α ^ 2) := by
    intro s hs
    rw [mem_closedBall]
    calc
      _ = √(dist s c ^ 2) := by
        symm
        apply Real.sqrt_sq
        apply dist_nonneg
      _ ≤ √(r1 ^ 2 - α ^ 2) := Real.sqrt_le_sqrt (h5 s (h1.left hs) (h2.left hs))

  have h3 := h1.right c (√(r1 ^ 2 - α ^ 2)) h6
  replace h3 := calc
    r1 ^ 2 ≤ √(r1 ^ 2 - α ^ 2) ^ 2 := by gcongr 1
    _ = r1 ^ 2 - α ^ 2 := by
      apply Real.sq_sqrt
      calc
        0 ≤ dist s0 c ^ 2 := by apply sq_nonneg
        _ ≤ _ := h5 s0 (h1.left hs0) (h2.left hs0)
  replace h3 : α = 0 := by nlinarith
  unfold α at h3
  replace h3 : dist x y = 0 := by linarith
  simpa [dist_eq_zero] using h3


theorem center_image_add_right (h1 : IsBounded S) (h0 : S.Nonempty) a :
    center ((· + a) '' S) = center S + a := by
  set T := ((· + a) '' S)
  have h1' : IsBounded T := by
    apply isBounded_image_iff.mpr
    use diam S
    intro x hx y hy
    simpa using dist_le_diam_of_mem h1 hx hy
  have h0' : T.Nonempty := by apply h0.image
  have h3 := IsMinimal.of_isBounded_nonempty T h1' h0'
  have h4 : IsMinimal T (center S + a) (radius S) := by
    split_ands
    · simp only [T, Set.image_subset_iff, preimage_add_right_closedBall, add_sub_cancel_right]
      exact subset_of_isBounded S h1
    · intro c' r' h
      simp only [T, Set.image_subset_iff, preimage_add_right_closedBall] at h
      exact radius_isMinimal S h1 h0 (c' - a) r' h
  exact center_eq_center_of_IsMinimal T h0' h3 h4

theorem center_image_sub_right (h1 : IsBounded S) (h0 : S.Nonempty) a :
    center ((· - a) '' S) = center S - a := by
  convert center_image_add_right S h1 h0 (-a) using 1


theorem radius_singleton (a : EuclideanSpace ℝ (Fin d)) : radius {a} = 0 := by
  suffices radius {a} ≤ 0 by
    apply le_antisymm this
    apply radius_nonneg
  apply radius_isMinimal {a} isBounded_singleton (Set.singleton_nonempty a) a 0
  simp

theorem hit_at_least_once_of_finite (h1 : S.Finite) (h0 : S.Nonempty) :
    {x ∈ S | dist (center S) x = radius S}.Nonempty := by
  have hr := radius_isMinimal S h1.isBounded h0
  have hc := subset_of_isBounded S h1.isBounded
  set c := center S
  set r := radius S
  let hit := {x ∈ S | dist c x = r}
  obtain ⟨y0, hy0, hy0'⟩ := supDist_mem_of_isFinite S c h1 h0
  dsimp at hy0'
  set r' := supDist S c
  have h2 : r ≤ r' := by
    apply hr c r'
    intro s hs
    simp only [mem_closedBall]
    apply dist_le_supDist S h1.isBounded c s hs
  have h3 : r' ≤ r := by simpa [hy0'] using hc hy0
  replace h2 : r = r' := by linarith only [h2, h3]
  have h4 : y0 ∈ hit := by simp [hit, hy0, hy0', h2, dist_comm]
  use y0

theorem hit_at_least_twice_of_finite (hS3 : S.encard ≥ 2) (hS4 : S.Finite) :
    {x ∈ S | dist (center S) x = radius S}.encard ≥ 2 := by
  have hS : IsBounded S := hS4.isBounded
  have hS2 : S.Nonempty := by
    apply Set.encard_ne_zero.mp
    by_contra! h1
    simp [h1] at hS3
  have hr := radius_isMinimal S hS hS2
  have hc := subset_of_isBounded S hS
  set c := center S
  set r := radius S
  let hit := {x ∈ S | dist c x = r}
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
    -- Case where no point of S lies on the boundary of the smallest enclosing ball
    rw [Set.encard_eq_zero] at h1
    obtain ⟨y0, hy0, hy0'⟩ := supDist_mem_of_isFinite S c hS4 hS2
    dsimp at hy0'
    set r' := supDist S c
    have h2 : r ≤ r' := by
      apply hr c r'
      intro s hs
      simp only [mem_closedBall]
      apply dist_le_supDist S hS c s hs
    have h3 : r' ≤ r := by simpa [hy0'] using hc hy0
    replace h2 : r = r' := by linarith only [h2, h3]
    have h4 : y0 ∈ hit := by simp [hit, hy0, hy0', h2, dist_comm]
    simp [h1] at h4
  · exfalso
    -- Case where exactly one point of S lies on the boundary of the smallest enclosing ball
    rw [Set.encard_eq_one] at h1
    obtain ⟨x, hx⟩ := h1
    have hx1 : x ∈ hit := by simp [hx]
    have hx2 : x ∈ S := hx1.left
    have hx3 := hx1.right
    obtain ⟨r', h2, h3⟩ : ∃ r', r' < r ∧ ∀ y ∈ S, y ≠ x → dist c y ≤ r' := by
      obtain ⟨y0, hy0, hy0'⟩ := supDist_mem_of_isFinite (S \ {x}) c hS4.diff (by
        have := hS4.fintype.finite
        rw [←Set.encard_ne_zero, Set.encard_diff_singleton_of_mem hx2]
        rw [Set.encard, ENat.card_eq_coe_natCard] at hS3 ⊢
        norm_cast at hS3 ⊢
        omega)
      dsimp at hy0'
      set r' := supDist (S \ {x}) c
      use r'
      split_ands
      · by_contra! h1
        specialize hc hy0.left
        simp [hy0'] at hc
        replace h1 : r = r' := by linarith
        apply hy0.right
        suffices y0 ∈ hit by simpa [hx] using this
        simp [hit, hy0.left, dist_comm, hy0', h1]
      · unfold r'
        intro y hy hy2
        rw [dist_comm]
        apply dist_le_supDist
        · exact IsBounded.subset hS Set.diff_subset
        · simp [hy, hy2]
    have hr_pos : r > 0 := radius_pos S hS hS3
    obtain ⟨t, ht1, ht2, ht3⟩ : ∃ t : ℝ, t > 0 ∧ t < 1 ∧ t * (2 * r) + (1 - t) * r' < r := by
      use (r - r') / (2 * (2 * r - r'))
      have : r * 2 - r' > 0 := by linarith
      split_ands
      · field_simp
        linarith
      · field_simp
        linarith
      · field_simp
        nlinarith
    let c' := t • x + (1 - t) • c
    have h4 y (hy1 : y ∈ S) (hy2 : y ≠ x) := calc
        dist y c' = ‖y - c'‖ := rfl
        _ = ‖t • (y - x) + (1 - t) • (y - c)‖ := by congr 1; module
        _ ≤ ‖t • (y - x)‖ + ‖(1 - t) • (y - c)‖ := by apply norm_add_le
        _ = ‖t‖ * ‖y - x‖ + ‖1 - t‖ * ‖y - c‖ := by rw [norm_smul, norm_smul]
        _ = t * dist y x + (1 - t) * dist y c := by
          congr 2 <;> (apply Real.norm_of_nonneg; linarith)
        _ ≤ t * (2 * r) + (1 - t) * r' := by
          gcongr 2
          · calc
              dist y x ≤ dist y c + dist c x := by apply dist_triangle
              _ ≤ r + r := by
                gcongr 1
                · exact hc hy1
                · exact hx3.le
              _ = 2 * r := by ring
          · linarith
          · rw [dist_comm]
            exact h3 y hy1 hy2
    set r1 := t * (2 * r) + (1 - t) * r'
    have h5 := calc
      dist x c' = ‖x - c'‖ := rfl
      _ = ‖(1 - t) • (x - c)‖ := by congr 1; module
      _ = ‖1 - t‖ * ‖x - c‖ := by rw [norm_smul]
      _ = (1 - t) * dist x c := by congr 1; apply Real.norm_of_nonneg; linarith
      _ = (1 - t) * r := by rw [dist_comm]; congr 1
    set r2 := (1 - t) * r
    have hr2 : r2 < r := calc
      (1 - t) * r < 1 * r := by gcongr 1; linarith
      _ = r := by ring

    have h6 : S ⊆ closedBall c' (r1 ⊔ r2) := by
      intro y hy
      by_cases hy1 : y = x
      · simp [hy1, h5]
      · simp [h4 y hy hy1]

    have h7 : r1 ⊔ r2 < r := by simp [ht3, hr2]
    specialize hr c' (r1 ⊔ r2) h6
    linarith
  · exact h1


open InnerProductSpace in
theorem center_mem_convexHull_sphere_of_finite
    {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (h1 : X.Finite) (h2 : X.encard ≥ 2) :
    center X ∈ convexHull ℝ {x ∈ X | dist x (center X) = radius X} := by
  have h3 : X.Nonempty := by
    apply Set.encard_ne_zero.mp
    by_contra! h1
    simp [h1] at h2
  have h4 := subset_of_isBounded X h1.isBounded
  have h5 := radius_isMinimal X h1.isBounded h3
  set c := center X
  set r := radius X

  have h1' := h1.fintype
  set Xs := {x ∈ X | dist x c = r}
  by_contra! h6

  obtain ⟨v, hv, h7⟩ : ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧
      ∀ x ∈ convexHull ℝ Xs, ⟪v, x - c⟫_ℝ > 0 := by
    set s : Set (EuclideanSpace ℝ (Fin n)) := {0}
    have hs1 : Convex ℝ s := by apply convex_singleton
    have hs2 : IsCompact s := by
      apply isCompact_singleton
    set t := (· - c) '' convexHull ℝ (Xs)
    have ht1 : Convex ℝ t := by
      let f := AffineMap.id ℝ _ - AffineMap.const ℝ _ c
      apply Convex.affine_image f
      apply convex_convexHull
    have ht2 : IsCompact t := by
      unfold t
      apply IsCompact.image
      · apply Set.Finite.isCompact_convexHull
        apply Set.Finite.subset h1
        simp [Xs]
      · fun_prop
    have ht3 : IsClosed t := by
      apply IsCompact.isClosed ht2
    have ht4 : Xs.Nonempty := by
      unfold Xs
      convert hit_at_least_once_of_finite X h1 h3 using 5 with x
      simp [dist_comm, c]
    have ht5 : t.Nonempty := by
      unfold t
      apply Set.image_nonempty.mpr
      exact Set.Nonempty.convexHull ht4
    have hst : Disjoint s t := by
      simp [s, t]
      intro x hx
      contrapose! h6
      convert hx using 1
      ext k
      let g : EuclideanSpace ℝ (Fin n) → ℝ := (WithLp.ofLp · k)
      apply_fun g at h6
      simp [g] at h6
      linarith only [h6]

    -- Use Hahn-Banach to get the separating functional, and Riesz representation theorem to get
    -- the separating hyperplane normal vector
    obtain ⟨f, u, v, g1, g2, g3⟩ := geometric_hahn_banach_compact_closed hs1 hs2 ht1 ht3 hst
    let w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f
    have hh (x : EuclideanSpace ℝ (Fin n)) : f x = ⟪w, x⟫_ℝ := by simp [w]
    replace g1 : u > 0 := by simpa [s] using g1
    use w
    use by
      by_contra! hw
      specialize g3 ht5.choose ht5.choose_spec
      simp [hh, hw] at g3
      linarith only [g1, g2, g3]
    intro x hx
    specialize g3 (x - c) (by simp [t, hx])
    simp [hh] at g3
    linarith only [g1, g2, g3]

  set Xint := X \ Xs
  let c' (ε : ℝ) := c + ε • v

  have h8 ε (hε : ε > 0) x := calc
    ‖x - c' ε‖ ^ 2 = ‖(x - c) - ε • v‖ ^ 2 := by congr 2; module
    _ = ‖x - c‖ ^ 2 - 2 * ε * ⟪v, x - c⟫_ℝ + ‖ε • v‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm, real_inner_smul_left]
      ring
    _ = ‖x - c‖ ^ 2 - 2 * ε * ⟪v, x - c⟫_ℝ + ε ^ 2 * ‖v‖ ^ 2 := by
      congr 1
      rw [norm_smul, mul_pow, Real.norm_of_nonneg]
      exact hε.le

  have h9 : Xs.toFinset.Nonempty := by
    apply Set.toFinset_nonempty.mpr
    unfold Xs
    convert hit_at_least_once_of_finite X h1 h3 using 5 with x
    simp [dist_comm, c]

  obtain ⟨a1, ha1, h10⟩ : ∃ a1 > 0, ∀ ε, ε > 0 → ε < a1 → ∀ x ∈ Xs, ‖x - c' ε‖ ^ 2 < r ^ 2 := by
    let δ x := ⟪v, x - c⟫_ℝ
    let d := Xs.toFinset.inf' h9 δ
    have hd1 xi (hxi : xi ∈ Xs) : d ≤ δ xi := Xs.toFinset.inf'_le δ (by simpa using hxi)
    have hd2 : ∃ xi ∈ Xs, δ xi = d := by
      convert Xs.toFinset.exists_mem_eq_inf' h9 δ using 2 with xi; simp [d]; tauto
    have hd3 : d > 0 := by
      obtain ⟨x0, hx0, hd⟩ := hd2
      rw [←hd]
      unfold δ
      apply h7 x0
      exact mem_convexHull_iff.mpr fun _ a _ => a hx0
    use 2 * d / ‖v‖ ^ 2, by field_simp; nlinarith only [hd3]
    intro ε hε1 hε2 xi hxi
    calc
      _ = _ := h8 ε hε1 xi
      _ ≤ ‖xi - c‖ ^ 2 - 2 * ε * d + ε ^ 2 * ‖v‖ ^ 2 := by
        gcongr 3
        exact hd1 xi hxi
      _ = ‖xi - c‖ ^ 2 + (-2 * ε * d + ε ^ 2 * ‖v‖ ^ 2) := by ring
      _ < ‖xi - c‖ ^ 2 + 0 := by
        gcongr 1
        calc
          -2 * ε * d + ε ^ 2 * ‖v‖ ^ 2 = ε * (-2 * d + ε * ‖v‖ ^ 2) := by ring
          _ < ε * 0 := by
            gcongr 1
            calc
              _ < -2 * d + (2 * d / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by gcongr 2
              _ = -2 * d + 2 * d := by
                congr 1
                field_simp
              _ = _ := by ring
          _ = _ := by ring
      _ = _ := by
        simp [Xs, dist_eq_norm] at hxi
        simp [hxi]

  obtain ⟨a2, ha2, h11⟩ : ∃ a2 > 0, ∀ ε, ε > 0 → ε < a2 → ∀ x ∈ Xint, ‖x - c' ε‖ ^ 2 < r ^ 2 := by
    by_cases hXint : Xint = ∅
    · simp [hXint]; use 1; norm_num
    replace hXint : Xint.toFinset.Nonempty := by
      apply Set.toFinset_nonempty.mpr
      exact Set.nonempty_iff_ne_empty.mpr hXint
    let f ε := Xint.toFinset.sup' hXint (fun x => ‖x - c' ε‖ ^ 2)
    have hf : Continuous f := by apply Continuous.finset_sup'_apply; fun_prop
    replace hf : ContinuousAt f 0 := by apply hf.continuousAt
    rw [Metric.continuousAt_iff] at hf
    have h1 : f 0 < r ^ 2 := by
      unfold f
      rw [Finset.sup'_lt_iff]
      intro x hx
      suffices dist x c ^ 2 < r ^ 2 by simpa [c', ←dist_eq_norm] using this
      rw [sq_lt_sq₀]
      · simp [Xint] at hx
        apply lt_of_le_of_ne
        · exact subset_of_isBounded X h1.isBounded hx.left
        · have := hx.right
          contrapose! this
          simp [Xs, hx.left, this]
      · apply dist_nonneg
      · apply radius_nonneg
    obtain ⟨δ, hδ, h⟩ := hf (r ^ 2 - f 0) (by linarith only [h1])
    use δ, hδ
    intro ε hε1 hε2
    simp only [dist_eq_norm] at h
    have h' : ‖ε - 0‖ < δ := by
      rw [Real.norm_of_nonneg]
      · linarith only [hε2]
      · linarith only [hε1]
    specialize h h'
    intro x hx
    calc
      _ ≤ f ε := by
        unfold f
        rw [Finset.le_sup'_iff]
        use x, by simpa using hx
      _ = (f ε - f 0) + f 0 := by ring
      _ ≤ ‖f ε - f 0‖ + f 0 := by gcongr 1; apply Real.le_norm_self
      _ < r ^ 2 := by linarith only [h]

  replace ⟨a3, ha3, h11⟩ : ∃ a3 > 0, ∀ ε, ε > 0 → ε < a3 → ∀ x ∈ X, ‖x - c' ε‖ ^ 2 < r ^ 2 := by
    use a1 ⊓ a2, lt_min ha1 ha2
    intro ε hε1 hε2 x hx
    obtain h | h : x ∈ Xs ∨ x ∈ Xint := by
      apply Set.mem_or_mem_of_mem_union
      convert hx using 1
      apply Set.union_diff_cancel
      simp [Xs]
    · apply h10 ε hε1 (calc
          ε < a1 ⊓ a2 := hε2
          _ ≤ a1 := by apply inf_le_left) x h
    · apply h11 ε hε1 (calc
          ε < a1 ⊓ a2 := hε2
          _ ≤ a2 := by apply inf_le_right) x h

  let ε0 := a3 / 2
  let r0 := X.toFinset.sup' (Set.toFinset_nonempty.mpr h3) (‖· - c' ε0‖)
  obtain ⟨x, hx, hr0⟩ := X.toFinset.exists_mem_eq_sup' (Set.toFinset_nonempty.mpr h3) (‖· - c' ε0‖)
  let c0 := c' ε0
  have h12 : X ⊆ closedBall c0 r0 := by
    intro x hx
    simp only [mem_closedBall, dist_eq_norm, r0]
    rw [Finset.le_sup'_iff]
    use x, by simpa using hx
  have h13 := calc
    r0 = √(r0 ^ 2) := by
      rw [Real.sqrt_sq]
      unfold r0
      rw [Finset.le_sup'_iff]
      use h3.choose, by simpa using h3.choose_spec
      apply norm_nonneg
    _ < √(r ^ 2) := by
      apply Real.sqrt_lt_sqrt
      · apply sq_nonneg
      unfold r0
      rw [hr0]
      apply h11 ε0
      · unfold ε0; linarith only [ha3]
      · unfold ε0; linarith only [ha3]
      · simpa using hx
    _ = r := by
      rw [Real.sqrt_sq]
      apply radius_nonneg
  have h14 : r ≤ r0 := radius_isMinimal X h1.isBounded h3 c0 r0 h12
  linarith only [h13, h14]



open Finset InnerProductSpace in
/--
Jung’s theorem in the case $$\left|S\right|\leq d+1$$.
-/
theorem radius_le_sqrt_of_card_le_d_succ
    (hS : IsBounded S) (hS3 : S.encard ≤ d + 1) :
    radius S ≤ √(d / (2 * d + 2) : ℝ) * diam S := by

  -- Handle the trivial cases where $$S$$ has cardinality 0 or 1
  obtain hS4 | hS4 | hS4 : S.encard = 0 ∨ S.encard = 1 ∨ S.encard ≥ 2 := by
    have := (Set.finite_of_encard_le_coe hS3).fintype
    unfold Set.encard
    rw [ENat.card_eq_coe_natCard]
    norm_cast
    omega
  · rw [Set.encard_eq_zero] at hS4
    subst hS4
    unfold radius supDist supEDist
    simp
  · have := (Set.finite_of_encard_le_coe hS3).fintype
    have h1 : S.toFinset.card = 1 := by apply ENat.coe_inj.mp; convert hS4 using 1; simp
    have ⟨a, ha⟩ := card_eq_one.mp h1
    rw [←coe_eq_singleton, Set.coe_toFinset] at ha
    subst ha
    simp [radius_singleton]

  have hS2 : S.Nonempty := by
    apply Set.encard_ne_zero.mp
    by_contra! h1
    simp [h1] at hS4

  -- Let $$c$$ denote the center of the ball containing $$S$$ of minimum radius $$r$$.
  set c := center S
  -- Translating $$S$$, we may assume without loss of generality that $$c=0$$.
  wlog hc : c = 0
  · let T := (· - c) '' S
    specialize this T
    specialize this (by
      rw [isBounded_image_iff]
      rw [isBounded_iff] at hS
      obtain ⟨R, hR⟩ := hS
      use ‖c‖ + R + ‖c‖
      intro x hx y hy
      calc
        dist (x - c) (y - c) ≤ dist (x - c) x + dist x y + dist y (y - c) := by apply dist_triangle4
        _ = ‖(x - c) - x‖ + dist x y + ‖y - (y - c)‖ := by congr 1
        _ = ‖c‖ + dist x y + ‖c‖ := by (iterate 2 congr 1) <;> simp
        _ ≤ ‖c‖ + R + ‖c‖ := by gcongr 2; exact hR hx hy)
    specialize this (by
      convert hS3 using 1
      apply ENat.card_image_of_injective
      apply add_left_injective (-c))
    specialize this (by
      convert hS4 using 1
      apply ENat.card_image_of_injective
      apply add_left_injective (-c))
    specialize this (by simpa [T] using hS2)
    specialize this (by simp [T, center_image_sub_right S hS hS2, c])
    convert this using 1
    · simp [T, radius_image_sub_right]
    · congr 1
      unfold diam
      congr 1
      iterate 2 rw [EMetric.diam_eq_sSup]
      congr 1
      ext x
      simp [T]

  set r := radius S
  let h3 := subset_of_isBounded S hS

  have h1' := (Set.finite_of_encard_le_coe hS3).fintype
  have h1 : S.toFinset.card ≥ 2 := by
    apply ENat.coe_le_coe.mp
    change _ ≥ _
    convert hS4 using 1
    simp

  -- Enumerate the elements of $$\left\{x\in S: \left\|x\right\|=r\right\}$$ by
  -- $$x_{1},\cdots,x_{n}$$ (and note that $$n\geq 2$$, as shown by the lemma).
  let S' := {x ∈ S | ‖x‖ = r}
  have hS' : S' ⊆ S := by simp [S']
  let n := Nat.card S'
  have hn : n ≥ 2 := by -- if only n ≥ 1 is needed here, might ignore hit_at_least_twice ...
    unfold n
    apply ENat.coe_le_coe.mp
    change _ ≥ _
    convert_to {x ∈ S | dist (center S) x = r}.encard ≥ 2 using 1
    · rw [←ENat.card_eq_coe_natCard, Set.encard]
      congr! 6 with x
      unfold c at hc
      simp [hc]
    exact hit_at_least_twice_of_finite S hS4 h1'.finite

  let x' : Icc 1 n ≃ S' :=
    ((Icc 1 n).equivFinOfCardEq (by simp [n])).trans (Finite.equivFinOfCardEq rfl).symm
  let y k : Icc 1 n := if hk : k ∈ Icc 1 n then ⟨k, hk⟩ else ⟨1, by simp; omega⟩
  -- writing the enumeration as a composition of elementary functions
  -- so as to simplify the proofs of range / injectivity properties later on
  let x := Subtype.val ∘ x' ∘ y
  have hy1 : Set.MapsTo y (Icc 1 n) .univ := by intro k hk; simp
  have hx'1 : Set.MapsTo x'.toFun .univ .univ := by simp
  have hval1 : Set.MapsTo (Subtype.val : S' → _) .univ S' := by simp
  have hx1 : Set.MapsTo x (Icc 1 n) S' := hval1.comp (hx'1.comp hy1)
  have hx2 : Set.InjOn x (Icc 1 n) := by
    have hy2 : Set.InjOn y (Icc 1 n) := by
      intro i hi j hj hij
      unfold y at hij
      split_ifs at hij with g1 g2 g2
      all_goals simp at hi hj hij g1 g2; omega
    have hx'2 : Set.InjOn x'.toFun .univ := x'.injective.injOn
    have hval2 : Set.InjOn (Subtype.val : S' → _) .univ := by simp
    exact hval2.comp (hx'2.comp hy2 hy1) (hx'1.comp hy1)
  have hx3 : Set.SurjOn x (Icc 1 n) S' := by
    have hy3 : Set.SurjOn y (Icc 1 n) .univ := by
      intro ⟨z, hz⟩ hz2
      simp [y] at hz ⊢
      use z
      split_ifs
      simp
      omega
    have hx'3 : Set.SurjOn x'.toFun .univ .univ := x'.surjective.surjOn
    have hval3 : Set.SurjOn (Subtype.val : S' → _) .univ S' := by simp [Set.SurjOn]
    exact hval3.comp (hx'3.comp hy3)
  have hx4 : x '' (Icc 1 n) = S' := hx3.image_eq_of_mapsTo hx1

  -- It follows from the uniqueness of the minimum enclosing ball of S that
  -- $$c$$ lies in the convex hull of $$x_{1},\cdots,x_{n}$$
  have h5 : c ∈ convexHull ℝ ((Icc 1 n).image x) := by
    convert_to c ∈ convexHull ℝ S' using 2
    · simpa using hx4
    unfold S'
    convert center_mem_convexHull_sphere_of_finite S h1'.finite hS4 using 6 with x
    unfold c at hc
    simp [hc]

  -- and therefore we can write
  -- $$\displaystyle c=\sum_{k=1}^{n}\lambda_{k}x_{k}$$, with $$\lambda_{k}\geq0$$,
  -- and $$ \sum_{k=1}^{n}\lambda_{k}=1$$

  obtain ⟨l, h6, h7, h8⟩ : ∃ (l : ℕ → ℝ),
      (∀ k ∈ Icc 1 n, l k ≥ 0) ∧ ∑ k ∈ Icc 1 n, l k = 1 ∧ c = ∑ k ∈ Icc 1 n, l k • x k := by
    rw [mem_convexHull'] at h5
    obtain ⟨w, g1, g2, g3⟩ := h5
    use w ∘ x
    split_ands
    · intro k hk
      exact g1 (x k) (mem_image_of_mem _ hk)
    · convert g2 using 1
      apply sum_nbij x
      · intro k hk; exact mem_image_of_mem _ hk
      · exact hx2
      · convert hx3 using 1
        simpa using hx4
      · simp
    · symm
      convert g3 using 1
      apply sum_nbij x
      · intro k hk; exact mem_image_of_mem _ hk
      · exact hx2
      · convert hx3 using 1
        simpa using hx4
      · intro k hk
        congr 1

  have h8' : diam S > 0 := by
    let a : Fin (Fintype.card S) ↪ S := h1'.equivFin.symm.toEmbedding
    let b : Fin 2 ↪ Fin (Fintype.card S) := Fin.castLEEmb (by simpa [←Set.toFinset_card] using h1)
    let x0 := a (b ⟨0, by simp⟩)
    let x1 := a (b ⟨1, by simp⟩)
    have x : x0 ≠ x1 := (a.injective.comp b.injective).ne (by simp)
    calc
      0 < dist x0 x1 := by apply dist_pos.mpr; exact x
      _ ≤ diam S := dist_le_diam_of_mem hS x0.2 x1.2

  have h9 (i : ℕ) (hi : i ∈ Icc 1 n) := by
    simp at hi
    exact calc
    1 - l i = ∑ k ∈ Icc 1 n, l k - l i := by rw [h7]
    _ = ∑ k ∈ Icc 1 n \ {i}, l k + l i - l i := by
      have h : {i} ⊆ Icc 1 n := by intro _; simp; omega
      simp [←sum_sdiff h]
    _ = ∑ k ∈ Icc 1 n \ {i}, l k * 1 := by ring_nf
    _ ≥ ∑ k ∈ Icc 1 n \ {i}, l k * (‖x k - x i‖ ^ 2 / diam S ^ 2) := by
      gcongr 2 with k hk
      · exact h6 k (by simp at hk ⊢; omega)
      · suffices dist (x k) (x i) ^ 2 ≤ diam S ^ 2 by field_simp; simpa using this
        gcongr 1
        apply dist_le_diam_of_mem hS
        · apply hS'
          apply hx1
          simp at hk ⊢
          omega
        · apply hS'
          apply hx1
          simp at hk ⊢
          omega
    _ = (1 / diam S ^ 2) * ∑ k ∈ Icc 1 n \ {i}, l k * ‖x k - x i‖ ^ 2 := by
      rw [mul_sum]
      congr! 1 with k hk
      field_simp
    _ = (1 / diam S ^ 2) * ∑ k ∈ Icc 1 n, l k * ‖x k - x i‖ ^ 2 := by
      congr 1
      have h : {i} ⊆ Icc 1 n := by intro _; simp; omega
      simp [←sum_sdiff h]
    _ = (1 / diam S ^ 2) * ∑ k ∈ Icc 1 n,
          (l k * ‖x k‖ ^ 2 + l k * ‖x i‖ ^ 2 - 2 * (l k * ⟪x k, x i⟫_ℝ)) := by
      congr! 2 with k hk
      rw [norm_sub_sq_real]
      ring
    _ = (1 / diam S ^ 2) * (
          ∑ k ∈ Icc 1 n, l k * ‖x k‖ ^ 2 + ∑ k ∈ Icc 1 n, l k * ‖x i‖ ^ 2 -
          2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
      congr 1
      conv_lhs => rw [sum_sub_distrib, sum_add_distrib]
      congr 2
      rw [mul_sum]
    _ = (1 / diam S ^ 2) * (
          ∑ k ∈ Icc 1 n, l k * r ^ 2 + ∑ k ∈ Icc 1 n, l k * r ^ 2 -
          2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
      congr! 6 with k hk
      · suffices x k ∈ S' by simp [S'] at this; simp [this]
        apply hx1
        simp at hk ⊢
        omega
      · suffices x i ∈ S' by simp [S'] at this; simp [this]
        apply hx1
        simp at hi ⊢
        omega
    _ = (1 / diam S ^ 2) * (
          r ^ 2 * ∑ k ∈ Icc 1 n, l k + r ^ 2 * ∑ k ∈ Icc 1 n, l k -
          2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
      congr 3
      all_goals
      · rw [mul_sum]
        congr! 1 with k hk
        ring
    _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
      congr 2
      rw [h7]
      ring
    _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * (∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ)) := by
      ring
    _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * (∑ k ∈ Icc 1 n, ⟪l k • x k, x i⟫_ℝ)) := by
      congr! 4 with k hk
      rw [real_inner_smul_left]
    _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * (⟪∑ k ∈ Icc 1 n, l k • x k, x i⟫_ℝ)) := by
      congr! 4 with k hk
      rw [sum_inner]
    _ = (1 / diam S ^ 2) * (2 * r ^ 2) := by simp [←h8, hc]
    _ = 2 * r ^ 2 / diam S ^ 2 := by field_simp

-- Summing $$1-\lambda_{i}$$ over $$i\in\left\{1,\cdots,n\right\}$$, we obtain
-- $$\displaystyle n-1\geq\frac{2nr^{2}}{\text{diam}(S)^{2}} $$

  have h10 := calc
    n - 1 = ∑ i ∈ Icc 1 n, 1 - ∑ i ∈ Icc 1 n, l i := by simp [h7]
    _ = ∑ i ∈ Icc 1 n, (1 - l i) := by rw [sum_sub_distrib]
    _ ≥ ∑ i ∈ Icc 1 n, (2 * r ^ 2 / diam S ^ 2) := by
      gcongr 2 with i hi
      exact h9 i hi
    _ = n * (2 * r ^ 2 / diam S ^ 2) := by simp [sum_const]
    _ = 2 * n * r ^ 2 / diam S ^ 2 := by ring


-- $$\Longleftrightarrow r\leq\left(\frac{n-1}{2n}\right)^{\frac{1}{2}}\text{diam}(S)$$

-- $$\leq\left(\frac{d}{2d+2}\right)^{\frac{1}{2}}\text{diam}(S)$$

  exact calc
    r = √(r ^ 2) := by
      symm
      apply Real.sqrt_sq
      calc
        0 ≤ _ := by apply dist_nonneg
        _ ≤ r := h3 hS2.choose_spec
    _ ≤ √(((n - 1) / (2 * n)) * diam S ^ 2) := by
      apply Real.sqrt_le_sqrt
      field_simp at h10 ⊢
      simpa using h10
    _ = √((n - 1) / (2 * n)) * √(diam S ^ 2) := by
      rw [Real.sqrt_mul]
      field_simp
      simp
      omega
    _ = √((n - 1) / (2 * n)) * diam S := by
      congr 1
      apply Real.sqrt_sq
      apply diam_nonneg
    _ ≤ √(d / (2 * d + 2)) * diam S := by
      gcongr 2
      field_simp
      have hn1 : n ≥ 1 := by omega
      have hn2 : n ≤ d + 1 := calc
        Nat.card S' ≤ Nat.card S := Nat.card_mono S.toFinite hS'
        _ ≤ d + 1 := by
          clear * - hS3
          apply ENat.coe_le_coe.mp
          convert hS3 using 1
          rw [←ENat.card_eq_coe_natCard, Set.encard]
      rify at hn1 hn2
      nlinarith



open Finset in
/--
Jung’s theorem in the case $$\left|S\right|\geq d+1$$.
-/
theorem radius_le_sqrt_of_card_ge_d_succ
    (hS : IsBounded S) (hS2 : S.encard ≥ d + 1) :
    radius S ≤ (√(d / (2 * d + 2) : ℝ) * diam S) := by

  have hS0 : S.Nonempty := by
    apply Set.encard_ne_zero.mp
    by_contra! h1
    simp [h1] at hS2

  suffices ∃ c, S ⊆ closedBall c (√(d / (2 * d + 2) : ℝ) * diam S) by
    obtain ⟨c, hc⟩ := this
    apply radius_isMinimal S hS hS0 c _ hc

  let F (x : S) := closedBall x.val (√(d / (2 * d + 2) : ℝ) * diam S)

  suffices (⋂ i, F i).Nonempty by
    let c := this.choose
    have hc : c ∈ (⋂ y : S, F y) := this.choose_spec
    simp [F] at hc
    use c
    simpa [mem_closedBall, dist_comm] using hc

  apply Convex.helly_theorem_compact (𝕜 := ℝ)
  · simpa using hS2
  · intro ⟨i, hi⟩
    apply convex_closedBall
  · intro ⟨i, hi⟩
    apply isCompact_closedBall
  · intro I hI
    replace hI : #I = d + 1 := by simpa using hI
    simp only [Set.iInter_coe_set, Set.nonempty_iInter, Set.mem_iInter]
    set c := center (Subtype.val '' I.toSet)
    have hc : radius (Subtype.val '' I.toSet) ≤ _ :=
      radius_le_sqrt_of_card_le_d_succ (Subtype.val '' I.toSet)
        (IsBounded.subset hS (Subtype.coe_image_subset S I))
        (calc
          _ ≤ I.toSet.encard := by apply Set.encard_image_le
          _ = _ := by simpa using ENat.coe_inj.mpr hI)
    have hc' := subset_of_isBounded (Subtype.val '' I.toSet)
      (IsBounded.subset hS (Subtype.coe_image_subset S I))
    rw [Set.image_subset_iff] at hc'
    use c
    intro i hi hi2
    specialize hc' hi2
    suffices dist c i ≤ √(d / (2 * d + 2) : ℝ) * diam (S) by simpa [F] using this
    replace hc : dist c i ≤ √(d / (2 * d + 2) : ℝ) * diam (Subtype.val '' I.toSet) := by
      simp at hc'
      simpa [dist_comm] using hc'.trans hc
    apply le_trans hc
    gcongr 1
    exact diam_mono (Subtype.coe_image_subset S I) hS


/-- The minimal ball enclosing a bounded set $$S\subset\mathbb{R}^{d}$$ has
radius $$r \leq (\frac{d}{2d+2})^{\frac{1}{2}}\text{diam}(S)$$ -/
theorem radius_le_sqrt_of_isBounded (hS : IsBounded S) :
    radius S ≤ (√(d / (2 * d + 2) : ℝ) * diam S) := by
  obtain h | h : S.encard ≤ d + 1 ∨ S.encard ≥ d + 1 := by apply le_total
  · exact radius_le_sqrt_of_card_le_d_succ S hS h
  · exact radius_le_sqrt_of_card_ge_d_succ S hS h

/-- (Jung’s theorem) Suppose $$S\subset\mathbb{R}^{d}$$ is bounded with diameter $$\text{diam}(S)$$.
Then $S$ is contained in a closed ball of radius $$(\frac{d}{2d+2})^{\frac{1}{2}}\text{diam}(S)$$
-/
theorem jung_theorem (hS : IsBounded S) :
    ∃ c, S ⊆ closedBall c (√(d / (2 * d + 2) : ℝ) * diam S) := by
  use center S
  apply (subset_of_isBounded S hS).trans
  apply closedBall_subset_closedBall
  exact radius_le_sqrt_of_isBounded S hS



end BoundingSphere
