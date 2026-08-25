import FamilyStickyGrounding.JohnDimOneExtrema1

open scoped InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- A compact convex body with one-dimensional affine span is exactly the
segment between the points realizing the extrema of its affine coordinate. -/
theorem exists_eq_segment_of_finrank_direction_affineSpan_eq_one
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space),
      (K : Set Space) = segment ℝ p q := by
  obtain ⟨c, hcK⟩ := K.nonempty
  obtain ⟨p, hpK, q, hqK, hpmin, hqmax⟩ :=
    exists_affineLineCoord_extrema K hdim c
  let f : Space → ℝ := affineLineCoord K hdim c
  have hcspan : c ∈ affineSpan ℝ (K : Set Space) := mem_affineSpan ℝ hcK
  have hpspan : p ∈ affineSpan ℝ (K : Set Space) := mem_affineSpan ℝ hpK
  have hqspan : q ∈ affineSpan ℝ (K : Set Space) := mem_affineSpan ℝ hqK
  refine ⟨p, hpK, q, hqK, Set.Subset.antisymm ?_ ?_⟩
  · intro x hxK
    have hxspan : x ∈ affineSpan ℝ (K : Set Space) := mem_affineSpan ℝ hxK
    have hpx : f p ≤ f x := hpmin hxK
    have hxq : f x ≤ f q := hqmax hxK
    by_cases hpq : f p = f q
    · have hfx : f x = f p := le_antisymm (hpq ▸ hxq) hpx
      have hfx' : affineLineCoord K hdim c x = affineLineCoord K hdim c p := by
        simpa [f] using hfx
      have hxp := eq_add_affineLineCoord_smul K hdim hcspan hxspan
      have hpp := eq_add_affineLineCoord_smul K hdim hcspan hpspan
      have hxpEq : x = p := by
        calc
          x = c + affineLineCoord K hdim c x • affineUnitDirection K hdim := hxp
          _ = c + affineLineCoord K hdim c p • affineUnitDirection K hdim := by rw [hfx']
          _ = p := hpp.symm
      simpa [hxpEq] using left_mem_segment ℝ p q
    · have hpxq : f p ≤ f q := hpmin hqK
      have hgap : 0 < f q - f p := sub_pos.mpr (lt_of_le_of_ne hpxq hpq)
      let t : ℝ := (f x - f p) / (f q - f p)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hpx) hgap.le
      have ht1 : t ≤ 1 := (div_le_one hgap).mpr (sub_le_sub_right hxq (f p))
      have hft : f x = (1 - t) * f p + t * f q := by
        dsimp [t]
        field_simp [ne_of_gt hgap]
        ring
      have hft' : affineLineCoord K hdim c x =
          (1 - t) * affineLineCoord K hdim c p +
            t * affineLineCoord K hdim c q := by
        simpa [f] using hft
      have hxp := eq_add_affineLineCoord_smul K hdim hcspan hxspan
      have hpp := eq_add_affineLineCoord_smul K hdim hcspan hpspan
      have hqq := eq_add_affineLineCoord_smul K hdim hcspan hqspan
      have hxline : x = AffineMap.lineMap p q t := by
        rw [AffineMap.lineMap_apply_module, hxp, hpp, hqq, hft']
        module
      rw [hxline]
      exact lineMap_mem_segment ℝ p q ⟨ht0, ht1⟩
  · exact K.convex.segment_subset hpK hqK

#print axioms exists_eq_segment_of_finrank_direction_affineSpan_eq_one

end
end Submission.Kakeya.ConvexGeometry
