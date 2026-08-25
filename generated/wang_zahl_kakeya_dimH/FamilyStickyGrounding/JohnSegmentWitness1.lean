import FamilyStickyGrounding.JohnSegmentWitnessBasic4

open scoped NNReal InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

def segmentAxisRadii (p q : Space) : Fin 3 → ℝ≥0 := fun i ↦
  if i = 0 then segmentAxisRadius p q else 0

/-- A nontrivial segment has an exact (degenerate) axis ellipsoid witness.
The inner and outer ellipsoids both collapse to the segment itself. -/
theorem exists_johnAxisWitness_of_eq_segment_of_ne
    (K : ConvexBody Space) {p q : Space} (hpq : p ≠ q)
    (hK : (K : Set Space) = segment ℝ p q) :
    Nonempty (JohnAxisWitness K) := by
  obtain ⟨frame, hframe⟩ := exists_frame_zero_eq (norm_segmentUnitDirection hpq)
  let center : Space := AffineMap.lineMap p q (2 : ℝ)⁻¹
  let radius : Fin 3 → ℝ≥0 := segmentAxisRadii p q
  have haxis : (segmentAxisRadius p q : ℝ) • segmentUnitDirection p q =
      (2 : ℝ)⁻¹ • (q - p) := segmentAxisRadius_smul_unitDirection hpq
  have hsum (z : Fin 3 → ℝ) :
      ∑ i, (z i * (radius i : ℝ)) • frame i =
        (z 0 * (segmentAxisRadius p q : ℝ)) • frame 0 := by
    rw [Fin.sum_univ_three]
    simp [radius, segmentAxisRadii]
  refine ⟨{
    center := center
    frame := frame
    radius := radius
    inner := ?_
    outer := ?_ }⟩
  · intro x hx
    rcases hx with ⟨z, hz, hxrep⟩
    rw [hK]
    have hz0sq : (z 0) ^ 2 ≤ 1 := by
      calc
        (z 0) ^ 2 ≤ ∑ i, (z i) ^ 2 :=
          Finset.single_le_sum (fun i _ ↦ sq_nonneg (z i)) (Finset.mem_univ 0)
        _ ≤ (1 : ℝ) ^ 2 := hz
        _ = 1 := by norm_num
    have hz0lo : -1 ≤ z 0 := by nlinarith [sq_nonneg (z 0 + 1)]
    have hz0hi : z 0 ≤ 1 := by nlinarith [sq_nonneg (z 0 - 1)]
    let t : ℝ := (z 0 + 1) / 2
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor <;> dsimp [t] <;> linarith
    have hxline : x = AffineMap.lineMap p q t := by
      calc
        x = center + ∑ i, (z i * (radius i : ℝ)) • frame i := hxrep
        _ = center + (z 0 * (segmentAxisRadius p q : ℝ)) • frame 0 := by rw [hsum]
        _ = center + z 0 • ((segmentAxisRadius p q : ℝ) •
              segmentUnitDirection p q) := by rw [hframe, mul_smul]
        _ = center + z 0 • ((2 : ℝ)⁻¹ • (q - p)) := by rw [haxis]
        _ = AffineMap.lineMap p q t := by
          exact segment_center_add_axis_eq_lineMap p q (z 0)
    rw [hxline]
    exact lineMap_mem_segment ℝ p q ht
  · intro x hxK
    rw [hK, segment_eq_image_lineMap] at hxK
    rcases hxK with ⟨t, ht, rfl⟩
    let z : Fin 3 → ℝ := fun i ↦ if i = 0 then 2 * t - 1 else 0
    refine ⟨z, ?_, ?_⟩
    · rw [Fin.sum_univ_three]
      simp [z]
      nlinarith [ht.1, ht.2]
    · calc
        AffineMap.lineMap p q t = center +
            (2 * t - 1) • ((2 : ℝ)⁻¹ • (q - p)) :=
          segment_axis_eq_center_add p q t
        _ = center + (2 * t - 1) •
            ((segmentAxisRadius p q : ℝ) • segmentUnitDirection p q) := by rw [haxis]
        _ = center + ((2 * t - 1) * (segmentAxisRadius p q : ℝ)) •
            segmentUnitDirection p q := by rw [mul_smul]
        _ = center + (z 0 * (segmentAxisRadius p q : ℝ)) • frame 0 := by
          simp [z, hframe]
        _ = center + ∑ i, (z i * (radius i : ℝ)) • frame i := by rw [hsum]

#print axioms exists_johnAxisWitness_of_eq_segment_of_ne

end
end Submission.Kakeya.ConvexGeometry
