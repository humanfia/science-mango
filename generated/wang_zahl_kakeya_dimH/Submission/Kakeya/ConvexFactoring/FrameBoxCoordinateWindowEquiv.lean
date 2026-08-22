import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindow

open scoped ENNReal NNReal Pointwise InnerProductSpace

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-!
# Exact coordinate-window description of a frame box

The forward containment was sufficient for overlap upper bounds.  The reverse
containment proved here is needed when coordinate estimates must produce an
actual `FrameBox` containment certificate, for example for metric tubes.
-/

/-- The coordinate window of an orthonormal frame box is not merely an outer
bound: it is exactly the parallelepiped carrier, including degenerate sides. -/
theorem FrameBox.centeredCoordinateWindow_subset_carrier (B : FrameBox) :
    centeredCoordinateWindow B.frame B.coordinateCenter B.coordinateHalf ⊆
      B.carrier := by
  intro x hx
  rw [mem_centeredCoordinateWindow_iff] at hx
  let d : Fin 3 → ℝ := fun i ↦
    ⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ
  let t : Fin 3 → ℝ := fun i ↦
    if h : (B.side i : ℝ) = 0 then (2 : ℝ)⁻¹
    else d i / (B.side i : ℝ) + (2 : ℝ)⁻¹
  have hd (i : Fin 3) : |d i| ≤ (B.side i : ℝ) / 2 := by
    simpa [d, FrameBox.coordinateCenter, FrameBox.coordinateHalf] using hx i
  have ht0 (i : Fin 3) : 0 ≤ t i := by
    by_cases hs : (B.side i : ℝ) = 0
    · simp [t, hs]
    · have hspos : 0 < (B.side i : ℝ) :=
        lt_of_le_of_ne NNReal.zero_le_coe (Ne.symm hs)
      have hd' := (abs_le.mp (hd i)).1
      have hdiv : -(2 : ℝ)⁻¹ ≤ d i / (B.side i : ℝ) := by
        apply (le_div_iff₀ hspos).2
        nlinarith
      simp only [t, hs, ↓reduceDIte]
      linarith
  have ht1 (i : Fin 3) : t i ≤ 1 := by
    by_cases hs : (B.side i : ℝ) = 0
    · norm_num [t, hs]
    · have hspos : 0 < (B.side i : ℝ) :=
        lt_of_le_of_ne NNReal.zero_le_coe (Ne.symm hs)
      have hd' := (abs_le.mp (hd i)).2
      have hdiv : d i / (B.side i : ℝ) ≤ (2 : ℝ)⁻¹ := by
        apply (div_le_iff₀ hspos).2
        nlinarith
      simp only [t, hs, ↓reduceDIte]
      linarith
  have htprod (i : Fin 3) :
      (t i - (2 : ℝ)⁻¹) * (B.side i : ℝ) = d i := by
    by_cases hs : (B.side i : ℝ) = 0
    · have hd0 : d i = 0 := by
        have h := hd i
        rw [hs] at h
        have habs : |d i| = 0 :=
          le_antisymm (by simpa using h) (abs_nonneg _)
        exact abs_eq_zero.mp habs
      simp [t, hs, hd0]
    · simp only [t, hs, ↓reduceDIte]
      field_simp
      ring
  refine ⟨∑ i, t i • B.edge i, ?_, ?_⟩
  · rw [mem_parallelepiped_iff]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  · have hsum : ∑ i, d i • B.frame i = x - B.center := by
      simpa [d, inner_sub_right] using B.frame.sum_repr' (x - B.center)
    calc
      B.corner + ∑ i, t i • B.edge i =
          B.center + (∑ i, t i • B.edge i -
            ∑ i, (2 : ℝ)⁻¹ • B.edge i) := by
              simp only [FrameBox.corner]
              abel
      _ = B.center + ∑ i,
          (t i • B.edge i - (2 : ℝ)⁻¹ • B.edge i) := by
            rw [Finset.sum_sub_distrib]
      _ = B.center + ∑ i,
          ((t i - (2 : ℝ)⁻¹) * (B.side i : ℝ)) • B.frame i := by
            congr 2
            funext i
            simp only [FrameBox.edge, smul_smul]
            rw [← sub_smul]
            congr 1
            ring
      _ = B.center + ∑ i, d i • B.frame i := by
            congr 2
            funext i
            rw [htprod i]
      _ = x := by rw [hsum]; abel

/-- Exact carrier/window identity for a three-dimensional frame box. -/
theorem FrameBox.carrier_eq_centeredCoordinateWindow (B : FrameBox) :
    B.carrier = centeredCoordinateWindow B.frame
      B.coordinateCenter B.coordinateHalf :=
  Set.Subset.antisymm B.carrier_subset_centeredCoordinateWindow
    B.centeredCoordinateWindow_subset_carrier

end

end Submission.Kakeya.ConvexGeometry
