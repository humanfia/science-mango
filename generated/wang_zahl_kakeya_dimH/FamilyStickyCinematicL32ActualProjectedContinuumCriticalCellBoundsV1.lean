import FamilyStickyCinematicL32ActualProjectedShadingContinuumCriticalSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1

open FamilyStickyCinematicL32ActualProjectedShadingContinuumCriticalSelectionV1
open FamilyStickyCinematicL32ContinuumCriticalDoubleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# Consumer-ready bounds for the actual continuum critical cell

The continuum selector retains integer dyadic labels.  This thin numerical
adapter turns those labels into the physical scales used by the postselected
Lemma 5.3--5.8 geometry, including both lower and upper endpoint bounds.
No nonemptiness or scale inequality is supplied by the caller.
-/

/-- The upper endpoint `2^label` is monotone in its integer label. -/
theorem dyadicCeilUpper_mono {a b : Int} (hab : a <= b) :
    dyadicCeilUpper a <= dyadicCeilUpper b := by
  unfold dyadicCeilUpper
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by exact_mod_cast hab)

/-- A label in the selected ceil-log interval has the full physical bounds
needed by the canonical rectangle scale. -/
theorem dyadicCeilUpper_bounds_of_mem_Icc
    {delta ceiling : Real} (hdelta : 0 < delta)
    (hdeltaCeiling : delta <= ceiling) {label : Int}
    (hlabel : label ∈ Finset.Icc (dyadicCeilBucket delta)
      (dyadicCeilBucket ceiling)) :
    delta <= dyadicCeilUpper label ∧
      dyadicCeilUpper label <= 2 * ceiling := by
  rw [Finset.mem_Icc] at hlabel
  have hceiling : 0 < ceiling := hdelta.trans_le hdeltaCeiling
  have hdeltaUpper := (dyadicCeilUpper_half_lt_and_le hdelta).2
  have hceilingHalf := (dyadicCeilUpper_half_lt_and_le hceiling).1
  have hlower := dyadicCeilUpper_mono hlabel.1
  have hupper := dyadicCeilUpper_mono hlabel.2
  constructor
  · exact hdeltaUpper.trans hlower
  · linarith

/-- Extract a single continuum critical cell together with the two exact
dyadic upper endpoints and every scale bound consumed after selection. -/
theorem exists_continuumCriticalDoubleDyadicCell_with_fullBounds
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (E : Set X)
    (normScale tangencyScale : X -> Real)
    {delta normCeiling tangencyCeiling : Real}
    (hdelta : 0 < delta)
    (hnormCeiling : delta <= normCeiling)
    (htangencyCeiling : delta <= tangencyCeiling)
    (hselection : HasContinuumCriticalDoubleDyadicSelection mu E
      normScale tangencyScale delta normCeiling tangencyCeiling) :
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket delta)
        (dyadicCeilBucket normCeiling),
      ∃ tangencyLabel ∈ Finset.Icc (dyadicCeilBucket delta)
          (dyadicCeilBucket tangencyCeiling),
        let tGlobal := dyadicCeilUpper normLabel
        let globalDelta := dyadicCeilUpper tangencyLabel
        mu E /
              (continuumCriticalDoubleDyadicBinFactor delta normCeiling
                tangencyCeiling : ENNReal) <=
            mu (continuumCriticalDoubleDyadicCell E normScale tangencyScale
              normLabel tangencyLabel) ∧
          delta <= tGlobal ∧
          tGlobal <= 2 * normCeiling ∧
          delta <= globalDelta ∧
          globalDelta <= 2 * tangencyCeiling ∧
          0 < tGlobal ∧
          0 < globalDelta ∧
          forall x, x ∈ continuumCriticalDoubleDyadicCell E normScale
              tangencyScale normLabel tangencyLabel ->
            tGlobal / 2 < normScale x ∧
              normScale x <= tGlobal ∧
              globalDelta / 2 < tangencyScale x ∧
              tangencyScale x <= globalDelta := by
  rcases hselection with
    ⟨normLabel, hnormLabel, tangencyLabel, htangencyLabel,
      hmeasure, htGlobalPos, hglobalDeltaPos, hbins⟩
  have htGlobalBounds := dyadicCeilUpper_bounds_of_mem_Icc
    hdelta hnormCeiling hnormLabel
  have hglobalDeltaBounds := dyadicCeilUpper_bounds_of_mem_Icc
    hdelta htangencyCeiling htangencyLabel
  refine ⟨normLabel, hnormLabel, tangencyLabel, htangencyLabel, ?_⟩
  exact ⟨hmeasure, htGlobalBounds.1, htGlobalBounds.2,
    hglobalDeltaBounds.1, hglobalDeltaBounds.2, htGlobalPos,
    hglobalDeltaPos, hbins⟩

#print axioms dyadicCeilUpper_mono
#print axioms dyadicCeilUpper_bounds_of_mem_Icc
#print axioms exists_continuumCriticalDoubleDyadicCell_with_fullBounds

end

end FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1
