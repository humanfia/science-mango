import FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
import FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1

open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# One continuum dyadic critical-scale selection

The norm scale has already been fixed before the global cover `B` is chosen.
Only the subsequent tangency critical scale must now be pigeonholed.  This
module is the one-label analogue of the earlier double-dyadic kernel, with
the exact number of admitted labels and no redundant second loss.
-/

universe u

variable {X : Type u} [MeasurableSpace X]

/-- Exact number of possible ceil-log labels in the compact interval. -/
def continuumCriticalSingleDyadicBinFactor (delta ceiling : Real) : Nat :=
  (dyadicCeilBucket ceiling + 1 - dyadicCeilBucket delta).toNat

/-- The literal continuum cell on which one critical-scale label is fixed. -/
def continuumCriticalSingleDyadicCell
    (E : Set X) (scale : X → Real) (label : Int) : Set X :=
  measurableLabelCell E (fun x => dyadicCeilBucket (scale x)) label

theorem measurableSet_continuumCriticalSingleDyadicCell
    {E : Set X} {scale : X → Real}
    (hE : MeasurableSet E) (hscale : Measurable scale) (label : Int) :
    MeasurableSet (continuumCriticalSingleDyadicCell E scale label) := by
  exact measurableSet_measurableLabelCell hE
    (measurable_dyadicCeilBucket.comp hscale) label

/-- Measurable one-scale dyadic selection with exact average-measure loss and
the half-open bin conclusion. -/
theorem exists_continuumCritical_single_dyadic_selection
    (mu : Measure X) {E : Set X} (scale : X → Real)
    {delta ceiling : Real}
    (hE : MeasurableSet E) (hdelta : 0 < delta)
    (hdeltaCeiling : delta ≤ ceiling)
    (hscaleMeasurable : Measurable scale)
    (hscaleBounds : ∀ x ∈ E,
      delta ≤ scale x ∧ scale x ≤ ceiling) :
    ∃ label ∈ Finset.Icc (dyadicCeilBucket delta)
        (dyadicCeilBucket ceiling),
      mu E / (continuumCriticalSingleDyadicBinFactor delta ceiling :
          ENNReal) ≤
        mu (continuumCriticalSingleDyadicCell E scale label) ∧
      0 < dyadicCeilUpper label ∧
      ∀ x ∈ continuumCriticalSingleDyadicCell E scale label,
        dyadicCeilUpper label / 2 < scale x ∧
        scale x ≤ dyadicCeilUpper label := by
  classical
  let labels : Finset Int :=
    Finset.Icc (dyadicCeilBucket delta) (dyadicCeilBucket ceiling)
  have hlabelLe : dyadicCeilBucket delta ≤ dyadicCeilBucket ceiling :=
    dyadicCeilBucket_mono hdelta hdeltaCeiling
  have hlabels : labels.Nonempty := by
    refine ⟨dyadicCeilBucket delta, ?_⟩
    simpa [labels] using hlabelLe
  have hrange : ∀ x ∈ E, dyadicCeilBucket (scale x) ∈ labels := by
    intro x hx
    change dyadicCeilBucket (scale x) ∈
      Finset.Icc (dyadicCeilBucket delta) (dyadicCeilBucket ceiling)
    rw [Finset.mem_Icc]
    have hbounds := hscaleBounds x hx
    have hxPositive : 0 < scale x := hdelta.trans_le hbounds.1
    exact ⟨dyadicCeilBucket_mono hdelta hbounds.1,
      dyadicCeilBucket_mono hxPositive hbounds.2⟩
  obtain ⟨label, hlabel, hmeasure⟩ :=
    exists_measurableLabelCell_measure_ge_average mu labels hlabels hE
      (measurable_dyadicCeilBucket.comp hscaleMeasurable) hrange
  refine ⟨label, ?_, ?_, ?_, ?_⟩
  · simpa [labels] using hlabel
  · simpa [labels, continuumCriticalSingleDyadicBinFactor,
      continuumCriticalSingleDyadicCell, Int.card_Icc, Function.comp_def]
      using hmeasure
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · intro x hx
    have hxE : x ∈ E := hx.1
    have hlabelEq : dyadicCeilBucket (scale x) = label := by
      simpa [continuumCriticalSingleDyadicCell, measurableLabelCell] using hx.2
    have hxPositive : 0 < scale x :=
      hdelta.trans_le (hscaleBounds x hxE).1
    have hbin := dyadicCeilUpper_half_lt_and_le hxPositive
    exact ⟨by simpa [hlabelEq] using hbin.1,
      by simpa [hlabelEq] using hbin.2⟩

#print axioms continuumCriticalSingleDyadicBinFactor
#print axioms continuumCriticalSingleDyadicCell
#print axioms measurableSet_continuumCriticalSingleDyadicCell
#print axioms exists_continuumCritical_single_dyadic_selection

end

end FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
