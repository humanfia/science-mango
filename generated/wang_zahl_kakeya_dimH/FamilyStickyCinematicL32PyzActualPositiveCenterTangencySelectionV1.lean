import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
import FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
import FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualPositiveCenterTangencySelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
open FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1

noncomputable section

/-! # Tangency selection on one positive norm-cover cell -/

universe u v

theorem exists_actualPositiveCenter_tangencySelection
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (hbasePos : 0 < mu base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hlocalized : ∀ x, x ∈ base →
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint x)).Nonempty) :
    let tangencyScale :=
      actualProjectedCenteredHalfLocalizedTangencyScale fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent
    ∃ tangencyLabel ∈
        Finset.Icc (dyadicCeilBucket (radius : Real))
          (dyadicCeilBucket (36 * globalScale)),
      let tangencyThreshold := dyadicCeilUpper tangencyLabel
      let E_t := continuumCriticalSingleDyadicCell base tangencyScale
        tangencyLabel
      MeasurableSet E_t ∧ 0 < mu E_t ∧
        mu base ≤
          (continuumCriticalSingleDyadicBinFactor (radius : Real)
            (36 * globalScale) : ENNReal) * mu E_t ∧
        E_t ⊆ base ∧
        (∀ x, x ∈ E_t →
          tangencyThreshold / 2 < tangencyScale x ∧
            tangencyScale x ≤ tangencyThreshold) ∧
        ∀ x, x ∈ E_t →
          (finiteIncidenceNormLocalizedFamilyValue
            (actualProjectedAmbientCriticalFamily fine physical.ambient)
            projectedTubePairCoefficientDistance globalScale globalCenter
            (physical.activeAtPoint x)).Nonempty := by
  dsimp only
  let tangencyScale :=
    actualProjectedCenteredHalfLocalizedTangencyScale fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      (36 * globalScale) tangencyExponent
  have hscaleMeasurable : Measurable tangencyScale := by
    simpa only [tangencyScale] using
      measurable_actualProjectedCenteredHalfLocalizedTangencyScale fine
        physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter (36 * globalScale) tangencyExponent
  have hscaleBounds : ∀ x ∈ base,
      (radius : Real) ≤ tangencyScale x ∧
        tangencyScale x ≤ 36 * globalScale := by
    intro x hx
    simpa only [tangencyScale,
      actualProjectedCenteredHalfLocalizedTangencyScale,
      FiniteProjectedShading.activeAtPoint] using
      (finiteIncidenceLocalizedTangencyScale_bounds physical.ambient
        (fun i x ↦ x ∈ physical.carrier i)
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
          hOuter hf hf1)
        hradiusTangency (hlocalized x hx))
  obtain ⟨label, hlabel, hmeasure, hthresholdPos, hbin⟩ :=
    exists_continuumCritical_single_dyadic_selection mu tangencyScale hbase
      (by exact_mod_cast hradius) hradiusTangency hscaleMeasurable hscaleBounds
  let threshold := dyadicCeilUpper label
  let E_t := continuumCriticalSingleDyadicCell base tangencyScale label
  have hEtMeasurable : MeasurableSet E_t :=
    measurableSet_continuumCriticalSingleDyadicCell hbase hscaleMeasurable
      label
  have hEtPos : 0 < mu E_t := by
    have hquotPos : 0 < mu base /
        (continuumCriticalSingleDyadicBinFactor (radius : Real)
          (36 * globalScale) : ENNReal) :=
      ENNReal.div_pos (ne_of_gt hbasePos) (ENNReal.natCast_ne_top _)
    exact hquotPos.trans_le (by simpa only [E_t] using hmeasure)
  have hlossZero :
      (continuumCriticalSingleDyadicBinFactor (radius : Real)
        (36 * globalScale) : ENNReal) ≠ 0 :=
    continuumCriticalSingleDyadicBinFactor_cast_ne_zero
      (by exact_mod_cast hradius) hradiusTangency
  have hmulRaw := div_retention_to_mul_upper hlossZero
    (ENNReal.natCast_ne_top _) (by simpa only [E_t] using hmeasure)
  have hmul : mu base ≤
      (continuumCriticalSingleDyadicBinFactor (radius : Real)
        (36 * globalScale) : ENNReal) * mu E_t := by
    simpa only [mul_comm] using hmulRaw
  refine ⟨label, hlabel, hEtMeasurable, hEtPos, hmul, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx
    simpa only [threshold, E_t] using hbin x hx
  · intro x hx
    exact hlocalized x hx.1

#print axioms exists_actualPositiveCenter_tangencySelection

end

end FamilyStickyCinematicL32PyzActualPositiveCenterTangencySelectionV1
