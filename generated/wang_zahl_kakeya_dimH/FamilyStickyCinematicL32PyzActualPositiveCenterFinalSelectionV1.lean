import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyE2SelectionV1
import FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
import FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualPositiveCenterFinalSelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyE2SelectionV1
open FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
open FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1

noncomputable section

/-! # Final positive-multiplicity selection on one tangency cell -/

universe u v

theorem exists_actualPositiveCenter_finalSelection
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
    (ceiling exponent threshold : Real) (hthreshold : 0 ≤ threshold)
    (hlocalized : ∀ x, x ∈ base →
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint x)).Nonempty) :
    let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
    ∃ finalLabel ∈ Finset.Icc (dyadicCeilBucket 1)
        (dyadicCeilBucket (Y1.ambient.card : Real)),
      let E2 := projectedPositiveMultiplicityDyadicCell Y1 finalLabel
      ∃ q ∈ E2,
        mu base ≤
            (continuumCriticalSingleDyadicBinFactor 1
              (physical.ambient.card : Real) : ENNReal) * mu E2 ∧
          0 < mu E2 ∧ MeasurableSet E2 ∧ E2 ⊆ base ∧
          (∀ x, x ∈ E2 → (Y1.activeAtPoint x).Nonempty) := by
  dsimp only
  obtain ⟨label, hlabel, hmeasure, hE2Pos, hE2Nonempty,
      hE2Measurable, hE2Subset, hactive, _hlabelPos, _hbin⟩ :=
    exists_actualProjectedCenteredHalfTangencyE2 mu base hbase hbasePos fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent threshold hthreshold hlocalized
  let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold
  let E2 := projectedPositiveMultiplicityDyadicCell Y1 label
  obtain ⟨q, hq⟩ := hE2Nonempty
  have hY1AmbientNonempty : Y1.ambient.Nonempty := by
    obtain ⟨i, hi⟩ := hactive q (by simpa only [Y1, E2] using hq)
    exact ⟨i, (Y1.mem_activeAtPoint q i).mp hi |>.1⟩
  have hOneAmbient : (1 : Real) ≤ (Y1.ambient.card : Real) := by
    exact_mod_cast (Finset.one_le_card.mpr hY1AmbientNonempty)
  have hlossZero :
      (continuumCriticalSingleDyadicBinFactor 1
        (Y1.ambient.card : Real) : ENNReal) ≠ 0 :=
    continuumCriticalSingleDyadicBinFactor_cast_ne_zero one_pos hOneAmbient
  have hmulRaw := div_retention_to_mul_upper hlossZero
    (ENNReal.natCast_ne_top _) (by simpa only [Y1, E2] using hmeasure)
  have hmul : mu base ≤
      (continuumCriticalSingleDyadicBinFactor 1
        (physical.ambient.card : Real) : ENNReal) * mu E2 := by
    have hambient : Y1.ambient = physical.ambient := rfl
    rw [hambient] at hmulRaw
    simpa only [mul_comm] using hmulRaw
  refine ⟨label, ?_, q, ?_, hmul, hE2Pos, ?_, ?_, ?_⟩
  · simpa only [Y1] using hlabel
  · simpa only [Y1, E2] using hq
  · simpa only [Y1, E2] using hE2Measurable
  · simpa only [Y1, E2] using hE2Subset
  · intro x hx
    exact hactive x (by simpa only [Y1, E2] using hx)

#print axioms exists_actualPositiveCenter_finalSelection

end

end FamilyStickyCinematicL32PyzActualPositiveCenterFinalSelectionV1
