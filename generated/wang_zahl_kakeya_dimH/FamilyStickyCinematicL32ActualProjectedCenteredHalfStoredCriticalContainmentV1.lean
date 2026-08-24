import FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1
import FamilyStickyCinematicL32FiniteNormCriticalBallV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfStoredCriticalContainmentV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1

noncomputable section

universe u

/-!
# Stored centered-half critical ball is literally retained

The pointwise tangency maximizer is still the one computed on the
norm-localized family.  If its selected dyadic upper endpoint is used as the
`Y₁` threshold, every member of that stored critical ball belongs to the
literal retained tube filter.  No maximizer is recomputed on the retained
family.
-/

/-- The total centered-half centre agrees with the finite maximizer centre
whenever the localized family is nonempty. -/
theorem centeredHalfTangencyCenter_eq_finiteCriticalMaximizerCenter
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty) :
    actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent q =
      finiteCriticalMaximizerCenter
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale globalCenter
          (physical.activeAtPoint q))
        (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
          hOuter hf hf1 (physical.activeAtPoint q))
        (radius : Real) ceiling exponent hlocalized := by
  have hlocalizedPoint : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (finiteIncidenceActiveAtPoint physical.ambient
        (fun i x => x ∈ physical.carrier i) q)).Nonempty := by
    simpa only [FiniteProjectedShading.activeAtPoint] using hlocalized
  simp only [actualProjectedCenteredHalfTangencyCenterTubeAt,
    finiteIncidenceLocalizedTangencyCenter, finiteIncidenceCriticalCenter,
    finiteIncidenceCriticalCenterValue, FiniteProjectedShading.activeAtPoint]
  rw [dif_pos hlocalizedPoint]
  rfl

/-- The stored centered-half scale agrees with the finite maximizer scale on
the same localized family. -/
theorem centeredHalfTangencyScale_eq_finiteCriticalMaximizerScale
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty) :
    actualProjectedCenteredHalfLocalizedTangencyScale fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent q =
      finiteCriticalMaximizerScale
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale globalCenter
          (physical.activeAtPoint q))
        (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
          hOuter hf hf1 (physical.activeAtPoint q))
        (radius : Real) ceiling exponent hlocalized := by
  have hlocalizedPoint : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (finiteIncidenceActiveAtPoint physical.ambient
        (fun i x => x ∈ physical.carrier i) q)).Nonempty := by
    simpa only [FiniteProjectedShading.activeAtPoint] using hlocalized
  simp only [actualProjectedCenteredHalfLocalizedTangencyScale,
    finiteIncidenceLocalizedTangencyScale, finiteIncidenceCriticalScale,
    finiteIncidenceCriticalScaleValue, FiniteProjectedShading.activeAtPoint]
  rw [dif_pos hlocalizedPoint]

/-- The actual stored tangency critical ball is contained in the literal
retained family as soon as the stored scale lies below the chosen `Y₁`
threshold. -/
theorem centeredHalfTangencyCriticalBall_subset_retained
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty)
    (hscaleUpper :
      actualProjectedCenteredHalfLocalizedTangencyScale fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent q ≤ threshold) :
    finiteNormCriticalBall
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale globalCenter
          (physical.activeAtPoint q))
        (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
          hOuter hf hf1 (physical.activeAtPoint q))
        (radius : Real) ceiling exponent hlocalized ⊆
      actualProjectedCenteredHalfRetainedTubeFamily fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent threshold q := by
  intro T hT
  rw [finiteNormCriticalBall, Finset.mem_filter] at hT
  rw [actualProjectedCenteredHalfRetainedTubeFamily, Finset.mem_filter]
  refine ⟨hT.1, ?_⟩
  rw [centeredHalfTangencyCenter_eq_finiteCriticalMaximizerCenter fine
    physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    ceiling exponent q hlocalized]
  apply hT.2.trans
  rw [← centeredHalfTangencyScale_eq_finiteCriticalMaximizerScale fine
    physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    ceiling exponent q hlocalized]
  exact hscaleUpper

#print axioms centeredHalfTangencyCenter_eq_finiteCriticalMaximizerCenter
#print axioms centeredHalfTangencyScale_eq_finiteCriticalMaximizerScale
#print axioms centeredHalfTangencyCriticalBall_subset_retained

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfStoredCriticalContainmentV1
