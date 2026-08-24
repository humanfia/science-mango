import FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32ActualProjectedCriticalScaleValueBridgesV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1

noncomputable section

universe u v

/-!
# Total actual scales equal their selected finite maximizers

These two proof-irrelevant equalities remove the nonempty-family proof terms
from downstream low-multiplicity statements.  They only unfold the honest
empty-family fallback after an actual nonemptiness producer is available.
-/

theorem actualProjectedAmbientNormScale_eq_finiteMaximizer
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (ceiling exponent : Real) (q : point)
    (hfamily : (actualProjectedAmbientCriticalFamily fine physical.ambient
      (physical.activeAtPoint q)).Nonempty) :
    actualProjectedAmbientNormScale fine physical ceiling exponent q =
      finiteCriticalMaximizerScale
        (actualProjectedAmbientCriticalFamily fine physical.ambient
          (physical.activeAtPoint q))
        projectedTubePairCoefficientDistance (radius : Real) ceiling exponent
        hfamily := by
  have hfamilyFinite :
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (finiteIncidenceActiveAtPoint physical.ambient
          (fun i x => x ∈ physical.carrier i) q)).Nonempty := by
    simpa only [FiniteProjectedShading.activeAtPoint] using hfamily
  rw [actualProjectedAmbientNormScale, finiteIncidenceCriticalScale,
    finiteIncidenceCriticalScaleValue, dif_pos hfamilyFinite]
  rfl

theorem actualProjectedCenteredHalfLocalizedTangencyScale_eq_finiteMaximizer
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) (q : point)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty) :
    actualProjectedCenteredHalfLocalizedTangencyScale fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent q =
      finiteCriticalMaximizerScale
        (finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily fine physical.ambient)
          projectedTubePairCoefficientDistance globalScale globalCenter
          (physical.activeAtPoint q))
        (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
          hOuter hf hf1 (physical.activeAtPoint q))
        (radius : Real) ceiling exponent hlocalized := by
  have hlocalizedFinite :
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (finiteIncidenceActiveAtPoint physical.ambient
          (fun i x => x ∈ physical.carrier i) q)).Nonempty := by
    simpa only [FiniteProjectedShading.activeAtPoint] using hlocalized
  rw [actualProjectedCenteredHalfLocalizedTangencyScale,
    finiteIncidenceLocalizedTangencyScale, finiteIncidenceCriticalScale,
    finiteIncidenceCriticalScaleValue, dif_pos hlocalizedFinite]
  rfl

#print axioms actualProjectedAmbientNormScale_eq_finiteMaximizer
#print axioms actualProjectedCenteredHalfLocalizedTangencyScale_eq_finiteMaximizer

end

end FamilyStickyCinematicL32ActualProjectedCriticalScaleValueBridgesV1
