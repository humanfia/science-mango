import FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32ActualProjectedAttainedTangencyBridgeV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Equality of the two canonical actual-tube tangency values

The projected source selector and the Lemma 5.7/5.8 consumer choose a global
minimum of the same compact value--first-jet cost.  Their choice mechanisms
need not be definitionally equal, but uniqueness of the minimum value makes
the scalar distances equal.  This is a source adapter, not a numerical
tangency premise.
-/

/-- The projected critical-scale distance is exactly the attained tangency
distance used by the tube-pair Lemma 5.7 interface. -/
theorem projectedTubePairTangencyDistance_eq_attained
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z) :
    projectedTubePairTangencyDistance T U f f1 f2 A B hAB
        hfDeriv hf1Deriv =
      tubePairAttainedTangencyDistance T U f f1 f2 A B hAB
        hfDeriv hf1Deriv := by
  let hexists := exists_trace_tangencyParameter_with_minimizer
    f f1 f2 (projectedTubePairDeltaA T U)
      (projectedTubePairDeltaB T U) (projectedTubePairDeltaD T U)
      hAB hfDeriv hf1Deriv
  let Delta := Classical.choose hexists
  let hDelta := Classical.choose_spec hexists
  let thetaDelta := Classical.choose hDelta
  have hspec := Classical.choose_spec hDelta
  change Delta = _
  have heq := eq_attainedTraceTangencyDistance_of_isMinimum
    f f1 f2 (projectedTubePairDeltaA T U)
      (projectedTubePairDeltaB T U) (projectedTubePairDeltaD T U)
      A B Delta thetaDelta hAB hfDeriv hf1Deriv
      hspec.2.1 hspec.2.2.1 hspec.2.2.2
  simpa only [tubePairAttainedTangencyDistance,
    projectedTubePairDeltaA, projectedTubePairDeltaB,
    projectedTubePairDeltaD, tubePairDeltaA, tubePairDeltaB,
    tubePairDeltaD, projectedTubeGraphA, projectedTubeGraphB,
    projectedTubeGraphD, projectedTubeGraphC, tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using heq

#print axioms projectedTubePairTangencyDistance_eq_attained

end

end FamilyStickyCinematicL32ActualProjectedAttainedTangencyBridgeV1
