import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41SharpCommonCReferenceTwoCenterBridgeV1

open Set
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

/-!
# Explicit bridge between two fixed-common-C reference centres

Both synthetic references below use the same graph-C coefficient.  Their
jet difference therefore sees only the reduced `(a,b,d)` coefficient
distance between the two underlying tubes.  In particular, the bridge does
not require either underlying tube itself to have graph-C equal to the
declared common value.
-/

/-- Two fixed-common-C references based on tubes at reduced coefficient
distance at most `rho` have the sharp `(2,4,401/100) * rho` jet bounds. -/
theorem globalCenterFixedCommonCReference_jetBounds
    {radius : NNReal} (localTube globalTube : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho : Real)
    (hdistance : tubePairCoefficientDistance localTube globalTube <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    forall z, z ∈ Icc A B ->
      |(globalCenterFixedCommonCReference localTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).rectangle.graph z -
        (globalCenterFixedCommonCReference globalTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).rectangle.graph z| <= 2 * rho ∧
      |(globalCenterFixedCommonCReference localTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).first z -
        (globalCenterFixedCommonCReference globalTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).first z| <= 4 * rho ∧
      |(globalCenterFixedCommonCReference localTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).second z -
        (globalCenterFixedCommonCReference globalTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).second z| <=
            (401 / 100 : Real) * rho := by
  have hraw := pairLocalTubeReference_fixedCommonC_jetBounds
    (normalizeTubeC localTube commonC) globalTube commonC f f1 f2 hfDeriv
      hf1Deriv A B hAB rho (by simp) (by simpa using hdistance) hparameter
        hfunction hfirst hsecond
  simpa only [pairLocalTubeReference, tubeC2GraphRectangle,
    tubeCinematicTraceFirstValue, tubeCinematicTraceSecondValue,
    globalCenterFixedCommonCReference, tubeGraphA_normalizeTubeC,
    tubeGraphB_normalizeTubeC, tubeGraphC_normalizeTubeC,
    tubeGraphD_normalizeTubeC] using hraw

/-- The second-jet-only form consumed by the two-centre Lemma 3.12
recentring interface. -/
theorem globalCenterFixedCommonCReference_second_dist_le
    {radius : NNReal} (localTube globalTube : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho : Real)
    (hdistance : tubePairCoefficientDistance localTube globalTube <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    forall z, z ∈ Icc A B ->
      |(globalCenterFixedCommonCReference localTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).second z -
        (globalCenterFixedCommonCReference globalTube commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).second z| <=
            (401 / 100 : Real) * rho := by
  intro z hz
  exact (globalCenterFixedCommonCReference_jetBounds localTube globalTube
    commonC f f1 f2 hfDeriv hf1Deriv A B hAB rho hdistance hparameter
      hfunction hfirst hsecond z hz).2.2

#print axioms globalCenterFixedCommonCReference_jetBounds
#print axioms globalCenterFixedCommonCReference_second_dist_le

end

end FamilyStickyCinematicL32Prop41SharpCommonCReferenceTwoCenterBridgeV1
