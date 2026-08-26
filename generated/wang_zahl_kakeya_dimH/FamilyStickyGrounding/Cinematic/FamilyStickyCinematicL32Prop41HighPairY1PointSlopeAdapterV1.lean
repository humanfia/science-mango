import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41HighPairCenterCoefficientSelectionBridgeV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41HighPairY1PointSlopeAdapterV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41HighPairCenterCoefficientSelectionBridgeV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyPyzActualPositiveCenterHighPairCarrierV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# High-pair adapter to the automatic Y1 point-slope producer

The automatic point-slope theorem needs one active tube at reduced
coefficient distance at least `tGlobal / 2` from the selected centre.  A
canonical active pair separated at scale `tGlobal` supplies exactly such a
tube by the metric half-distance selector.

The scale-`tGlobal` pair lower bound remains explicit.  In particular, this
module does not replace it with the weaker currently tracked
`radius`-separation of the retained family.
-/

/-- Select one endpoint of a globally separated canonical active pair and
feed it directly to the automatic physical-point slope theorem. -/
theorem active_orientedFirstGenerationPair_exists_pointSlope_of_globalLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
      (Real × Real) iota)
    (E : Set (Real × Real))
    (activeAtPoint : Real × Real -> Finset iota)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (hwidth : (1 / 2 : Real) <= outerB - outerA)
    (hglobalDelta : 0 < globalDelta) (htGlobal : 0 < tGlobal)
    (hsmallScale :
      2 * globalDelta - (radius : Real) < tGlobal / 2400)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (q : Real × Real) (hq : q ∈ E)
    (hqTheta : q.2 ∈ centeredFractionIcc outerA outerB (1 / 16 : Real))
    (curves : Finset (Tube radius))
    (hcurves : curves = activeTubeImage fine (activeAtPoint q))
    (p : FirstGenerationCurvePair curves)
    (hpairCoefficientLower :
      let orientation := canonicalFirstGenerationPairOrientation curves p
      tGlobal <= tubePairCoefficientDistance
        (orientation.first : Tube radius)
        (orientation.second : Tube radius)) :
    exists i, i ∈ activeAtPoint q ∧
      tGlobal / 2 <=
        tubePairCoefficientDistance (fine.tubes i) (tubeAt q) ∧
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 q.2 -
          tubeCinematicTraceFirstValue (tubeAt q) f f1 q.2| <=
        activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal := by
  obtain ⟨i, hi, hcoefficientLower⟩ :=
    active_orientedFirstGenerationPair_exists_halfFar_index
      fine activeAtPoint tubeAt q curves hcurves p hpairCoefficientLower
  obtain ⟨_Delta, _thetaDelta, _theta0, _hDeltaNonneg, _hDeltaBudget,
      _hthetaDelta, _hDeltaDef, _htheta0, _hcritical, _hcriticalValue,
      _hlocality, hslope⟩ :=
    FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1.ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedCritical_pointLocality_and_slope
      fine physical E activeAtPoint tubeAt f f1 f2 outerA outerB hOuter
      hf hf1 tGlobal globalDelta facts hwidth hglobalDelta htGlobal hsmallScale
      hparameter hft hf1Lower hf1Upper hf2 hf2Continuous q hq hqTheta
      i hi hcoefficientLower
  exact ⟨i, hi, hcoefficientLower, hslope⟩

#print axioms active_orientedFirstGenerationPair_exists_pointSlope_of_globalLower

end

end FamilyStickyCinematicL32Prop41HighPairY1PointSlopeAdapterV1
