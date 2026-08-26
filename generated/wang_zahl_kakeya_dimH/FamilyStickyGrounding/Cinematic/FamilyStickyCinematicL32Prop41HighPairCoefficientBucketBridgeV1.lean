import FamilyStickyGrounding.FamilyStickyPyzActualPositiveCenterHighPairCarrierV1
import FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41HighPairCoefficientBucketBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyPyzActualPositiveCenterHighPairCarrierV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Honest coefficient and c-bucket facts for high actual pairs

The high-payload carrier supplies unordered pairs of distinct actual tubes.
The retained centered-half family supplies their quantitative coefficient
separation, while the active-geometry package supplies an approximate
`c`-bucket relative to its selected centre.  This module transports those
two produced facts to the canonical orientation of each high pair.

It deliberately does not assert an exact common-`c` identity, a common
positive-width rectangle, or the sharp-curvature branch.
-/

/-- A canonical orientation of a pair whose carrier is exactly the retained
tube family inherits the retained family's coefficient lower bound. -/
theorem retained_orientedFirstGenerationPair_reducedCoefficientLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real)
    (curves : Finset (Tube radius))
    (hcurves : curves =
      actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
        threshold q)
    (p : FirstGenerationCurvePair curves) :
    let orientation := canonicalFirstGenerationPairOrientation curves p
    (radius : Real) <= tubePairCoefficientDistance
      (orientation.first : Tube radius)
      (orientation.second : Tube radius) := by
  let orientation := canonicalFirstGenerationPairOrientation curves p
  change (radius : Real) <= tubePairCoefficientDistance
    (orientation.first : Tube radius) (orientation.second : Tube radius)
  have hfirstRetained : (orientation.first : Tube radius) ∈
      actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
        threshold q := by
    rw [← hcurves]
    exact orientation.first.property
  have hsecondRetained : (orientation.second : Tube radius) ∈
      actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
        threshold q := by
    rw [← hcurves]
    exact orientation.second.property
  have hne : (orientation.first : Tube radius) ≠
      (orientation.second : Tube radius) := by
    intro heq
    apply orientation.first_ne_second
    exact Subtype.ext heq
  rw [tubePairCoefficientDistance_eq_projected]
  exact retainedTubeFamily_pairwise_separated fine physical f f1 f2 outerA
    outerB hOuter hf hf1 globalScale globalCenter ceiling exponent threshold q
    (orientation.first : Tube radius) hfirstRetained
    (orientation.second : Tube radius) hsecondRetained hne

/-- If a high-pair carrier is the active image of the literal centered-half
`Y1`, the existing active-image/retained equality produces the coefficient
lower bound without any new separation callback. -/
theorem activeY1_orientedFirstGenerationPair_reducedCoefficientLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty)
    (curves : Finset (Tube radius))
    (hcurves : curves = activeTubeImage fine
      ((actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent threshold).activeAtPoint q))
    (p : FirstGenerationCurvePair curves) :
    let orientation := canonicalFirstGenerationPairOrientation curves p
    (radius : Real) <= tubePairCoefficientDistance
      (orientation.first : Tube radius)
      (orientation.second : Tube radius) := by
  have himage := activeTubeImage_centeredHalfY1_eq_retained
    base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter ceiling exponent threshold q hlocalized
  have hcurvesRetained : curves =
      actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
        threshold q := hcurves.trans himage
  exact retained_orientedFirstGenerationPair_reducedCoefficientLower
    fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter ceiling exponent threshold q curves hcurvesRetained p

/-- Two members of one high active carrier lie in an approximate common
`c` bucket of width `radius`: each is within `radius / 2` of the same
produced centre. -/
theorem active_orientedFirstGenerationPair_approxCBucket
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
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
    (q : Real × Real) (hq : q ∈ E)
    (curves : Finset (Tube radius))
    (hcurves : curves = activeTubeImage fine (activeAtPoint q))
    (p : FirstGenerationCurvePair curves) :
    let orientation := canonicalFirstGenerationPairOrientation curves p
    |tubeGraphC (orientation.first : Tube radius) -
        tubeGraphC (orientation.second : Tube radius)| <= (radius : Real) := by
  let orientation := canonicalFirstGenerationPairOrientation curves p
  change |tubeGraphC (orientation.first : Tube radius) -
      tubeGraphC (orientation.second : Tube radius)| <= (radius : Real)
  have hfirstImage : (orientation.first : Tube radius) ∈
      activeTubeImage fine (activeAtPoint q) := by
    rw [← hcurves]
    exact orientation.first.property
  have hsecondImage : (orientation.second : Tube radius) ∈
      activeTubeImage fine (activeAtPoint q) := by
    rw [← hcurves]
    exact orientation.second.property
  obtain ⟨i, hi, hfirstEq⟩ :=
    (mem_activeTubeImage_iff fine (activeAtPoint q)
      (orientation.first : Tube radius)).mp hfirstImage
  obtain ⟨j, hj, hsecondEq⟩ :=
    (mem_activeTubeImage_iff fine (activeAtPoint q)
      (orientation.second : Tube radius)).mp hsecondImage
  have hfirstBucket := facts.hactiveCBucket q hq i hi
  have hsecondBucket := facts.hactiveCBucket q hq j hj
  rw [hfirstEq] at hfirstBucket
  rw [hsecondEq] at hsecondBucket
  have hsecondBucket' :
      |tubeGraphC (tubeAt q) -
        tubeGraphC (orientation.second : Tube radius)| <=
          (radius : Real) / 2 := by
    rw [abs_sub_comm]
    exact hsecondBucket
  calc
    |tubeGraphC (orientation.first : Tube radius) -
        tubeGraphC (orientation.second : Tube radius)| =
      |(tubeGraphC (orientation.first : Tube radius) -
          tubeGraphC (tubeAt q)) +
        (tubeGraphC (tubeAt q) -
          tubeGraphC (orientation.second : Tube radius))| := by ring_nf
    _ <= |tubeGraphC (orientation.first : Tube radius) -
          tubeGraphC (tubeAt q)| +
        |tubeGraphC (tubeAt q) -
          tubeGraphC (orientation.second : Tube radius)| := abs_add_le _ _
    _ <= (radius : Real) / 2 + (radius : Real) / 2 :=
      add_le_add hfirstBucket hsecondBucket'
    _ = (radius : Real) := by ring

#print axioms retained_orientedFirstGenerationPair_reducedCoefficientLower
#print axioms activeY1_orientedFirstGenerationPair_reducedCoefficientLower
#print axioms active_orientedFirstGenerationPair_approxCBucket

end

end FamilyStickyCinematicL32Prop41HighPairCoefficientBucketBridgeV1
