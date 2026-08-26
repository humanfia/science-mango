import FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41HighPairCoefficientBucketBridgeV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41HighPairCenterCoefficientSelectionBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyPyzActualPositiveCenterHighPairCarrierV1
open FamilyStickyCinematicL32Prop41HighPairCoefficientBucketBridgeV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Selecting one high-pair tube far from a prescribed centre

The reduced coefficient distance is an `l1` pseudometric.  Consequently,
if a pair is separated by at least `t`, then relative to every third tube
one endpoint is separated by at least `t / 2`.  The active-carrier wrappers
below retain the actual index witnessing that endpoint.

No locality, slope, tangency, or curvature conclusion is asserted here.
-/

/-- A coefficient-separated pair cannot have both endpoints strictly
closer than half its lower separation scale to the same centre. -/
theorem pairCoefficientLower_forces_one_halfFar_from_center
    {radius : NNReal} (T U V : Tube radius) {t : Real}
    (hlower : t <= tubePairCoefficientDistance T U) :
    t / 2 <= tubePairCoefficientDistance T V ∨
      t / 2 <= tubePairCoefficientDistance U V := by
  by_cases hT : t / 2 <= tubePairCoefficientDistance T V
  · exact Or.inl hT
  · right
    have hTlt : tubePairCoefficientDistance T V < t / 2 :=
      lt_of_not_ge hT
    have htriangle := tubePairCoefficientDistance_triangle T U V
    rw [tubePairCoefficientDistance_comm V U] at htriangle
    linarith

/-- For a canonical pair in an active tube image, extract an actual active
index realizing one endpoint that is half-far from the prescribed centre. -/
theorem active_orientedFirstGenerationPair_exists_halfFar_index
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (activeAtPoint : Real × Real -> Finset iota)
    (tubeAt : Real × Real -> Tube radius)
    (q : Real × Real) (curves : Finset (Tube radius))
    (hcurves : curves = activeTubeImage fine (activeAtPoint q))
    (p : FirstGenerationCurvePair curves) {t : Real}
    (hlower :
      let orientation := canonicalFirstGenerationPairOrientation curves p
      t <= tubePairCoefficientDistance
        (orientation.first : Tube radius)
        (orientation.second : Tube radius)) :
    exists i, i ∈ activeAtPoint q ∧
      t / 2 <= tubePairCoefficientDistance (fine.tubes i) (tubeAt q) := by
  let orientation := canonicalFirstGenerationPairOrientation curves p
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
  have hfar := pairCoefficientLower_forces_one_halfFar_from_center
    (orientation.first : Tube radius) (orientation.second : Tube radius)
      (tubeAt q) hlower
  rcases hfar with hfirstFar | hsecondFar
  · rw [← hfirstEq] at hfirstFar
    exact ⟨i, hi, hfirstFar⟩
  · rw [← hsecondEq] at hsecondFar
    exact ⟨j, hj, hsecondFar⟩

/-- The active `Y1` high-pair coefficient lower bound therefore selects an
active index whose tube is at least `radius / 2` from any prescribed centre
tube at the same payload point. -/
theorem activeY1_orientedFirstGenerationPair_exists_halfRadiusFar_index
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
      (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) (q : Real × Real)
    (hlocalized : (FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1.finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1.projectedTubePairCoefficientDistance
      globalScale globalCenter (physical.activeAtPoint q)).Nonempty)
    (tubeAt : Real × Real -> Tube radius)
    (curves : Finset (Tube radius))
    (hcurves : curves = activeTubeImage fine
      ((actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent threshold).activeAtPoint q))
    (p : FirstGenerationCurvePair curves) :
    exists i,
      i ∈ (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
        exponent threshold).activeAtPoint q ∧
      (radius : Real) / 2 <=
        tubePairCoefficientDistance (fine.tubes i) (tubeAt q) := by
  let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold
  have hlower :=
    activeY1_orientedFirstGenerationPair_reducedCoefficientLower
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold q hlocalized curves
      hcurves p
  have hchosen := active_orientedFirstGenerationPair_exists_halfFar_index
    fine Y1.activeAtPoint tubeAt q curves (by simpa only [Y1] using hcurves)
      p hlower
  simpa only [Y1] using hchosen

#print axioms pairCoefficientLower_forces_one_halfFar_from_center
#print axioms active_orientedFirstGenerationPair_exists_halfFar_index
#print axioms activeY1_orientedFirstGenerationPair_exists_halfRadiusFar_index

end

end FamilyStickyCinematicL32Prop41HighPairCenterCoefficientSelectionBridgeV1
