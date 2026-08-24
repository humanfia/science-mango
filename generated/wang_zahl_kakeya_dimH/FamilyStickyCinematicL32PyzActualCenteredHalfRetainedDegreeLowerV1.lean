import FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1
import FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzActualCenteredHalfRetainedDegreeLowerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1

noncomputable section

/-!
# Retained tube cardinality in the actual E2 degree window

The retained Tube family is the image of the actual final index fibre.  An
image never has larger cardinality than its source, so the upper endpoint of
the E2 dyadic window and its factor-two comparison to the lower endpoint give
the estimate without an injectivity or essentially-distinctness premise.
-/

theorem retained_card_le_two_mul_degreeLower
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real)
    (label : Int) (q : Real × Real)
    (hlocalized : (finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter
      (physical.activeAtPoint q)).Nonempty)
    (hq : q ∈ projectedPositiveMultiplicityDyadicCell
      (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent threshold) label)
    (hactive : ((actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent threshold).activeAtPoint q).Nonempty) :
    (actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
      outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
      threshold q).card ≤ 2 * pyzE2DegreeLower label := by
  let Y1 := actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
    exponent threshold
  have himage := activeTubeImage_centeredHalfY1_eq_retained base hbase fine
    physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    ceiling exponent threshold q hlocalized
  calc
    (actualProjectedCenteredHalfRetainedTubeFamily fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter ceiling exponent
        threshold q).card = (activeTubeImage fine (Y1.activeAtPoint q)).card :=
      himage.symm ▸ rfl
    _ ≤ (Y1.activeAtPoint q).card := by
      classical
      unfold activeTubeImage
      exact Finset.card_image_le
    _ ≤ pyzE2DegreeUpper label :=
      active_card_le_pyzE2DegreeUpper_of_mem_cell Y1 label q
        (by simpa only [Y1] using hq) (by simpa only [Y1] using hactive)
    _ ≤ 2 * pyzE2DegreeLower label :=
      pyzE2DegreeUpper_le_two_mul_lower label

end
end FamilyStickyCinematicL32PyzActualCenteredHalfRetainedDegreeLowerV1
