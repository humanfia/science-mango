import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternCardLowerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstSelectedMassChainV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstSelectedMassChainV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternCardLowerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstUniformPackageV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

noncomputable section

universe u v

/-!
# Actual raw E2 mass to label-first three-shift selected mass

The raw spatial cover gives a lower cardinality estimate in denominator-free
form, while the G-prime label-first chain gives a lower bound with the same raw
label cardinality on its left.  Multiplying the first inequality by the
degree-gap factor and then using the second eliminates that intermediate raw
cardinality without division.

This is a mass telescope, not a sampled-cover assertion.
-/

/-- Pure denominator-free telescope eliminating one finite cardinality. -/
theorem volume_mul_nat_le_area_mul_budget_of_card_bounds
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (labels : Finset index)
    (area : ENNReal) (degreeMass budget : Nat)
    (hvolume : volume source <= (labels.card : ENNReal) * area)
    (hbudget : labels.card * degreeMass <= budget) :
    volume source * (degreeMass : ENNReal) <=
      area * (budget : ENNReal) := by
  have hbudgetENN :
      ((labels.card * degreeMass : Nat) : ENNReal) <=
        (budget : ENNReal) := by
    exact_mod_cast hbudget
  calc
    volume source * (degreeMass : ENNReal) <=
        ((labels.card : ENNReal) * area) *
          (degreeMass : ENNReal) := by
      gcongr
    _ = area * ((labels.card : ENNReal) *
          (degreeMass : ENNReal)) := by
      ac_rfl
    _ = area * ((labels.card * degreeMass : Nat) : ENNReal) := by
      simp
    _ <= area * (budget : ENNReal) := by
      gcongr

/-- Compose an already established raw E2/card lower bound with the exact
G-prime edge-mass, label-first survival, and three-shift selected-card chain. -/
theorem ActualGPrimeFineSeparatedBallPairOutcome.volume_mul_degreeGap_le_selected_of_cardLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat)
    (G : ActualGPrimeFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstPaperFineUniformPackage fine N D keep
      G.left G.right ballRadius omega f outerA outerB globalDelta tGlobal)
    (source : Set (Real × Real)) (fineArea : ENNReal)
    (hvolume : volume source <=
      (D.fineLabels.card : ENNReal) * fineArea) :
    volume source *
        (degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) <=
      fineArea *
        ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (fun _ _ => True)).card *
          (finiteFamilyMetricBall
            N.family N.distance ballRadius G.left).card *
          (finiteFamilyMetricBall
            N.family N.distance ballRadius G.right).card *
          24 * P.selected.card : Nat) := by
  apply volume_mul_nat_le_area_mul_budget_of_card_bounds
    source D.fineLabels fineArea
      (degreeLower *
        (degreeLower - automaticCanonicalNearCap N ballRadius))
      ((richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius)
          (fun _ _ => True)).card *
        (finiteFamilyMetricBall
          N.family N.distance ballRadius G.left).card *
        (finiteFamilyMetricBall
          N.family N.distance ballRadius G.right).card *
        24 * P.selected.card)
      hvolume
  exact _root_.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstSelectedMassChainV1.ActualGPrimeFineSeparatedBallPairOutcome.mass_le_selected
    fine N D keep ballRadius degreeLower G omega f outerA outerB globalDelta
      tGlobal P

/-- The occupied spatial label type for the actual projected E2 cell. -/
abbrev ActualProjectedE2SpatialLabel
    {iota : Type u} [DecidableEq iota]
    (physical Y1 : FiniteProjectedShading (Real × Real) iota)
    (label : Int) (mesh : Real) :=
  SpatialActivePatternLabel physical.ambient physical.activeAtPoint
    (projectedPositiveMultiplicityDyadicCell Y1 label) mesh

/-- The literal incidence data built on all occupied spatial E2 labels. -/
noncomputable def actualCenteredHalfProjectedE2SpatialIncidenceData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical Y1 : FiniteProjectedShading (Real × Real) iota)
    (label : Int) (mesh : Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent fineT coarseDelta coarseT : Real) :
    CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota)
      (ActualProjectedE2SpatialLabel physical Y1 label mesh) :=
  let source := projectedPositiveMultiplicityDyadicCell Y1 label
  let patternAt := physical.activeAtPoint
  let fineLabels : Finset
      (ActualProjectedE2SpatialLabel physical Y1 label mesh) := Finset.univ
  let pointAt := spatialActivePatternRepresentative
    physical.ambient patternAt source mesh
  let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent
  y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real) fineT coarseDelta coarseT

/-- Fully actual quantitative composition from the literal raw spatial E2
cover to the label-first sampler's three-shift `P.selected`.  Its inputs after
the geometric source data are the genuine G-prime outcome and uniform package;
there is no cover or mass callback. -/
theorem actualCenteredHalfProjectedE2_volume_mul_degreeGap_le_labelFirstSelected
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical Y1 : FiniteProjectedShading (Real × Real) iota)
    (label : Int) {mesh : Real} (hmesh : 0 < mesh)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource
      (projectedPositiveMultiplicityDyadicCell Y1 label) globalCenter
      (actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent)
      f outerA outerB globalScale)
    (hparameter : ∀ z, z ∈ Icc outerA outerB -> |z| ≤ 1)
    (fineT coarseDelta coarseT : Real)
    (hmeshBase : mesh ≤ Real.sqrt ((radius : Real) / fineT) / 2)
    (N : CanonicalNormNonconcentrationData iota)
    (keep : iota -> ActualProjectedE2SpatialLabel physical Y1 label mesh ->
      Prop)
    (ballRadius : Real) (degreeLower : Nat)
    (G : ActualGPrimeFineSeparatedBallPairOutcome N
      (actualCenteredHalfProjectedE2SpatialIncidenceData fine physical Y1
        label mesh f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent fineT coarseDelta coarseT)
      keep ballRadius degreeLower)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (P : ActualGPrimeLabelFirstPaperFineUniformPackage fine N
      (actualCenteredHalfProjectedE2SpatialIncidenceData fine physical Y1
        label mesh f f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter ceiling exponent fineT coarseDelta coarseT)
      keep G.left G.right ballRadius omega f outerA outerB coarseDelta
        coarseT) :
    volume (projectedPositiveMultiplicityDyadicCell Y1 label) *
        (degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) <=
      (ENNReal.ofReal (2 * (radius : Real)) *
          ENNReal.ofReal (Real.sqrt ((radius : Real) / fineT))) *
        ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (fun _ _ => True)).card *
          (finiteFamilyMetricBall
            N.family N.distance ballRadius G.left).card *
          (finiteFamilyMetricBall
            N.family N.distance ballRadius G.right).card *
          24 * P.selected.card : Nat) := by
  let D := actualCenteredHalfProjectedE2SpatialIncidenceData fine physical Y1
    label mesh f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent fineT coarseDelta coarseT
  let fineArea : ENNReal :=
    ENNReal.ofReal (2 * (radius : Real)) *
      ENNReal.ofReal (Real.sqrt ((radius : Real) / fineT))
  have hvolumeRaw :=
    actualCenteredHalfProjectedE2_volume_le_spatialActivePattern_card_mul_fineArea
      fine physical Y1 label hmesh f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent pointSource hparameter fineT
      coarseDelta coarseT hmeshBase
  have hvolume : volume (projectedPositiveMultiplicityDyadicCell Y1 label) <=
      (D.fineLabels.card : ENNReal) * fineArea := by
    simpa only [D, fineArea,
      actualCenteredHalfProjectedE2SpatialIncidenceData,
      y1FineCoarseRectangleData] using hvolumeRaw
  exact _root_.FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1.ActualGPrimeFineSeparatedBallPairOutcome.volume_mul_degreeGap_le_selected_of_cardLower
    fine N D keep ballRadius degreeLower G omega f outerA outerB coarseDelta
      coarseT P (projectedPositiveMultiplicityDyadicCell Y1 label) fineArea
      hvolume

#print axioms volume_mul_nat_le_area_mul_budget_of_card_bounds
#print axioms ActualGPrimeFineSeparatedBallPairOutcome.volume_mul_degreeGap_le_selected_of_cardLower
#print axioms actualCenteredHalfProjectedE2SpatialIncidenceData
#print axioms actualCenteredHalfProjectedE2_volume_mul_degreeGap_le_labelFirstSelected

end

end FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
