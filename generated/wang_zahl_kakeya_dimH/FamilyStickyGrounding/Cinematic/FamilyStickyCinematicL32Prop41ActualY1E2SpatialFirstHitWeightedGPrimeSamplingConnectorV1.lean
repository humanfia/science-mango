import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFirstHitY2ConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFirstHitY2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u v

/-!
# Actual spatial E2 first-hit mass to weighted G-prime sampling

The weight of a fine label is the volume of its deterministic first-hit
`Y₂` fibre.  Thus the automatic spatial cover supplies an exact identity,
not a cover-cardinality surrogate.  The weighted G-prime selector and random
sample then transport that mass to one genuine survivor family.
-/

/-- First-hit volume assigned to one literal fine label. -/
noncomputable def actualGPrimeE2FirstHitLabelWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (r : fineLabel) : ENNReal :=
  volume (firstHitFineRectangleY2
    (projectedPositiveMultiplicityDyadicCell D.shading label)
    D.fineLabels D.fineRectangleAt (radius : Real) r)

/-- Weighted G-prime sample together with the exact first-hit E2 mass
identity and its denominator-free mass transport. -/
structure ActualGPrimeE2FirstHitWeightedSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (ballRadius : Real) where
  sampled : ActualGPrimeWeightedFineSeparatedSampledOutcome N D
    (fun _ _ => True) ballRadius (pyzE2DegreeLower label)
      (actualGPrimeE2FirstHitLabelWeight D label)
  firstHit_mass_eq :
    (∑ r ∈ D.fineLabels, actualGPrimeE2FirstHitLabelWeight D label r) =
      volume (projectedPositiveMultiplicityDyadicCell D.shading label)
  source_mul_gap_le_eight_pairCount_mul_survivorWeight :
    volume (projectedPositiveMultiplicityDyadicCell D.shading label) *
        ((pyzE2DegreeLower label *
          (pyzE2DegreeLower label -
            automaticCanonicalNearCap N ballRadius) : Nat) : ENNReal) <=
      8 *
        ((richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius)
          (fun _ _ => True)).card : ENNReal) *
        actualGPrimeLabelFirstSurvivorWeight N D (fun _ _ => True)
          sampled.pair.left sampled.pair.right ballRadius sampled.omega
            (actualGPrimeE2FirstHitLabelWeight D label)

/-- Generic connector once the exact first-hit mass identity and the actual
E2 degree inputs have been established. -/
theorem exists_actualGPrimeE2FirstHitWeightedSampledOutcome_of_mass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (ballRadius : Real)
    (hmass :
      (∑ r ∈ D.fineLabels, actualGPrimeE2FirstHitLabelWeight D label r) =
        volume (projectedPositiveMultiplicityDyadicCell D.shading label))
    (hfineLabels : D.fineLabels.Nonempty)
    (hdegree : forall r, r ∈ D.fineLabels ->
      pyzE2DegreeLower label <=
        (actualGPrimeRetainedFineActiveFiber
          N D (fun _ _ => True) r).card)
    (hroom : automaticCanonicalNearCap N ballRadius <
      pyzE2DegreeLower label)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    Nonempty (ActualGPrimeE2FirstHitWeightedSampledOutcome
      N D label ballRadius) := by
  obtain ⟨Q⟩ := exists_actualGPrimeWeightedFineSeparatedSampledOutcome
    N D (fun _ _ => True) ballRadius (pyzE2DegreeLower label)
      (actualGPrimeE2FirstHitLabelWeight D label) hfineLabels hdegree hroom
        hsymm htriangle hnearRadiusLower hnearRadiusUpper
          hballRadiusLower hballRadiusUpper
  refine ⟨{
    sampled := Q
    firstHit_mass_eq := hmass
    source_mul_gap_le_eight_pairCount_mul_survivorWeight := ?_ }⟩
  rw [← hmass]
  exact Q.source_mul_gap_le_eight_pairCount_mul_survivorWeight

/-- Fully actual paper-fine spatial specialization.  The only support inputs
are nonemptiness of the E2 cell and of its active fibres; spatial coverage and
the first-hit mass identity are generated by the existing automatic package. -/
theorem exists_actualCenteredHalfPaperFineE2_spatialFirstHit_weightedSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (label : Int) {mesh : Real} (hmesh : 0 < mesh)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (ceiling exponent globalDelta : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource
      (actualCenteredHalfPaperFineE2 base hbase fine physical label f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta)
      globalCenter
      (actualCenteredHalfPaperFineTubeAt fine physical f f1 f2 outerA outerB
        hOuter hf hf1 tGlobal globalCenter ceiling exponent)
      f outerA outerB tGlobal)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hmeshBase : mesh <= Real.sqrt ((radius : Real) /
      prop41Y1PaperFineT (radius : Real) globalDelta tGlobal) / 2)
    (hsource : (actualCenteredHalfPaperFineE2 base hbase fine physical label
      f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
        exponent globalDelta).Nonempty)
    (hactive : forall q,
      q ∈ actualCenteredHalfPaperFineE2 base hbase fine physical label
        f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
          exponent globalDelta ->
      ((actualCenteredHalfPaperFineY1 base hbase fine physical f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta).activeAtPoint q).Nonempty)
    (N : CanonicalNormNonconcentrationData iota)
    (hNfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        ((actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
          physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
            globalDelta globalCenter ceiling exponent).fine.tubes i)
        ((actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
          physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
            globalDelta globalCenter ceiling exponent).fine.tubes j))
    (ballRadius : Real)
    (hroom : automaticCanonicalNearCap N ballRadius <
      pyzE2DegreeLower label)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    let D := actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
      physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalDelta globalCenter ceiling exponent
    Nonempty (ActualGPrimeE2FirstHitWeightedSampledOutcome
      N D label ballRadius) := by
  dsimp only
  let Y1 := actualCenteredHalfPaperFineY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
      globalDelta
  let source := actualCenteredHalfPaperFineE2 base hbase fine physical label
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
      globalDelta
  let patternAt := physical.activeAtPoint
  let fineLabels : Finset
      (ActualCenteredHalfPaperFineE2SpatialLabel base hbase fine physical
        label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
          ceiling exponent globalDelta) := Finset.univ
  let pointAt := spatialActivePatternRepresentative physical.ambient patternAt
    source mesh
  let tubeAt := actualCenteredHalfPaperFineTubeAt fine physical f f1 f2
    outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  let D := actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
    physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
      globalDelta globalCenter ceiling exponent
  change source.Nonempty at hsource
  change forall q, q ∈ source -> (Y1.activeAtPoint q).Nonempty at hactive
  have pointSource' : ActualCenteredHalfPointRectangleSource source
      globalCenter tubeAt f outerA outerB tGlobal := by
    simpa only [source, tubeAt, actualCenteredHalfPaperFineE2,
      actualCenteredHalfPaperFineY1, actualCenteredHalfPaperFineTubeAt] using
        pointSource
  have hspatialLabels : D.fineLabels = fineLabels := by rfl
  have hpointAt : D.pointAt = pointAt := by rfl
  have hshading : D.shading = Y1 := by rfl
  have hfineLabels : D.fineLabels.Nonempty := by
    obtain ⟨q, hq⟩ := hsource
    have hpattern : patternAt q ⊆ physical.ambient :=
      finiteIncidenceActiveAtPoint_subset physical.ambient
        (fun i x => x ∈ physical.carrier i) q
    have hy : |q.2| <= 1 := by
      have htheta := pointSource'.hpointTheta q hq
      apply hparameter q.2
      rcases htheta with ⟨hthetaLeft, hthetaRight⟩
      constructor
      · simp only [centeredFractionLeft] at hthetaLeft
        linarith
      · simp only [centeredFractionRight] at hthetaRight
        linarith
    let r := spatialActivePatternOwnLabel physical.ambient patternAt source
      hmesh q hq hpattern hy
    rw [hspatialLabels]
    exact ⟨r, Finset.mem_univ r⟩
  have hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading label := by
    intro r _hr
    rw [hpointAt, hshading]
    exact (spatialActivePatternRepresentative_spec physical.ambient patternAt
      source mesh r).1
  have hactiveD : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty := by
    intro r hr
    exact hactive (D.pointAt r) (hcell r hr)
  have hDactual : D = actualCenteredHalfY1FineCoarseRectangleData base hbase
      fine physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
        tGlobal globalCenter ceiling exponent globalDelta fineT globalDelta
          tGlobal := by rfl
  have hsubsetD : forall r, r ∈ D.fineLabels ->
      D.shading.activeAtPoint (D.pointAt r) ⊆ N.family := by
    intro r hr
    rw [hNfamily, hDactual]
    exact actualCenteredHalfY1_activeAtFine_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 tGlobal globalCenter ceiling exponent globalDelta fineT
      globalDelta tGlobal r (by simpa only [hspatialLabels] using hr)
  have hdegreeD : forall r, r ∈ D.fineLabels ->
      pyzE2DegreeLower label <=
        (actualGPrimeRetainedFineActiveFiber
          N D (fun _ _ => True) r).card := by
    intro r hr
    exact pyzE2DegreeLower_le_actualGPrimeRetainedFineActiveFiber_true
      N D label r hr (hcell r hr) (hactiveD r hr) (hsubsetD r hr)
  have hsymm : forall x y, N.distance x y = N.distance y x := by
    intro x y
    rw [hdistance x y, hdistance y x]
    exact projectedTubePairCoefficientDistance_comm _ _
  have htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y := by
    intro x center y
    rw [hdistance x y, hdistance x center, hdistance center y]
    exact projectedTubePairCoefficientDistance_triangle _ _ _
  have hDpaper : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt
      tubeAt f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal := by
    rfl
  have Hpackage :=
    actualCenteredHalfProjectedE2_spatialActivePattern_firstHitY2_package
      fine physical Y1 label hmesh f f1 f2 outerA outerB hOuter hf hf1
        tGlobal globalCenter ceiling exponent pointSource' hparameter fineT
          globalDelta tGlobal hmeshBase
  have hmass :
      (∑ r ∈ D.fineLabels, actualGPrimeE2FirstHitLabelWeight D label r) =
        volume (projectedPositiveMultiplicityDyadicCell D.shading label) := by
    have hmass' := Hpackage.2.2.2.1 volume
    rw [hDpaper]
    simpa only [actualGPrimeE2FirstHitLabelWeight,
      y1FineCoarseRectangleData, fineLabels, pointAt, tubeAt,
      actualCenteredHalfPaperFineTubeAt, actualCenteredHalfPaperFineE2,
      patternAt, source, Y1] using hmass'
  exact exists_actualGPrimeE2FirstHitWeightedSampledOutcome_of_mass
    N D label ballRadius hmass hfineLabels hdegreeD hroom hsymm htriangle
      hnearRadiusLower hnearRadiusUpper hballRadiusLower hballRadiusUpper

#print axioms actualGPrimeE2FirstHitLabelWeight
#print axioms ActualGPrimeE2FirstHitWeightedSampledOutcome
#print axioms exists_actualGPrimeE2FirstHitWeightedSampledOutcome_of_mass
#print axioms exists_actualCenteredHalfPaperFineE2_spatialFirstHit_weightedSampledOutcome

end

end FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
