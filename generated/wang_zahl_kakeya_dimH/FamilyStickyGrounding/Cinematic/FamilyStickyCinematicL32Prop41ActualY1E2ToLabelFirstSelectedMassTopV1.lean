import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstUniformPackageV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u

/-!
# Actual E2 to label-first selected mass: top connector

This module assembles the existing actual centered-half G-prime producer,
the label-first sampler, and the exact-`c` paper-fine uniform producer.  The
occupied spatial-label cardinal disappears algebraically in the final mass
inequality; no cover statement for the sampled labels is asserted.

Audit status: this connector is conditional only.  Its
`ActualGlobalNormIndexFamilyFixedCProvenance` input is not produced by the
ordinary `G'` outcome.  The ordinary-survivor route instead uses explicit
`c` normalization and does not consume this theorem as a final endpoint.
-/

/-- The literal centered-half `Y1` at the paper global scales. -/
noncomputable def actualCenteredHalfPaperFineY1
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (ceiling exponent globalDelta : Real) :
    FiniteProjectedShading (Real × Real) iota :=
  actualProjectedCenteredHalfTangencyY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
      exponent globalDelta

/-- The genuine centered-half selector used by both the cover and uniform
geometry package. -/
noncomputable def actualCenteredHalfPaperFineTubeAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) : Real × Real -> Tube radius :=
  actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent

/-- The actual positive-multiplicity E2 cell of the centered-half `Y1`. -/
def actualCenteredHalfPaperFineE2
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (label : Int)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (ceiling exponent globalDelta : Real) : Set (Real × Real) :=
  projectedPositiveMultiplicityDyadicCell
    (actualCenteredHalfPaperFineY1 base hbase fine physical f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
        globalDelta) label

/-- Occupied active-pattern/floor labels on the actual E2 cell. -/
abbrev ActualCenteredHalfPaperFineE2SpatialLabel
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (label : Int) (mesh : Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (ceiling exponent globalDelta : Real) :=
  ActualProjectedE2SpatialLabel physical
    (actualCenteredHalfPaperFineY1 base hbase fine physical f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
        globalDelta) label mesh

/-- Paper-fine incidence data on every occupied actual spatial E2 label. -/
noncomputable def actualCenteredHalfPaperFineE2SpatialIncidenceData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (label : Int) (mesh : Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) :
    CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota)
      (ActualCenteredHalfPaperFineE2SpatialLabel base hbase fine physical
        label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
          ceiling exponent globalDelta) :=
  actualCenteredHalfProjectedE2SpatialIncidenceData fine physical
    (actualCenteredHalfPaperFineY1 base hbase fine physical f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
        globalDelta)
    label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
      ceiling exponent
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal

/-- End-to-end actual producer.  The only support assumptions are genuine
nonemptiness of the E2 cell and of its active fibres.  All spatial coverage,
first-hit mass, G-prime average mass, label survival, and three-shift losses
are theorem-generated rather than supplied as callbacks. -/
theorem exists_actualCenteredHalfPaperFineE2_labelFirstSelected_mass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (label : Int) {mesh : Real} (hmesh : 0 < mesh)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource
      (actualCenteredHalfPaperFineE2 base hbase fine physical label f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta)
      globalCenter
      (actualCenteredHalfPaperFineTubeAt fine physical f f1 f2 outerA outerB
        hOuter hf hf1 tGlobal globalCenter ceiling exponent)
      f outerA outerB tGlobal)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical
      (actualCenteredHalfPaperFineE2 base hbase fine physical label f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta)
      (actualCenteredHalfPaperFineY1 base hbase fine physical f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta).activeAtPoint
      (actualCenteredHalfPaperFineTubeAt fine physical f f1 f2 outerA outerB
        hOuter hf hf1 tGlobal globalCenter ceiling exponent)
      f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalDelta)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
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
    (hballRadiusUpper : ballRadius <= N.ceiling)
    (commonC : Real)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical tGlobal
      globalCenter
      (actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
        physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
          globalDelta globalCenter ceiling exponent)
      commonC)
    (hsmall : ActualY1PaperFineThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    let _Y1 := actualCenteredHalfPaperFineY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
        exponent globalDelta
    let source := actualCenteredHalfPaperFineE2 base hbase fine physical
      label f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
        exponent globalDelta
    let D := actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
      physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalDelta globalCenter ceiling exponent
    exists G : ActualGPrimeFineSeparatedBallPairOutcome N D
      (fun _ _ => True) ballRadius (pyzE2DegreeLower label),
    exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
    exists P : ActualGPrimeLabelFirstPaperFineUniformPackage fine N D
      (fun _ _ => True) G.left G.right ballRadius omega f outerA outerB
        globalDelta tGlobal,
      volume source *
          (pyzE2DegreeLower label *
            (pyzE2DegreeLower label -
              automaticCanonicalNearCap N ballRadius) : Nat) <=
        (ENNReal.ofReal (2 * (radius : Real)) *
            ENNReal.ofReal (Real.sqrt ((radius : Real) /
              prop41Y1PaperFineT (radius : Real) globalDelta tGlobal))) *
          ((richSeparatedCenterPairs N.family
              (canonicalTenRadiusSeparated N ballRadius)
              (fun _ _ => True)).card *
            (finiteFamilyMetricBall N.family N.distance ballRadius G.left).card *
            (finiteFamilyMetricBall N.family N.distance ballRadius G.right).card *
            24 * P.selected.card : Nat) := by
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
  have facts' : ActualCenteredHalfY1ActiveGeometryFacts fine physical source
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalDelta := by
    simpa only [source, Y1, tubeAt, actualCenteredHalfPaperFineE2,
      actualCenteredHalfPaperFineY1, actualCenteredHalfPaperFineTubeAt] using
        facts
  have hspatialLabels : D.fineLabels = fineLabels := by
    rfl
  have hpointAt : D.pointAt = pointAt := by
    rfl
  have hshading : D.shading = Y1 := by
    rfl
  have hfineLabels : D.fineLabels.Nonempty := by
    obtain ⟨q, hq⟩ := hsource
    have hpattern : patternAt q ⊆ physical.ambient := by
      exact finiteIncidenceActiveAtPoint_subset physical.ambient
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
          tGlobal := by
    rfl
  have hsymm : forall x y, N.distance x y = N.distance y x := by
    intro x y
    rw [hdistance x y, hdistance y x]
    exact projectedTubePairCoefficientDistance_comm _ _
  have htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y := by
    intro x center y
    rw [hdistance x y, hdistance x center, hdistance center y]
    exact projectedTubePairCoefficientDistance_triangle _ _ _
  obtain ⟨G⟩ :=
    exists_actualCenteredHalfY1_fineSeparatedBallPair_of_E2 base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalCenter ceiling exponent globalDelta fineT globalDelta
      tGlobal D hDactual N hNfamily label ballRadius hfineLabels hcell
      hactiveD hroom hsymm htriangle hnearRadiusLower hnearRadiusUpper
      hballRadiusLower hballRadiusUpper
  obtain ⟨omega, O⟩ := exists_actualGPrimeLabelFirstSampledOutcome N D
    (fun _ _ => True) G.left G.right ballRadius
  have hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ source := by
    intro r _hr
    exact (spatialActivePatternRepresentative_spec physical.ambient patternAt
      source mesh r).1
  have hDpaper : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt
      tubeAt f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal := by
    rfl
  have C' : ActualGlobalNormIndexFamilyFixedCProvenance fine physical tGlobal
      globalCenter D commonC := by
    simpa only [D, actualCenteredHalfPaperFineE2SpatialIncidenceData] using C
  obtain ⟨P⟩ := exists_actualGPrimeLabelFirstPaperFineUniformPackage fine
    physical source Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
    outerA outerB hOuter hf hf1 tGlobal globalDelta facts' pointSource'
    hpointE sharp hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
    tGlobal globalCenter N D hDpaper (fun _ _ => True) G.left G.right
    ballRadius hNfamily hdistance G.cross_separated commonC C' omega O
    G.bilateral hsmall
  refine ⟨G, omega, P, ?_⟩
  exact actualCenteredHalfProjectedE2_volume_mul_degreeGap_le_labelFirstSelected
    fine physical Y1 label hmesh f f1 f2 outerA outerB hOuter hf hf1
    tGlobal globalCenter ceiling exponent pointSource' hparameter fineT
    globalDelta tGlobal hmeshBase N (fun _ _ => True) ballRadius
    (pyzE2DegreeLower label) G omega P

#print axioms actualCenteredHalfPaperFineY1
#print axioms actualCenteredHalfPaperFineTubeAt
#print axioms actualCenteredHalfPaperFineE2
#print axioms actualCenteredHalfPaperFineE2SpatialIncidenceData
#print axioms exists_actualCenteredHalfPaperFineE2_labelFirstSelected_mass

end

end FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
