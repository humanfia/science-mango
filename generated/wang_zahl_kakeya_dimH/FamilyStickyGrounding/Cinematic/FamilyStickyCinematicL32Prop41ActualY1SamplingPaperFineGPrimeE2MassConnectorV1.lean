import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeBudgetSampleConnectorV1
import FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeE2MassConnectorV1

open Set MeasureTheory
open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeMassBlockProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeMassBudgetNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeBudgetSampleConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

noncomputable section

universe u v w

/-!
# The actual E2 source of the G-prime mass budget

The concrete G-prime endpoint consumes an exact source-mass budget.  For
fine source points in one positive-center E2 cell, all of the structural
parts of that budget are already present:

* a nonempty good-pair family contains a fine-label witness;
* one E2 label gives a uniform active-degree lower bound;
* the positive-center payload certifies nonempty active fibres throughout
  its selected E2 cell.

The only datum not forced by the current pipeline is the displayed natural
number inequality comparing that E2 degree with the rich-block and dyadic
bucket losses.  The endpoint below leaves exactly this readable numerical
condition, rather than an opaque `AutomaticRichRetainedMassBudget` premise.
-/

/-- A genuine good pair carries a literal fine-label witness. -/
theorem fineLabels_nonempty_of_goodPairs_nonempty
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (hgood : D.goodPairs.Nonempty) :
    D.fineLabels.Nonempty := by
  obtain ⟨pair, hpair⟩ := hgood
  have hpair' := D.mem_goodPairs_iff.mp hpair
  exact ⟨pair.2, hpair'.2.1⟩

/-- Uniform membership in one E2 cell and the single scalar dominance
inequality imply the exact source budget consumed by G-prime.  Fine-label
nonemptiness is recovered from the already-required nonempty good-pair
family. -/
theorem automaticRichRetainedMassBudget_of_E2Dominance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (label : Int) (richness degreeUpper : Nat)
    (hgood : D.goodPairs.Nonempty)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hdominance : coarseDegreeBucketLoss D *
      ((richness + 1) * degreeUpper) <= pyzE2DegreeLower label) :
    AutomaticRichRetainedMassBudget D richness degreeUpper := by
  have hfine : D.fineLabels.Nonempty :=
    fineLabels_nonempty_of_goodPairs_nonempty D hgood
  have hsource : ActiveDegreeRichRetainedMassBudget D
      (pyzE2DegreeLower label) richness degreeUpper :=
    activeDegreeRichRetainedMassBudget_of_dominance D
      (pyzE2DegreeLower label) richness degreeUpper hfine hdominance
  unfold ActiveDegreeRichRetainedMassBudget at hsource
  unfold AutomaticRichRetainedMassBudget
  exact hsource.trans
    (fineLabels_mul_pyzE2DegreeLower_le_goodPairs_card D label hcell hactive)

/-- The canonical high inequality alone does not imply the G-prime mass
dominance.  At the genuine dyadic endpoint `pyzE2DegreeLower 11 = 1024`,
the high threshold with `logCount = 22` holds, while the smallest typical
bucket loss and degree block already fail once richness is `256`.

Thus a bound on the product of bucket loss, richness, and selected degree is
mathematically necessary; it cannot be recovered from `24 * logCount <=
degreeLower` alone. -/
theorem highThreshold_does_not_imply_E2MassDominance :
    24 * 22 <= pyzE2DegreeLower 11 /\
      not (2 * ((256 + 1) * 2) <= pyzE2DegreeLower 11) := by
  norm_num [pyzE2DegreeLower,
    FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1.dyadicCeilUpper]

/-- The positive-center payload turns source membership in its selected E2
set into both structural hypotheses required by the preceding budget lemma.
The shading equality is the exact alignment condition between a coarse
rectangle data record and the payload's centered-half Y1. -/
theorem positiveCenterPayload_uniform_E2_sources
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (hshading : D.shading = positiveCenterY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent payload.tangencyLabel)
    (hpointE2 : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ positiveCenterE2 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent payload.tangencyLabel payload.finalLabel) :
    (forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading
        payload.finalLabel) ∧
    (forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty) := by
  obtain ⟨_hfinalLabel, _hq, _hmeasure, _hEtPos, _hEtSubset,
      _htangencyBin, _hE2Pos, _hE2Measurable, _hE2Subset, hactiveE2⟩ :=
    payload.certificate
  constructor
  · intro r hr
    rw [hshading]
    simpa only [positiveCenterE2] using hpointE2 r hr
  · intro r hr
    rw [hshading]
    exact hactiveE2 (D.pointAt r) (hpointE2 r hr)

/-- In a positive-center E2 source, the opaque G-prime budget follows from
one explicit natural-number comparison. -/
theorem automaticRichRetainedMassBudget_of_positiveCenterPayloadDominance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (richness degreeUpper : Nat)
    (hgood : D.goodPairs.Nonempty)
    (hshading : D.shading = positiveCenterY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent payload.tangencyLabel)
    (hpointE2 : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ positiveCenterE2 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent payload.tangencyLabel payload.finalLabel)
    (hdominance : coarseDegreeBucketLoss D *
      ((richness + 1) * degreeUpper) <=
        pyzE2DegreeLower payload.finalLabel) :
    AutomaticRichRetainedMassBudget D richness degreeUpper := by
  have hsources := positiveCenterPayload_uniform_E2_sources mu base hbase
    fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
    globalCenter tangencyExponent payload D hshading hpointE2
  exact automaticRichRetainedMassBudget_of_E2Dominance D payload.finalLabel
    richness degreeUpper hgood hsources.1 hsources.2 hdominance

/-- Generic E2-dominance replacement for the opaque mass premise in the
actual centered-half G-prime sampler. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_E2Dominance
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (label : Int)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) (ballRadius : Real)
    (hradiusBall : (radius : Real) <= ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= 16) :
    exists N : CanonicalNormNonconcentrationData iota,
      N.family =
          actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      (forall i j, N.distance i j =
        projectedTubePairCoefficientDistance
          (D.fine.tubes i) (D.fine.tubes j)) ∧
      ∃ bucket ∈ Finset.range (coarseDegreeBucketLoss D),
        0 < comparableBase bucket ∧
        D.goodPairs.card <= coarseDegreeBucketLoss D *
          (D.retainedGoodPairs
            (coarseDegreeBucketKeep D bucket)).card ∧
        (coarseDegreeBucketLoss D *
            ((automaticCanonicalRichness N ballRadius + 1) *
              (2 * comparableBase bucket)) <= pyzE2DegreeLower label ->
          exists keep : iota -> fineLabel -> Prop,
            exists left right : iota,
              exists rectangles : Finset C2GraphRectangle,
                exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
                  ActualConcreteGPrimeCommonCoarseSampledOutcome fine physical
                    globalScale globalCenter N D ballRadius bucket keep left
                      right rectangles omega) := by
  obtain ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection,
      hsampleIf⟩ :=
    exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_budget
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT D hD hgood hradius hradiusSixteen hexponent
      ballRadius hradiusBall hnearRadiusUpper
  refine ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection, ?_⟩
  intro hdominance
  apply hsampleIf
  exact automaticRichRetainedMassBudget_of_E2Dominance D label
    (automaticCanonicalRichness N ballRadius) (2 * comparableBase bucket)
    hgood hcell hactive hdominance

/-- Positive-center specialization of the preceding endpoint.  Uniform E2
membership and active-fibre nonemptiness are extracted from the payload, so
the implication exposes only the genuine numerical dominance condition. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_positiveCenterE2Dominance
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (sourceBase : Set (Real × Real))
    (hsourceBase : MeasurableSet sourceBase)
    (mu : Measure (Real × Real))
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu sourceBase hsourceBase
      fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter tangencyExponent)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hshading : D.shading = positiveCenterY1 sourceBase hsourceBase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent payload.tangencyLabel)
    (hpointE2 : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ positiveCenterE2 sourceBase hsourceBase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent payload.tangencyLabel payload.finalLabel)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) (ballRadius : Real)
    (hradiusBall : (radius : Real) <= ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= 16) :
    exists N : CanonicalNormNonconcentrationData iota,
      N.family =
          actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      (forall i j, N.distance i j =
        projectedTubePairCoefficientDistance
          (D.fine.tubes i) (D.fine.tubes j)) ∧
      ∃ bucket ∈ Finset.range (coarseDegreeBucketLoss D),
        0 < comparableBase bucket ∧
        D.goodPairs.card <= coarseDegreeBucketLoss D *
          (D.retainedGoodPairs
            (coarseDegreeBucketKeep D bucket)).card ∧
        (coarseDegreeBucketLoss D *
            ((automaticCanonicalRichness N ballRadius + 1) *
              (2 * comparableBase bucket)) <=
              pyzE2DegreeLower payload.finalLabel ->
          exists keep : iota -> fineLabel -> Prop,
            exists left right : iota,
              exists rectangles : Finset C2GraphRectangle,
                exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
                  ActualConcreteGPrimeCommonCoarseSampledOutcome fine physical
                    globalScale globalCenter N D ballRadius bucket keep left
                      right rectangles omega) := by
  have hsources := positiveCenterPayload_uniform_E2_sources mu sourceBase
    hsourceBase fine physical f f1 f2 outerA outerB hOuter hf hf1
    globalScale globalCenter tangencyExponent payload D hshading hpointE2
  exact
    exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_E2Dominance
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT D hD hgood payload.finalLabel hsources.1 hsources.2
      hradius hradiusSixteen hexponent ballRadius hradiusBall
      hnearRadiusUpper

#print axioms fineLabels_nonempty_of_goodPairs_nonempty
#print axioms automaticRichRetainedMassBudget_of_E2Dominance
#print axioms highThreshold_does_not_imply_E2MassDominance
#print axioms positiveCenterPayload_uniform_E2_sources
#print axioms automaticRichRetainedMassBudget_of_positiveCenterPayloadDominance
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_E2Dominance
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_positiveCenterE2Dominance

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeE2MassConnectorV1
