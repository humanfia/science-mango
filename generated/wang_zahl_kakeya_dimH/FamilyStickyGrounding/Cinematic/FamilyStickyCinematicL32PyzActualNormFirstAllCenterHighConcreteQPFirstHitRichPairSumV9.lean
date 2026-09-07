import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitMassBudgetV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWideSourceFirstHitGeometryV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPThreeBallPackingV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitMassBudgetV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# The rich-pair sum before discarding the actual first-hit mass

The existing cardinal-envelope route replaces each concrete selected
first-hit mass by a uniform wide-area cap before summing over high centres.
This module stops before that replacement.  It retains the same named
`Q/P` witnesses, their literal rich-pair cardinality, and their actual
selected first-hit mass.

The resulting cross-centre sum is honest but is not yet a packing theorem:
the remaining mathematical input is an upper bound for the rich-pair
cardinality weighted by the same first-hit mass.
-/

/-- The exact local degree-gap factor used by the high branch. -/
noncomputable def nativeHighConcreteDegreeGap
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : ENNReal :=
  ((pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel *
      (pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
        automaticCanonicalNearCap
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)) (G.ballRadius c)) : Nat) : ENNReal)

/-- The local pre-cap right-hand side: bin loss, the literal rich-pair
cardinality, and the selected first-hit mass from the same concrete package. -/
noncomputable def nativeHighConcreteFirstHitRichPairRHS
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) : ENNReal :=
  actualAllCenterPostNormBinLoss radius D.globalScale D.physical.ambient.card *
    (72 * (nativeHighConcreteRichPairCard D G c : ENNReal) *
      nativeHighConcreteSelectedFirstHitMass D G c h)

/-- The fully actual local high-base inequality before the selected first-hit
weight is bounded by a wide-area cap. -/
theorem highBase_mul_degreeGap_le_firstHitRichPairRHS
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    volume (D.highBase c) * nativeHighConcreteDegreeGap D G c <=
      nativeHighConcreteFirstHitRichPairRHS D G c h := by
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  let P := positiveCenterHighPayload_baseConcreteP
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  have hselected :=
    P.source_mul_gap_le_seventyTwo_pairCount_mul_selectedWeight
      D.S.family N R (fun _ _ => True) (G.ballRadius c)
        (pyzE2DegreeLower H.payload.finalLabel)
        (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel) Q.sampled
  have hselected' :
      volume (projectedPositiveMultiplicityDyadicCell R.shading
          H.payload.finalLabel) *
          nativeHighConcreteDegreeGap D G c <=
        72 * (nativeHighConcreteRichPairCard D G c : ENNReal) *
          nativeHighConcreteSelectedFirstHitMass D G c h := by
    rw [← Q.firstHit_mass_eq]
    change
      (∑ r ∈ R.fineLabels,
          actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r) *
          ((pyzE2DegreeLower H.payload.finalLabel *
            (pyzE2DegreeLower H.payload.finalLabel -
              automaticCanonicalNearCap N (G.ballRadius c)) : Nat) :
                ENNReal) <=
        72 *
          ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N (G.ballRadius c))
            (fun _ _ => True)).card : ENNReal) *
          finiteENNRealWeight P.selected
            (actualGPrimeLabelFirstSurvivorWeightAt N R (fun _ _ => True)
              Q.sampled.pair.left Q.sampled.pair.right (G.ballRadius c)
                Q.sampled.omega
                  (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel))
    simp only [finiteENNRealWeight,
      actualGPrimeLabelFirstSurvivorWeightAt]
    convert hselected using 1 ; rfl
  have hsource :
      volume (actualCenteredHalfPaperFineE2 E_t hEt D.S.family D.physical
          H.payload.finalLabel D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
            D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
              D.tangencyExponent globalDelta) *
          nativeHighConcreteDegreeGap D G c <=
        72 * (nativeHighConcreteRichPairCard D G c : ENNReal) *
          nativeHighConcreteSelectedFirstHitMass D G c h := by
    simpa only [R, actualCenteredHalfPaperFineE2SpatialIncidenceData,
      actualCenteredHalfProjectedE2SpatialIncidenceData,
      y1FineCoarseRectangleData, actualCenteredHalfPaperFineY1,
      actualCenteredHalfPaperFineE2] using hselected'
  unfold nativeHighConcreteFirstHitRichPairRHS
  exact positiveCenterHighPayload_base_mul_degree_le_binLoss_mul_of_E2_mul_le
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H
          (nativeHighConcreteDegreeGap D G c)
          (72 * (nativeHighConcreteRichPairCard D G c : ENNReal) *
            nativeHighConcreteSelectedFirstHitMass D G c h) hsource

/-- The exact rich-pair cardinality weighted by the selected first-hit mass
over the local witnesses retained by an outcome. -/
noncomputable def nativeHighConcreteWeightedFirstHitRichPairBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) : ENNReal :=
  ∑ c : D.HighCenter,
    (nativeHighConcreteRichPairCard D G c : ENNReal) *
      nativeHighConcreteSelectedFirstHitMass D G c
        (nativeHighConcreteQPLocalAt hout c)

/-- If the high cells carry half the source mass, the same local witnesses
kept by `hout` satisfy the pre-cap rich-pair/first-hit sum inequality. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_sum_firstHitRichPairRHS
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 2 <=
      ∑ c : D.HighCenter,
        nativeHighConcreteFirstHitRichPairRHS D G c
          (nativeHighConcreteQPLocalAt hout c) := by
  classical
  have hbaseSum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [NativeBranchCore.highBase,
      NativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  have hhalf' : D.sourceMass / 2 <=
      ∑ c : D.HighCenter, volume (D.highBase c) :=
    hhalf.trans_eq hbaseSum.symm
  have hhalfUniv : D.sourceMass / 2 <=
      ∑ c ∈ (Finset.univ : Finset D.HighCenter),
        volume (D.highBase c) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using hhalf'
  have hsum := half_sourceMass_le_sum_rhs_of_degreeGap
    (high := (Finset.univ : Finset D.HighCenter))
    (weight := fun c => volume (D.highBase c))
    (rhs := fun c => nativeHighConcreteFirstHitRichPairRHS D G c
      (nativeHighConcreteQPLocalAt hout c))
    (degreeGap := fun c =>
      pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel *
        (pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
          automaticCanonicalNearCap
            (positiveCenterHighPayloadGlobalNormData
              (D.chosenHighPayloadAt c)) (G.ballRadius c)))
    D.sourceMass hhalfUniv
    (by
      intro c _hc
      have hc := G.hroom c
      have hd : 1 <=
          pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel := by
        omega
      have hdiff : 1 <=
          pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
            automaticCanonicalNearCap
              (positiveCenterHighPayloadGlobalNormData
                (D.chosenHighPayloadAt c)) (G.ballRadius c) := by
        omega
      calc
        1 = 1 * 1 := by norm_num
        _ <= pyzE2DegreeLower
              (D.chosenHighPayloadAt c).payload.finalLabel *
            (pyzE2DegreeLower
                (D.chosenHighPayloadAt c).payload.finalLabel -
              automaticCanonicalNearCap
                (positiveCenterHighPayloadGlobalNormData
                  (D.chosenHighPayloadAt c)) (G.ballRadius c)) :=
          Nat.mul_le_mul hd hdiff)
    (by
      intro c _hc
      simpa only [nativeHighConcreteDegreeGap] using
        highBase_mul_degreeGap_le_firstHitRichPairRHS D G c
          (nativeHighConcreteQPLocalAt hout c))
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using hsum

/-- Factored form of the preceding honest endpoint.  Its only unresolved
quantity is the actual rich-pair count weighted by the same selected
first-hit mass. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_binLoss_mul_weightedFirstHitRichPairBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 2 <=
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (72 * nativeHighConcreteWeightedFirstHitRichPairBudget hout) := by
  calc
    D.sourceMass / 2 <=
        ∑ c : D.HighCenter,
          nativeHighConcreteFirstHitRichPairRHS D G c
            (nativeHighConcreteQPLocalAt hout c) :=
      NativeHighConcreteQPOutcome.sourceMass_half_le_sum_firstHitRichPairRHS
        hout hhalf
    _ = actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (72 * nativeHighConcreteWeightedFirstHitRichPairBudget hout) := by
      unfold nativeHighConcreteFirstHitRichPairRHS
        nativeHighConcreteWeightedFirstHitRichPairBudget
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      ac_rfl

#print axioms nativeHighConcreteDegreeGap
#print axioms nativeHighConcreteFirstHitRichPairRHS
#print axioms highBase_mul_degreeGap_le_firstHitRichPairRHS
#print axioms nativeHighConcreteWeightedFirstHitRichPairBudget
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_sum_firstHitRichPairRHS
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_binLoss_mul_weightedFirstHitRichPairBudget

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
