import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitGlobalMassV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighFineLabelNormalizedMassV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitGlobalMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# Degree-gap-normalized native-high first-hit mass

The earlier finite aggregation takes a maximum only after replacing the
literal first-hit label weight by the crude product of a sharing cap and a
dyadic degree square.  Here the degree gap is divided out before summing.
The remaining coefficient is the exact, dimensionless multiplicity

`#(separated endpoint pairs carrying r) /
  (degreeLower * (degreeLower - nearCap))`.

Thus neither an ambient-cardinality bound nor a conclusion-valued callback is
inserted at this interface.
-/

/-- The exact worst normalized fine-label pair multiplicity at one native
high centre. -/
noncomputable def nativeHighFineLabelNormalizedMultiplicityLoss
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : ENNReal :=
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
  R.fineLabels.sup fun r =>
    ((actualGPrimeFineSeparatedPairsAt N R (fun _ _ => True)
      (G.ballRadius c) r).card : ENNReal) /
        nativeHighConcreteDegreeGap D G c

/-- The single exact normalized multiplicity loss over all native high
centres. -/
noncomputable def nativeHighFineLabelNormalizedMultiplicityLossMax
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) : ENNReal :=
  Finset.univ.sup (nativeHighFineLabelNormalizedMultiplicityLoss D G)

/-- The full pre-max first-hit pair mass after dividing by its own genuine
degree gap, before any maximum or cardinal envelope. -/
noncomputable def nativeHighDegreeGapNormalizedPairMassBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} (G : NativeHighGeometry D) : ENNReal :=
  ∑ c : D.HighCenter,
    nativeHighPreMaxFirstHitCenterPairMass D G c /
      nativeHighConcreteDegreeGap D G c

theorem nativeHighConcreteDegreeGap_ne_zero
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : nativeHighConcreteDegreeGap D G c ≠ 0 := by
  have hroom := G.hroom c
  have hpos : 0 <
      pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel *
        (pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
          automaticCanonicalNearCap
            (positiveCenterHighPayloadGlobalNormData
              (D.chosenHighPayloadAt c)) (G.ballRadius c)) := by
    exact Nat.mul_pos (Nat.zero_lt_of_lt hroom) (Nat.sub_pos_of_lt hroom)
  unfold nativeHighConcreteDegreeGap
  exact_mod_cast hpos.ne'

theorem nativeHighConcreteDegreeGap_ne_top
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : nativeHighConcreteDegreeGap D G c ≠ ∞ := by
  unfold nativeHighConcreteDegreeGap
  exact ENNReal.natCast_ne_top _

/-- At one centre, dividing the exact label-first pair mass by the degree gap
costs only the exact maximum normalized label multiplicity. -/
theorem normalizedCenterPairMass_le_localLoss_mul_labelMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    nativeHighPreMaxFirstHitCenterPairMass D G c /
        nativeHighConcreteDegreeGap D G c <=
      nativeHighFineLabelNormalizedMultiplicityLoss D G c *
        nativeHighPreMaxFirstHitLabelMass D G c := by
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
  rw [nativeHighPreMaxFirstHitCenterPairMass_eq_labelFirst]
  unfold actualGPrimeWeightedFineSeparatedPairMass
  unfold nativeHighFineLabelNormalizedMultiplicityLoss
    nativeHighPreMaxFirstHitLabelMass
  dsimp only
  calc
    (∑ r ∈ R.fineLabels,
        actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r *
          ((actualGPrimeFineSeparatedPairsAt N R (fun _ _ => True)
            (G.ballRadius c) r).card : ENNReal)) /
          nativeHighConcreteDegreeGap D G c =
      ∑ r ∈ R.fineLabels,
        actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r *
          (((actualGPrimeFineSeparatedPairsAt N R (fun _ _ => True)
            (G.ballRadius c) r).card : ENNReal) /
              nativeHighConcreteDegreeGap D G c) := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
    _ <= ∑ r ∈ R.fineLabels,
        actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r *
          nativeHighFineLabelNormalizedMultiplicityLoss D G c := by
      apply Finset.sum_le_sum
      intro r hr
      gcongr
      exact Finset.le_sup (f := fun r =>
        ((actualGPrimeFineSeparatedPairsAt N R (fun _ _ => True)
          (G.ballRadius c) r).card : ENNReal) /
            nativeHighConcreteDegreeGap D G c) hr
    _ = nativeHighFineLabelNormalizedMultiplicityLoss D G c *
        ∑ r ∈ R.fineLabels,
          actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- The genuine local degree-gap inequality can be divided before summing;
no dyadic-degree or sharing-cap envelope is paid here. -/
theorem highBase_le_binLoss_mul_normalizedCenterPairMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    volume (D.highBase c) <=
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (nativeHighPreMaxFirstHitCenterPairMass D G c /
          nativeHighConcreteDegreeGap D G c) := by
  rw [← mul_div_assoc]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (nativeHighConcreteDegreeGap_ne_zero D G c))
    (Or.inl (nativeHighConcreteDegreeGap_ne_top D G c))).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    highBase_mul_degreeGap_le_binLoss_mul_preMaxFirstHitCenterPairMass
      D G c h

/-- Exact finite aggregation after degree-gap normalization.  The high-half
premise is the actual branch alternative, not a conclusion-valued callback. -/
theorem sourceMass_half_le_binLoss_mul_normalizedPairMassBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 2 <=
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighDegreeGapNormalizedPairMassBudget G := by
  classical
  let hout := nativeHighConcreteQPOutcome_of_half D G hhalf
  have hbaseSum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [NativeBranchCore.highBase,
      NativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  calc
    D.sourceMass / 2 <= ∑ c : D.HighCenter, volume (D.highBase c) :=
      hhalf.trans_eq hbaseSum.symm
    _ <= ∑ c : D.HighCenter,
        actualAllCenterPostNormBinLoss radius D.globalScale
            D.physical.ambient.card *
          (nativeHighPreMaxFirstHitCenterPairMass D G c /
            nativeHighConcreteDegreeGap D G c) := by
      exact Finset.sum_le_sum fun c _hc =>
        highBase_le_binLoss_mul_normalizedCenterPairMass D G c
          (nativeHighConcreteQPLocalAt hout c)
    _ = actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighDegreeGapNormalizedPairMassBudget G := by
      rw [nativeHighDegreeGapNormalizedPairMassBudget, Finset.mul_sum]

/-- The normalized budget is controlled by the exact normalized fine-label
multiplicity maximum times the literal first-hit mass budget. -/
theorem normalizedPairMassBudget_le_maxLoss_mul_labelMassBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    nativeHighDegreeGapNormalizedPairMassBudget G <=
      nativeHighFineLabelNormalizedMultiplicityLossMax D G *
        nativeHighPreMaxFirstHitLabelMassBudget G := by
  classical
  unfold nativeHighDegreeGapNormalizedPairMassBudget
    nativeHighPreMaxFirstHitLabelMassBudget
  calc
    (∑ c : D.HighCenter,
        nativeHighPreMaxFirstHitCenterPairMass D G c /
          nativeHighConcreteDegreeGap D G c) <=
      ∑ c : D.HighCenter,
        nativeHighFineLabelNormalizedMultiplicityLoss D G c *
          nativeHighPreMaxFirstHitLabelMass D G c := by
        exact Finset.sum_le_sum fun c _hc =>
          normalizedCenterPairMass_le_localLoss_mul_labelMass D G c
    _ <= ∑ c : D.HighCenter,
        nativeHighFineLabelNormalizedMultiplicityLossMax D G *
          nativeHighPreMaxFirstHitLabelMass D G c := by
      apply Finset.sum_le_sum
      intro c hc
      gcongr
      exact Finset.le_sup
        (f := nativeHighFineLabelNormalizedMultiplicityLoss D G) hc
    _ = nativeHighFineLabelNormalizedMultiplicityLossMax D G *
        ∑ c : D.HighCenter,
          nativeHighPreMaxFirstHitLabelMass D G c := by
      rw [Finset.mul_sum]

/-- Callback-free native-high endpoint with all first-hit and degree-gap
cancellation performed.  Its sole unresolved scalar is the exact normalized
fine-label pair multiplicity, the paper packing quantity. -/
theorem sourceMass_half_le_binLoss_mul_normalizedMultiplicityMax_mul_sourceMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 2 <=
      (actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighFineLabelNormalizedMultiplicityLossMax D G) *
          D.sourceMass := by
  let hout := nativeHighConcreteQPOutcome_of_half D G hhalf
  calc
    D.sourceMass / 2 <=
        actualAllCenterPostNormBinLoss radius D.globalScale
            D.physical.ambient.card *
          nativeHighDegreeGapNormalizedPairMassBudget G :=
      sourceMass_half_le_binLoss_mul_normalizedPairMassBudget D G hhalf
    _ <= actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (nativeHighFineLabelNormalizedMultiplicityLossMax D G *
          nativeHighPreMaxFirstHitLabelMassBudget G) := by
      gcongr
      exact normalizedPairMassBudget_le_maxLoss_mul_labelMassBudget D G
    _ <= actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (nativeHighFineLabelNormalizedMultiplicityLossMax D G *
          D.sourceMass) := by
      gcongr
      exact NativeHighConcreteQPOutcome.preMaxFirstHitLabelMassBudget_le_sourceMass
        hout
    _ = (actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighFineLabelNormalizedMultiplicityLossMax D G) *
          D.sourceMass := by
      ac_rfl

#print axioms nativeHighFineLabelNormalizedMultiplicityLoss
#print axioms nativeHighFineLabelNormalizedMultiplicityLossMax
#print axioms nativeHighDegreeGapNormalizedPairMassBudget
#print axioms nativeHighConcreteDegreeGap_ne_zero
#print axioms normalizedCenterPairMass_le_localLoss_mul_labelMass
#print axioms highBase_le_binLoss_mul_normalizedCenterPairMass
#print axioms sourceMass_half_le_binLoss_mul_normalizedPairMassBudget
#print axioms normalizedPairMassBudget_le_maxLoss_mul_labelMassBudget
#print axioms
  sourceMass_half_le_binLoss_mul_normalizedMultiplicityMax_mul_sourceMass

end

end Family8Family7NativeHighFineLabelNormalizedMassV1
