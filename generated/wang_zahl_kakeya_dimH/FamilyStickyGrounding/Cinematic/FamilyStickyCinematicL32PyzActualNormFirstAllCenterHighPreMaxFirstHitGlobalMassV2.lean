import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitGlobalMassV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# Global mass of the labels used by the pre-max pair sum

The pair-incidence budget counts a fine label with its genuine separated-pair
multiplicity.  Before that multiplicity is inserted, however, the first-hit
pieces themselves are charged exactly once.  This module records the global
mass statement for the very same labels and weights.

Thus any remaining loss cannot be blamed on overlap of the first-hit
partition: it lies precisely in the pair-incidence multiplier.
-/

/-- Total first-hit label mass at one actual high centre, before multiplying
by any pair incidence. -/
noncomputable def nativeHighPreMaxFirstHitLabelMass
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
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  ∑ r ∈ R.fineLabels,
    actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r

/-- The local label mass is exactly the actual E2 cell mass. -/
theorem nativeHighPreMaxFirstHitLabelMass_eq_paperFineE2
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    let H := D.chosenHighPayloadAt c
    let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
    nativeHighPreMaxFirstHitLabelMass D G c =
      volume (actualCenteredHalfPaperFineE2 E_t hEt D.S.family D.physical
        H.payload.finalLabel D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
            D.tangencyExponent globalDelta) := by
  dsimp only
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  have hmass := Q.firstHit_mass_eq
  simpa only [H, E_t, hEt, globalDelta, nativeHighPreMaxFirstHitLabelMass, R,
    actualCenteredHalfPaperFineE2SpatialIncidenceData,
    actualCenteredHalfProjectedE2SpatialIncidenceData,
    y1FineCoarseRectangleData, actualCenteredHalfPaperFineY1,
    actualCenteredHalfPaperFineE2] using hmass

/-- The entire local first-hit partition stays inside its high base cell. -/
theorem nativeHighPreMaxFirstHitLabelMass_le_highBase
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    nativeHighPreMaxFirstHitLabelMass D G c <=
      volume (D.highBase c) := by
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, hEtSubset, _htangencyBin,
      _hE2Pos, _hE2Measurable, hE2Subset, _hactive⟩ :=
    H.payload.certificate
  rw [nativeHighPreMaxFirstHitLabelMass_eq_paperFineE2 D G c h]
  apply measure_mono
  simpa only [actualCenteredHalfPaperFineE2,
    actualCenteredHalfPaperFineY1, positiveCenterE2,
    positiveCenterY1, positiveCenterTangencyCell, E_t, hEt,
    globalDelta] using hE2Subset.trans hEtSubset

/-- Global first-hit label mass.  This is the unweighted companion of the
pre-max pair-incidence budget. -/
noncomputable def nativeHighPreMaxFirstHitLabelMassBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} (G : NativeHighGeometry D) : ENNReal :=
  ∑ c : D.HighCenter, nativeHighPreMaxFirstHitLabelMass D G c

/-- Across all high centres, the same full first-hit label family has total
mass at most the source mass.  Hence labels are already charged once; only
their genuine pair-incidence multiplicity remains open. -/
theorem NativeHighConcreteQPOutcome.preMaxFirstHitLabelMassBudget_le_sourceMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) :
    nativeHighPreMaxFirstHitLabelMassBudget G <= D.sourceMass := by
  let hlocal := nativeHighConcreteQPLocalAt hout
  calc
    nativeHighPreMaxFirstHitLabelMassBudget G <=
        ∑ c : D.HighCenter, volume (D.highBase c) := by
      exact Finset.sum_le_sum fun c _hc =>
        nativeHighPreMaxFirstHitLabelMass_le_highBase
          D G c (hlocal c)
    _ = ∑ c ∈ D.high, volume (D.cell c.1) := by
      simpa only [NativeBranchCore.highBase, NativeBranchCore.positiveBase,
        Finset.univ_eq_attach] using
          Finset.sum_attach D.high (fun c => volume (D.cell c.1))
    _ <= ∑ c : D.PositiveCenter, volume (D.cell c.1) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ D.high) (fun _ _ _ => bot_le)
    _ = ∑ center ∈ actualAllCenterPositiveCenters volume D.centers D.cell,
        volume (D.cell center) := by
      simpa only [Finset.univ_eq_attach] using
        Finset.sum_attach
          (actualAllCenterPositiveCenters volume D.centers D.cell)
          (fun center => volume (D.cell center))
    _ <= ∑ center ∈ D.centers, volume (D.cell center) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => bot_le)
    _ = D.sourceMass := D.hsourceMass.symm

#print axioms nativeHighPreMaxFirstHitLabelMass
#print axioms nativeHighPreMaxFirstHitLabelMass_eq_paperFineE2
#print axioms nativeHighPreMaxFirstHitLabelMass_le_highBase
#print axioms nativeHighPreMaxFirstHitLabelMassBudget
#print axioms NativeHighConcreteQPOutcome.preMaxFirstHitLabelMassBudget_le_sourceMass

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitGlobalMassV2
