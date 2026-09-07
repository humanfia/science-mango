import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstHighGlobalGridShiftSynchronizationV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeCanonicalSharingCapV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval

namespace FamilyStickyCinematicL32PyzActualNormFirstHighCanonicalSharingCapV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstHighOwnerFubiniV5
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeCanonicalSharingCapV3
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstHighGlobalGridShiftSynchronizationV2

noncomputable section

universe u

/-!
# Native high mass charged to actual separated pairs

The native high synchronization theorem retains one global grid and trace
shift at loss `648`.  The canonical sharing theorem then removes the chosen
packages: every repeated endpoint pair is charged through the two literal
radius-`R` metric balls and hence through the square of the canonical
nonconcentration cap.  No owner-degree or ambient-cardinality callback occurs
in the endpoint below.
-/

/-- At one native high center, the pre-max first-hit pair mass is bounded by
the genuine weighted fine endpoint-pair mass at the survivor separation
radius `4R/5`, with only the explicit synchronization loss and the squared
canonical radius-`R` ball cap. -/
theorem nativeHighPreMaxFirstHitCenterPairMass_le_canonicalCap_sq_mul_pairMass
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
    let N := positiveCenterHighPayloadGlobalNormData H
    let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
      D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
        D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
          (36 * D.globalScale) D.tangencyExponent
    nativeHighPreMaxFirstHitCenterPairMass D G c <=
      648 *
        (((automaticCanonicalCenterSharingNatCap N (G.ballRadius c) *
          automaticCanonicalCenterSharingNatCap N (G.ballRadius c) : Nat) :
            ENNReal) *
          actualGPrimeWeightedFineSeparatedPairMass N R (fun _ _ => True)
            (actualGPrimeSurvivorSeparationRadius (G.ballRadius c))
              (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)) := by
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
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  obtain ⟨packageAt, selectedPairs, _gridLabel, _shiftLabel, _hsubset,
      _hsynchronized, hmass, _hnonempty⟩ :=
    exists_nativeHighCenter_synchronizedGridShift_pairMass D G c h
  have hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance (R.fine.tubes i) (R.fine.tubes j) := by
    intro i j
    rfl
  have hsymm : forall x y, N.distance x y = N.distance y x := by
    intro x y
    rw [hdistance x y, hdistance y x]
    exact projectedTubePairCoefficientDistance_comm _ _
  have hcap :=
    finiteENNRealWeight_packageSelected_le_cap_sq_mul_weightedPairMass
      D.S.family N R (fun _ _ => True) (G.ballRadius c)
        (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
          D.f D.outerA D.outerB globalDelta D.globalScale packageAt
            selectedPairs hdistance hsymm (G.hballRadiusLower c)
              (G.hballRadiusUpper c)
  calc
    nativeHighPreMaxFirstHitCenterPairMass D G c <=
        648 * finiteENNRealWeight selectedPairs (fun pair =>
          actualGPrimePairPackageSelectedWeight D.S.family N R
            (fun _ _ => True) pair.1 (G.ballRadius c)
              (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
                D.f D.outerA D.outerB globalDelta D.globalScale
                  (packageAt pair)) := hmass
    _ <= 648 *
        (((automaticCanonicalCenterSharingNatCap N (G.ballRadius c) *
          automaticCanonicalCenterSharingNatCap N (G.ballRadius c) : Nat) :
            ENNReal) *
          actualGPrimeWeightedFineSeparatedPairMass N R (fun _ _ => True)
            (actualGPrimeSurvivorSeparationRadius (G.ballRadius c))
              (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)) := by
      gcongr

#print axioms nativeHighPreMaxFirstHitCenterPairMass_le_canonicalCap_sq_mul_pairMass

end

end FamilyStickyCinematicL32PyzActualNormFirstHighCanonicalSharingCapV2
