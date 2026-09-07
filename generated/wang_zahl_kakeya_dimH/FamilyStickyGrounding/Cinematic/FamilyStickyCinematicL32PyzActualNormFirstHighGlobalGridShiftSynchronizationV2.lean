import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstHighOwnerFubiniV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval

namespace FamilyStickyCinematicL32PyzActualNormFirstHighGlobalGridShiftSynchronizationV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstHighOwnerFubiniV5

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# The native high branch with one global grid and trace shift

The previous owner-Fubini endpoint constructs a genuine weighted uniform
package for every rich pair with nonempty common-label fibre. Here those
actual packages are retained and synchronized by the two finite three-shift
pigeonholes from the generic synchronization theorem. In particular, no
pairwise scalar owner envelope is used in the conclusion.

The remaining statement is deliberately a sum over synchronized actual
packages. Bounding repeated fine labels/owners across different pairs is a
separate geometric degree problem and is not asserted here.
-/

/-- At one native high centre, actual pair packages may be selected with a
single C-grid label and a single trace-shift label, at total loss 648. -/
theorem exists_nativeHighCenter_synchronizedGridShift_pairMass
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
    let activePairs := actualGPrimeCommonActivePairs
      N R (fun _ _ => True) (G.ballRadius c)
    exists packageAt : forall pair : {p // p ∈ activePairs},
        ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
          D.S.family N R (fun _ _ => True) pair.1 (G.ballRadius c)
            (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
              D.f D.outerA D.outerB globalDelta D.globalScale,
      exists selectedPairs : Finset {p // p ∈ activePairs},
        exists gridLabel shiftLabel : Fin 3,
          selectedPairs ⊆ Finset.univ ∧
          (forall pair, pair ∈ selectedPairs ->
            (packageAt pair).package.gridLabel = gridLabel ∧
            (packageAt pair).package.shiftLabel = shiftLabel) ∧
          nativeHighPreMaxFirstHitCenterPairMass D G c <=
            648 * finiteENNRealWeight selectedPairs (fun pair =>
              actualGPrimePairPackageSelectedWeight D.S.family N R
                (fun _ _ => True) pair.1 (G.ballRadius c)
                  (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
                    D.f D.outerA D.outerB globalDelta D.globalScale
                      (packageAt pair)) ∧
          (activePairs.Nonempty -> selectedPairs.Nonempty) := by
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
  obtain ⟨_ownerEnvelopeAt, _hpre, _howner, hrealized, _hzero, _htotal⟩ :=
    exists_nativeHighCenter_actualOwnerEnvelopeSum D G c h
  have hpackage : forall pair,
      pair ∈ richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N (G.ballRadius c)) (fun _ _ => True) ->
      (actualGPrimeCommonFineCenterLabels
        N R (fun _ _ => True) pair.1 pair.2).Nonempty ->
      Nonempty (ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        D.S.family N R (fun _ _ => True) pair (G.ballRadius c)
          (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
            D.f D.outerA D.outerB globalDelta D.globalScale) := by
    intro pair hp hcommon
    obtain ⟨_r, _hr, O, _hO⟩ := hrealized pair hp hcommon
    exact ⟨O⟩
  have hsync := exists_actualGPrime_synchronizedGridShift_pairMass
    D.S.family N R (fun _ _ => True) (G.ballRadius c)
      (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
        D.f D.outerA D.outerB globalDelta D.globalScale
          (G.hballRadiusLower c) hpackage
  simpa only [nativeHighPreMaxFirstHitCenterPairMass, H, E_t, hEt,
    globalDelta, N, R] using hsync

#print axioms exists_nativeHighCenter_synchronizedGridShift_pairMass

end

end FamilyStickyCinematicL32PyzActualNormFirstHighGlobalGridShiftSynchronizationV2
