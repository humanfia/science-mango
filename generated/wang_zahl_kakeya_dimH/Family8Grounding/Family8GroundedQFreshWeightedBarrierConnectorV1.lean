import Family8Grounding.Family8GroundedQFreshThresholdScaleTransportV1
import Family8Grounding.Family8GroundedWeightedEarlierBarrierTransportV1
import Family8Grounding.Family8SameSelectedQFibreGenericWeightedCrossingValueTransportV1
import Family8Grounding.Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
import Mathlib.Tactic

/-!
# Weighted q-fresh pointwise and grounded barrier connector

This connector specializes the generic finite-loss barrier algebra to the
literal q-fibre successor.  Its primary interface asks only that the
destination relative scale equal the source relative scale; a convenience
wrapper derives this equality from `QFreshCrossingActualScaleMatch`.  The only
remaining analytic data are then the two inequalities that the real V2
consumers require:

* at each earlier stage, the common-ratio destination threshold multiplied
  by the literal card/floor loss is below the source threshold;
* at the current source stage, that same weighted threshold is below the
  literal source crossing value.

The finite nonzero loss and the weighted crossing-value comparison are
produced internally.  No exact affine reindexing, concentration equality,
unit loss, callback, finished barrier, or stage-progress premise occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8GroundedQFreshWeightedBarrierConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Family8ContractedJohnActualTubeProxyV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8GroundedQFreshThresholdScaleTransportV1
open Family8GroundedWeightedEarlierBarrierTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SameSelectedQFibreCrossingValueTransportV1
open Family8SameSelectedQFibreGenericWeightedCrossingValueTransportV1
open Family8SameSelectedQFibreWeightedCrossingValueTransportV1
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {sourceDelta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {sourceDepth : Nat}
  {Dsource : ActualTubeDatum sourceDelta sourceIndex}
  {hDsource : Dsource.IsAdmissible}
  {Csource : CoherentStickyMultiscaleCover Dsource.family}
  {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
  {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
  {sourceEta : Nat -> Real} {N : Nat}
  {Wsource : FirstParentwiseNormalizedCrossingWitness
    Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
      sourceEta N}
  {step : SameObjectCrossingPaperStep Wsource}
  {destinationDepth : Nat}
  {hDdestination :
    step.integrated.dualChild.qFibreChildDatum.IsAdmissible}
  {Cdestination : CoherentStickyMultiscaleCover
    step.integrated.dualChild.qFibreChildDatum.family}
  {Sdestination : FiniteScaleSequence
    (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
      destinationDepth}
  {destinationEpsilon : Real}
  {hDestinationEpsilon : 0 <= destinationEpsilon}
  {destinationEta : Nat -> Real}
  {Wdestination : FirstParentwiseNormalizedCrossingWitness
    step.integrated.dualChild.qFibreChildDatum hDdestination
      Cdestination Sdestination destinationEpsilon
        hDestinationEpsilon destinationEta N}

/-- Rewrite one literal destination threshold on the common source relative
scale.  This consumes exactly the relative-scale equality used by the
downstream threshold, and no endpoint-scale or concentration equality. -/
theorem destinationThreshold_eq_sourceRelativeScale
    (Hrelative :
      Wdestination.rho / Sdestination.tau Wdestination.m =
        Wsource.rho / Ssource.tau Wsource.m)
    (stage : Nat) :
    actualCrossingThresholdAt Wdestination stage =
      (((Wsource.rho / Ssource.tau Wsource.m : NNReal) : ENNReal) ^
        destinationEta stage) := by
  unfold actualCrossingThresholdAt
  rw [Hrelative]

/-- The two weakest scalar absorption fields left after the actual q-fresh
scale match.

`earlier_commonRatio_scaled` is consumed only by
`EarlierBarrierTransport`; `current_commonRatio_scaled` is consumed only by
`GroundedPaperFactorTransitionCertificate.current_stage_barrier`. -/
structure QFreshWeightedScalarAbsorption : Prop where
  earlier_commonRatio_scaled : forall stage : Nat,
    stage < Wsource.stage ->
      sourceRawQFibreCardFloorLoss (Wsrc := Wsource) *
          (((Wsource.rho / Ssource.tau Wsource.m : NNReal) : ENNReal) ^
            destinationEta stage) <=
        actualCrossingThresholdAt Wsource stage
  current_commonRatio_scaled :
    sourceRawQFibreCardFloorLoss (Wsrc := Wsource) *
        (((Wsource.rho / Ssource.tau Wsource.m : NNReal) : ENNReal) ^
          destinationEta Wsource.stage) <=
      actualCrossingValue Wsource

namespace QFreshWeightedScalarAbsorption

/-- Produce the generic weighted pointwise seam.  The loss, its two
nondegeneracy facts, and the source-to-destination value inequality are all
theorems of the literal source step and destination crossing. -/
theorem toWeightedEarlierBarrierPointwiseSeam
    (Hrelative :
      Wdestination.rho / Sdestination.tau Wdestination.m =
        Wsource.rho / Ssource.tau Wsource.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := Wsource) (destinationEta := destinationEta)) :
    WeightedEarlierBarrierPointwiseSeam Wsource Wdestination
      (sourceRawQFibreCardFloorLoss (Wsrc := Wsource)) where
  loss_ne_zero :=
    sourceRawQFibreCardFloorLoss_ne_zero (Wsource := Wsource)
  loss_ne_top := sourceRawQFibreCardFloorLoss_ne_top (Wsrc := Wsource)
  threshold_scaled_le := by
    intro stage hstage
    rw [destinationThreshold_eq_sourceRelativeScale Hrelative stage]
    exact B.earlier_commonRatio_scaled stage hstage
  value_le_weighted :=
    crossingValue_le_cardFloorLoss_mul_anyDestination step Wdestination

/-- Produce the ordinary, unweighted earlier-barrier transport required by
the existing V2 run. -/
theorem earlierBarrierTransport
    (Hrelative :
      Wdestination.rho / Sdestination.tau Wdestination.m =
        Wsource.rho / Ssource.tau Wsource.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := Wsource) (destinationEta := destinationEta)) :
    EarlierBarrierTransport Wsource Wdestination :=
  earlierBarrierTransport_of_weightedPointwiseSeam
    (B.toWeightedEarlierBarrierPointwiseSeam Hrelative)

/-- Produce exactly the current-stage destination barrier field, with the
finite loss cancelled rather than erased. -/
theorem currentStageBarrier
    (Hrelative :
      Wdestination.rho / Sdestination.tau Wdestination.m =
        Wsource.rho / Ssource.tau Wsource.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := Wsource) (destinationEta := destinationEta)) :
    actualCrossingThresholdAt Wdestination Wsource.stage <=
      actualCrossingValue Wdestination := by
  apply currentStageBarrier_of_weightedSourceValueBound
    (B.toWeightedEarlierBarrierPointwiseSeam Hrelative)
  rw [destinationThreshold_eq_sourceRelativeScale
    Hrelative Wsource.stage]
  exact B.current_commonRatio_scaled

/-- Assemble the grounded edge.  Successor membership is definitionally the
same q-fibre atom already in `step.paperTransition.successor`. -/
theorem groundedCertificate
    (Hrelative :
      Wdestination.rho / Sdestination.tau Wdestination.m =
        Wsource.rho / Ssource.tau Wsource.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := Wsource) (destinationEta := destinationEta)) :
    GroundedPaperFactorTransitionCertificate
      Wsource step Wdestination := by
  apply groundedCertificate_of_weightedPointwiseSeam
    (B.toWeightedEarlierBarrierPointwiseSeam Hrelative)
  rw [destinationThreshold_eq_sourceRelativeScale
    Hrelative Wsource.stage]
  exact B.current_commonRatio_scaled

end QFreshWeightedScalarAbsorption

/-! ## Literal doubly-buffered specialization -/

/-- The same connector with the destination cover pinned definitionally to
the real doubly-buffered q-fresh cover.  `H` is not converted to a legacy
faithful successor and no cover equality is requested. -/
theorem doublyBufferedGroundedCertificate
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      Wsource step.integrated)
    {destinationDepth : Nat}
    {Sdestination : FiniteScaleSequence
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    (Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum
        step.integrated.dualChild.qFibreChild_admissible
        H.readiness.qFreshCover Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N)
    (Hrelative :
      Wdestination.rho / Sdestination.tau Wdestination.m =
        Wsource.rho / Ssource.tau Wsource.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := Wsource) (destinationEta := destinationEta)) :
    GroundedPaperFactorTransitionCertificate
      Wsource step Wdestination :=
  B.groundedCertificate Hrelative

/-- Convenience adapter for callers that already carry the stronger endpoint
scale certificate.  The primary connector above records only the relative
ratio equality that its proof consumes. -/
theorem doublyBufferedGroundedCertificate_of_actualScaleMatch
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      Wsource step.integrated)
    {destinationDepth : Nat}
    {Sdestination : FiniteScaleSequence
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    (Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum
        step.integrated.dualChild.qFibreChild_admissible
        H.readiness.qFreshCover Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N)
    (Hscale : QFreshCrossingActualScaleMatch
      Wsource step Wdestination)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := Wsource) (destinationEta := destinationEta)) :
    GroundedPaperFactorTransitionCertificate
      Wsource step Wdestination :=
  doublyBufferedGroundedCertificate H Wdestination
    Hscale.relativeScale_eq B

#print axioms destinationThreshold_eq_sourceRelativeScale
#print axioms QFreshWeightedScalarAbsorption
#print axioms
  QFreshWeightedScalarAbsorption.toWeightedEarlierBarrierPointwiseSeam
#print axioms QFreshWeightedScalarAbsorption.earlierBarrierTransport
#print axioms QFreshWeightedScalarAbsorption.currentStageBarrier
#print axioms QFreshWeightedScalarAbsorption.groundedCertificate
#print axioms doublyBufferedGroundedCertificate
#print axioms doublyBufferedGroundedCertificate_of_actualScaleMatch

end
end Family8GroundedQFreshWeightedBarrierConnectorV1
