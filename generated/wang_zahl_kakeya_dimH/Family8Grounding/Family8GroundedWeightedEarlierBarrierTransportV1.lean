import Family8Grounding.Family8GroundedEarlierBarrierTransportProducerV1
import Mathlib.Tactic

/-!
# Weighted producer for grounded earlier-barrier transport

This file replaces exact monotonicity of crossing values by the honest
one-sided estimate

`actualCrossingValue Wsource <= K * actualCrossingValue Wdestination`.

Such an estimate by itself does not give the unweighted destination barrier
needed by the strict-crossing API.  The matching threshold statement is
therefore scaled in the opposite direction:

`K * destinationThreshold <= sourceThreshold`.

After composing with the actual source barrier, the same finite nonzero
factor occurs on both sides and can be cancelled.  Consequently the result
is the existing, unmodified `EarlierBarrierTransport`; no weighted variant
of the stage-progress theorem is needed.

An equivalent constructor takes the explicit divided estimate

`destinationThreshold <= sourceThreshold / K`.

The current source stage remains analytically independent of the earlier
stages.  A final constructor accepts a weighted source-value bound at that
stage, rather than accepting the desired destination barrier itself.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8GroundedWeightedEarlierBarrierTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8GroundedEarlierBarrierTransportProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## Pure scalar cancellation -/

/-- Cancel a finite nonzero loss after composing a scaled threshold
comparison, a source barrier, and a weighted value comparison. -/
theorem destination_barrier_of_weighted_chain
    {K destinationThreshold sourceThreshold sourceValue destinationValue :
      ENNReal}
    (hKzero : K ≠ 0) (hKtop : K ≠ ∞)
    (threshold_scaled : K * destinationThreshold <= sourceThreshold)
    (source_barrier : sourceThreshold <= sourceValue)
    (value_weighted : sourceValue <= K * destinationValue) :
    destinationThreshold <= destinationValue := by
  apply
    (ENNReal.mul_le_mul_iff_right hKzero hKtop).mp
  exact threshold_scaled.trans (source_barrier.trans value_weighted)

/-- The same scalar connector with the threshold loss displayed as an
explicit division by `K`. -/
theorem destination_barrier_of_divided_threshold
    {K destinationThreshold sourceThreshold sourceValue destinationValue :
      ENNReal}
    (hKzero : K ≠ 0) (hKtop : K ≠ ∞)
    (threshold_divided : destinationThreshold <= sourceThreshold / K)
    (source_barrier : sourceThreshold <= sourceValue)
    (value_weighted : sourceValue <= K * destinationValue) :
    destinationThreshold <= destinationValue := by
  apply destination_barrier_of_weighted_chain hKzero hKtop
      (source_barrier := source_barrier) (value_weighted := value_weighted)
  have hmul : destinationThreshold * K <= sourceThreshold :=
    (ENNReal.le_div_iff_mul_le (Or.inl hKzero) (Or.inl hKtop)).mp
      threshold_divided
  simpa only [mul_comm] using hmul

/-! ## Weighted pointwise seam -/

/-- The exact scalar data needed to transport every actual earlier source
barrier through a multiplicative crossing-value loss.

The structure stores neither a universal source barrier nor the desired
destination barrier. -/
structure WeightedEarlierBarrierPointwiseSeam
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    (Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N)
    {destinationDelta : NNReal} {destinationIndex : Type}
    [Fintype destinationIndex] [DecidableEq destinationIndex]
    {destinationDepth : Nat}
    {Ddestination : ActualTubeDatum destinationDelta destinationIndex}
    {hDdestination : Ddestination.IsAdmissible}
    {Cdestination : CoherentStickyMultiscaleCover Ddestination.family}
    {Sdestination : FiniteScaleSequence destinationDelta destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    (Wdestination : FirstParentwiseNormalizedCrossingWitness
      Ddestination hDdestination Cdestination Sdestination
        destinationEpsilon hDestinationEpsilon destinationEta N)
    (K : ENNReal) : Prop where
  loss_ne_zero : K ≠ 0
  loss_ne_top : K ≠ ∞
  threshold_scaled_le : forall stage : Nat, stage < Wsource.stage ->
    K * actualCrossingThresholdAt Wdestination stage <=
      actualCrossingThresholdAt Wsource stage
  value_le_weighted : actualCrossingValue Wsource <=
    K * actualCrossingValue Wdestination

namespace WeightedEarlierBarrierPointwiseSeam

/-- Build the multiplicative form from the equivalent explicit divided
threshold estimates. -/
theorem of_divided_thresholds
    {sourceDelta : NNReal} {sourceIndex : Type}
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
    {destinationDelta : NNReal} {destinationIndex : Type}
    [Fintype destinationIndex] [DecidableEq destinationIndex]
    {destinationDepth : Nat}
    {Ddestination : ActualTubeDatum destinationDelta destinationIndex}
    {hDdestination : Ddestination.IsAdmissible}
    {Cdestination : CoherentStickyMultiscaleCover Ddestination.family}
    {Sdestination : FiniteScaleSequence destinationDelta destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      Ddestination hDdestination Cdestination Sdestination
        destinationEpsilon hDestinationEpsilon destinationEta N}
    {K : ENNReal} (hKzero : K ≠ 0) (hKtop : K ≠ ∞)
    (threshold_divided : forall stage : Nat, stage < Wsource.stage ->
      actualCrossingThresholdAt Wdestination stage <=
        actualCrossingThresholdAt Wsource stage / K)
    (value_weighted : actualCrossingValue Wsource <=
      K * actualCrossingValue Wdestination) :
    WeightedEarlierBarrierPointwiseSeam
      Wsource Wdestination K where
  loss_ne_zero := hKzero
  loss_ne_top := hKtop
  threshold_scaled_le := by
    intro stage hstage
    have hmul : actualCrossingThresholdAt Wdestination stage * K <=
        actualCrossingThresholdAt Wsource stage :=
      (ENNReal.le_div_iff_mul_le (Or.inl hKzero) (Or.inl hKtop)).mp
        (threshold_divided stage hstage)
    simpa only [mul_comm] using hmul
  value_le_weighted := value_weighted

end WeightedEarlierBarrierPointwiseSeam

/-! ## Existing V2 transport, unchanged -/

/-- Produce the existing unweighted V2 earlier-barrier transport.  The
universal `sourceBarrier` is the literal proof supplied by the V2 API and is
specialized to the source witness's selected scale and parent. -/
theorem earlierBarrierTransport_of_weightedPointwiseSeam
    {sourceDelta : NNReal} {sourceIndex : Type}
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
    {destinationDelta : NNReal} {destinationIndex : Type}
    [Fintype destinationIndex] [DecidableEq destinationIndex]
    {destinationDepth : Nat}
    {Ddestination : ActualTubeDatum destinationDelta destinationIndex}
    {hDdestination : Ddestination.IsAdmissible}
    {Cdestination : CoherentStickyMultiscaleCover Ddestination.family}
    {Sdestination : FiniteScaleSequence destinationDelta destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      Ddestination hDdestination Cdestination Sdestination
        destinationEpsilon hDestinationEpsilon destinationEta N}
    {K : ENNReal}
    (H : WeightedEarlierBarrierPointwiseSeam
      Wsource Wdestination K) :
    EarlierBarrierTransport Wsource Wdestination where
  transport := by
    intro stage hstage sourceBarrier
    have hsource : actualCrossingThresholdAt Wsource stage <=
        actualCrossingValue Wsource :=
      sourceBarrier Wsource.m Wsource.notLarge Wsource.rho
        Wsource.buffered Wsource.q
    exact destination_barrier_of_weighted_chain
      H.loss_ne_zero H.loss_ne_top (H.threshold_scaled_le stage hstage)
        hsource H.value_le_weighted

/-- Direct explicit-division constructor for the existing V2 transport. -/
theorem earlierBarrierTransport_of_dividedThresholds
    {sourceDelta : NNReal} {sourceIndex : Type}
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
    {destinationDelta : NNReal} {destinationIndex : Type}
    [Fintype destinationIndex] [DecidableEq destinationIndex]
    {destinationDepth : Nat}
    {Ddestination : ActualTubeDatum destinationDelta destinationIndex}
    {hDdestination : Ddestination.IsAdmissible}
    {Cdestination : CoherentStickyMultiscaleCover Ddestination.family}
    {Sdestination : FiniteScaleSequence destinationDelta destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      Ddestination hDdestination Cdestination Sdestination
        destinationEpsilon hDestinationEpsilon destinationEta N}
    {K : ENNReal} (hKzero : K ≠ 0) (hKtop : K ≠ ∞)
    (threshold_divided : forall stage : Nat, stage < Wsource.stage ->
      actualCrossingThresholdAt Wdestination stage <=
        actualCrossingThresholdAt Wsource stage / K)
    (value_weighted : actualCrossingValue Wsource <=
      K * actualCrossingValue Wdestination) :
    EarlierBarrierTransport Wsource Wdestination :=
  earlierBarrierTransport_of_weightedPointwiseSeam
    (WeightedEarlierBarrierPointwiseSeam.of_divided_thresholds
      hKzero hKtop threshold_divided value_weighted)

/-! ## Independent current-stage scalar connector -/

/-- A weighted bound by the literal source crossing value implies the
ordinary current-stage destination barrier.  This consumes no already
finished destination barrier. -/
theorem currentStageBarrier_of_weightedSourceValueBound
    {sourceDelta : NNReal} {sourceIndex : Type}
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
    {destinationDelta : NNReal} {destinationIndex : Type}
    [Fintype destinationIndex] [DecidableEq destinationIndex]
    {destinationDepth : Nat}
    {Ddestination : ActualTubeDatum destinationDelta destinationIndex}
    {hDdestination : Ddestination.IsAdmissible}
    {Cdestination : CoherentStickyMultiscaleCover Ddestination.family}
    {Sdestination : FiniteScaleSequence destinationDelta destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      Ddestination hDdestination Cdestination Sdestination
        destinationEpsilon hDestinationEpsilon destinationEta N}
    {K : ENNReal}
    (H : WeightedEarlierBarrierPointwiseSeam
      Wsource Wdestination K)
    (current_scaled :
      K * actualCrossingThresholdAt Wdestination Wsource.stage <=
        actualCrossingValue Wsource) :
    actualCrossingThresholdAt Wdestination Wsource.stage <=
      actualCrossingValue Wdestination := by
  exact destination_barrier_of_weighted_chain
    H.loss_ne_zero H.loss_ne_top current_scaled le_rfl
      H.value_le_weighted

/-! ## Same-selected q-fresh grounded edge -/

/-- Assemble the full grounded q-fresh edge from the weighted pointwise
seam and an independent weighted current-stage source-value bound.

In particular, the desired unweighted current-stage destination barrier is
derived here rather than supplied as an input. -/
theorem groundedCertificate_of_weightedPointwiseSeam
    {sourceDelta : NNReal} {sourceIndex : Type}
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
      (badParentFreshChildRadius sourceDelta Wsource.rho)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum hDdestination
        Cdestination Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N}
    {K : ENNReal}
    (H : WeightedEarlierBarrierPointwiseSeam
      Wsource Wdestination K)
    (current_scaled :
      K * actualCrossingThresholdAt Wdestination Wsource.stage <=
        actualCrossingValue Wsource) :
    GroundedPaperFactorTransitionCertificate
      Wsource step Wdestination where
  successorDatum_mem := qFreshDatum_mem_paperTransition_successor step
  earlierBarrierTransport :=
    earlierBarrierTransport_of_weightedPointwiseSeam H
  current_stage_barrier :=
    currentStageBarrier_of_weightedSourceValueBound H current_scaled

#print axioms destination_barrier_of_weighted_chain
#print axioms destination_barrier_of_divided_threshold
#print axioms WeightedEarlierBarrierPointwiseSeam.of_divided_thresholds
#print axioms earlierBarrierTransport_of_weightedPointwiseSeam
#print axioms earlierBarrierTransport_of_dividedThresholds
#print axioms currentStageBarrier_of_weightedSourceValueBound
#print axioms groundedCertificate_of_weightedPointwiseSeam

end
end Family8GroundedWeightedEarlierBarrierTransportV1
