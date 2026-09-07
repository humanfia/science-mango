import Family8Grounding.Family8PaperFactorFiniteRunV2
import Mathlib.Tactic

/-!
# Pointwise producer for grounded earlier-barrier transport

The selector-grounded V2 run deliberately exposes cross-object barrier
transport as a seam.  This file lowers that seam to the first scalar facts
that genuinely depend on successor geometry:

* the destination threshold is at most the source threshold at every actual
  earlier source stage; and
* the source crossing value is at most the destination crossing value.

The complete universal earlier barrier is never accepted as an input.
Instead it is instantiated from `Wsource.earlier_parentwise_barrier` on the
literal source scale and parent, then composed with the two pointwise scalar
comparisons above.

The destination datum is definitionally the same selected q-fresh child
stored by the integrated source successor and the paper transition.  Thus
the connector cannot silently switch to another factor or parent.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped ENNReal NNReal

namespace Family8GroundedEarlierBarrierTransportProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentFactorListStateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseCrossingIntegratedSuccessorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## The earliest pointwise comparison seam -/

/-- Pointwise scalar comparisons from the literal source crossing to a
crossing selector on its exact selected q-fresh child.

No universal barrier and no stage inequality is a field. -/
structure QFreshCrossingPointwiseTransportSeam
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
    (step : SameObjectCrossingPaperStep Wsource)
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
    (Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum hDdestination
        Cdestination Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N) where
  threshold_le : forall stage : Nat, stage < Wsource.stage ->
    actualCrossingThresholdAt Wdestination stage <=
      actualCrossingThresholdAt Wsource stage
  value_le : actualCrossingValue Wsource <=
    actualCrossingValue Wdestination

namespace QFreshCrossingPointwiseTransportSeam

/-- Equality of the literal threshold and pointwise value is a sufficient
special case.  This is the direct adapter for a future same-cover equality
producer. -/
theorem of_equalities
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
    (threshold_eq : forall stage : Nat, stage < Wsource.stage ->
      actualCrossingThresholdAt Wdestination stage =
        actualCrossingThresholdAt Wsource stage)
    (value_eq : actualCrossingValue Wsource =
      actualCrossingValue Wdestination) :
    QFreshCrossingPointwiseTransportSeam
      Wsource step Wdestination where
  threshold_le := by
    intro stage hstage
    exact (threshold_eq stage hstage).le
  value_le := value_eq.le

end QFreshCrossingPointwiseTransportSeam

/-! ## Instantiating the actual source barrier -/

/-- The universal earlier barrier stored by `Wsource`, specialized to its
own literal crossing scale and dependent parent. -/
theorem source_threshold_le_crossingValue_of_earlier
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
    {stage : Nat} (hstage : stage < Wsource.stage) :
    actualCrossingThresholdAt Wsource stage <=
      actualCrossingValue Wsource := by
  exact
    (actualEarlierParentwiseBarrierAt Wsource hstage)
      Wsource.m Wsource.notLarge Wsource.rho
        Wsource.buffered Wsource.q

/-! ## Complete transport producer -/

/-- Build the V2 earlier-barrier transport from the two pointwise scalar
comparisons.  The `sourceBarrier` argument is the actual universal proof
handed to the transport by V2, and is instantiated rather than ignored. -/
theorem earlierBarrierTransport_of_qFreshPointwiseSeam
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
    (H : QFreshCrossingPointwiseTransportSeam
      Wsource step Wdestination) :
    EarlierBarrierTransport Wsource Wdestination where
  transport := by
    intro stage hstage sourceBarrier
    have hsource : actualCrossingThresholdAt Wsource stage <=
        actualCrossingValue Wsource :=
      sourceBarrier Wsource.m Wsource.notLarge Wsource.rho
        Wsource.buffered Wsource.q
    exact (H.threshold_le stage hstage).trans
      (hsource.trans H.value_le)

/-! ## Automatic same-selected destination membership -/

/-- The destination datum used above is already the selected q-fresh atom
in the exact paper successor list. -/
theorem qFreshDatum_mem_paperTransition_successor
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
    (step : SameObjectCrossingPaperStep Wsource) :
    ActualFactorDatum.ofDatum
        step.integrated.dualChild.qFibreChildDatum ∈
      step.paperTransition.successor.factors := by
  rw [step.paperTransition.successor_factors_eq]
  simp only [
    ParentwiseBadParentMassAwareFactorListState.successorFactors,
    badParentSuccessorFactorList, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (Or.inl rfl))

/-- Assemble the full grounded edge once the independent current-stage
destination barrier is available.  Earlier stages and destination membership
are produced by this file. -/
theorem groundedCertificate_of_qFreshPointwiseSeam
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
    (H : QFreshCrossingPointwiseTransportSeam
      Wsource step Wdestination)
    (currentStageBarrier :
      actualCrossingThresholdAt Wdestination Wsource.stage <=
        actualCrossingValue Wdestination) :
    GroundedPaperFactorTransitionCertificate
      Wsource step Wdestination where
  successorDatum_mem := qFreshDatum_mem_paperTransition_successor step
  earlierBarrierTransport :=
    earlierBarrierTransport_of_qFreshPointwiseSeam H
  current_stage_barrier := currentStageBarrier

#print axioms QFreshCrossingPointwiseTransportSeam.of_equalities
#print axioms source_threshold_le_crossingValue_of_earlier
#print axioms earlierBarrierTransport_of_qFreshPointwiseSeam
#print axioms qFreshDatum_mem_paperTransition_successor
#print axioms groundedCertificate_of_qFreshPointwiseSeam

end
end Family8GroundedEarlierBarrierTransportProducerV1
