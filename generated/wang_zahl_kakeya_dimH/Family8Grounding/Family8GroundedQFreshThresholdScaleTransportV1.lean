import Family8Grounding.Family8GroundedEarlierBarrierTransportProducerV1
import Family8Grounding.Family8SelectedFiberFaithfulCoherentSuccessorV1
import Mathlib.Tactic

/-!
# Actual-scale producer for the q-fresh crossing threshold

The earlier-barrier connector originally exposed a pointwise threshold
comparison at every earlier selector stage.  This file derives that entire
family of comparisons from a smaller geometric scale seam.

The destination crossing is on the literal selected q-fresh child.  Its
selected upper and lower scales are required to be the actual contracted-
John/eighth images of the source crossing's selected upper and lower scales.
The common fixed factor `3/64` then cancels from their quotient.  With the
same selector exponent schedule, the two literal thresholds are equal at
every stage, hence in particular satisfy the required inequality.

No concentration value comparison, universal barrier, stage strictness, or
successor membership is a field here.  The concentration-value transport is
kept independent for the same-destination CF connector.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8GroundedQFreshThresholdScaleTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Family8ContractedJohnActualTubeProxyV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8GroundedEarlierBarrierTransportProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SelectedFiberFaithfulCoherentSuccessorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## Exact q-fresh scale algebra -/

/-- The same contracted-John/eighth normalization is applied to both
endpoints, so its fixed coefficient cancels from their relative scale. -/
theorem qFreshProxyScale_div_qFreshProxyScale_eq
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
    (upper lower : NNReal) (hlower : 0 < lower) :
    qFreshProxyScale Wsource upper /
        qFreshProxyScale Wsource lower =
      upper / lower := by
  apply NNReal.eq
  simp only [qFreshProxyScale, contractedJohnProxyRadius,
    NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
  have hrhoReal : (Wsource.rho : Real) ≠ 0 := by
    exact_mod_cast (crossingRhoPos Wsource).ne'
  have hlowerReal : (lower : Real) ≠ 0 := by
    exact_mod_cast hlower.ne'
  field_simp [hrhoReal, hlowerReal]

/-- The bottom of every destination scale chain is definitionally the
literal q-fresh proxy image of the source datum radius. -/
theorem destination_bottom_radius_eq_qFreshProxyScale
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
    {destinationDepth : Nat}
    (Sdestination : FiniteScaleSequence
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth) :
    Sdestination.radius (Fin.last destinationDepth) =
      qFreshProxyScale Wsource sourceDelta := by
  rw [Sdestination.bottom_eq]
  rfl

/-- The preceding type-level endpoint identity exposes the actual fixed
`3/64` radius coefficient rather than silently treating it as the paper
relative scale. -/
theorem destination_bottom_radius_eq_fixed_mul_source_ratio
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
    {destinationDepth : Nat}
    (Sdestination : FiniteScaleSequence
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth) :
    Sdestination.radius (Fin.last destinationDepth) =
      (3 / 64 : NNReal) * (sourceDelta / Wsource.rho) := by
  calc
    Sdestination.radius (Fin.last destinationDepth) =
        badParentFreshChildRadius sourceDelta Wsource.rho :=
      Sdestination.bottom_eq
    _ = (3 / 64 : NNReal) * (sourceDelta / Wsource.rho) :=
      badParentFreshChildRadius_eq_fixed_mul_ratio
        (crossingRhoPos Wsource)

/-! ## The actual selected-scale seam -/

/-- The two selected destination scales are the literal q-fresh images of
the two selected source scales.  These are object-level scale equalities,
not a prepackaged threshold inequality. -/
structure QFreshCrossingActualScaleMatch
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
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    (Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum hDdestination
        Cdestination Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N) : Prop where
  rho_eq : Wdestination.rho =
    qFreshProxyScale Wsource Wsource.rho
  tau_eq : Sdestination.tau Wdestination.m =
    qFreshProxyScale Wsource (Ssource.tau Wsource.m)

namespace QFreshCrossingActualScaleMatch

/-- The literal relative scales of the two selected crossings are equal;
the proof performs the fixed-coefficient cancellation. -/
theorem relativeScale_eq
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
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum hDdestination
        Cdestination Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N}
    (H : QFreshCrossingActualScaleMatch
      Wsource step Wdestination) :
    Wdestination.rho / Sdestination.tau Wdestination.m =
      Wsource.rho / Ssource.tau Wsource.m := by
  rw [H.rho_eq, H.tau_eq]
  exact qFreshProxyScale_div_qFreshProxyScale_eq
    Wsource Wsource.rho (Ssource.tau Wsource.m)
      (hDsource.delta_pos.trans_le (Ssource.delta_le_tau Wsource.m))

end QFreshCrossingActualScaleMatch

/-! ## Threshold comparison producer -/

/-- At any stage where the exponent schedules agree, the actual threshold
is equal after the grounded q-fresh scale transport. -/
theorem actualCrossingThresholdAt_eq_of_actualScaleMatch
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
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum hDdestination
        Cdestination Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N}
    (H : QFreshCrossingActualScaleMatch
      Wsource step Wdestination)
    (stage : Nat) (heta : destinationEta stage = sourceEta stage) :
    actualCrossingThresholdAt Wdestination stage =
      actualCrossingThresholdAt Wsource stage := by
  have hpow := congrArg
    (fun ratio : NNReal => ((ratio : ENNReal) ^ sourceEta stage))
      H.relativeScale_eq
  simpa only [actualCrossingThresholdAt, heta] using hpow

/-- Hence a prefix equality of exponent schedules produces the whole
earlier-stage threshold inequality required by the barrier connector. -/
theorem actualCrossingThreshold_le_of_actualScaleMatch
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
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {destinationEta : Nat -> Real}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum hDdestination
        Cdestination Sdestination destinationEpsilon
          hDestinationEpsilon destinationEta N}
    (H : QFreshCrossingActualScaleMatch
      Wsource step Wdestination)
    (eta_eq : forall stage : Nat, stage < Wsource.stage ->
      destinationEta stage = sourceEta stage) :
    forall stage : Nat, stage < Wsource.stage ->
      actualCrossingThresholdAt Wdestination stage <=
        actualCrossingThresholdAt Wsource stage := by
  intro stage hstage
  exact (actualCrossingThresholdAt_eq_of_actualScaleMatch
    H stage (eta_eq stage hstage)).le

/-- In the intended repeated selector, the exponent schedule is global and
therefore definitionally the same on source and destination.  No exponent
transport input remains in this specialization. -/
theorem actualCrossingThreshold_le_of_actualScaleMatch_sameEta
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
      (contractedJohnProxyRadius sourceDelta Wsource.rho / 8)
        destinationDepth}
    {destinationEpsilon : Real}
    {hDestinationEpsilon : 0 <= destinationEpsilon}
    {Wdestination : FirstParentwiseNormalizedCrossingWitness
      step.integrated.dualChild.qFibreChildDatum hDdestination
        Cdestination Sdestination destinationEpsilon
          hDestinationEpsilon sourceEta N}
    (H : QFreshCrossingActualScaleMatch
      Wsource step Wdestination) :
    forall stage : Nat, stage < Wsource.stage ->
      actualCrossingThresholdAt Wdestination stage <=
        actualCrossingThresholdAt Wsource stage := by
  exact actualCrossingThreshold_le_of_actualScaleMatch H
    (fun _stage _hstage => rfl)

#print axioms qFreshProxyScale_div_qFreshProxyScale_eq
#print axioms destination_bottom_radius_eq_qFreshProxyScale
#print axioms destination_bottom_radius_eq_fixed_mul_source_ratio
#print axioms QFreshCrossingActualScaleMatch.relativeScale_eq
#print axioms actualCrossingThresholdAt_eq_of_actualScaleMatch
#print axioms actualCrossingThreshold_le_of_actualScaleMatch
#print axioms actualCrossingThreshold_le_of_actualScaleMatch_sameEta

end
end Family8GroundedQFreshThresholdScaleTransportV1
