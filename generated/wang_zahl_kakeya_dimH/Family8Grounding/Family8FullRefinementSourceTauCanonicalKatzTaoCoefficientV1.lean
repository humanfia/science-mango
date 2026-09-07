import Family8Grounding.Family8TauActiveNativeKatzTaoTransportV4
import Family8Grounding.Family8CardWeightedEq46CoefficientPowerEnvelopeV1
import Family8Grounding.Family8FullRefinementActualDatumV1
import Mathlib.Tactic

/-!
# Canonical finite Katz--Tao input and source-tau coefficient power bound

Use the same actual every-scale constant `CKT` for the tau-active native
Katz--Tao certificate and for the inner selected-parent estimate.  The
card-weighted cancellation has already removed raw parent and bucket cards;
the remaining coefficient is bounded by one explicit delta power, with the
same Katz--Tao exponent counted twice.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauCanonicalKatzTaoCoefficientV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CardWeightedEq46CoefficientPowerEnvelopeV1
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8TauActiveNativeKatzTaoTransportV4.Witness
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

/-- Actual canonical source-tau Katz--Tao datum together with the complete
card-weighted coefficient envelope.  No target/inner-factor inequality is an
input to this theorem. -/
theorem sourceTau_nativeKatzTao_and_cardWeightedCoefficient_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    {loss : Nat} {CKT : ENNReal}
    {etaKT tauExponent lossExponent ktExponent
      constantAbsorbExponent : Real}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (htauExponent : 0 ≤ tauExponent)
    (hloss : (loss : ENNReal) ≤
      (delta : ENNReal) ^ (-lossExponent))
    (hCKTPower : CKT ≤ (delta : ENNReal) ^ (-ktExponent))
    (hconstantAbsorbExponent : 0 < constantAbsorbExponent)
    (hsmall : delta ≤
      cardWeightedEq46FixedConstantThreshold constantAbsorbExponent) :
    IsKatzTao CKT
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily ∧
      ((ordinaryFiberNatCapFixedConstant *
            (delta : ENNReal) ^ (-etaKT)) *
          (Sseq.tau W.m : ENNReal) ^ (-tauExponent)) *
        ((loss : ENNReal) * (1024 * CKT) * CKT) ≤
      (delta : ENNReal) ^
        (-(etaKT + tauExponent + lossExponent +
          ktExponent + ktExponent + constantAbsorbExponent)) := by
  let S := tauScaleCover (fullRefinementDatum D) Cmulti Sseq W
  have hKTTau : S.IsKatzTaoAtScale CKT := by
    exact hKTEvery (Sseq.tau W.m) (Sseq.delta_le_tau W.m)
      (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m)
  have hnative0 :=
    tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
      (fullRefinementDatum D) Cmulti Sseq W hKTTau
  have hfamily :
      (tauActiveCoarseDatum (fullRefinementDatum D) Cmulti Sseq W).family.bodyFamily =
        S.activeCoarseFamily := by
    funext k
    rfl
  rw [hfamily] at hnative0
  have hnative : IsKatzTao CKT S.activeCoarseFamily := hnative0
  refine ⟨by simpa only [S] using hnative, ?_⟩
  exact cardWeightedEq46Coefficient_le_delta_negativePower
    (delta := delta) (tau := Sseq.tau W.m)
    (loss := (loss : ENNReal)) (CKT := CKT) (KT := CKT)
    (etaKT := etaKT) (tauExponent := tauExponent)
    (lossExponent := lossExponent)
    (coarseKTExponent := ktExponent)
    (innerKTExponent := ktExponent)
    (constantAbsorbExponent := constantAbsorbExponent)
    hD.delta_pos (Sseq.delta_le_tau W.m) htauExponent hloss
    hCKTPower hCKTPower hconstantAbsorbExponent hsmall

#print axioms sourceTau_nativeKatzTao_and_cardWeightedCoefficient_le_power

end
end Family8FullRefinementSourceTauCanonicalKatzTaoCoefficientV1
