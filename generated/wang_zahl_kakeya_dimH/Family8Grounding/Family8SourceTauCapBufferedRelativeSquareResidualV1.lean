import Family8Grounding.Family8CanonicalBufferedSourceTauCapXCrossV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SourceTauCapBufferedRelativeSquareResidualV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8FullRefinementActualDatumV1
open Family8CanonicalBufferedSourceTauCapXCrossV1
open Family8CanonicalBufferedSourceTauCapXCrossV1.Witness

noncomputable section

/-!
# Residual after crossing the source cap with the buffered relative square

The mass-popular base coefficient contains `(tau / b)^2`, whereas the sharp
source-cap cancellation consumes `(delta / tau)^2`.  Their exact quotient is
`(tau^2 / (delta*b))^2`.  This file exposes that residual with equality; it
does not hide it in a delta-power estimate.
-/

theorem bufferedRelativeSquare_factorization
    {delta tau b : NNReal}
    (hdelta : 0 < delta) (htau : 0 < tau) (hb : 0 < b) :
    (((tau : ENNReal) / (b : ENNReal)) ^ 2) =
      (((delta : ENNReal) / (tau : ENNReal)) ^ 2) *
        ((((tau : ENNReal) ^ 2) /
          ((delta : ENNReal) * (b : ENNReal))) ^ 2) := by
  have hnn : tau / b =
      (delta / tau) * (tau ^ (2 : Nat) / (delta * b)) := by
    field_simp [hdelta.ne', htau.ne', hb.ne']
  have hratio : (tau : ENNReal) / (b : ENNReal) =
      ((delta : ENNReal) / (tau : ENNReal)) *
        ((tau : ENNReal) ^ 2 /
          ((delta : ENNReal) * (b : ENNReal))) := by
    calc
      (tau : ENNReal) / (b : ENNReal) = (tau / b : NNReal) := by
        rw [ENNReal.coe_div hb.ne']
      _ = ((delta / tau) *
          (tau ^ (2 : Nat) / (delta * b)) : NNReal) :=
        congrArg (fun x : NNReal => (x : ENNReal)) hnn
      _ = (delta / tau : NNReal) *
          (tau ^ (2 : Nat) / (delta * b) : NNReal) := by rfl
      _ = ((delta : ENNReal) / (tau : ENNReal)) *
          ((tau : ENNReal) ^ 2 /
            ((delta : ENNReal) * (b : ENNReal))) := by
        rw [ENNReal.coe_div htau.ne',
          ENNReal.coe_div (mul_ne_zero hdelta.ne' hb.ne'),
          ENNReal.coe_pow, ENNReal.coe_mul]
  rw [hratio]
  ring

theorem sourceCap_mul_X_mul_bufferedSquare_le_residual
    {delta tau b : NNReal} {C X XUpper : ENNReal}
    (hdelta : 0 < delta) (hdeltaTau : delta <= tau) (hb : 0 < b)
    (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hX : X <= XUpper) :
    ((katzTaoDoubledFiberNatCap delta tau C : ENNReal) * X) *
        (((tau : ENNReal) / (b : ENNReal)) ^ 2) <=
      ((ordinaryFiberNatCapFixedConstant * C) * XUpper) *
        ((((tau : ENNReal) ^ 2) /
          ((delta : ENNReal) * (b : ENNReal))) ^ 2) := by
  have htau : 0 < tau := hdelta.trans_le hdeltaTau
  have hcross := sourceCap_mul_X_mul_relativeSquare_le
    hdelta hdeltaTau hCone hCfinite hX
  rw [bufferedRelativeSquare_factorization hdelta htau hb]
  calc
    ((katzTaoDoubledFiberNatCap delta tau C : ENNReal) * X) *
        ((((delta : ENNReal) / (tau : ENNReal)) ^ 2) *
          ((((tau : ENNReal) ^ 2) /
            ((delta : ENNReal) * (b : ENNReal))) ^ 2)) =
      (((katzTaoDoubledFiberNatCap delta tau C : ENNReal) * X) *
        (((delta : ENNReal) / (tau : ENNReal)) ^ 2)) *
          ((((tau : ENNReal) ^ 2) /
            ((delta : ENNReal) * (b : ENNReal))) ^ 2) := by
      ac_rfl
    _ <= ((ordinaryFiberNatCapFixedConstant * C) * XUpper) *
        ((((tau : ENNReal) ^ 2) /
          ((delta : ENNReal) * (b : ENNReal))) ^ 2) :=
      mul_le_mul' hcross le_rfl

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBufferedInterval_sourceCap_mul_cardScaleMass_bufferedSquare_le
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    {etaKTSource : Real} (hetaKTSource : 0 < etaKTSource) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let b := canonicalBufferedRadius W
    let hbuffered : Sseq.IsBuffered P.epsilon W.m b :=
      canonicalBufferedRadius_isBuffered
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf
    let U := bufferedIntervalCover E hE Cmulti Sseq P.epsilon
      P.epsilon_pos.le W.m b hbuffered
    ((katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
          ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) *
        (activeCoarseCardScaleMass U : ENNReal)) *
      (((Sseq.tau W.m : ENNReal) /
        (canonicalBufferedRadius W : ENNReal)) ^ 2) <=
      ((ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKTSource)) * (1024 * CKT)) *
        ((((Sseq.tau W.m : ENNReal) ^ 2) /
          ((delta : ENNReal) *
            (canonicalBufferedRadius W : ENNReal))) ^ 2) := by
  dsimp only
  have hcross :=
    canonicalBufferedInterval_sourceCap_mul_cardScaleMass_cross_le
      D hD Cmulti Sseq P W hepsilonHalf hbufferedHalf hKTEvery
        hetaKTSource
  have htau : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hb : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  rw [bufferedRelativeSquare_factorization hD.delta_pos htau hb]
  calc
    ((katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
          ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) *
        (activeCoarseCardScaleMass
          (bufferedIntervalCover (fullRefinementDatum D)
            (fullRefinementDatum_isAdmissible hD) Cmulti Sseq P.epsilon
              P.epsilon_pos.le W.m (canonicalBufferedRadius W)
              (canonicalBufferedRadius_isBuffered W hD.delta_pos
                P.epsilon_pos.le hepsilonHalf)) : ENNReal)) *
      ((((delta : ENNReal) / (Sseq.tau W.m : ENNReal)) ^ 2) *
        ((((Sseq.tau W.m : ENNReal) ^ 2) /
          ((delta : ENNReal) *
            (canonicalBufferedRadius W : ENNReal))) ^ 2)) =
      (((katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
          ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) *
        (activeCoarseCardScaleMass
          (bufferedIntervalCover (fullRefinementDatum D)
            (fullRefinementDatum_isAdmissible hD) Cmulti Sseq P.epsilon
              P.epsilon_pos.le W.m (canonicalBufferedRadius W)
              (canonicalBufferedRadius_isBuffered W hD.delta_pos
                P.epsilon_pos.le hepsilonHalf)) : ENNReal)) *
        (((delta : ENNReal) / (Sseq.tau W.m : ENNReal)) ^ 2)) *
      ((((Sseq.tau W.m : ENNReal) ^ 2) /
        ((delta : ENNReal) *
          (canonicalBufferedRadius W : ENNReal))) ^ 2) := by
      ac_rfl
    _ <= ((ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKTSource)) * (1024 * CKT)) *
        ((((Sseq.tau W.m : ENNReal) ^ 2) /
          ((delta : ENNReal) *
            (canonicalBufferedRadius W : ENNReal))) ^ 2) :=
      mul_le_mul' hcross le_rfl

#print axioms bufferedRelativeSquare_factorization
#print axioms sourceCap_mul_X_mul_bufferedSquare_le_residual
#print axioms
  canonicalBufferedInterval_sourceCap_mul_cardScaleMass_bufferedSquare_le

end Witness
end
end Family8SourceTauCapBufferedRelativeSquareResidualV1
