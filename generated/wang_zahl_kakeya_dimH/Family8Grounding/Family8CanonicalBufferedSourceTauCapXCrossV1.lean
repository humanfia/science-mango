import Family8Grounding.Family8LocalFiberCapRelativeSquareCancellationV1
import Family8Grounding.Family8NormalizedBufferedIntervalKatzTaoV2
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedSourceTauCapXCrossV1

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
open Family8NormalizedBufferedIntervalKatzTaoV2
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8StickyParentHullVolumeBoundV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1.StickyScaleCover
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8LocalFiberCapRelativeSquareCancellationV1
open Family8FullRefinementActualDatumV1

noncomputable section

/-!
# Sharp source-cap by buffered parent-mass cross

The source-to-tau Katz--Tao cap is not estimated as a standalone delta
power.  It is kept multiplied by its exact opposite relative square.  This
is the strongest scale-free scalar statement available before a later count
or density expression supplies that square.
-/

theorem sourceCap_mul_X_mul_relativeSquare_le
    {delta tau : NNReal} {C X XUpper : ENNReal}
    (hdelta : 0 < delta) (hdeltaTau : delta <= tau)
    (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hX : X <= XUpper) :
    ((katzTaoDoubledFiberNatCap delta tau C : ENNReal) * X) *
        (((delta : ENNReal) / (tau : ENNReal)) ^ 2) <=
      (ordinaryFiberNatCapFixedConstant * C) * XUpper := by
  have hcap := katzTaoDoubledFiberNatCap_mul_relativeSquare_le_fixed
    hdelta hdeltaTau hCone hCfinite
  calc
    ((katzTaoDoubledFiberNatCap delta tau C : ENNReal) * X) *
        (((delta : ENNReal) / (tau : ENNReal)) ^ 2) =
      ((katzTaoDoubledFiberNatCap delta tau C : ENNReal) *
        (((delta : ENNReal) / (tau : ENNReal)) ^ 2)) * X := by
      ac_rfl
    _ <= (ordinaryFiberNatCapFixedConstant * C) * XUpper :=
      mul_le_mul' hcap hX

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Canonical specialization on the literal source-mass interval cover.  Its
active coarse family is definitionally the paper's full `T_b` family. -/
theorem canonicalBufferedInterval_sourceCap_mul_cardScaleMass_cross_le
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
      (((delta : ENNReal) / (Sseq.tau W.m : ENNReal)) ^ 2) <=
        (ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKTSource)) * (1024 * CKT) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let b := canonicalBufferedRadius W
  let hbuffered : Sseq.IsBuffered P.epsilon W.m b :=
    canonicalBufferedRadius_isBuffered
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf
  let U := bufferedIntervalCover E hE Cmulti Sseq P.epsilon
    P.epsilon_pos.le W.m b hbuffered
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hKTU : U.IsKatzTaoAtScale CKT :=
    bufferedIntervalCover_isKatzTaoAtScale
      E hE Cmulti Sseq P.epsilon P.epsilon_pos.le W.m b hbuffered hKTEvery
  have hfamily : U.activeCoarseFamily = G.activeCoarseFamily := by
    rfl
  have hcontained : forall k,
      (U.activeCoarseFamily k : Set Space) <=
        (closedBallFourBody : Set Space) := by
    intro k
    rw [hfamily]
    exact activeCoarseFamily_body_subset_closedBall_four
      E hE G (hbufferedHalf.trans (by norm_num)) k
  have hX : (activeCoarseCardScaleMass U : ENNReal) <= 1024 * CKT :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale_of_contained
      U hbufferedHalf hKTU hcontained
  have hdeltaOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast (hD.delta_le_half.trans (by norm_num))
  have hCone : 1 <= (delta : ENNReal) ^ (-etaKTSource) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hD.delta_pos) hdeltaOne (by linarith)
  have hCfinite : (delta : ENNReal) ^ (-etaKTSource) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  exact sourceCap_mul_X_mul_relativeSquare_le
    hD.delta_pos (Sseq.delta_le_tau W.m) hCone hCfinite hX

#print axioms sourceCap_mul_X_mul_relativeSquare_le
#print axioms
  canonicalBufferedInterval_sourceCap_mul_cardScaleMass_cross_le

end Witness
end
end Family8CanonicalBufferedSourceTauCapXCrossV1
