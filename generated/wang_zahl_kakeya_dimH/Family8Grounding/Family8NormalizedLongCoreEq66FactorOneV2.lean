import Family8Grounding.Family8CanonicalGlobalOuterScaleCountIdentityV1
import Family8Grounding.Family8LongIntervalKatzTaoCountNormalizationV2
import Family8Grounding.Family8NormalizedLongCoreLongIntervalGainV1
import Family8Grounding.Family8NormalizedLongIntervalCoreBootstrapV1
import Mathlib.Tactic

/-!
# The normalized LongCore Equation (66) factor is at least one, V2

This is the scalar insertion needed to replay the Equation (66) triple on a
`NormalizedLongIntervalCoreWitness`.  It uses the literal canonical global
cover.  Its active coarse count is nonzero, so the long-interval Katz--Tao
right-hand side is at least one.  The existing normalized-core bootstrap and
local-to-global gain then put that one below the exact Section-8 outer factor.

No identified-witness conversion and no average-multiplicity comparison are
used.  V1 is an unimported elaboration draft.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreEq66FactorOneV2

open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8CanonicalGlobalOuterScaleCountIdentityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8LongIntervalKatzTaoCountNormalizationV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The exact canonical global factor inserted in the normalized LongCore
Equation (66) triple is at least one. -/
theorem one_le_canonicalBufferedGlobal_eq66Factor
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (A : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hKTEvery : C.base.IsKatzTaoAtEveryScale (A : ENNReal))
    (hAKT : 1024 * A <=
      S.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta)))) :
    (1 : ENNReal) <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (canonicalBufferedRadius W) 1
          (canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  let d := S.tau W.m
  let b := canonicalBufferedRadius W
  let X := activeCoarseCardScaleMass G
  let etaPrime := 10 * P.eta W.stage / (P.epsilon * beta)
  have hd : 0 < d := hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hdOne : d <= 1 :=
    (S.tau_le_theta W.m).trans (S.theta_le_one W.m)
  have hdb : d <= b := by
    dsimp only [d, b]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have hb : 0 < b := hd.trans_le hdb
  have hcoarse : G.activeCoarse.Nonempty := by
    dsimp only [G]
    exact canonicalBufferedGlobalCover_activeCoarse_nonempty
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf hfine
  have hcount : 0 < G.activeCoarse.card := Finset.card_pos.mpr hcoarse
  have hKT : G.IsKatzTaoAtScale (A : ENNReal) := by
    dsimp only [G]
    exact hKTEvery (canonicalBufferedRadius W)
      ((S.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos
          P.epsilon_pos.le))
      (canonicalBufferedRadius_le_one W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf)
  have hbootstrap :
      longIntervalKatzTaoRHSENNReal d b X P.epsilon etaPrime beta <=
        longIntervalFrostmanTargetENNReal d b X etaPrime gamma := by
    simpa only [d, b, X, etaPrime, G] using
      (Family8NormalizedLongIntervalCoreBootstrapV1.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_coreActual
        D hD C S P W A hbeta hgamma hepsilonHalf hrhoHalf hfine
          hC htauSmall hKT hAKT)
  have hetaPrime : 0 < etaPrime := by
    dsimp only [etaPrime]
    exact div_pos (mul_pos (by norm_num) (P.eta_pos W.stage))
      (mul_pos P.epsilon_pos hbeta)
  have hloss : 0 < longIntervalDeltaLoss P.epsilon etaPrime := by
    rw [longIntervalDeltaLoss]
    linarith [P.epsilon_pos]
  have hdOneENN : (d : ENNReal) <= 1 := by exact_mod_cast hdOne
  have honeD : (1 : ENNReal) <=
      (d : ENNReal) ^ (-longIntervalDeltaLoss P.epsilon etaPrime) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hd) hdOneENN (by linarith)
  have hcountOne : 1 <= (G.activeCoarse.card : ENNReal) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcount.ne')
  have honeCount : (1 : ENNReal) <=
      (G.activeCoarse.card : ENNReal) ^ beta := by
    simpa only [ENNReal.one_rpow] using
      (ENNReal.rpow_le_rpow hcountOne hbeta.le)
  have honeKT : (1 : ENNReal) <=
      katzTaoMultiplicityRHS d G.activeCoarse.card
        (longIntervalDeltaLoss P.epsilon etaPrime) beta := by
    unfold katzTaoMultiplicityRHS
    simpa only [one_mul] using (mul_le_mul' honeD honeCount)
  have hnormalize :
      katzTaoMultiplicityRHS d G.activeCoarse.card
          (longIntervalDeltaLoss P.epsilon etaPrime) beta =
        longIntervalKatzTaoRHSENNReal d b X
          P.epsilon etaPrime beta := by
    apply katzTaoMultiplicityRHS_eq_longIntervalKatzTaoRHSENNReal
      hd hb hcount
    rfl
  have hbetaOne : beta <= 1 := by
    nlinarith [P.epsilon_gap, P.epsilon_pos]
  have hgain :
      (d : ENNReal) ^ (10 * etaPrime) <=
        (delta : ENNReal) ^ (10 * P.eta W.stage) := by
    simpa only [d, etaPrime] using
      (Family8NormalizedLongCoreLongIntervalGainV1.NormalizedLongIntervalCoreWitness.tau_longIntervalGain_le_globalTenEta
        C S P W hbeta hbetaOne)
  calc
    (1 : ENNReal) <=
        longIntervalKatzTaoRHSENNReal d b X P.epsilon etaPrime beta := by
      rw [← hnormalize]
      exact honeKT
    _ <= longIntervalFrostmanTargetENNReal d b X etaPrime gamma :=
      hbootstrap
    _ = (d : ENNReal) ^ (10 * etaPrime) *
          sectionEightScaleCountFrostmanFactor
            b 1 G.activeCoarse.card gamma := by
      unfold longIntervalFrostmanTargetENNReal
      rw [mul_assoc,
        activeCoarseCardScaleMass_middleFactor_eq_sectionEight]
    _ <= (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            b 1 G.activeCoarse.card gamma :=
      mul_le_mul' hgain le_rfl
    _ = (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            (canonicalBufferedRadius W) 1
            (canonicalBufferedGlobalCover W hD.delta_pos
              P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma := rfl

#print axioms one_le_canonicalBufferedGlobal_eq66Factor

end
end Family8NormalizedLongCoreEq66FactorOneV2
