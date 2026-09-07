import Family8Grounding.Family8CanonicalBufferedGlobalGeneralizedOuterAutomaticV1
import Family8Grounding.Family8GeneralizedOuterLongIntervalNormalizationV1
import Family8Grounding.Family8IdentifiedDividingWitnessLongIntervalBootstrapV1
import Family8Grounding.Family8LongIntervalKatzTaoCountNormalizationV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ParameterLadderV1
open Family8LongIntervalBootstrapNumericsV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ExplicitConcentrationGeneralizedReturnV1
open Family8ExplicitConcentrationCanonicalScalarBudgetsV1
open Family8CanonicalBufferedGlobalGeneralizedOuterAutomaticV1.Witness
open Family8GeneralizedOuterLongIntervalNormalizationV1
open Family8LongIntervalKatzTaoCountNormalizationV2

noncomputable section

/-!
# The canonical full coarse family satisfies the long-interval outer bound

This is the literal equation-(66) route.  Polynomial-John extraction and
fresh selection first give generalized Katz--Tao for the full-shaded active
coarse family.  The coefficient and scale losses are then normalized to the
global scale, and the actual two-sided bound for
`X = b^2 * |T_b|` converts the ordinary Katz--Tao expression to the paper's
long-interval Frostman target.
-/

def canonicalFullCoarseGeneralizedLoss
    (epsilon beta tailEta constantEta cardAbsorbEta freshAbsorbEta
      scaleAbsorbEta : Real) : Real :=
  (epsilon + beta * (tailEta + constantEta) + cardAbsorbEta) +
    (tailEta + constantEta + freshAbsorbEta) + scaleAbsorbEta

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_longIntervalTarget
    {epsilonKT targetEta sourceEta tailEta constantEta sourceDensityEta
      densityAbsorbEta coefficientAbsorbEta freshAbsorbEta cardAbsorbEta
      returnScaleAbsorbEta longScaleAbsorbEta coefficientEta : Real}
    {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters beta epsilonKT targetEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (A : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    (hAone : 1 <= (A : ENNReal))
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale (A : ENNReal))
    (hsourceEta : 0 < sourceEta)
    (hsourceDensityEta : 0 < sourceDensityEta)
    (hepsilonKT : 0 <= epsilonKT)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (htargetEta : 0 <= targetEta)
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hfreshAbsorbEta : 0 < freshAbsorbEta)
    (hcardAbsorbEta : 0 < cardAbsorbEta)
    (hreturnScaleAbsorbEta : 0 < returnScaleAbsorbEta)
    (hlongScaleAbsorbEta : 0 < longScaleAbsorbEta)
    (hdensityBudget :
      2 * (tailEta + constantEta) + sourceDensityEta +
          densityAbsorbEta <= targetEta)
    (hcoefficientBudget :
      tailEta + constantEta + coefficientAbsorbEta <= targetEta)
    (hscalarSmall : canonicalBufferedRadius W / 8 <=
      canonicalOuterScalarThreshold (A : ENNReal) sourceEta
        sourceDensityEta)
    (houterSmall : canonicalBufferedRadius W / 8 <=
      explicitConcentrationGeneralizedReturnThreshold sourceEta tailEta
        constantEta densityAbsorbEta coefficientAbsorbEta freshAbsorbEta
        cardAbsorbEta returnScaleAbsorbEta epsilonKT beta)
    (hdelta0 : canonicalBufferedRadius W / 64 <= delta0)
    (hlongScaleSmall : canonicalBufferedRadius W <=
      Family8ExplicitConcentrationFreshReturnNormalizationV2.explicitConcentrationFreshReturnScaleThreshold
        (canonicalFullCoarseGeneralizedLoss epsilonKT beta tailEta
          constantEta cardAbsorbEta freshAbsorbEta returnScaleAbsorbEta)
        longScaleAbsorbEta)
    (hcoefficientPower : 128 * (A : ENNReal) <=
      (Sseq.tau W.m : ENNReal) ^ (-coefficientEta))
    (hlossBudget :
      canonicalFullCoarseGeneralizedLoss epsilonKT beta tailEta
          constantEta cardAbsorbEta freshAbsorbEta returnScaleAbsorbEta +
        longScaleAbsorbEta + coefficientEta * (1 - beta) <=
          longIntervalDeltaLoss P.epsilon
            (10 * P.eta W.stage / (P.epsilon * beta)))
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hAKT : 1024 * A <=
      Sseq.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta)))) :
    (Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness.canonicalBufferedGlobalFullCoarseDatum
        D Cmulti Sseq W hD.delta_pos P.epsilon_pos.le
          hepsilonHalf).shading.averageMultiplicity <=
      longIntervalFrostmanTargetENNReal
        (Sseq.tau W.m) (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf))
        (10 * P.eta W.stage / (P.epsilon * beta)) gamma := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  let d := Sseq.tau W.m
  let b := canonicalBufferedRadius W
  let X := activeCoarseCardScaleMass G
  let outerEta := canonicalFullCoarseGeneralizedLoss epsilonKT beta
    tailEta constantEta cardAbsorbEta freshAbsorbEta returnScaleAbsorbEta
  have hd : 0 < d := hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hdOne : d <= 1 :=
    (Sseq.tau_le_theta W.m).trans (Sseq.theta_le_one W.m)
  have hdb : d <= b := by
    dsimp only [d, b]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have hb : 0 < b := hd.trans_le hdb
  have hcoarse : G.activeCoarse.Nonempty :=
    canonicalBufferedGlobalCover_activeCoarse_nonempty W hD.delta_pos
      P.epsilon_pos.le hepsilonHalf hfine
  have hcount : 0 < G.activeCoarse.card := Finset.card_pos.mpr hcoarse
  have hbetaOne : beta <= 1 := by
    have hgap := P.epsilon_gap
    have heps := P.epsilon_pos
    linarith
  have houter :
      (Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness.canonicalBufferedGlobalFullCoarseDatum
          D Cmulti Sseq W hD.delta_pos P.epsilon_pos.le
            hepsilonHalf).shading.averageMultiplicity <=
        generalizedKatzTaoMultiplicityRHS (b / 8) (128 * (A : ENNReal))
          G.activeCoarse.card outerEta beta := by
    dsimp only [outerEta, b, G, canonicalFullCoarseGeneralizedLoss]
    exact canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_generalized_auto
      hKTP D hD Cmulti Sseq W P.epsilon_pos.le hepsilonHalf hfine
        hbufferedSixteenth hAone ENNReal.coe_ne_top hKTEvery hsourceEta
        hsourceDensityEta hepsilonKT htailEta hconstantEta htargetEta
        hdensityAbsorbEta hcoefficientAbsorbEta hfreshAbsorbEta
        hcardAbsorbEta hreturnScaleAbsorbEta hbeta.le
        hbetaOne hdensityBudget hcoefficientBudget hscalarSmall
        houterSmall hdelta0
  have hordinary :
      generalizedKatzTaoMultiplicityRHS (b / 8) (128 * (A : ENNReal))
          G.activeCoarse.card outerEta beta <=
        katzTaoMultiplicityRHS d G.activeCoarse.card
          (longIntervalDeltaLoss P.epsilon
            (10 * P.eta W.stage / (P.epsilon * beta))) beta := by
    exact generalizedKatzTaoMultiplicityRHS_div_eight_le_global
      hd hdOne hdb (by
        change 0 <= canonicalFullCoarseGeneralizedLoss epsilonKT beta
          tailEta constantEta cardAbsorbEta freshAbsorbEta
            returnScaleAbsorbEta
        unfold canonicalFullCoarseGeneralizedLoss
        have hq : 0 < tailEta + constantEta := by linarith
        have hprod : 0 <= beta * (tailEta + constantEta) :=
          mul_nonneg hbeta.le hq.le
        linarith)
      hlongScaleAbsorbEta hbetaOne (by
        simpa only [b, outerEta] using hlongScaleSmall)
      (by simpa only [d] using hcoefficientPower)
      (by simpa only [outerEta] using hlossBudget)
  have hGKT : G.IsKatzTaoAtScale (A : ENNReal) :=
    hKTEvery b
      ((Sseq.delta_le_tau W.m).trans hdb)
      (by
        dsimp only [b]
        exact canonicalBufferedRadius_le_one W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf)
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
          (show (2 : NNReal) <= 16 by norm_num)))
  have hbootstrap :=
    Family8IdentifiedDividingWitnessLongIntervalBootstrapV1.Witness.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_actual
      D hD Cmulti Sseq P W A hbeta hgamma hepsilonHalf hrhoHalf hfine
        hC htauSmall hGKT hAKT
  have hX : X = (G.activeCoarse.card : NNReal) * b ^ 2 := by
    rfl
  have hcountEq :
      katzTaoMultiplicityRHS d G.activeCoarse.card
          (longIntervalDeltaLoss P.epsilon
            (10 * P.eta W.stage / (P.epsilon * beta))) beta =
        longIntervalKatzTaoRHSENNReal d b X P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta)) beta :=
    katzTaoMultiplicityRHS_eq_longIntervalKatzTaoRHSENNReal
      hd hb hcount hX
  exact houter.trans (hordinary.trans (by
    rw [hcountEq]
    simpa only [d, b, X, G] using hbootstrap))

#print axioms canonicalFullCoarseGeneralizedLoss
#print axioms
  canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_longIntervalTarget

end Witness
end
end Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1
