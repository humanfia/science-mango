import Family8Grounding.Family8CanonicalBufferedGlobalFullCoarseDatumV1
import Family8Grounding.Family8ExplicitConcentrationGeneralizedOuterV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalGeneralizedOuterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness
open Family8ExplicitConcentrationGeneralizedReturnV1
open Family8ExplicitConcentrationGeneralizedOuterV3

noncomputable section

/-!
# Generalized Katz--Tao on the canonical full-shaded coarse datum

This specializes the branch-free polynomial-John/fresh-selection outer
estimate to the literal paper family `T_b`.  The source object is normalized
exactly once from its automatic radius-two support.  Its density is supplied
by the honest full shading, its index cardinality is the literal active
coarse cardinality, and a second normalization internal to the fresh
endpoint occurs at scale `b / 64`.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilonW : Real} {etaW : Nat -> Real}

theorem canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_generalized
    {beta epsilon targetEta sourceEta tailEta constantEta
      sourceDensityEta densityAbsorbEta coefficientAbsorbEta
      freshAbsorbEta cardAbsorbEta scaleAbsorbEta : Real}
    {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters beta epsilon targetEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti N epsilonW etaW Sseq)
    (hepsilonW : 0 <= epsilonW)
    (hepsilonWHalf : epsilonW <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    {CKT : ENNReal} (hCKTone : 1 <= CKT) (hCKTfinite : CKT ≠ ∞)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (hsourceEta : 0 <= sourceEta)
    (hCpower : 128 * CKT <=
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^
        (-sourceEta)))
    (hepsilon0 : 0 <= epsilon)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (htargetEta : 0 <= targetEta)
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hfreshAbsorbEta : 0 < freshAbsorbEta)
    (hcardAbsorbEta : 0 < cardAbsorbEta)
    (hscaleAbsorbEta : 0 < scaleAbsorbEta)
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1)
    (hdensityPower :
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^
          sourceDensityEta) <= (1 / 128 : ENNReal))
    (hdensityBudget :
      2 * (tailEta + constantEta) + sourceDensityEta +
          densityAbsorbEta <= targetEta)
    (hcoefficientBudget :
      tailEta + constantEta + coefficientAbsorbEta <= targetEta)
    (hsmall : canonicalBufferedRadius W / 8 <=
      explicitConcentrationGeneralizedReturnThreshold sourceEta tailEta
        constantEta densityAbsorbEta coefficientAbsorbEta freshAbsorbEta
        cardAbsorbEta scaleAbsorbEta epsilon beta)
    (hdelta0 : canonicalBufferedRadius W / 64 <= delta0) :
    (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos hepsilonW hepsilonWHalf).shading.averageMultiplicity <=
      generalizedKatzTaoMultiplicityRHS
        (canonicalBufferedRadius W / 8) (128 * CKT)
        (canonicalBufferedGlobalCover W hD.delta_pos
          hepsilonW hepsilonWHalf).activeCoarse.card
        ((epsilon + beta * (tailEta + constantEta) + cardAbsorbEta) +
          (tailEta + constantEta + freshAbsorbEta) + scaleAbsorbEta) beta := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilonW hepsilonWHalf
  have hcoarse : G.activeCoarse.Nonempty :=
    canonicalBufferedGlobalCover_activeCoarse_nonempty W hD.delta_pos
      hepsilonW hepsilonWHalf hfine
  let _ : Nonempty {k // k ∈ G.activeCoarse} :=
    Finset.nonempty_coe_sort.mpr hcoarse
  let E := canonicalBufferedGlobalUnitCoarseDatum D Cmulti Sseq W
    hD.delta_pos hepsilonW hepsilonWHalf
  have hbpos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hepsilonW
  have hEpos : 0 < canonicalBufferedRadius W / 8 :=
    div_pos hbpos (by norm_num)
  have hEhalf : canonicalBufferedRadius W / 8 <= (2 : NNReal)⁻¹ := by
    calc
      canonicalBufferedRadius W / 8 <= canonicalBufferedRadius W :=
        div_le_self (show 0 <= canonicalBufferedRadius W from bot_le)
          (by norm_num)
      _ <= (2 : NNReal)⁻¹ :=
        hbufferedSixteenth.trans (by
          simpa only [one_div] using
            (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
              (show (2 : NNReal) <= 16 by norm_num)))
  have hsupport : forall k,
      (E.family.tubes k).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
    exact canonicalBufferedGlobalUnitCoarseDatum_contained_in_unit_ball
      D hD Cmulti Sseq W hepsilonW hepsilonWHalf hbufferedSixteenth
  have hscaledOne : (1 : ENNReal) <= 128 * CKT := by
    calc
      (1 : ENNReal) <= 128 := by norm_num
      _ = 128 * 1 := by norm_num
      _ <= 128 * CKT :=
        mul_le_mul_of_nonneg_left hCKTone (by norm_num)
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hEKT : IsKatzTao (128 * CKT) E.family.bodyFamily := by
    exact canonicalBufferedGlobalUnitCoarseDatum_isKatzTao
      D hD Cmulti Sseq W hepsilonW hepsilonWHalf hbufferedSixteenth
        hKTEvery
  have hEdensity :
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^
          sourceDensityEta) <= E.shading.shadingDensity :=
    hdensityPower.trans
      (canonicalBufferedGlobalUnitCoarseDatum_density_lower
        D hD Cmulti Sseq W hepsilonW hepsilonWHalf hfine
          hbufferedSixteenth)
  have hEdelta0 : (canonicalBufferedRadius W / 8) / 8 <= delta0 := by
    rw [canonicalBufferedGlobal_doubleEighthScale_eq D Cmulti Sseq W]
    exact hdelta0
  have houter := averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS
    hKTP E hEpos hEhalf hsupport hscaledOne hscaledFinite hEKT
      hsourceEta hCpower hepsilon0 htailEta hconstantEta htargetEta
      hdensityAbsorbEta hcoefficientAbsorbEta hfreshAbsorbEta
      hcardAbsorbEta hscaleAbsorbEta hbeta0 hbeta1 hEdensity
      hdensityBudget hcoefficientBudget hsmall hEdelta0
  rw [canonicalBufferedGlobalUnitCoarseDatum_averageMultiplicity
    D Cmulti Sseq W hD.delta_pos hepsilonW hepsilonWHalf] at houter
  simpa only [E, G, canonicalBufferedGlobalFullCoarseDatum_card] using houter

#print axioms
  canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_generalized

end Witness
end
end Family8CanonicalBufferedGlobalGeneralizedOuterV1
