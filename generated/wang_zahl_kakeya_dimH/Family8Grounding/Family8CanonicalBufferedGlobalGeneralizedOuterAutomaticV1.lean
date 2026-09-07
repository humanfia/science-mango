import Family8Grounding.Family8CanonicalBufferedGlobalGeneralizedOuterV1
import Family8Grounding.Family8ExplicitConcentrationCanonicalScalarBudgetsV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalGeneralizedOuterAutomaticV1

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
open Family8ExplicitConcentrationGeneralizedReturnV1
open Family8ExplicitConcentrationCanonicalScalarBudgetsV1
open Family8CanonicalBufferedGlobalGeneralizedOuterV1.Witness

noncomputable section

/-!
# Automatic fixed-scalar canonical generalized outer estimate

The one radius threshold below simultaneously absorbs the Katz--Tao factor
`128` created by the first normalization and supplies the normalized
full-shading density floor `1 / 128`.  Thus no density or coefficient
inequality is exposed by this canonical successor.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilonW : Real} {etaW : Nat -> Real}

theorem canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_generalized_auto
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
    (hsourceEta : 0 < sourceEta)
    (hsourceDensityEta : 0 < sourceDensityEta)
    (hepsilon0 : 0 <= epsilon)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (htargetEta : 0 <= targetEta)
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hfreshAbsorbEta : 0 < freshAbsorbEta)
    (hcardAbsorbEta : 0 < cardAbsorbEta)
    (hscaleAbsorbEta : 0 < scaleAbsorbEta)
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1)
    (hdensityBudget :
      2 * (tailEta + constantEta) + sourceDensityEta +
          densityAbsorbEta <= targetEta)
    (hcoefficientBudget :
      tailEta + constantEta + coefficientAbsorbEta <= targetEta)
    (hscalarSmall : canonicalBufferedRadius W / 8 <=
      canonicalOuterScalarThreshold CKT sourceEta sourceDensityEta)
    (houterSmall : canonicalBufferedRadius W / 8 <=
      explicitConcentrationGeneralizedReturnThreshold sourceEta tailEta
        constantEta densityAbsorbEta coefficientAbsorbEta freshAbsorbEta
        cardAbsorbEta scaleAbsorbEta epsilon beta)
    (hdelta0 : canonicalBufferedRadius W / 64 <= delta0) :
    (Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness.canonicalBufferedGlobalFullCoarseDatum
        D Cmulti Sseq W hD.delta_pos hepsilonW
          hepsilonWHalf).shading.averageMultiplicity <=
      generalizedKatzTaoMultiplicityRHS
        (canonicalBufferedRadius W / 8) (128 * CKT)
        (canonicalBufferedGlobalCover W hD.delta_pos
          hepsilonW hepsilonWHalf).activeCoarse.card
        ((epsilon + beta * (tailEta + constantEta) + cardAbsorbEta) +
          (tailEta + constantEta + freshAbsorbEta) + scaleAbsorbEta) beta := by
  have hbpos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hepsilonW
  have hrho : 0 < canonicalBufferedRadius W / 8 :=
    div_pos hbpos (by norm_num)
  have hCpower : 128 * CKT <=
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^
        (-sourceEta)) :=
    normalizedKatzTaoConstant_le_negativePower hrho hCKTfinite
      hsourceEta hscalarSmall
  have hdensityPower :
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^
        sourceDensityEta) <= (1 / 128 : ENNReal) :=
    densityPower_le_one_div_128 hrho hsourceDensityEta hscalarSmall
  exact
    canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_generalized
      hKTP D hD Cmulti Sseq W hepsilonW hepsilonWHalf hfine
        hbufferedSixteenth hCKTone hCKTfinite hKTEvery hsourceEta.le
        hCpower hepsilon0 htailEta hconstantEta htargetEta
        hdensityAbsorbEta hcoefficientAbsorbEta hfreshAbsorbEta
        hcardAbsorbEta hscaleAbsorbEta hbeta0 hbeta1 hdensityPower
        hdensityBudget hcoefficientBudget houterSmall hdelta0

#print axioms
  canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_generalized_auto

end Witness
end
end Family8CanonicalBufferedGlobalGeneralizedOuterAutomaticV1
