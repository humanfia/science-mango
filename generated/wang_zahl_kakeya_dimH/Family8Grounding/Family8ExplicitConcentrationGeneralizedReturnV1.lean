import Family8Grounding.Family8ExplicitConcentrationAutomaticFreshKatzTaoV1
import Family8Grounding.Family8ExplicitConcentrationFreshReturnNormalizationV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExplicitConcentrationGeneralizedReturnV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorPolynomialJohnKatzTaoV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8KatzTaoSamplingMultiplicityV1
open Family8KatzTaoJohnCoefficientBudgetV1
open Family8ScaleContainedB2FreshKatzTaoEndpointV1
open Family8ExplicitConcentrationSamplingFreshKatzTaoV1
open Family8ExplicitConcentrationAutomaticFreshKatzTaoV1
open Family8ExplicitConcentrationFreshReturnNormalizationV2
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Complete generalized return for the nontrivial sampling branch

The sampled and fresh-selected cardinalities are eliminated here.  The
conclusion is the native generalized Katz--Tao right-hand side for the
original source datum and original scale.
-/

def explicitConcentrationGeneralizedReturnThreshold
    (sourceEta tailEta constantEta densityAbsorbEta coefficientAbsorbEta
      freshAbsorbEta cardAbsorbEta scaleAbsorbEta epsilon beta : Real) :
    NNReal :=
  min
    (explicitConcentrationAutomaticFreshThreshold sourceEta tailEta
      constantEta densityAbsorbEta coefficientAbsorbEta)
    (min
      (explicitConcentrationFreshReturnLossThreshold freshAbsorbEta)
      (min
        (finiteConstantSmallDeltaThreshold 4 cardAbsorbEta)
        (explicitConcentrationFreshReturnScaleThreshold
          (epsilon + beta * (tailEta + constantEta) + cardAbsorbEta)
          scaleAbsorbEta)))

theorem explicitConcentrationGeneralizedReturnThreshold_pos
    (sourceEta tailEta constantEta densityAbsorbEta coefficientAbsorbEta
      freshAbsorbEta cardAbsorbEta scaleAbsorbEta epsilon beta : Real) :
    0 < explicitConcentrationGeneralizedReturnThreshold sourceEta tailEta
      constantEta densityAbsorbEta coefficientAbsorbEta freshAbsorbEta
      cardAbsorbEta scaleAbsorbEta epsilon beta := by
  unfold explicitConcentrationGeneralizedReturnThreshold
  exact lt_min
    (explicitConcentrationAutomaticFreshThreshold_pos _ _ _ _ _)
    (lt_min
      (explicitConcentrationFreshReturnLossThreshold_pos _)
      (lt_min
        (finiteConstantSmallDeltaThreshold_pos _ _)
        (explicitConcentrationFreshReturnScaleThreshold_pos _ _)))

/-- The nontrivial branch `ceil(C) ≤ #T`, with every sampling, fresh, and
fixed-scale loss returned to the original generalized right-hand side. -/
theorem averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_samplingBranch
    {beta epsilon targetEta sourceEta tailEta constantEta
      sourceDensityEta densityAbsorbEta coefficientAbsorbEta
      freshAbsorbEta cardAbsorbEta scaleAbsorbEta : Real}
    {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hKTP : KatzTaoAtParameters beta epsilon targetEta delta0)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsupport : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal} (hCone : 1 ≤ C) (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hsourceEta : 0 ≤ sourceEta)
    (hCpower : C ≤ (delta : ENNReal) ^ (-sourceEta))
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (htargetEta : 0 ≤ targetEta)
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hfreshAbsorbEta : 0 < freshAbsorbEta)
    (hcardAbsorbEta : 0 < cardAbsorbEta)
    (hscaleAbsorbEta : 0 < scaleAbsorbEta)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hdensity : (delta : ENNReal) ^ sourceDensityEta ≤
      D.shading.shadingDensity)
    (hdensityBudget :
      2 * (tailEta + constantEta) + sourceDensityEta +
          densityAbsorbEta ≤ targetEta)
    (hcoefficientBudget :
      tailEta + constantEta + coefficientAbsorbEta ≤ targetEta)
    (hsmall : delta ≤
      explicitConcentrationGeneralizedReturnThreshold sourceEta tailEta
        constantEta densityAbsorbEta coefficientAbsorbEta freshAbsorbEta
        cardAbsorbEta scaleAbsorbEta epsilon beta)
    (hkCard : explicitConcentrationSamplingMultiplicity C ≤
      Fintype.card iota)
    (hdelta0 : delta / 8 ≤ delta0) :
    D.shading.averageMultiplicity ≤
      generalizedKatzTaoMultiplicityRHS delta C (Fintype.card iota)
        ((epsilon + beta * (tailEta + constantEta) + cardAbsorbEta) +
          (tailEta + constantEta + freshAbsorbEta) + scaleAbsorbEta) beta := by
  let q : Real := tailEta + constantEta
  let k : Nat := explicitConcentrationSamplingMultiplicity C
  let Csample : ENNReal :=
    explicitConcentrationSampleKatzTaoConstant delta C
  let tail : ENNReal :=
    ENNReal.ofReal (explicitConcentrationSamplingTail delta C)
  have hsmallAutomatic : delta ≤
      explicitConcentrationAutomaticFreshThreshold sourceEta tailEta
        constantEta densityAbsorbEta coefficientAbsorbEta :=
    hsmall.trans (min_le_left _ _)
  obtain ⟨sampledCard, selectedCard, hscaledSample, hselectedCard,
      hsourceBound⟩ :=
    exists_sample_and_fresh_katzTao_of_source_power
      hKTP D hdeltaPos hdeltaHalf hsupport hCone hCfinite hKT
        hsourceEta hCpower htailEta hconstantEta htargetEta
        hdensityAbsorbEta hcoefficientAbsorbEta hdensity hdensityBudget
        hcoefficientBudget hsmallAutomatic hkCard hdelta0
  have hdeltaOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hqPos : 0 < q := by
    dsimp only [q]
    linarith
  have hCsamplePower : Csample ≤
      (delta : ENNReal) ^ (-q) := by
    dsimp only [Csample, q, explicitConcentrationSampleKatzTaoConstant,
      explicitConcentrationSamplingTail,
      explicitConcentrationSamplingMultiplicity]
    exact automaticPolynomialJohn_coefficient_le_rpow
      hdeltaPos hdeltaOne hsourceEta htailEta hconstantEta hCfinite
        hCone hCpower
        (hsmallAutomatic.trans (min_le_left _ _))
  have hCsampleFinite : Csample ≠ ∞ := by
    simpa only [Csample] using
      explicitConcentrationSampleKatzTaoConstant_ne_top delta C
  have htailOne : (1 : ENNReal) ≤ tail := by
    dsimp only [tail, explicitConcentrationSamplingTail,
      explicitConcentrationSamplingMultiplicity]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (one_le_polynomialJohnTailParameter delta
        (katzTaoSamplingMultiplicity C))
  have hJohnOne : (1 : ENNReal) ≤ johnCatalogueVolumeConstant := by
    norm_num [johnCatalogueVolumeConstant]
  have hCsampleOne : (1 : ENNReal) ≤ Csample := by
    calc
      (1 : ENNReal) = 1 * 1 := by simp
      _ ≤ tail * johnCatalogueVolumeConstant :=
        mul_le_mul' htailOne hJohnOne
      _ = Csample := by rfl
  have htailCsample : tail ≤ Csample := by
    calc
      tail = tail * 1 := by simp
      _ ≤ tail * johnCatalogueVolumeConstant :=
        mul_le_mul' le_rfl hJohnOne
      _ = Csample := by rfl
  have hdeltaEightPos : 0 < delta / 8 := div_pos hdeltaPos (by norm_num)
  have hscalePowerNN :
      delta ^ (-q) ≤ (delta / 8) ^ (-q) := by
    exact NNReal.rpow_le_rpow_of_nonpos hdeltaEightPos
      (div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8))
      (neg_nonpos.mpr hqPos.le)
  have hscalePower :
      (delta : ENNReal) ^ (-q) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-q) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdeltaPos.ne' (-q),
      ← ENNReal.coe_rpow_of_ne_zero hdeltaEightPos.ne' (-q)]
    exact ENNReal.coe_le_coe.mpr hscalePowerNN
  have hselectedCast : (selectedCard : ENNReal) ≤ sampledCard := by
    exact_mod_cast hselectedCard
  have hscaledSelected :
      (k : ENNReal) * (selectedCard : ENNReal) ≤
        (((delta / 8 : NNReal) : ENNReal) ^ (-q)) *
          (Fintype.card iota : ENNReal) := by
    calc
      (k : ENNReal) * (selectedCard : ENNReal) ≤
          (k : ENNReal) * (sampledCard : ENNReal) :=
        mul_le_mul' le_rfl hselectedCast
      _ ≤ tail * (Fintype.card iota : ENNReal) := by
        simpa only [k, tail] using hscaledSample
      _ ≤ (((delta / 8 : NNReal) : ENNReal) ^ (-q)) *
          (Fintype.card iota : ENNReal) :=
        mul_le_mul' (htailCsample.trans (hCsamplePower.trans hscalePower))
          le_rfl
  have hk : 0 < k := by
    exact katzTaoSamplingMultiplicity_pos (zero_lt_one.trans_le hCone)
      hCfinite
  have hkC : (k : ENNReal) ≤ 2 * C := by
    exact katzTaoSamplingMultiplicity_coe_le_two_mul hCone hCfinite
  have hfreshLoss :
      (sourceKatzTaoFreshLoss Csample : ENNReal) ≤
        (delta : ENNReal) ^ (-(q + freshAbsorbEta)) := by
    apply sourceKatzTaoFreshLoss_coe_le_delta_negativePower
      hdeltaPos hCsampleFinite hCsampleOne hCsamplePower hfreshAbsorbEta
    exact hsmall.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hcardSmall : delta / 8 ≤
      finiteConstantSmallDeltaThreshold 4 cardAbsorbEta := by
    exact (div_le_self (show 0 ≤ delta from bot_le)
      (by norm_num : (1 : NNReal) ≤ 8)).trans
        (hsmall.trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have hscaleSmall : delta ≤
      explicitConcentrationFreshReturnScaleThreshold
        (epsilon + beta * q + cardAbsorbEta) scaleAbsorbEta := by
    simpa only [q] using hsmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  exact hsourceBound.trans (by
    simpa only [k, q, Csample] using
      returnedFreshSample_le_generalizedKatzTaoMultiplicityRHS
        hdeltaPos hk hbeta0 hbeta1 hcardAbsorbEta hkC hscaledSelected
          hcardSmall hfreshLoss hscaleAbsorbEta hscaleSmall)

#print axioms explicitConcentrationGeneralizedReturnThreshold_pos
#print axioms
  averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_samplingBranch

end
end Family8ExplicitConcentrationGeneralizedReturnV1
