import Family8Grounding.Family8ExplicitConcentrationSamplingFreshKatzTaoV1
import Family8Grounding.Family8ExplicitConcentrationFreshPowerBudgetsV4
import Family8Grounding.Family8KatzTaoJohnCoefficientBudgetV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExplicitConcentrationAutomaticFreshKatzTaoV1

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
open Family8ExplicitConcentrationFreshPowerBudgetsV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Automatic scalar budgets for explicit-concentration fresh Katz--Tao

The polynomial-John coefficient controls both the sampled Katz--Tao
constant and its logarithmic tail.  The fresh conflict loss is then linear
in that same sampled constant.  Consequently the two scalar premises of the
fresh endpoint follow from one source density power and one uniform small
scale threshold.
-/

def explicitConcentrationAutomaticFreshThreshold
    (sourceEta tailEta constantEta densityAbsorbEta
      coefficientAbsorbEta : Real) : NNReal :=
  min
    (johnCoefficientThreshold johnCataloguePolynomialCostConstant
      (15 + sourceEta) tailEta constantEta)
    (min
      (explicitConcentrationFreshDensityThreshold densityAbsorbEta)
      (explicitConcentrationFreshCoefficientThreshold
        coefficientAbsorbEta))

theorem explicitConcentrationAutomaticFreshThreshold_pos
    (sourceEta tailEta constantEta densityAbsorbEta
      coefficientAbsorbEta : Real) :
    0 < explicitConcentrationAutomaticFreshThreshold sourceEta tailEta
      constantEta densityAbsorbEta coefficientAbsorbEta := by
  unfold explicitConcentrationAutomaticFreshThreshold
  exact lt_min
    (johnCoefficientThreshold_pos _ _ _ _)
    (lt_min
      (explicitConcentrationFreshDensityThreshold_pos densityAbsorbEta)
      (explicitConcentrationFreshCoefficientThreshold_pos
        coefficientAbsorbEta))

/-- The arbitrary-concentration, non-admissible source branch with both
fresh-selection scalar budgets discharged by explicit powers. -/
theorem exists_sample_and_fresh_katzTao_of_source_power
    {beta epsilon targetEta sourceEta tailEta constantEta
      sourceDensityEta densityAbsorbEta coefficientAbsorbEta : Real}
    {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hKTP : KatzTaoAtParameters beta epsilon targetEta delta0)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsupport : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal} (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hsourceEta : 0 <= sourceEta)
    (hCpower : C <= (delta : ENNReal) ^ (-sourceEta))
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (htargetEta : 0 <= targetEta)
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hdensity : (delta : ENNReal) ^ sourceDensityEta <=
      D.shading.shadingDensity)
    (hdensityBudget :
      2 * (tailEta + constantEta) + sourceDensityEta +
          densityAbsorbEta <= targetEta)
    (hcoefficientBudget :
      tailEta + constantEta + coefficientAbsorbEta <= targetEta)
    (hsmall : delta <=
      explicitConcentrationAutomaticFreshThreshold sourceEta tailEta
        constantEta densityAbsorbEta coefficientAbsorbEta)
    (hkCard : explicitConcentrationSamplingMultiplicity C <=
      Fintype.card iota)
    (hdelta0 : delta / 8 <= delta0) :
    exists sampledCard selectedCard : Nat,
      (explicitConcentrationSamplingMultiplicity C : ENNReal) *
          (sampledCard : ENNReal) <=
        ENNReal.ofReal (explicitConcentrationSamplingTail delta C) *
          (Fintype.card iota : ENNReal) ∧
      selectedCard <= sampledCard ∧
      D.shading.averageMultiplicity <=
        ((2 * explicitConcentrationSamplingMultiplicity C : Nat) : ENNReal) *
          (sourceKatzTaoFreshLoss
            (explicitConcentrationSampleKatzTaoConstant delta C) : ENNReal) *
          katzTaoMultiplicityRHS (delta / 8) selectedCard epsilon beta := by
  have hdeltaOne : delta <= 1 := hdeltaHalf.trans (by norm_num)
  let Csample := explicitConcentrationSampleKatzTaoConstant delta C
  let tail : ENNReal :=
    ENNReal.ofReal (explicitConcentrationSamplingTail delta C)
  have hCsamplePower : Csample <=
      (delta : ENNReal) ^ (-(tailEta + constantEta)) := by
    simpa only [Csample, explicitConcentrationSampleKatzTaoConstant,
      explicitConcentrationSamplingTail,
      explicitConcentrationSamplingMultiplicity] using
        automaticPolynomialJohn_coefficient_le_rpow
          hdeltaPos hdeltaOne hsourceEta htailEta hconstantEta
            hCfinite hCone hCpower
              (hsmall.trans (min_le_left _ _))
  have hCsampleFinite : Csample ≠ ∞ := by
    simpa only [Csample] using
      explicitConcentrationSampleKatzTaoConstant_ne_top delta C
  have htailOne : (1 : ENNReal) <= tail := by
    dsimp only [tail, explicitConcentrationSamplingTail,
      explicitConcentrationSamplingMultiplicity]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (one_le_polynomialJohnTailParameter delta
        (katzTaoSamplingMultiplicity C))
  have hJohnOne : (1 : ENNReal) <= johnCatalogueVolumeConstant := by
    norm_num [johnCatalogueVolumeConstant]
  have hCsampleOne : (1 : ENNReal) <= Csample := by
    calc
      (1 : ENNReal) = 1 * 1 := by simp
      _ <= tail * johnCatalogueVolumeConstant :=
        mul_le_mul' htailOne hJohnOne
      _ = Csample := by
        rfl
  have htailCsample : tail <= Csample := by
    calc
      tail = tail * 1 := by simp
      _ <= tail * johnCatalogueVolumeConstant :=
        mul_le_mul' le_rfl hJohnOne
      _ = Csample := by rfl
  have hdensityPower :
      ((((delta / 8 : NNReal) : ENNReal) ^ targetEta) *
          (128 * (sourceKatzTaoFreshLoss Csample : ENNReal))) *
        (32 * tail) <= D.shading.shadingDensity := by
    refine (explicitConcentration_fresh_density_power_budget
      hdeltaPos hdeltaOne htargetEta hCsampleFinite hCsampleOne
        htailCsample hCsamplePower hdensityAbsorbEta ?_ ?_).trans hdensity
    · exact hsmall.trans
        ((min_le_right _ _).trans (min_le_left _ _))
    · simpa only using hdensityBudget
  have hcoefficientPower :
      128 * Csample <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-targetEta) := by
    apply explicitConcentration_fresh_coefficient_power_budget
      hdeltaPos hdeltaOne htargetEta hCsamplePower
        hcoefficientAbsorbEta
    · exact hsmall.trans
        ((min_le_right _ _).trans (min_le_right _ _))
    · simpa only using hcoefficientBudget
  exact exists_sample_and_fresh_katzTao_of_explicit_concentration
    hKTP D hdeltaPos hdeltaHalf hsupport hCone hCfinite hKT hkCard
      hdelta0
      (by simpa only [Csample, tail] using hdensityPower)
      (by simpa only [Csample] using hcoefficientPower)

#print axioms explicitConcentrationAutomaticFreshThreshold_pos
#print axioms exists_sample_and_fresh_katzTao_of_source_power

end
end Family8ExplicitConcentrationAutomaticFreshKatzTaoV1
