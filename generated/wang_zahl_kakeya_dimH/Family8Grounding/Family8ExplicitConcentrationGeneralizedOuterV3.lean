import Family8Grounding.Family8ExplicitConcentrationGeneralizedReturnV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExplicitConcentrationGeneralizedOuterV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoSamplingMultiplicityV1
open Family8FrostmanOneFromPointwisePackingV1
open Family8ExplicitConcentrationSamplingFreshKatzTaoV1
open Family8ExplicitConcentrationGeneralizedReturnV1

noncomputable section

/-!
# Branch-free generalized Katz--Tao return

The complementary small-cardinality branch uses only the pointwise
multiplicity cap, so it does not require source admissibility.  Combining it
with fresh selection removes the final cardinality branch from the API.
-/

theorem averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_card_lt_samplingMultiplicity
    {beta eta : Real} {delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (heta0 : 0 ≤ eta) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hCard : Fintype.card iota <
      explicitConcentrationSamplingMultiplicity C) :
    D.shading.averageMultiplicity ≤
      generalizedKatzTaoMultiplicityRHS delta C (Fintype.card iota)
        eta beta := by
  let d : ENNReal := (delta : ENNReal)
  let N : ENNReal := (Fintype.card iota : ENNReal)
  have hNRealC : (Fintype.card iota : Real) < C.toReal := by
    exact Nat.lt_ceil.mp (by
      simpa only [explicitConcentrationSamplingMultiplicity,
        katzTaoSamplingMultiplicity] using hCard)
  have hNC : N ≤ C := by
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hCfinite).mp
    change (Fintype.card iota : Real) < C.toReal
    exact hNRealC
  have hOneSub : 0 ≤ 1 - beta := by linarith
  have hNpow : N ^ (1 - beta) ≤ C ^ (1 - beta) :=
    ENNReal.rpow_le_rpow hNC hOneSub
  have hNfactor : N = N ^ (1 - beta) * N ^ beta := by
    calc
      N = N ^ (1 : Real) := (ENNReal.rpow_one N).symm
      _ = N ^ ((1 - beta) + beta) := by congr 1; ring
      _ = N ^ (1 - beta) * N ^ beta :=
        ENNReal.rpow_add_of_nonneg (1 - beta) beta hOneSub hbeta0
  have hlossOne : 1 ≤ d ^ (-eta) := by
    dsimp only [d]
    rw [← ENNReal.coe_rpow_of_ne_zero hdeltaPos.ne' (-eta)]
    exact_mod_cast NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdeltaPos (hdeltaHalf.trans (by norm_num)) (neg_nonpos.mpr heta0)
  have havg : D.shading.averageMultiplicity ≤ N := by
    simpa only [N] using averageMultiplicity_le_indexCard D.shading
  unfold generalizedKatzTaoMultiplicityRHS
  change D.shading.averageMultiplicity ≤
    d ^ (-eta) * C ^ (1 - beta) * N ^ beta
  calc
    D.shading.averageMultiplicity ≤ N := havg
    _ = N ^ (1 - beta) * N ^ beta := hNfactor
    _ ≤ C ^ (1 - beta) * N ^ beta := mul_le_mul_left hNpow _
    _ = 1 * (C ^ (1 - beta) * N ^ beta) := by simp
    _ ≤ d ^ (-eta) * (C ^ (1 - beta) * N ^ beta) :=
      mul_le_mul_left hlossOne _
    _ = d ^ (-eta) * C ^ (1 - beta) * N ^ beta := by rw [mul_assoc]

theorem averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS
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
    (hepsilon0 : 0 ≤ epsilon)
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
    (hdelta0 : delta / 8 ≤ delta0) :
    D.shading.averageMultiplicity ≤
      generalizedKatzTaoMultiplicityRHS delta C (Fintype.card iota)
        ((epsilon + beta * (tailEta + constantEta) + cardAbsorbEta) +
          (tailEta + constantEta + freshAbsorbEta) + scaleAbsorbEta) beta := by
  by_cases hkCard : explicitConcentrationSamplingMultiplicity C ≤
      Fintype.card iota
  · exact
      Family8ExplicitConcentrationGeneralizedReturnV1.averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_samplingBranch
        hKTP D hdeltaPos hdeltaHalf hsupport hCone hCfinite hKT
          hsourceEta hCpower htailEta hconstantEta htargetEta
          hdensityAbsorbEta hcoefficientAbsorbEta hfreshAbsorbEta
          hcardAbsorbEta hscaleAbsorbEta hbeta0 hbeta1 hdensity
          hdensityBudget hcoefficientBudget hsmall hkCard hdelta0
  · have heta0 : 0 ≤
        (epsilon + beta * (tailEta + constantEta) + cardAbsorbEta) +
          (tailEta + constantEta + freshAbsorbEta) + scaleAbsorbEta := by
      have hq0 : 0 ≤ tailEta + constantEta := by linarith
      have hbetaq0 : 0 ≤ beta * (tailEta + constantEta) :=
        mul_nonneg hbeta0 hq0
      linarith
    exact
      averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_card_lt_samplingMultiplicity
        D hdeltaPos hdeltaHalf hCfinite heta0 hbeta0 hbeta1
          (Nat.lt_of_not_ge hkCard)

#print axioms
  averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_card_lt_samplingMultiplicity
#print axioms averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS

end
end Family8ExplicitConcentrationGeneralizedOuterV3
