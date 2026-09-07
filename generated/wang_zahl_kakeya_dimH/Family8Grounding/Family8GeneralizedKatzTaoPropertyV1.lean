import Family8Grounding.Family8GeneralizedKatzTaoSamplingNumericsV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8GeneralizedKatzTaoPropertyV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedKatzTaoSamplingNumericsV1
open Family8KatzTaoSamplingDensityBudgetV1
open Family8KatzTaoJohnCoefficientBudgetV1
open Family8PolynomialJohnFrameBoxCardPowerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Quantifier-level generalized Katz--Tao estimate

This file turns the branch-free finite-sampling estimate into the full
quantified generalized Katz--Tao statement.  All losses are allocated from
the requested `epsilon`; the four small-scale conditions are absorbed into
one explicit terminal scale.
-/

/-- The quantified generalized Katz--Tao conclusion used by the multiscale
argument.  The concentration parameter is the literal power appearing in
the source hypotheses. -/
def GeneralizedKatzTaoAtParameters
    (beta epsilon eta : Real) (delta0 : NNReal) : Prop :=
  ∀ (delta : NNReal) (iota : Type) [Fintype iota] [DecidableEq iota]
      (D : ActualTubeDatum delta iota),
    D.IsAdmissible →
    delta ≤ delta0 →
    KatzTaoHypotheses D eta →
    D.shading.averageMultiplicity ≤
      generalizedKatzTaoMultiplicityRHS delta
        ((delta : ENNReal) ^ (-eta)) (Fintype.card iota) epsilon beta

/-- On scales at most one, hypotheses with a smaller loss exponent imply
hypotheses with a larger loss exponent. -/
theorem katzTaoHypotheses_of_eta_le
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {etaSmall etaLarge : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (heta : etaSmall ≤ etaLarge)
    (hsmall : KatzTaoHypotheses D etaSmall) :
    KatzTaoHypotheses D etaLarge := by
  have hdOne : (delta : ENNReal) ≤ 1 := by
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  constructor
  · exact
      (ENNReal.rpow_le_rpow_of_exponent_ge hdOne heta).trans hsmall.1
  · exact hsmall.2.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith))

/-- A Katz--Tao parameter theorem can be used with any smaller hypothesis
exponent, without changing its multiplicity conclusion. -/
theorem katzTaoAtParameters_of_eta_le
    {beta epsilon etaSmall etaLarge : Real} {delta0 : NNReal}
    (h : KatzTaoAtParameters beta epsilon etaLarge delta0)
    (heta : etaSmall ≤ etaLarge) :
    KatzTaoAtParameters beta epsilon etaSmall delta0 := by
  intro delta iota _ _ D hD hdelta hsmall
  exact h delta iota D hD hdelta
    (katzTaoHypotheses_of_eta_le D hD heta hsmall)

/-- Increasing the displayed loss exponent only enlarges the generalized
Katz--Tao right-hand side on admissible scales. -/
theorem generalizedKatzTaoMultiplicityRHS_mono_epsilon
    {delta : NNReal} {C : ENNReal} {tubeCount : Nat}
    {epsilonSmall epsilonLarge beta : Real}
    (hdeltaOne : delta ≤ 1) (hepsilon : epsilonSmall ≤ epsilonLarge) :
    generalizedKatzTaoMultiplicityRHS delta C tubeCount epsilonSmall beta ≤
      generalizedKatzTaoMultiplicityRHS delta C tubeCount epsilonLarge beta := by
  have hdOne : (delta : ENNReal) ≤ 1 := by exact_mod_cast hdeltaOne
  unfold generalizedKatzTaoMultiplicityRHS
  exact mul_le_mul'
    (mul_le_mul'
      (ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith))
      (le_refl _))
    (le_refl _)

/-- The single terminal scale used by the quantifier-level generalized KKT
theorem. -/
def generalizedKatzTaoPropertyThreshold
    (sourceDelta0 : NNReal) (sourceEta epsilon : Real) : NNReal :=
  min sourceDelta0
    (min
      (katzTaoSamplingDensityThreshold (2 * sourceEta + 2 * sourceEta)
        sourceEta)
      (min
        (johnCoefficientThreshold johnCataloguePolynomialCostConstant
          (15 + sourceEta) (2 * sourceEta) (2 * sourceEta))
        (finiteConstantSmallDeltaThreshold 4 (epsilon / 4))))

theorem generalizedKatzTaoPropertyThreshold_pos
    {sourceDelta0 : NNReal} {sourceEta epsilon : Real}
    (hsourceDelta0 : 0 < sourceDelta0) :
    0 < generalizedKatzTaoPropertyThreshold
      sourceDelta0 sourceEta epsilon := by
  rw [generalizedKatzTaoPropertyThreshold, lt_min_iff, lt_min_iff,
    lt_min_iff]
  exact ⟨hsourceDelta0,
    katzTaoSamplingDensityThreshold_pos _ _,
    johnCoefficientThreshold_pos _ _ _ _,
    finiteConstantSmallDeltaThreshold_pos _ _⟩

/-- Full, branch-free generalized Katz--Tao theorem derived from the actual
`KatzTaoProperty`. -/
theorem KatzTaoProperty.exists_generalizedKatzTao_parameters
    {beta epsilon : Real} (hKT : KatzTaoProperty beta)
    (hepsilon : 0 < epsilon) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        GeneralizedKatzTaoAtParameters beta epsilon eta delta0 := by
  have hepsilonQuarter : 0 < epsilon / 4 := by positivity
  obtain ⟨etaRaw, deltaRaw, hetaRaw, hdeltaRaw, hdeltaRawHalf, hRaw⟩ :=
    hKT.exists_parameters hepsilonQuarter
  let eta : Real := min (etaRaw / 8) (epsilon / 16)
  have heta : 0 < eta := by
    change 0 < min (etaRaw / 8) (epsilon / 16)
    rw [lt_min_iff]
    constructor <;> positivity
  have heta0 : 0 ≤ eta := heta.le
  have hfourEtaRaw : 2 * eta + 2 * eta ≤ etaRaw := by
    have hle : eta ≤ etaRaw / 8 := min_le_left _ _
    linarith
  have hfourEtaEpsilon : 2 * eta + 2 * eta ≤ epsilon / 4 := by
    have hle : eta ≤ epsilon / 16 := min_le_right _ _
    linarith
  have hRawSmall :
      KatzTaoAtParameters beta (epsilon / 4)
        (2 * eta + 2 * eta) deltaRaw :=
    katzTaoAtParameters_of_eta_le hRaw hfourEtaRaw
  let delta0 : NNReal :=
    generalizedKatzTaoPropertyThreshold deltaRaw eta epsilon
  have hdelta0 : 0 < delta0 := by
    exact generalizedKatzTaoPropertyThreshold_pos hdeltaRaw
  have hdelta0Raw : delta0 ≤ deltaRaw := by
    exact min_le_left _ _
  have hdelta0Half : delta0 ≤ (2 : NNReal)⁻¹ :=
    hdelta0Raw.trans hdeltaRawHalf
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_⟩
  intro delta iota _ _ D hD hdelta hHypotheses
  have hdeltaRaw' : delta ≤ deltaRaw := hdelta.trans hdelta0Raw
  have hdeltaDensity :
      delta ≤ katzTaoSamplingDensityThreshold
        (2 * eta + 2 * eta) eta := by
    exact hdelta.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaCoefficient :
      delta ≤ johnCoefficientThreshold johnCataloguePolynomialCostConstant
        (15 + eta) (2 * eta) (2 * eta) := by
    exact hdelta.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaFactor :
      delta ≤ finiteConstantSmallDeltaThreshold 4 (epsilon / 4) := by
    exact hdelta.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hgap : 0 < 2 * eta + 2 * eta - 2 * eta := by linarith
  have hsource :=
    averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_katzTaoHypotheses
      hRawSmall D hD hdeltaRaw' heta0 hepsilonQuarter.le
        (by positivity : 0 < 2 * eta) (by positivity : 0 < 2 * eta)
        hgap hbeta0 hbeta1 hepsilonQuarter hdeltaDensity
        hdeltaCoefficient hdeltaFactor hHypotheses
  have hbetaLoss : beta * (2 * eta + 2 * eta) ≤ epsilon / 4 := by
    calc
      beta * (2 * eta + 2 * eta) ≤ 1 * (2 * eta + 2 * eta) := by
        exact mul_le_mul_of_nonneg_right hbeta1 (by positivity)
      _ ≤ epsilon / 4 := by simpa using hfourEtaEpsilon
  have hloss :
      epsilon / 4 + beta * (2 * eta + 2 * eta) + epsilon / 4 ≤
        epsilon := by
    linarith
  have hdeltaOne : delta ≤ 1 := hD.delta_le_half.trans (by norm_num)
  exact hsource.trans
    (generalizedKatzTaoMultiplicityRHS_mono_epsilon
      hdeltaOne hloss)

#print axioms katzTaoHypotheses_of_eta_le
#print axioms katzTaoAtParameters_of_eta_le
#print axioms generalizedKatzTaoMultiplicityRHS_mono_epsilon
#print axioms generalizedKatzTaoPropertyThreshold_pos
#print axioms KatzTaoProperty.exists_generalizedKatzTao_parameters

end
end Family8GeneralizedKatzTaoPropertyV1
