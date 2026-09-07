import Family8Grounding.Family8StickySelectedFiberLowCFStrictMiddleV2
import Family8Grounding.Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
import Family8Grounding.Family8StickySelectedFiberLowCFPowerBudgetsV2
import Mathlib.Tactic

/-!
# LongCore-oriented selected low-CF strict middle endpoint

The selected count is bounded by its full parent fibre, and the literal factor four is absorbed by the long-interval relative power.  Thus only source-side power comparisons and standard ParameterLadder exponent conditions remain.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFLongMiddleEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickySelectedFiberLowCFPowerBudgetsV2
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open Family8StickySelectedFiberLowCFStrictMiddleV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho globalDelta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The low-CF branch reaches the exact literal `hMiddle` conclusion from
source-side power comparisons only. -/
theorem four_mul_selectedFiberSourceAverage_le_longMiddle_of_sourcePowers
    {frostmanBeta frostmanEpsilon frostmanEta gamma : Real}
    {p a kappa globalEta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower L : ENNReal}
    (hlowerTop : lower ≠ ∞) (hLTop : L ≠ ∞)
    (hLow : IsFrostmanIn (lower * (16 * L))
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q))
    (K : ENNReal)
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 ≤ delta0)
    (hadmissible :
      (restrictActualTubeDatum
        (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne q)) selected).IsAdmissible)
    (hcard :
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower L) *
          (selected.card : ENNReal))
    (hmass :
      (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
        (stickyFiberContractedJohnProxyDatum
          S Y hrho hrhoOne q)).shading.shadingMass ≤
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower L) *
          (restrictActualTubeDatum
            (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne q)) selected).shading.shadingMass)
    (hp : 0 < p) (ha : 0 < a)
    (hsmall : contractedJohnProxyRadius delta rho / 8 ≤
      contractedJohnSourcePowerEndpointThreshold a)
    (hcardEnvelopePower :
      selectedFiberLowCFCardEnvelope S q selected lower L ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-p)))
    (hsourceDensityPower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          frostmanEta) ≤
        (((stickyFiberSourceShading S Y q.1).shadingDensity / 93312 / 128) /
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-(p + a)))))
    (hbasePower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 * p + a))) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-frostmanEta)) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              2 / 2)))
    (hselected : selected.Nonempty)
    (hparentCount : (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
      K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))))
    {absorbExp : Real}
    (hglobalDeltaOne : globalDelta ≤ 1)
    (hK0 : K ≠ 0) (hKTop : K ≠ ∞)
    (habsorbExp : 0 < absorbExp)
    (hratioSmall : delta / rho ≤
      contractedJohnMiddleFourActualPowerThreshold
        K frostmanEpsilon frostmanBeta gamma (p + a) absorbExp)
    (hratioDelta : (((delta / rho : NNReal) : ENNReal)) ≤
      (globalDelta : ENNReal) ^ (frostmanEpsilon ^ 2))
    (hnet : 0 ≤
      contractedJohnMiddleRatioGain
        frostmanEpsilon frostmanBeta gamma (p + a) kappa - absorbExp)
    (hbudget : 10 * globalEta ≤
      frostmanEpsilon ^ 2 *
        (contractedJohnMiddleRatioGain
          frostmanEpsilon frostmanBeta gamma (p + a) kappa - absorbExp))
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta) :
    4 * (stickyFiberSourceShading S Y q.1).averageMultiplicity ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          delta rho selected.card gamma := by
  have hselectedCardFull :
      (selected.card : ENNReal) ≤
        (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) := by
    exact_mod_cast (Finset.card_le_univ selected)
  have hcount : (selected.card : ENNReal) ≤
      K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))) :=
    hselectedCardFull.trans hparentCount
  have hratioPos : 0 < delta / rho := div_pos hdelta hrho
  have habsorbRaw :=
    four_mul_fixed_mul_ratioGain_le_globalTenEta
      (delta := globalDelta) (q := delta / rho)
      (K := K) (stoppingEpsilon := frostmanEpsilon)
      (beta := frostmanBeta) (gamma := gamma)
      (lossExp := p + a) (kappa := kappa)
      (absorbExp := absorbExp) (eta := globalEta)
      hglobalDeltaOne hratioPos hK0 hKTop habsorbExp hratioSmall
        hratioDelta hnet hbudget
  have habsorb :
      4 *
          (contractedJohnMiddleActualFixedCoefficient
              K frostmanEpsilon frostmanBeta gamma (p + a) *
            (((delta : ENNReal) / (rho : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma (p + a) kappa)) ≤
        (globalDelta : ENNReal) ^ (10 * globalEta) := by
    simpa only [ENNReal.coe_div hrho.ne'] using habsorbRaw
  obtain ⟨hdensityBudget, hbaseBudget, hlossPower⟩ :=
    selectedFiberLowCF_density_base_loss_budgets
      S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho q selected lower L
        hp ha hsmall hcardEnvelopePower hsourceDensityPower hbasePower
  exact four_mul_selectedFiberSourceAverage_le_strictMiddle
    hF S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho q selected
      hlowerTop hLTop hLow K hdelta0 hadmissible hcard hmass
      hdensityBudget hbaseBudget hlossPower hselected hcount
      hbetaTwo hgammaTwo hgap habsorb

#print axioms
  four_mul_selectedFiberSourceAverage_le_longMiddle_of_sourcePowers

end
end Family8StickySelectedFiberLowCFLongMiddleEndpointV1
