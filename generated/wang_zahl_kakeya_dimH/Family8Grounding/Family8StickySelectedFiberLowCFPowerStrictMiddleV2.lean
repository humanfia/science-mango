import Family8Grounding.Family8StickySelectedFiberLowCFStrictMiddleV2
import Family8Grounding.Family8StickySelectedFiberLowCFPowerBudgetsV2
import Mathlib.Tactic

/-!
# Source-power form of the literal selected low-CF strict middle endpoint, V2

V1 omitted the namespace exporting the active subtype family.  In this corrected successor the normalized-proxy density, base, and loss budgets are discharged by the
source-power producer before invoking the exact strict middle consumer.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFPowerStrictMiddleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
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
theorem four_mul_selectedFiberSourceAverage_le_strictMiddle_of_sourcePowers
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
    (hcount : (selected.card : ENNReal) ≤
      K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))))
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta)
    (habsorb :
      4 *
          (contractedJohnMiddleActualFixedCoefficient
              K frostmanEpsilon frostmanBeta gamma (p + a) *
            (((delta : ENNReal) / (rho : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma (p + a) kappa)) ≤
        (globalDelta : ENNReal) ^ (10 * globalEta)) :
    4 * (stickyFiberSourceShading S Y q.1).averageMultiplicity ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          delta rho selected.card gamma := by
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
  four_mul_selectedFiberSourceAverage_le_strictMiddle_of_sourcePowers

end
end Family8StickySelectedFiberLowCFPowerStrictMiddleV2
