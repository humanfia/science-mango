import Family8Grounding.Family8StickySelectedFiberLowCFFreshRetentionProducerV2
import Family8Grounding.Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3
import Family8Grounding.Family8StickySelectedFiberLowCFLongMiddleEndpointV1
import Mathlib.Tactic

/-!
# Fresh low-CF selected-fibre long-middle producer

The genuine fresh selector and the strict long-middle endpoint are composed
on the literal same selected subtype.  The selected-dependent card envelope
is discharged automatically from the full-fibre and low-barrier powers.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFFreshLongMiddleProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open Family8StickySelectedFiberLowCFLongMiddleEndpointV1
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho globalDelta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- At a fixed low-CF parent, the genuine fresh selector directly supplies
the literal long-middle estimate, with no selected-dependent scalar input. -/
theorem exists_fresh_selected_four_mul_sourceAverage_le_longMiddle
    {frostmanBeta frostmanEpsilon frostmanEta gamma : Real}
    {lowerExp cardExp a cardAbsorbExp kappa globalEta : Real}
    {delta0 : NNReal}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower : ENNReal} (hlowerTop : lower ≠ ∞)
    (hLow : IsFrostmanIn lower
      (S.fiberFamily q.1) (S.activeCoarseFamily q))
    (hcombined : 0 < lowerExp + cardExp)
    (ha : 0 < a) (hcardAbsorbExp : 0 < cardAbsorbExp)
    (hsmallFresh : contractedJohnProxyRadius delta rho / 8 ≤
      selectedParentLowCFFreshCardEnvelopePowerThreshold
        a cardAbsorbExp)
    (hlowerPower : lower ≤
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
        (-lowerExp)))
    (hfullCardPower :
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-cardExp)))
    (K : ENNReal)
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 ≤ delta0)
    (hsmallSource : contractedJohnProxyRadius delta rho / 8 ≤
      Family8StickyFiberContractedJohnSourcePowerEndpointV1.contractedJohnSourcePowerEndpointThreshold a)
    (hsourceDensityPower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          frostmanEta) ≤
        (((stickyFiberSourceShading S Y q.1).shadingDensity / 93312 / 128) /
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)))))
    (hbasePower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 * (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a))) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-frostmanEta)) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              2 / 2)))
    (hparentCount : (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
      K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))))
    {absorbExp : Real}
    (hglobalDeltaOne : globalDelta ≤ 1)
    (hK0 : K ≠ 0) (hKTop : K ≠ ∞)
    (habsorbExp : 0 < absorbExp)
    (hratioSmall : delta / rho ≤
      contractedJohnMiddleFourActualPowerThreshold
        K frostmanEpsilon frostmanBeta gamma
          ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
          absorbExp)
    (hratioDelta : (((delta / rho : NNReal) : ENNReal)) ≤
      (globalDelta : ENNReal) ^ (frostmanEpsilon ^ 2))
    (hnet : 0 ≤
      contractedJohnMiddleRatioGain
        frostmanEpsilon frostmanBeta gamma
          ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
          kappa - absorbExp)
    (hbudget : 10 * globalEta ≤
      frostmanEpsilon ^ 2 *
        (contractedJohnMiddleRatioGain
          frostmanEpsilon frostmanBeta gamma
            ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
            kappa - absorbExp))
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta) :
    ∃ selected : Finset {i // i ∈ S.fiber q.1},
      selected.Nonempty ∧
      4 * (stickyFiberSourceShading S Y q.1).averageMultiplicity ≤
        (globalDelta : ENNReal) ^ (10 * globalEta) *
          sectionEightScaleCountFrostmanFactor
            delta rho selected.card gamma := by
  have hp :
      0 < 2 * lowerExp + 2 * cardExp + a + cardAbsorbExp := by
    nlinarith
  obtain ⟨selected, hselected, hadmissible, hLTop, hLowSelected,
      hcard, hmass⟩ :=
    exists_lowCF_fresh_selected_cardEnvelope_retention
      S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho q hlowerTop hLow
  have hcardEnvelopePower :=
    selectedParentLowCFFresh_cardEnvelope_le_power
      S hdelta hrho hrhoOne hdeltaRho q selected
        hcombined ha hcardAbsorbExp hsmallFresh hlowerPower hfullCardPower
  refine ⟨selected, hselected, ?_⟩
  exact four_mul_selectedFiberSourceAverage_le_longMiddle_of_sourcePowers
    (p := 2 * lowerExp + 2 * cardExp + a + cardAbsorbExp)
    (a := a) (kappa := kappa) (globalEta := globalEta)
    hF S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho q selected
      hlowerTop hLTop hLowSelected K hdelta0 hadmissible hcard hmass
      hp ha hsmallSource hcardEnvelopePower hsourceDensityPower hbasePower
      hselected hparentCount hglobalDeltaOne hK0 hKTop habsorbExp
      hratioSmall hratioDelta hnet hbudget hbetaTwo hgammaTwo hgap

#print axioms exists_fresh_selected_four_mul_sourceAverage_le_longMiddle

end
end Family8StickySelectedFiberLowCFFreshLongMiddleProducerV1
