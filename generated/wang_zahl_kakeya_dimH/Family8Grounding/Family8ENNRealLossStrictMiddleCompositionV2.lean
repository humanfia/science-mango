import Family8Grounding.Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2
import Family8Grounding.Family8ContractedJohnMiddleActualVolumeEnvelopeV4
import Mathlib.Tactic

/-!
# Strict Section 8 middle bound from an honest ENNReal retention loss, V2

V1 omitted one namespace and did not explicitly transport the literal
Finset cardinality to its subtype cardinality.  This corrected successor
keeps the selected cardinality literal and exposes both Frostman budgets.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ENNRealLossStrictMiddleCompositionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleActualVolumeEnvelopeV4
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-- An honest selected normalized Frostman estimate, the relative middle
envelope, and one scalar absorption give the literal strict `hMiddle` bound.
The factor `4` is the one occurring in the same-assembly retained product. -/
theorem four_mul_sourceAverage_le_globalPower_mul_sectionEight
    {proxyScale fineScale coarseScale globalDelta delta0 : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {frostmanBeta frostmanEpsilon frostmanEta gamma : Real}
    {lossExp kappa globalEta : Real}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (D : ActualTubeDatum proxyScale iota)
    (selected : Finset iota)
    (loss C K : ENNReal)
    (hloss0 : loss ≠ 0) (hlossTop : loss ≠ ∞)
    (hdelta0 : proxyScale / 8 ≤ delta0)
    (hadmissible :
      (restrictActualTubeDatum (eighthNormalizedDatum D)
        selected).IsAdmissible)
    (hcard : (Fintype.card iota : ENNReal) ≤
      loss * (selected.card : ENNReal))
    (hmass :
      (eighthNormalizedDatum D).shading.shadingMass ≤
        loss *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass)
    (hKT : IsKatzTao C
      (restrictActualTubeDatum (eighthNormalizedDatum D)
        selected).family.bodyFamily)
    (hdensityBudget :
      ((proxyScale / 8 : NNReal) : ENNReal) ^ frostmanEta ≤
        (eighthNormalizedDatum D).shading.shadingDensity / loss)
    (hbaseBudget :
      loss * (C * volume (unitBallBody : Set Space)) ≤
        ((proxyScale / 8 : NNReal) : ENNReal) ^ (-frostmanEta) *
          ((Fintype.card iota : ENNReal) *
            (((proxyScale / 8 : NNReal) : ENNReal) ^ 2 / 2)))
    (hfine : 0 < fineScale) (hcoarse : 0 < coarseScale)
    (hproxyEighth : 0 < proxyScale / 8)
    (hproxyEighthHalf : proxyScale / 8 ≤ (2 : NNReal)⁻¹)
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta)
    (hscaleEq : ((proxyScale / 8 : NNReal) : ENNReal) =
      (3 / 64 : ENNReal) *
        ((fineScale : ENNReal) / (coarseScale : ENNReal)))
    (hlossPower : loss ≤
      ((proxyScale / 8 : NNReal) : ENNReal) ^ (-lossExp))
    (hselected : selected.Nonempty)
    (hcount : (selected.card : ENNReal) ≤
      K * (((fineScale : ENNReal) / (coarseScale : ENNReal)) ^
        (-(2 + kappa))))
    (habsorb :
      4 *
          (contractedJohnMiddleActualFixedCoefficient
              K frostmanEpsilon frostmanBeta gamma lossExp *
            (((fineScale : ENNReal) / (coarseScale : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma lossExp kappa)) ≤
        (globalDelta : ENNReal) ^ (10 * globalEta)) :
    4 * D.shading.averageMultiplicity ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          fineScale coarseScale selected.card gamma := by
  let refined := restrictActualTubeDatum
    (eighthNormalizedDatum D) selected
  have hsource : D.shading.averageMultiplicity ≤
      loss * frostmanMultiplicityRHS (proxyScale / 8)
        refined.actualFamilyVolume frostmanEpsilon frostmanBeta := by
    simpa only [refined] using
      source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS
        hF D selected loss C hloss0 hlossTop hdelta0 hadmissible hcard
          hmass hKT hdensityBudget hbaseBudget
  have hcountPos : 0 < Fintype.card {i // i ∈ selected} := by
    simpa only [Fintype.card_coe] using hselected.card_pos
  have hcountSubtype :
      (Fintype.card {i // i ∈ selected} : ENNReal) ≤
        K * (((fineScale : ENNReal) / (coarseScale : ENNReal)) ^
          (-(2 + kappa))) := by
    simpa only [Fintype.card_coe] using hcount
  have hrelative :
      loss * frostmanMultiplicityRHS (proxyScale / 8)
          refined.actualFamilyVolume frostmanEpsilon frostmanBeta ≤
        contractedJohnMiddleActualFixedCoefficient
            K frostmanEpsilon frostmanBeta gamma lossExp *
          (((fineScale : ENNReal) / (coarseScale : ENNReal)) ^
            contractedJohnMiddleRatioGain
              frostmanEpsilon frostmanBeta gamma lossExp kappa) *
          sectionEightScaleCountFrostmanFactor
            fineScale coarseScale selected.card gamma := by
    simpa only [refined, Fintype.card_coe] using
      (loss_mul_actualRHS_le_fixed_mul_ratioGain_mul_sectionEight_of_scale
        (D := refined) (loss := loss) (K := K)
        (epsilon := frostmanEpsilon) (beta := frostmanBeta)
        (gamma := gamma) (lossExp := lossExp) (kappa := kappa)
        hfine hcoarse hproxyEighth hproxyEighthHalf hbetaTwo hgammaTwo hgap
          hscaleEq hlossPower hcountPos hcountSubtype)
  calc
    4 * D.shading.averageMultiplicity ≤
        4 * (loss * frostmanMultiplicityRHS (proxyScale / 8)
          refined.actualFamilyVolume frostmanEpsilon frostmanBeta) :=
      mul_le_mul' le_rfl hsource
    _ ≤ 4 *
        (contractedJohnMiddleActualFixedCoefficient
            K frostmanEpsilon frostmanBeta gamma lossExp *
          (((fineScale : ENNReal) / (coarseScale : ENNReal)) ^
            contractedJohnMiddleRatioGain
              frostmanEpsilon frostmanBeta gamma lossExp kappa) *
          sectionEightScaleCountFrostmanFactor
            fineScale coarseScale selected.card gamma) :=
      mul_le_mul' le_rfl hrelative
    _ = (4 *
          (contractedJohnMiddleActualFixedCoefficient
              K frostmanEpsilon frostmanBeta gamma lossExp *
            (((fineScale : ENNReal) / (coarseScale : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma lossExp kappa))) *
        sectionEightScaleCountFrostmanFactor
          fineScale coarseScale selected.card gamma := by
      ac_rfl
    _ ≤ (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          fineScale coarseScale selected.card gamma :=
      mul_le_mul' habsorb le_rfl

#print axioms four_mul_sourceAverage_le_globalPower_mul_sectionEight

end
end Family8ENNRealLossStrictMiddleCompositionV2
