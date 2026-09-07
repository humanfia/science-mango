import Family8Grounding.Family8EndpointIdentityTauActiveFreshRetainedCardScaleV1
import Family8Grounding.Family8EndpointIdentityTauActiveLowFreshCardScalePowerLowerV1
import Family8Grounding.Family8LongIntervalBootstrapNumericsV1
import Family8Grounding.Family8MultiplicityLossMonotonicityV4
import Mathlib.Tactic

/-!
# Same-fresh-child `X` bounds for the low long interval

The generalized long-interval consumer is written with the finite quantity

`X = (# selectedFresh : NNReal) * delta ^ 2`,

whereas the two endpoint estimates are naturally stated with the definitionally
equivalent `ENNReal` quantity `proposition66ACardScaleVolume`.  This file makes
that harmless coercion explicit and packages the lower and upper bounds for
one literal `selectedLow` and one literal `selectedFresh`.  No selector is run
here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8LowFreshLongIntervalXBoundsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8EndpointIdentityTauActiveFreshRetainedCardScaleV1
open Family8EndpointIdentityTauActiveLowFreshCardScalePowerLowerV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8MultiplicityLossMonotonicityV4
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- The literal finite `X` expected by the generalized long-interval
consumer when its tube type is the retained fresh subtype. -/
def lowFreshLongIntervalX (delta : NNReal) (tubeCount : Nat) : NNReal :=
  (tubeCount : NNReal) * delta ^ 2

/-- The finite consumer normalization is exactly the existing Proposition
6.6(A) card-scale normalization after coercion to `ENNReal`. -/
theorem coe_lowFreshLongIntervalX_eq_proposition66ACardScaleVolume
    (delta : NNReal) (tubeCount : Nat) :
    (lowFreshLongIntervalX delta tubeCount : ENNReal) =
      proposition66ACardScaleVolume delta tubeCount := by
  unfold lowFreshLongIntervalX proposition66ACardScaleVolume
  simp only [ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_pow]
  ac_rfl

/-- The three `X` facts used by the generalized numerical consumer.  The
normalization equality `X = tubeCount * delta^2` is definitional through
`lowFreshLongIntervalX`. -/
structure LowFreshLongIntervalXBounds
    (delta : NNReal) (tubeCount : Nat)
    (epsilon etaPrime : Real) : Prop where
  card_pos : 0 < tubeCount
  lower :
    (delta / 8) ^ etaPrime <= lowFreshLongIntervalX delta tubeCount
  upper :
    lowFreshLongIntervalX delta tubeCount <=
      (delta / 8) ^ (-longIntervalDeltaLoss epsilon etaPrime)

/-- Pure scalar conversion from the two endpoint-native card-scale bounds to
the exact finite bounds consumed by the long-interval theorem.

The lower conversion only uses `delta / 8 <= delta` and nonnegativity of
`etaPrime`.  The upper conversion first discards the favorable factor eight,
then enlarges the loss exponent using `etaKT <= longIntervalDeltaLoss` and
the fact that the lower scale is at most one. -/
theorem lowFreshLongIntervalXBounds_of_cardScale_bounds
    {delta : NNReal} {tubeCount : Nat}
    {epsilon etaKT etaPrime : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hcardPos : 0 < tubeCount)
    (hetaPrime0 : 0 <= etaPrime)
    (hetaLoss : etaKT <= longIntervalDeltaLoss epsilon etaPrime)
    (hcardScaleLower :
      (delta : ENNReal) ^ etaPrime <=
        proposition66ACardScaleVolume delta tubeCount)
    (hcardScaleUpper :
      8 * proposition66ACardScaleVolume delta tubeCount <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-etaKT)) :
    LowFreshLongIntervalXBounds delta tubeCount epsilon etaPrime := by
  have hd : 0 < delta / 8 := div_pos hdelta (by norm_num)
  have hdOne : delta / 8 <= 1 := by
    exact (div_le_self (show 0 <= delta from bot_le)
      (by norm_num : (1 : NNReal) <= 8)).trans hdeltaOne
  have hscale :
      ((delta / 8 : NNReal) : ENNReal) <= (delta : ENNReal) := by
    exact_mod_cast
      (div_le_self (show 0 <= delta from bot_le)
        (by norm_num : (1 : NNReal) <= 8))
  have hLowerENN :
      ((delta / 8 : NNReal) : ENNReal) ^ etaPrime <=
        (lowFreshLongIntervalX delta tubeCount : ENNReal) := by
    rw [coe_lowFreshLongIntervalX_eq_proposition66ACardScaleVolume]
    exact (ENNReal.rpow_le_rpow hscale hetaPrime0).trans hcardScaleLower
  have hLower :
      (delta / 8) ^ etaPrime <= lowFreshLongIntervalX delta tubeCount := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.ne'] using hLowerENN
  have hcardScaleLeEight :
      proposition66ACardScaleVolume delta tubeCount <=
        8 * proposition66ACardScaleVolume delta tubeCount := by
    calc
      proposition66ACardScaleVolume delta tubeCount =
          1 * proposition66ACardScaleVolume delta tubeCount := by rw [one_mul]
      _ <= 8 * proposition66ACardScaleVolume delta tubeCount :=
        mul_le_mul' (by norm_num : (1 : ENNReal) <= 8) le_rfl
  have hpowerLoss :
      ((delta / 8 : NNReal) : ENNReal) ^ (-etaKT) <=
        ((delta / 8 : NNReal) : ENNReal) ^
          (-longIntervalDeltaLoss epsilon etaPrime) :=
    coe_rpow_neg_mono_loss hdOne hetaLoss
  have hUpperENN :
      (lowFreshLongIntervalX delta tubeCount : ENNReal) <=
        ((delta / 8 : NNReal) : ENNReal) ^
          (-longIntervalDeltaLoss epsilon etaPrime) := by
    rw [coe_lowFreshLongIntervalX_eq_proposition66ACardScaleVolume]
    exact hcardScaleLeEight.trans (hcardScaleUpper.trans hpowerLoss)
  have hUpper :
      lowFreshLongIntervalX delta tubeCount <=
        (delta / 8) ^ (-longIntervalDeltaLoss epsilon etaPrime) := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.ne'] using hUpperENN
  exact {
    card_pos := hcardPos
    lower := hLower
    upper := hUpper
  }

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Endpoint identity package for one literal low restriction and one literal
fresh child.  The lower field comes from the Frostman source-mass/card-retention
chain, and the upper field comes from the Katz--Tao coefficient bound on those
same objects. -/
theorem endpointIdentity_tauActive_lowFresh_longIntervalXBounds
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {etaSource : Real} (hF : FrostmanHypotheses D etaSource)
    (A : ENNReal)
    {etaKT lossExponent absorbExponent etaPrime : Real}
    (hcoefficient :
      128 * A <= ((delta / 8 : NNReal) : ENNReal) ^ (-etaKT))
    (hloss : (sourceKatzTaoFreshLoss A : ENNReal) <=
      (delta : ENNReal) ^ (-lossExponent))
    (hconstant : (16 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent))
    (hexponent :
      2 * etaSource + lossExponent + absorbExponent <= etaPrime)
    (hetaPrime0 : 0 <= etaPrime)
    (hetaLoss :
      etaKT <= longIntervalDeltaLoss P.epsilon etaPrime) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
    let S := endpointScaleSequence delta hdeltaOne
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    forall selectedLow : Finset {k // k ∈ T.activeCoarse},
      Dtau.shading.shadingMass <= 2 *
        (restrictActualTubeDatum Dtau selectedLow).shading.shadingMass ->
      (restrictActualTubeDatum Dtau selectedLow).IsAdmissible ->
      IsKatzTao A
        (restrictActualTubeDatum Dtau selectedLow).family.bodyFamily ->
      forall selectedFresh : Finset {k // k ∈ selectedLow},
        selectedFresh.Nonempty ->
        selectedFresh.card <= selectedLow.card ->
        (selectedLow.card : ENNReal) <=
          (sourceKatzTaoFreshLoss A : ENNReal) *
            (selectedFresh.card : ENNReal) ->
        LowFreshLongIntervalXBounds delta selectedFresh.card
          P.epsilon etaPrime := by
  dsimp only
  intro selectedLow hmass hDlow hKTlow
    selectedFresh hselectedFresh hcardUpper hcardLower
  have hcardScaleLower :=
    endpointIdentity_frostman_to_tauActive_freshCardScale_powerLower
      D hD P W hF A hloss hconstant hexponent
        selectedLow hmass hDlow selectedFresh hcardLower
  have hcardScaleUpper :=
    endpointIdentity_tauActive_eight_mul_freshCardScale_le
      D hD P W A hcoefficient selectedLow hDlow hKTlow
        selectedFresh hcardUpper
  exact lowFreshLongIntervalXBounds_of_cardScale_bounds
    hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      (Finset.card_pos.mpr hselectedFresh) hetaPrime0 hetaLoss
      hcardScaleLower hcardScaleUpper

#print axioms coe_lowFreshLongIntervalX_eq_proposition66ACardScaleVolume
#print axioms lowFreshLongIntervalXBounds_of_cardScale_bounds
#print axioms endpointIdentity_tauActive_lowFresh_longIntervalXBounds

end
end Family8LowFreshLongIntervalXBoundsV1
