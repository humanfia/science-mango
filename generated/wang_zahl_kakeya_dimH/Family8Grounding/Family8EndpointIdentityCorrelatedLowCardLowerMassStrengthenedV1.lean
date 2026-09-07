import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointIdentityTauActiveParentAdmissibilityV1
import Family8Grounding.Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
import Family8Grounding.Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV5
import Family8Grounding.Family8GreedyFactorTwoLowFreshCardLowerRetainedV1
import Family8Grounding.Family8LowFreshCorrelatedPowerBudgetsV1
import Family8Grounding.Family8LongIntervalBootstrapNumericsV1
import Family8Grounding.Family8MultiplicityLossMonotonicityV4
import Family8Grounding.Family8Section8FixedPositiveSelfImprovementBudgetV3
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Mathlib.Tactic

/-!
# Correlated low-card endpoint callback with the existing same-core high branch

The endpoint mass-strengthened theorem has already made the literal greedy
low/high choice.  Its low callback therefore must consume that exact
`selectedLow`; invoking a second low/high dichotomy here would lose the
same-object high payload.  This sibling instead runs the strengthened fresh
selector once on the supplied low restriction and retains its card lower
bound on the same `selectedLow`/`selectedFresh`.

The correlated exponent premise constructs one coefficient

`A = delta ^ (-(etaKT / 8))`

and all of its scalar budgets.  Exact endpoint identities transport the
source Frostman density to the tau-active datum.  The Katz--Tao hypothesis is
weakened from the fixed-nu loss to the long-interval loss before selection,
so the retained average bound is already in the terminal consumer's form.
The high branch is not copied or modified: it remains the existing
mass-strengthened same-core occurrence/John/Cordoba payload.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityCorrelatedLowCardLowerMassStrengthenedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8EndpointIdentityTauActiveParentAdmissibilityV1
open Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV5
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8GreedyFactorTwoLowFreshCardLowerRetainedV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LowFreshCorrelatedPowerBudgetsV1
open Family8LongIntervalBootstrapNumericsV1
open Family8MultiplicityLossMonotonicityV4
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The fixed-nu Katz--Tao loss fits inside every nonnegative terminal
long-interval loss.  This is the exact monotonicity direction needed before
the fresh selector is run. -/
theorem sectionEightFixedNu_le_longIntervalDeltaLoss
    (P : ParameterLadder epsilon0 beta gamma)
    {etaPrime : Real} (hetaPrime : 0 <= etaPrime) :
    sectionEightFixedNu P <=
      longIntervalDeltaLoss P.epsilon etaPrime := by
  have hetaZero := P.eta_le_epsilon_div_five 0
  dsimp only [sectionEightFixedNu, longIntervalDeltaLoss]
  linarith [P.epsilon_pos]

/-- Correlated endpoint split with a retained same-choice low bundle.

The conclusion is the existing mass-strengthened endpoint proposition with
only its abstract `lowResult` instantiated.  Consequently its right branch
is definitionally the legacy same-core high payload; no high witness is
reselected and no high conclusion is strengthened. -/
theorem exists_endpointIdentity_correlated_retainedLowCardLower_or_sameCoreOccurrenceWeightedCordoba_massStrengthened
    {etaKT outputEta etaPrime : Real} {delta0 : NNReal}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hKTP : KatzTaoAtParameters
      beta (sectionEightFixedNu P) etaKT delta0)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hetaKT : 0 < etaKT)
    (houtputShare : 16 * outputEta <= etaKT)
    (hetaPrime : 0 <= etaPrime)
    (hdelta0 : delta / 8 <= delta0)
    (hsmall : delta <=
      lowFreshCorrelatedPowerThreshold etaKT (P.eta 0))
    (hF : FrostmanHypotheses D outputEta)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover
        (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))) W).activeCoarseFamily) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
    EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
      D hD P W A
        (RetainedFactorTwoFreshLowWithCardLower Dtau A
          (longIntervalDeltaLoss P.epsilon etaPrime) beta)
        r hr KT := by
  dsimp only
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
  let lowResult : Prop :=
    RetainedFactorTwoFreshLowWithCardLower Dtau A
      (longIntervalDeltaLoss P.epsilon etaPrime) beta
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W
  have hDtau : Dtau.IsAdmissible := by
    simpa only [E, C, S, T, Dtau] using
      (endpointIdentity_tauActiveParent_isAdmissible D hD P W)
  have hmassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
    change (tauActiveCoarseDatum E C S W).shading.shadingMass =
      D.shading.shadingMass
    simpa only [E, C, S] using
      (endpointLongCore_tauActive_shadingMass_eq_source D hD P W)
  have hdensityEq :
      Dtau.shading.shadingDensity = D.shading.shadingDensity := by
    change (tauActiveCoarseDatum E C S W).shading.shadingDensity =
      D.shading.shadingDensity
    simpa only [E, C, S] using
      (endpointLongCore_identity_tauActive_shadingDensity_eq_source
        D hD P W)
  let B : LowFreshCorrelatedPowerBudgets
      delta etaKT outputEta (P.eta 0) A := by
    simpa only [A] using
      (lowFreshCorrelatedPowerBudgets_of_le_threshold
        P hD.delta_pos hetaKT houtputShare hsmall)
  have hKTPLong : KatzTaoAtParameters beta
      (longIntervalDeltaLoss P.epsilon etaPrime) etaKT delta0 :=
    katzTaoAtParameters_of_epsilon_le hKTP
      (sectionEightFixedNu_le_longIntervalDeltaLoss P hetaPrime)
  have hsourceMass : D.shading.shadingMass ≠ 0 := by
    have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
      D hD hF
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos)
      ENNReal.coe_ne_top).trans_le hfloor)
  have closeLow : forall selected : Finset
      (ActiveParentIndex T),
      D.shading.shadingMass <=
        2 * (restrictActualTubeDatum Dtau selected).shading.shadingMass ->
      IsKatzTao A
        (restrictActualTubeDatum Dtau selected).family.bodyFamily ->
      lowResult := by
    intro selected hmassSource hlocalKT
    have hmassTau : Dtau.shading.shadingMass <=
        2 * (restrictActualTubeDatum Dtau selected).shading.shadingMass :=
      hmassEq.le.trans hmassSource
    have hDlow :
        (restrictActualTubeDatum Dtau selected).IsAdmissible :=
      Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hDtau selected
    have hdelta0Tau : S.tau W.m / 8 <= delta0 := by
      simpa only [htau] using hdelta0
    have hdensityBudgetTau :
        (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
            (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
          Dtau.shading.shadingDensity := by
      have hdensityBudgetSource :
          (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
              (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
            D.shading.shadingDensity := by
        simpa only [htau] using B.density_budget.trans hF.1
      exact hdensityBudgetSource.trans_eq hdensityEq.symm
    have hcoefficientTau :
        128 * A <=
          ((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-etaKT) := by
      simpa only [htau] using B.coefficient_budget
    exact retainedFactorTwoFreshLowWithCardLower_of_lowRestriction
      hKTPLong Dtau selected hmassTau hDlow A hlocalKT
        hdelta0Tau hdensityBudgetTau hcoefficientTau
  have hsplit :=
    exists_endpointIdentity_source_lowCallback_or_sameCoreOccurrenceWeightedCordoba_massStrengthened
      D hD P W A lowResult closeLow hsourceMass r hr KT hKT
  simpa only [E, C, S, T, Dtau, A, lowResult] using hsplit

#print axioms sectionEightFixedNu_le_longIntervalDeltaLoss
#print axioms
  exists_endpointIdentity_correlated_retainedLowCardLower_or_sameCoreOccurrenceWeightedCordoba_massStrengthened

end
end Family8EndpointIdentityCorrelatedLowCardLowerMassStrengthenedV1
