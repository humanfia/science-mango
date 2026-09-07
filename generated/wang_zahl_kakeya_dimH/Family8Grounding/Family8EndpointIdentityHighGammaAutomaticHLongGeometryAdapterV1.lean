import Family8Grounding.Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
import Family8Grounding.Family8EndpointIdentityHighGammaParameterLongCoreConnectorV1
import Family8Grounding.Family8EndpointLongCoreSixteenthRadiusThresholdV1
import Family8Grounding.Family8ParameterCappedOutputEtaStrongFrostmanLongCoreOnlyMainLemmaV1
import Mathlib.Tactic

/-!
# Uniform high-gamma automatic LongCore handoff

This file is a thin consumer of the automatic parentwise LongCore endpoint.
It performs the finite-stage and small-scale bookkeeping needed by the
`hLongGeometry` interface: one positive raw scale simultaneously enforces the
selector threshold, the common endpoint threshold, the one-sixteenth radius
bound, the `rho / 8 <= delta0` bound, and every stage-dependent finite-loss
threshold.

The parentwise selector and its normalized compatibility witness are never
callbacks.  They are the canonical objects chosen by the imported automatic
endpoint.  The only remaining inputs are the two genuine analytic inequalities
already named by the high-gamma parameter connector: the assembly-density gate
and the base/card-scale gate.

This is the high-gamma slice of the top interface.  It does not assert that
either analytic gate has already been produced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaAutomaticHLongGeometryAdapterV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8CanonicalBufferedGlobalFirstFactorEndpointV1
open Family8CanonicalEndpointBaseThresholdV1
open Family8CanonicalLowerBufferedScaleV4
open Family8EndpointIdentityCoreSelectorV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaParameterLongCoreConnectorV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1
open Family8EndpointLongCoreSixteenthRadiusThresholdV1
open Family8FirstCrossingRecomputedThirdFixedLossPowerV3
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8HighGammaParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SectionEightOutputEtaV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-! ## Finite-stage threshold bundling -/

/-- Minimum of a natural-indexed threshold over the prefix `0, ..., N`. -/
def prefixMinThreshold (f : Nat -> NNReal) : Nat -> NNReal
  | 0 => f 0
  | n + 1 => min (prefixMinThreshold f n) (f (n + 1))

theorem prefixMinThreshold_pos
    (f : Nat -> NNReal) (hf : forall j, 0 < f j) (N : Nat) :
    0 < prefixMinThreshold f N := by
  induction N with
  | zero => exact hf 0
  | succ N ih =>
      rw [prefixMinThreshold]
      exact lt_min ih (hf (N + 1))

theorem prefixMinThreshold_le
    (f : Nat -> NNReal) {j N : Nat} (hj : j <= N) :
    prefixMinThreshold f N <= f j := by
  induction N with
  | zero =>
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      exact le_rfl
  | succ N ih =>
      rw [prefixMinThreshold]
      by_cases hlast : j = N + 1
      · subst j
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (by omega))

/-- The three genuinely stage-dependent small-scale thresholds in the
automatic high-gamma DSO.  The same finite-constant threshold pays both the
outer and middle coefficient four. -/
def highGammaAutomaticStageThreshold
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) (stage : Nat) : NNReal :=
  min
    (activeFrozenComparableLossAbsorptionThreshold
      (longCoreHighGammaQuarterReserve P stage))
    (min
      (finiteConstantSmallDeltaThreshold (4 : ENNReal)
        (longCoreHighGammaQuarterReserve P stage))
      (recomputedThirdFixedLossPowerThreshold sourceEta
        (longCoreHighGammaThirdAbsorb P stage) innerEpsilon gamma))

theorem highGammaAutomaticStageThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) (stage : Nat) :
    0 < highGammaAutomaticStageThreshold
      P sourceEta innerEpsilon stage := by
  unfold highGammaAutomaticStageThreshold
  exact lt_min
    (activeFrozenComparableLossAbsorptionThreshold_pos _)
    (lt_min (finiteConstantSmallDeltaThreshold_pos _ _)
      (recomputedThirdFixedLossPowerThreshold_pos _ _ _ _))

/-- Uniform finite minimum over every stage which a normalized witness can
store. -/
def highGammaAutomaticUniformStageThreshold
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) : NNReal :=
  prefixMinThreshold
    (highGammaAutomaticStageThreshold P sourceEta innerEpsilon) P.N

theorem highGammaAutomaticUniformStageThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) :
    0 < highGammaAutomaticUniformStageThreshold
      P sourceEta innerEpsilon := by
  exact prefixMinThreshold_pos _
    (highGammaAutomaticStageThreshold_pos P sourceEta innerEpsilon) P.N

theorem highGammaAutomaticUniformStageThreshold_le
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) {stage : Nat}
    (hstage : stage <= P.N) :
    highGammaAutomaticUniformStageThreshold P sourceEta innerEpsilon <=
      highGammaAutomaticStageThreshold P sourceEta innerEpsilon stage := by
  exact prefixMinThreshold_le _ hstage

theorem highGammaAutomaticStageThreshold_le_frozen
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) (stage : Nat) :
    highGammaAutomaticStageThreshold P sourceEta innerEpsilon stage <=
      activeFrozenComparableLossAbsorptionThreshold
        (longCoreHighGammaQuarterReserve P stage) := by
  exact min_le_left _ _

theorem highGammaAutomaticStageThreshold_le_four
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) (stage : Nat) :
    highGammaAutomaticStageThreshold P sourceEta innerEpsilon stage <=
      finiteConstantSmallDeltaThreshold (4 : ENNReal)
        (longCoreHighGammaQuarterReserve P stage) := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem highGammaAutomaticStageThreshold_le_third
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta innerEpsilon : Real) (stage : Nat) :
    highGammaAutomaticStageThreshold P sourceEta innerEpsilon stage <=
      recomputedThirdFixedLossPowerThreshold sourceEta
        (longCoreHighGammaThirdAbsorb P stage) innerEpsilon gamma := by
  exact (min_le_right _ _).trans (min_le_right _ _)

/-! ## Endpoint radius target -/

/-- Pull back an arbitrary positive radius target through the endpoint power
`delta ^ (1 - epsilon)`. -/
def endpointLongCoreTargetRadiusThreshold
    (P : ParameterLadder epsilon0 beta gamma) (target : NNReal) : NNReal :=
  positivePowerPullbackThreshold (1 - P.epsilon) target

theorem endpointLongCoreTargetRadiusThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    {target : NNReal} (htarget : 0 < target) :
    0 < endpointLongCoreTargetRadiusThreshold P target := by
  apply positivePowerPullbackThreshold_pos
  · have hepsilonLt : P.epsilon < 1 :=
      parameterLadder_epsilon_lt_one P hbeta hgamma
    linarith
  · exact htarget

theorem canonicalBufferedRadius_le_target_of_endpointSmall
    {fine : UniformTubeFamily delta index}
    {C : CoherentStickyMultiscaleCover fine}
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hdeltaOne : delta <= 1)
    (W : NormalizedLongIntervalCoreWitness
      fine C P.N P.epsilon P.eta
        (endpointScaleSequence delta hdeltaOne))
    (target : NNReal)
    (hsmall : delta <= endpointLongCoreTargetRadiusThreshold P target) :
    canonicalBufferedRadius W <= target := by
  have hepsilonLt : P.epsilon < 1 :=
    parameterLadder_epsilon_lt_one P hbeta hgamma
  have hpowerPos : 0 < 1 - P.epsilon := by linarith
  have hdeltaPower : delta ^ (1 - P.epsilon) <= target :=
    rpow_le_target_of_le_positivePowerPullbackThreshold hpowerPos hsmall
  calc
    canonicalBufferedRadius W <=
        ((endpointScaleSequence delta hdeltaOne).tau W.m) ^
          (1 - P.epsilon) :=
      canonicalLowerBufferedScale_le_tau_rpow_one_sub
        ((endpointScaleSequence delta hdeltaOne).theta_le_one W.m)
        P.epsilon_pos.le
    _ = delta ^ (1 - P.epsilon) := by
      rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
        endpointScaleSequence_tau_zero]
    _ <= target := hdeltaPower

/-! ## One positive raw scale -/

/-- All mechanical scale inputs of the automatic high-gamma endpoint. -/
def highGammaAutomaticRawDelta0
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT sourceEta : Real) (delta0 : NNReal) : NNReal :=
  let P := H.ladder
  let sourceLoss := sectionEightSourceLoss P targetEpsilon
  min (endpointIdentityFirstCrossingImpossibleThreshold P)
    (min (canonicalEndpointBaseThreshold P (4 * sourceLoss) etaKT)
      (min (endpointLongCoreSixteenthRadiusThreshold P)
        (min (endpointLongCoreTargetRadiusThreshold P
              ((8 : NNReal) * delta0))
          (highGammaAutomaticUniformStageThreshold
            P sourceEta sourceLoss))))

theorem highGammaAutomaticRawDelta0_pos
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT sourceEta : Real) {delta0 : NNReal}
    (hdelta0 : 0 < delta0) :
    0 < highGammaAutomaticRawDelta0
      H targetEpsilon etaKT sourceEta delta0 := by
  dsimp only [highGammaAutomaticRawDelta0]
  exact lt_min
    (endpointIdentityFirstCrossingImpossibleThreshold_pos H.ladder)
    (lt_min
      (canonicalEndpointBaseThreshold_pos H.ladder hbeta hgamma _ _)
      (lt_min
        (endpointLongCoreSixteenthRadiusThreshold_pos
          H.ladder hbeta hgamma)
        (lt_min
          (endpointLongCoreTargetRadiusThreshold_pos
            H.ladder hbeta hgamma (by positivity))
          (highGammaAutomaticUniformStageThreshold_pos
            H.ladder sourceEta
              (sectionEightSourceLoss H.ladder targetEpsilon)))))

theorem highGammaAutomaticRawDelta0_le_selector
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT sourceEta : Real) (delta0 : NNReal) :
    highGammaAutomaticRawDelta0 H targetEpsilon etaKT sourceEta delta0 <=
      endpointIdentityFirstCrossingImpossibleThreshold H.ladder := by
  exact min_le_left _ _

theorem highGammaAutomaticRawDelta0_le_base
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT sourceEta : Real) (delta0 : NNReal) :
    highGammaAutomaticRawDelta0 H targetEpsilon etaKT sourceEta delta0 <=
      canonicalEndpointBaseThreshold H.ladder
        (4 * sectionEightSourceLoss H.ladder targetEpsilon) etaKT := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem highGammaAutomaticRawDelta0_le_sixteenth
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT sourceEta : Real) (delta0 : NNReal) :
    highGammaAutomaticRawDelta0 H targetEpsilon etaKT sourceEta delta0 <=
      endpointLongCoreSixteenthRadiusThreshold H.ladder := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))

theorem highGammaAutomaticRawDelta0_le_delta0Radius
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT sourceEta : Real) (delta0 : NNReal) :
    highGammaAutomaticRawDelta0 H targetEpsilon etaKT sourceEta delta0 <=
      endpointLongCoreTargetRadiusThreshold H.ladder
        ((8 : NNReal) * delta0) := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))

theorem highGammaAutomaticRawDelta0_le_uniformStage
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (targetEpsilon etaKT sourceEta : Real) (delta0 : NNReal) :
    highGammaAutomaticRawDelta0 H targetEpsilon etaKT sourceEta delta0 <=
      highGammaAutomaticUniformStageThreshold H.ladder sourceEta
        (sectionEightSourceLoss H.ladder targetEpsilon) := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        (min_le_right _ _)))

/-- The endpoint ladder epsilon is automatically below one half in the
positive-gap unit-interval range. -/
theorem highGammaLadder_epsilon_le_half
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1) :
    H.ladder.epsilon <= 1 / 2 := by
  have hgapUpper : gamma - beta < 1 := by linarith
  nlinarith [H.ladder.epsilon_gap]

/-! ## The only non-mechanical inputs -/

/-- A source Frostman hypothesis at an exponent capped by `P.eta 0` is
definitionally the output hypothesis requested by the automatic endpoint. -/
theorem outputFrostmanHypotheses_of_sourceCap
    (P : ParameterLadder epsilon0 beta gamma)
    {sourceEta : Real} (hSourceEtaLe : sourceEta <= P.eta 0)
    (D : ActualTubeDatum delta index)
    (hFSource : FrostmanHypotheses D sourceEta) :
    FrostmanHypotheses D (sectionEightOutputEta P sourceEta) := by
  simpa only [sectionEightOutputEta, sectionEightFixedNu,
    min_eq_left hSourceEtaLe] using hFSource

/-- The two genuine analytic conclusions at one legal invocation of the top
geometry interface.  The full raw-scale bound is a parameter, and the witness
in both fields is the automatic normalized projection of the automatically
selected parentwise core.  No witness or selector is supplied by a producer. -/
structure AutomaticHighGammaAnalyticGatesAtRaw
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT sourceEta : Real) (delta0 : NNReal)
    (hSourceEtaLe : sourceEta <= H.ladder.eta 0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaAutomaticRawDelta0
      H targetEpsilon etaKT sourceEta delta0)
    (hFSource : FrostmanHypotheses D sourceEta) where
  density :
    endpointIdentityHighGammaDensityGate D hD H
      (automaticNormalizedLongCoreWitness D hD H.ladder hbeta hgamma
        (hdeltaRaw.trans
          (highGammaAutomaticRawDelta0_le_selector
            H targetEpsilon etaKT sourceEta delta0))
        (outputFrostmanHypotheses_of_sourceCap
          H.ladder hSourceEtaLe D hFSource))
      sourceEta (highGammaLadder_epsilon_le_half H hbeta hgamma)
      (outputFrostmanHypotheses_of_sourceCap
        H.ladder hSourceEtaLe D hFSource)
  base :
    endpointIdentityHighGammaBaseGate D hD H
      (automaticNormalizedLongCoreWitness D hD H.ladder hbeta hgamma
        (hdeltaRaw.trans
          (highGammaAutomaticRawDelta0_le_selector
            H targetEpsilon etaKT sourceEta delta0))
        (outputFrostmanHypotheses_of_sourceCap
          H.ladder hSourceEtaLe D hFSource)) sourceEta

/-- A gate producer is invoked only after every legal top-geometry parameter
and datum hypothesis is available.  Thus a future proof may use the target,
exponent caps, exact and relative-scale estimates, the complete raw-scale
bound, and the source Frostman hypothesis. -/
abbrev AutomaticHighGammaAnalyticGateProducer
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1) : Prop :=
  forall targetEpsilon : Real, forall _hTarget : 0 < targetEpsilon,
  forall etaKT sourceEta : Real, forall delta0 : NNReal,
  forall _hEtaKT : 0 < etaKT,
  forall _hEtaKTCap : etaKT <= H.ladder.epsilon ^ 2 * H.ladder.eta 0 / 32,
  forall _hSourceEta : 0 < sourceEta,
  forall hSourceEtaLe : sourceEta <= H.ladder.eta 0,
  forall _hDelta0 : 0 < delta0,
  forall _hDelta0Half : delta0 <= (2 : NNReal)⁻¹,
  forall _hKTExact : KatzTaoAtParameters beta
    (sectionEightFixedNu H.ladder) etaKT delta0,
  forall _hKTRelative : KatzTaoAtRelativeScaleParameters beta
    (sectionEightFixedNu H.ladder) etaKT delta0,
  forall _hFExact : FrostmanAtParameters gamma
    (sectionEightSourceLoss H.ladder targetEpsilon) sourceEta delta0,
  forall _hFRelative : FrostmanAtRelativeScaleParameters gamma
    (sectionEightSourceLoss H.ladder targetEpsilon) sourceEta delta0,
  forall (delta : NNReal) (index : Type)
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible),
  forall hdeltaRaw : delta <= highGammaAutomaticRawDelta0
    H targetEpsilon etaKT sourceEta delta0,
  forall hFSource : FrostmanHypotheses D sourceEta,
  forall _hmass : D.shading.shadingMass ≠ 0,
    Nonempty (AutomaticHighGammaAnalyticGatesAtRaw
      H hbeta hgamma targetEpsilon etaKT sourceEta delta0 hSourceEtaLe
      D hD hdeltaRaw hFSource)

/-! ## Exact `hLongGeometry` slice -/

/-- Fill the exact high-gamma slice of the capped strong-Frostman
`hLongGeometry` input.  Every scalar and scale premise of the automatic DSO is
derived from the finite raw-scale bundle; the per-invocation record returned
by `hGates` contains only the two analytic inputs. -/
theorem exists_highGamma_hLongGeometry_of_automaticAnalyticGates
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hGates : AutomaticHighGammaAnalyticGateProducer H hbeta hgamma) :
    exists epsilon0' : Real,
    exists P : ParameterLadder epsilon0' beta gamma,
    forall targetEpsilon : Real, 0 < targetEpsilon ->
    forall etaKT sourceEta : Real, forall delta0 : NNReal,
      0 < etaKT ->
      etaKT <= P.epsilon ^ 2 * P.eta 0 / 32 ->
      0 < sourceEta -> sourceEta <= P.eta 0 ->
      0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
      KatzTaoAtParameters
        beta (sectionEightFixedNu P) etaKT delta0 ->
      KatzTaoAtRelativeScaleParameters
        beta (sectionEightFixedNu P) etaKT delta0 ->
      FrostmanAtParameters gamma
        (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 ->
      FrostmanAtRelativeScaleParameters gamma
        (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 ->
        exists rawDelta0 : NNReal, 0 < rawDelta0 /\
          forall (delta : NNReal) (index : Type)
            [Fintype index] [DecidableEq index]
            (D : ActualTubeDatum delta index)
            (hD : D.IsAdmissible),
              delta <= rawDelta0 ->
              FrostmanHypotheses D sourceEta ->
              D.shading.shadingMass ≠ 0 ->
                forall _W : NormalizedLongIntervalCoreWitness
                  (fullRefinementDatum D).family
                    (identityRadiusCoherentCover
                      (fullRefinementDatum D).family)
                    P.N P.epsilon P.eta
                      (endpointScaleSequence delta
                        (hD.delta_le_half.trans (by norm_num))),
                  DividingScaleOutput D P
                    (4 * sectionEightSourceLoss P targetEpsilon) := by
  refine ⟨epsilon0, H.ladder, ?_⟩
  intro targetEpsilon hTarget etaKT sourceEta delta0
    hEtaKT hEtaKTCap hSourceEta hSourceEtaLe
    hDelta0 hDelta0Half hKTExact hKTRelative hFExact hFRelative
  let rawDelta0 : NNReal :=
    highGammaAutomaticRawDelta0
      H targetEpsilon etaKT sourceEta delta0
  have hRawDelta0 : 0 < rawDelta0 := by
    dsimp only [rawDelta0]
    exact highGammaAutomaticRawDelta0_pos H hbeta hgamma
      targetEpsilon etaKT sourceEta hDelta0
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFSource hmass _W
  let P := H.ladder
  let sourceLoss := sectionEightSourceLoss P targetEpsilon
  have hdeltaRaw : delta <= highGammaAutomaticRawDelta0
      H targetEpsilon etaKT sourceEta delta0 := by
    simpa only [rawDelta0] using hdelta
  have hepsilonHalf : P.epsilon <= 1 / 2 :=
    highGammaLadder_epsilon_le_half H hbeta hgamma
  have hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P := by
    exact hdeltaRaw.trans
      (highGammaAutomaticRawDelta0_le_selector
        H targetEpsilon etaKT sourceEta delta0)
  have hdeltaBase : delta <=
      canonicalEndpointBaseThreshold P (4 * sourceLoss) etaKT := by
    exact hdelta.trans
      (highGammaAutomaticRawDelta0_le_base
        H targetEpsilon etaKT sourceEta delta0)
  have hsmallSixteenth : delta <=
      endpointLongCoreSixteenthRadiusThreshold P := by
    exact hdelta.trans
      (highGammaAutomaticRawDelta0_le_sixteenth
        H targetEpsilon etaKT sourceEta delta0)
  have hsmallDelta0Radius : delta <=
      endpointLongCoreTargetRadiusThreshold P ((8 : NNReal) * delta0) := by
    exact hdelta.trans
      (highGammaAutomaticRawDelta0_le_delta0Radius
        H targetEpsilon etaKT sourceEta delta0)
  have hsmallUniform : delta <=
      highGammaAutomaticUniformStageThreshold P sourceEta sourceLoss := by
    exact hdelta.trans
      (highGammaAutomaticRawDelta0_le_uniformStage
        H targetEpsilon etaKT sourceEta delta0)
  have hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta) :=
    outputFrostmanHypotheses_of_sourceCap
      P hSourceEtaLe D hFSource
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
  have hbufferedSixteenth :
      canonicalBufferedRadius W <= (1 / 16 : NNReal) := by
    exact canonicalBufferedRadius_le_sixteenth_of_endpointSmall
      P hbeta hgamma (hD.delta_le_half.trans (by norm_num)) W
        hsmallSixteenth
  have hbufferedDelta0 :
      canonicalBufferedRadius W <= (8 : NNReal) * delta0 := by
    exact canonicalBufferedRadius_le_target_of_endpointSmall
      P hbeta hgamma (hD.delta_le_half.trans (by norm_num)) W
        ((8 : NNReal) * delta0) hsmallDelta0Radius
  have hthirdDelta0 : canonicalBufferedRadius W / 8 <= delta0 := by
    apply (div_le_iff₀ (by norm_num : (0 : NNReal) < 8)).2
    simpa only [mul_comm] using hbufferedDelta0
  have hStageSmall : delta <=
      highGammaAutomaticStageThreshold P sourceEta sourceLoss W.stage := by
    exact hsmallUniform.trans
      (highGammaAutomaticUniformStageThreshold_le
        P sourceEta sourceLoss W.stage_le)
  have hsmallFrozen : delta <=
      activeFrozenComparableLossAbsorptionThreshold
        (longCoreHighGammaQuarterReserve P W.stage) :=
    hStageSmall.trans
      (highGammaAutomaticStageThreshold_le_frozen
        P sourceEta sourceLoss W.stage)
  have hsmallFour : delta <=
      finiteConstantSmallDeltaThreshold (4 : ENNReal)
        (longCoreHighGammaQuarterReserve P W.stage) :=
    hStageSmall.trans
      (highGammaAutomaticStageThreshold_le_four
        P sourceEta sourceLoss W.stage)
  have hsmallThird : delta <=
      recomputedThirdFixedLossPowerThreshold sourceEta
        (longCoreHighGammaThirdAbsorb P W.stage) sourceLoss gamma :=
    hStageSmall.trans
      (highGammaAutomaticStageThreshold_le_third
        P sourceEta sourceLoss W.stage)
  have hsmallThirdEffective : delta <=
      recomputedThirdFixedLossPowerThreshold sourceEta
        (longCoreHighGammaThirdAbsorb P W.stage)
          ((4 * sourceLoss) / 4) gamma := by
    simpa only [show (4 * sourceLoss) / 4 = sourceLoss by ring] using
      hsmallThird
  have hhigh :
      10 * P.eta W.stage < P.epsilon ^ 2 * (3 * gamma - 2) :=
    H.ten_eta_lt_gain W.stage
  have hSourceEtaStage : sourceEta <= P.eta W.stage := by
    exact hSourceEtaLe.trans
      (eta_zero_le_eta_of_stage_le P W.stage W.stage_le)
  have hSourceLossStage : sourceLoss <= P.eta W.stage := by
    dsimp only [sourceLoss]
    exact (sectionEightSourceLoss_le_fixedNu P targetEpsilon).trans
      (eta_zero_le_eta_of_stage_le P W.stage W.stage_le)
  have hthirdBudget : sourceEta +
        longCoreHighGammaThirdAbsorb P W.stage +
          (4 * sourceLoss) / 4 <= 3 * P.eta W.stage := by
    dsimp only [longCoreHighGammaThirdAbsorb]
    rw [show (4 * sourceLoss) / 4 = sourceLoss by ring]
    nlinarith [P.eta_pos W.stage]
  have hEffectiveTarget : 0 < 4 * sourceLoss := by
    have hSourceLoss : 0 < sourceLoss := by
      dsimp only [sourceLoss]
      exact sectionEightSourceLoss_pos P hTarget
    positivity
  have hFExactEffective : FrostmanAtParameters gamma
      ((4 * sourceLoss) / 4) sourceEta delta0 := by
    convert hFExact using 1
    ring
  obtain ⟨gates⟩ := hGates targetEpsilon hTarget
    etaKT sourceEta delta0 hEtaKT hEtaKTCap
    hSourceEta hSourceEtaLe hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative
    delta index D hD hdeltaRaw hFSource hmass
  have hDensity := gates.density
  have hBase := gates.base
  exact
    dividingScaleOutput_of_endpointIdentity_highGamma_parentwiseLongCore_automatic
      D hD P (4 * sourceLoss) etaKT sourceEta delta0
      hbeta hEffectiveTarget hSourceEta hgamma hepsilonHalf
      hselectorSmall hdeltaBase hFOutput hFExactEffective
      hbufferedSixteenth hhigh hsmallFrozen hsmallFour hsmallFour
      hthirdDelta0 hsmallThirdEffective hthirdBudget hDensity hBase

#print axioms prefixMinThreshold_le
#print axioms highGammaAutomaticUniformStageThreshold_le
#print axioms canonicalBufferedRadius_le_target_of_endpointSmall
#print axioms highGammaAutomaticRawDelta0_pos
#print axioms AutomaticHighGammaAnalyticGatesAtRaw
#print axioms AutomaticHighGammaAnalyticGateProducer
#print axioms exists_highGamma_hLongGeometry_of_automaticAnalyticGates

end
end Family8EndpointIdentityHighGammaAutomaticHLongGeometryAdapterV1
