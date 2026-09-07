import Family8Grounding.Family8EndpointIdentityParameterLadderProducerV2
import Family8Grounding.Family8HRowFreshGroundedRunEq66ToDSOV1
import Family8Grounding.Family8ParameterCappedOutputEtaStrongFrostmanLongCoreOnlyMainLemmaV1
import Mathlib.Tactic

/-!
# Low-gamma grounded-run adapter for the top LongGeometry interface

This module is deliberately only glue.  It packages the literal inputs of
`dividingScaleOutput_of_groundedRun_hRowFresh_rawEq66` at the endpoint identity
cover and sequence, and exposes the resulting DSO through the ordinary
`ParameterLadder` top interface.  No high-gamma ladder or stronger all-scale
statement is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8EndpointIdentityLowGammaGroundedRunHLongGeometryAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8EndpointIdentityCoreSelectorV2
open Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityParameterLadderProducerV2
open Family8FullRefinementActualDatumV1
open Family8HRowFreshGroundedRunEq66ToDSOV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
variable {epsilon0 beta gamma targetEpsilon sourceEta : Real}

universe v

/-! ## Literal grounded-run context -/

/-- The literal data which the grounded-run / raw-Equation-(66) DSO consumes,
specialized only to the identity cover and one-step endpoint sequence used by
the top `hLongGeometry` callback.

The genuine mathematical seams remain fields: the `GroundedPaperFactorFiniteRun`,
its per-step power bounds and ledger identification, the collapsed/outer and
exponent budgets, the scale/card identifications, `hThirdLoss`, and
`hRawEq66`.  There is no field whose type is already a DSO. -/
structure LowGammaGroundedRunRawEq66Context
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family
      (identityRadiusCoherentCover (fullRefinementDatum Dsource).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hDsource.delta_le_half.trans (by norm_num))))
    (outputEta : Real) where
  fineIndex : Type
  coarseIndex : Type
  rowIndex : Type
  cellIndex : Type v
  [fineFintype : Fintype fineIndex]
  [fineDecidableEq : DecidableEq fineIndex]
  [coarseFintype : Fintype coarseIndex]
  [coarseDecidableEq : DecidableEq coarseIndex]
  [rowFintype : Fintype rowIndex]
  [rowDecidableEq : DecidableEq rowIndex]
  fine : UniformTubeFamily
    ((endpointScaleSequence delta
      (hDsource.delta_le_half.trans (by norm_num))).tau W.m) fineIndex
  G : ConvexFamily coarseIndex
  U : StickyScaleCover fine (canonicalBufferedRadius W)
  Y : Shading fine.bodyFamily
  Q : ConvexFactorization fine.bodyFamily G
  A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1
  X : ENNReal
  CKT : ENNReal
  selectorLoss : ENNReal
  sourceMass : ENNReal
  sourceDensity : ENNReal
  massRetentionLoss : ENNReal
  densityRetentionLoss : ENNReal
  selectedThird : SameObjectCorrelatedSelectedThirdCertificate
    (delta := delta) U Y Q A X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss outputEta
  a : NNReal
  b : NNReal
  Drow : ShadedConvexPlankFamily rowIndex a b
  theta : NNReal
  Crow : MutualThickeningClustering Drow theta
  q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1)
  cell : cellIndex → Set Space
  hcell : ∀ p, MeasurableSet (cell p)
  selectedCells : Finset cellIndex
  hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0
  hactive : (activeRetainedOwnerCellIndices
    Drow Crow q cell hcell selectedCells).Nonempty
  epsilonRow : Real
  betaRow : Real
  etaRow : Real
  M : NNReal
  correlationLoss : ENNReal
  Z : Prop66Eq66ComposerFromHRowFresh
    Drow Crow q cell hcell selectedCells hmass hactive
      epsilonRow betaRow etaRow M A.frozenCoarse.averageMultiplicity
        correlationLoss
  hCoefficientToRow : HRowFreshCorrelatedCoefficientToRowFactor
    (delta := delta) X selectorLoss outputEta
    Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M
  runN : Nat
  sourceStage : Nat
  finalStage : Nat
  sourceState : PaperFactorState
  finalState : PaperFactorState
  run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
    sourceState finalState
  uniformityExp : Real
  freshExp : Real
  hUniformityExp : 0 ≤ uniformityExp
  hFreshExp : 0 ≤ freshExp
  hUniformity : ∀ step, step ∈ run.productLedger.steps →
    step.uniformityLoss ≤
      ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
        (-uniformityExp)
  hFresh : ∀ step, step ∈ run.productLedger.steps →
    step.freshRetentionLoss ≤
      ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
        (-freshExp)
  middleScale : NNReal
  middleCount : Nat
  thirdCount : Nat
  hThirdCount : thirdCount = Fintype.card coarseIndex
  collapsedPrefix : ENNReal
  outerPrefix : ENNReal
  firstLoss : ENNReal
  thirdLoss : ENNReal
  countLoss : ENNReal
  ledgerId : CorrelatedEq66LedgerIdentification
    run.productLedger delta sourceIndex middleCount thirdCount
      firstLoss thirdLoss countLoss
  hCollapsed : collapsedPrefix ≤
    outerPrefix * A.frozenCoarse.averageMultiplicity
  hOuterRowFactor : outerPrefix *
      hRowFreshProp66Factor
        Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M ≤
    firstLoss * sectionEightScaleCountFrostmanFactor
      delta middleScale middleCount gamma
  hExponentBudget :
    ((runN : Real) * (uniformityExp + freshExp)) +
        ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
      3 * P.eta W.stage
  Aouter : NNReal
  hepsilonHalf : P.epsilon ≤ 1 / 2
  hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹
  hfine : (fullRefinementDatum Dsource).family.refinement.refined.Nonempty
  hC : canonicalFrostmanConstant
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
      closedBallFourBody ≤
    ((endpointScaleSequence delta
      (hDsource.delta_le_half.trans (by norm_num))).tau W.m : ENNReal) ^
      (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
        P W.stage)
  htauSmall :
    (endpointScaleSequence delta
      (hDsource.delta_le_half.trans (by norm_num))).tau W.m ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage
  hKTEvery :
    (identityRadiusCoherentCover
      (fullRefinementDatum Dsource).family).base.IsKatzTaoAtEveryScale
        (Aouter : ENNReal)
  hAKT : 1024 * Aouter ≤
    ((endpointScaleSequence delta
      (hDsource.delta_le_half.trans (by norm_num))).tau W.m) ^
      (-longIntervalDeltaLoss P.epsilon
        (10 * P.eta W.stage / (P.epsilon * beta)))
  hMiddleScale : middleScale = canonicalBufferedRadius W
  hCoarseCard : U.coarseCard =
    (canonicalBufferedGlobalCover W hDsource.delta_pos
      P.epsilon_pos.le hepsilonHalf).activeCoarse.card
  hThirdLoss : A.frozenCoarse.averageMultiplicity ≤ thirdLoss
  hRawEq66 : Dsource.shading.averageMultiplicity ≤
    collapsedPrefix * A.frozenCoarse.averageMultiplicity

/-- The certificate is consumed only by the already exact grounded-run DSO
endpoint.  The low-gamma hypothesis is used solely to supply its `gamma ≤ 1`
premise. -/
theorem LowGammaGroundedRunRawEq66Context.toDividingScaleOutput
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family
      (identityRadiusCoherentCover (fullRefinementDatum Dsource).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hDsource.delta_le_half.trans (by norm_num))))
    (outputEta : Real)
    (K : LowGammaGroundedRunRawEq66Context.{v} Dsource hDsource P W outputEta)
    (hbeta : 0 < beta) (hLowGamma : gamma ≤ 2 / 3)
    (hSmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  letI := K.fineFintype
  letI := K.fineDecidableEq
  letI := K.coarseFintype
  letI := K.coarseDecidableEq
  letI := K.rowFintype
  letI := K.rowDecidableEq
  have hGammaOne : gamma ≤ 1 := by linarith
  exact dividingScaleOutput_of_groundedRun_hRowFresh_rawEq66
    Dsource hDsource
    (identityRadiusCoherentCover (fullRefinementDatum Dsource).family)
    (endpointScaleSequence delta
      (hDsource.delta_le_half.trans (by norm_num)))
    P W K.fine K.G K.U K.Y K.Q K.A K.X K.CKT K.selectorLoss
    K.sourceMass K.sourceDensity K.massRetentionLoss K.densityRetentionLoss
    outputEta K.selectedThird K.Drow K.Crow K.q K.cell K.hcell
    K.selectedCells K.hmass K.hactive K.M K.correlationLoss K.Z
    K.hCoefficientToRow K.run K.hUniformityExp K.hFreshExp
    K.hUniformity K.hFresh K.middleScale K.middleCount K.thirdCount
    K.hThirdCount K.collapsedPrefix K.outerPrefix K.firstLoss K.thirdLoss
    K.countLoss K.ledgerId K.hCollapsed K.hOuterRowFactor
    K.hExponentBudget K.Aouter hbeta hGammaOne K.hepsilonHalf K.hrhoHalf
    K.hfine K.hC K.htauSmall K.hKTEvery K.hAKT K.hMiddleScale
    K.hCoarseCard K.hThirdLoss K.hRawEq66 hSmall hTargetEpsilon

/-! ## Full-context producer and top adapter -/

/-- The only raw scale needed by this glue layer is the exact final DSO
threshold.  All earlier construction thresholds stay with the full-context
producer which builds the literal run certificate. -/
def lowGammaGroundedRunRawDelta0
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon : Real) : NNReal :=
  sectionEightThreeScaleActualThreshold gamma
    (sectionEightSourceLoss P targetEpsilon)

theorem lowGammaGroundedRunRawDelta0_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon : Real) :
    0 < lowGammaGroundedRunRawDelta0 P targetEpsilon := by
  exact sectionEightThreeScaleActualThreshold_pos _ _

/-- A producer is invoked with the same full parameter/datum context as the
top LongGeometry callback.  Its output is a literal grounded-run certificate,
not a DSO and not an assumed theorem. -/
abbrev LowGammaGroundedRunFullContextProducer
    (P : ParameterLadder epsilon0 beta gamma) : Prop :=
  forall targetEpsilon : Real, forall _hTarget : 0 < targetEpsilon,
  forall etaKT sourceEta : Real, forall delta0 : NNReal,
  forall _hEtaKT : 0 < etaKT,
  forall _hEtaKTCap : etaKT ≤ P.epsilon ^ 2 * P.eta 0 / 32,
  forall _hSourceEta : 0 < sourceEta,
  forall _hSourceEtaCap : sourceEta ≤ P.eta 0,
  forall _hDelta0 : 0 < delta0,
  forall _hDelta0Half : delta0 ≤ (2 : NNReal)⁻¹,
  forall _hKTExact : KatzTaoAtParameters beta
    (sectionEightFixedNu P) etaKT delta0,
  forall _hKTRelative : KatzTaoAtRelativeScaleParameters beta
    (sectionEightFixedNu P) etaKT delta0,
  forall _hFExact : FrostmanAtParameters gamma
    (sectionEightSourceLoss P targetEpsilon) sourceEta delta0,
  forall _hFRelative : FrostmanAtRelativeScaleParameters gamma
    (sectionEightSourceLoss P targetEpsilon) sourceEta delta0,
    exists contextDelta0 : NNReal, 0 < contextDelta0 ∧
      forall (delta : NNReal) (sourceIndex : Type)
        [Fintype sourceIndex] [DecidableEq sourceIndex]
        (Dsource : ActualTubeDatum delta sourceIndex)
        (hDsource : Dsource.IsAdmissible),
      forall _hdelta : delta ≤ contextDelta0,
      forall _hFSource : FrostmanHypotheses Dsource sourceEta,
      forall _hmass : Dsource.shading.shadingMass ≠ 0,
      forall W : NormalizedLongIntervalCoreWitness
        (fullRefinementDatum Dsource).family
        (identityRadiusCoherentCover (fullRefinementDatum Dsource).family)
        P.N P.epsilon P.eta
        (endpointScaleSequence delta
          (hDsource.delta_le_half.trans (by norm_num))),
        Nonempty
          (LowGammaGroundedRunRawEq66Context.{v}
            Dsource hDsource P W sourceEta)

/-- The ordinary-ladder low-gamma result in exactly the capped strong-Frostman
`hLongGeometry` shape used by the top consumer. -/
theorem exists_lowGamma_hLongGeometry_of_groundedRunFullContext
    (hbeta : 0 < beta) (hgap : beta < gamma)
    (hLowGamma : gamma ≤ 2 / 3)
    (hContext : LowGammaGroundedRunFullContextProducer
      (endpointIdentityParameterLadder hbeta hgap)) :
    exists epsilon0' : Real,
    exists P : ParameterLadder epsilon0' beta gamma,
    forall targetEpsilon : Real, 0 < targetEpsilon →
    forall etaKT sourceEta : Real, forall delta0 : NNReal,
      0 < etaKT →
      etaKT ≤ P.epsilon ^ 2 * P.eta 0 / 32 →
      0 < sourceEta → sourceEta ≤ P.eta 0 →
      0 < delta0 → delta0 ≤ (2 : NNReal)⁻¹ →
      KatzTaoAtParameters
        beta (sectionEightFixedNu P) etaKT delta0 →
      KatzTaoAtRelativeScaleParameters
        beta (sectionEightFixedNu P) etaKT delta0 →
      FrostmanAtParameters gamma
        (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 →
      FrostmanAtRelativeScaleParameters gamma
        (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 →
        exists rawDelta0 : NNReal, 0 < rawDelta0 ∧
          forall (delta : NNReal) (sourceIndex : Type)
            [Fintype sourceIndex] [DecidableEq sourceIndex]
            (Dsource : ActualTubeDatum delta sourceIndex)
            (hDsource : Dsource.IsAdmissible),
              delta ≤ rawDelta0 →
              FrostmanHypotheses Dsource sourceEta →
              Dsource.shading.shadingMass ≠ 0 →
                forall W : NormalizedLongIntervalCoreWitness
                  (fullRefinementDatum Dsource).family
                  (identityRadiusCoherentCover
                    (fullRefinementDatum Dsource).family)
                  P.N P.epsilon P.eta
                  (endpointScaleSequence delta
                    (hDsource.delta_le_half.trans (by norm_num))),
                  DividingScaleOutput Dsource P
                    (4 * sectionEightSourceLoss P targetEpsilon) := by
  let P := endpointIdentityParameterLadder hbeta hgap
  refine ⟨endpointIdentityEpsilon0 beta gamma, P, ?_⟩
  intro targetEpsilon hTarget etaKT sourceEta delta0
    hEtaKT hEtaKTCap hSourceEta hSourceEtaCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative
  obtain ⟨contextDelta0, hContextDelta0, hContextAt⟩ :=
    hContext targetEpsilon hTarget etaKT sourceEta delta0
      hEtaKT hEtaKTCap hSourceEta hSourceEtaCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExact hFRelative
  let rawDelta0 := min contextDelta0
    (lowGammaGroundedRunRawDelta0 P targetEpsilon)
  have hRawDelta0 : 0 < rawDelta0 := by
    dsimp only [rawDelta0]
    exact lt_min hContextDelta0
      (lowGammaGroundedRunRawDelta0_pos P targetEpsilon)
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta sourceIndex _ _ Dsource hDsource hdelta hFSource hmass W
  have hdeltaContext : delta ≤ contextDelta0 := by
    exact hdelta.trans (by
      dsimp only [rawDelta0]
      exact min_le_left _ _)
  have hdeltaDSO :
      delta ≤ lowGammaGroundedRunRawDelta0 P targetEpsilon := by
    exact hdelta.trans (by
      dsimp only [rawDelta0]
      exact min_le_right _ _)
  obtain ⟨K⟩ := hContextAt delta sourceIndex Dsource hDsource
    hdeltaContext hFSource hmass W
  have hSmall : delta ≤ sectionEightThreeScaleActualThreshold gamma
      ((4 * sectionEightSourceLoss P targetEpsilon) / 4) := by
    simpa only [lowGammaGroundedRunRawDelta0,
      show (4 * sectionEightSourceLoss P targetEpsilon) / 4 =
        sectionEightSourceLoss P targetEpsilon by ring] using hdeltaDSO
  have hEffectiveTarget :
      0 < 4 * sectionEightSourceLoss P targetEpsilon := by
    have hSourceLoss : 0 < sectionEightSourceLoss P targetEpsilon :=
      sectionEightSourceLoss_pos P hTarget
    positivity
  exact K.toDividingScaleOutput Dsource hDsource P W sourceEta hbeta
    hLowGamma hSmall hEffectiveTarget

/-- Name the exact proposition shared by the low- and high-gamma adapters. -/
abbrev CappedStrongFrostmanHLongGeometry (beta gamma : Real) : Prop :=
  exists epsilon0 : Real,
  exists P : ParameterLadder epsilon0 beta gamma,
  forall targetEpsilon : Real, 0 < targetEpsilon →
  forall etaKT sourceEta : Real, forall delta0 : NNReal,
    0 < etaKT →
    etaKT ≤ P.epsilon ^ 2 * P.eta 0 / 32 →
    0 < sourceEta → sourceEta ≤ P.eta 0 →
    0 < delta0 → delta0 ≤ (2 : NNReal)⁻¹ →
    KatzTaoAtParameters beta (sectionEightFixedNu P) etaKT delta0 →
    KatzTaoAtRelativeScaleParameters
      beta (sectionEightFixedNu P) etaKT delta0 →
    FrostmanAtParameters gamma
      (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 →
    FrostmanAtRelativeScaleParameters gamma
      (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 →
      exists rawDelta0 : NNReal, 0 < rawDelta0 ∧
        forall (delta : NNReal) (sourceIndex : Type)
          [Fintype sourceIndex] [DecidableEq sourceIndex]
          (Dsource : ActualTubeDatum delta sourceIndex)
          (hDsource : Dsource.IsAdmissible),
            delta ≤ rawDelta0 →
            FrostmanHypotheses Dsource sourceEta →
            Dsource.shading.shadingMass ≠ 0 →
              forall W : NormalizedLongIntervalCoreWitness
                (fullRefinementDatum Dsource).family
                (identityRadiusCoherentCover
                  (fullRefinementDatum Dsource).family)
                P.N P.epsilon P.eta
                (endpointScaleSequence delta
                  (hDsource.delta_le_half.trans (by norm_num))),
                DividingScaleOutput Dsource P
                  (4 * sectionEightSourceLoss P targetEpsilon)

/-- Pure case-split glue: a low-gamma and a high-gamma producer with the same
top proposition combine without strengthening either branch. -/
theorem cappedStrongFrostman_hLongGeometry_of_gamma_split
    (hLow : gamma ≤ 2 / 3 →
      CappedStrongFrostmanHLongGeometry beta gamma)
    (hHigh : 2 / 3 < gamma →
      CappedStrongFrostmanHLongGeometry beta gamma) :
    CappedStrongFrostmanHLongGeometry beta gamma := by
  by_cases hgamma : gamma ≤ 2 / 3
  · exact hLow hgamma
  · exact hHigh (lt_of_not_ge hgamma)

#print axioms LowGammaGroundedRunRawEq66Context
#print axioms LowGammaGroundedRunRawEq66Context.toDividingScaleOutput
#print axioms lowGammaGroundedRunRawDelta0_pos
#print axioms LowGammaGroundedRunFullContextProducer
#print axioms exists_lowGamma_hLongGeometry_of_groundedRunFullContext
#print axioms CappedStrongFrostmanHLongGeometry
#print axioms cappedStrongFrostman_hLongGeometry_of_gamma_split

end
end Family8EndpointIdentityLowGammaGroundedRunHLongGeometryAdapterV1
