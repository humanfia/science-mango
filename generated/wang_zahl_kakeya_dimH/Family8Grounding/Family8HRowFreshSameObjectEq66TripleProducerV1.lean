import Family8Grounding.Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
import Family8Grounding.Family8NormalizedLongCoreEq66FactorOneV2
import Mathlib.Tactic

/-!
# Same-object Equation (66) triple after the HRow-fresh grounded run

The grounded HRow-fresh assembly already fixes one source datum, one frozen
assembly, and one selected-third certificate.  This module supplies the
remaining scalar step to the terminal correlated consumer.  Its sole
analytic input is the raw Equation-(66) source-to-frozen-third inequality on
that literal assembly.  The displayed `delta^(10 eta)` factor, the selected
coarse cardinality, and the ledger third loss are inserted here rather than
being assumed as the terminal `hTriple` statement.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8HRowFreshSameObjectEq66TripleProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8NormalizedLongCoreEq66FactorOneV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex fineIndex coarseIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  [Fintype fineIndex] [DecidableEq fineIndex]
  [Fintype coarseIndex] [DecidableEq coarseIndex]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-!
`hRawEq66` below is the earliest geometric seam: it is the uninflated
source-to-frozen-average conclusion delivered by the graph/incidence
argument.  The remaining hypotheses only identify the already selected
middle radius and coarse count with the canonical LongCore objects and place
the literal frozen average below the ledger's chosen third-loss scalar.
-/

/-- Turn the raw same-assembly Equation-(66) correlation into the exact
terminal `hTriple`.  No row, parent, coarse index, or fresh subtype is
selected in this proof. -/
theorem hTriple_of_sameObject_rawEq66
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti
        P.N P.epsilon P.eta Sseq)
    (fine : UniformTubeFamily (Sseq.tau W.m) fineIndex)
    (G : ConvexFamily coarseIndex)
    (U : StickyScaleCover fine (canonicalBufferedRadius W))
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal)
    (outputEta : Real)
    (T : NormalizedLongCoreCorrelatedEq66Inputs
      Dsource hDsource Cmulti Sseq P W fine G U Y Q A
        X CKT selectorLoss sourceMass sourceDensity
          massRetentionLoss densityRetentionLoss outputEta)
    (Aouter : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹)
    (hfine : (fullRefinementDatum Dsource).family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover W hDsource.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody ≤
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale (Aouter : ENNReal))
    (hAKT : 1024 * Aouter ≤
      Sseq.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta))))
    (hMiddleScale : T.middleScale = canonicalBufferedRadius W)
    (hCoarseCard : U.coarseCard =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hThirdLoss : A.frozenCoarse.averageMultiplicity ≤ T.thirdLoss)
    (hRawEq66 : Dsource.shading.averageMultiplicity ≤
      T.collapsedPrefix * A.frozenCoarse.averageMultiplicity) :
    Dsource.shading.averageMultiplicity ≤
      T.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              T.middleScale 1 T.thirdCount gamma) * T.thirdLoss) := by
  let E := fullRefinementDatum Dsource
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hDsource
  have hThirdCount : T.thirdCount =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card := by
    calc
      T.thirdCount = Fintype.card coarseIndex := T.thirdCount_eq
      _ = U.coarseCard := T.selectedThird.activeCoarseCard_eq
      _ = (canonicalBufferedGlobalCover W hDsource.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarse.card := hCoarseCard
  have hFactorOneCanonical : (1 : ENNReal) ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (canonicalBufferedRadius W) 1
          (canonicalBufferedGlobalCover W hDsource.delta_pos
            P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma :=
    one_le_canonicalBufferedGlobal_eq66Factor
      E hE Cmulti Sseq P W Aouter hbeta hgamma hepsilonHalf hrhoHalf
        hfine hC htauSmall hKTEvery hAKT
  have hFactorOne : (1 : ENNReal) ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          T.middleScale 1 T.thirdCount gamma := by
    rw [hMiddleScale, hThirdCount]
    exact hFactorOneCanonical
  have hInflatedThird : A.frozenCoarse.averageMultiplicity ≤
      ((delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            T.middleScale 1 T.thirdCount gamma) * T.thirdLoss := by
    calc
      A.frozenCoarse.averageMultiplicity ≤ T.thirdLoss := hThirdLoss
      _ = 1 * T.thirdLoss := by rw [one_mul]
      _ ≤ ((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              T.middleScale 1 T.thirdCount gamma) * T.thirdLoss :=
        mul_le_mul' hFactorOne le_rfl
  exact hRawEq66.trans (mul_le_mul' le_rfl hInflatedThird)

#print axioms hTriple_of_sameObject_rawEq66

end
end Family8HRowFreshSameObjectEq66TripleProducerV1
