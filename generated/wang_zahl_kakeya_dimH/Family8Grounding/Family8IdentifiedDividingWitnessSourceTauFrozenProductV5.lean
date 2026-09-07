import Family8Grounding.Family8IdentifiedDividingWitnessSourceTauFrozenProductV3
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessSourceTauFrozenProductV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedCrossingSourceTauActualAverageV2
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
open Family8IdentifiedDividingWitnessSourceTauFrozenProductV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# The direct source-tau frozen product on one identified witness

The predecessor exposed retention and the frozen outer/fibre product as two
inequalities on the same canonical assembly.  This successor composes them
and keeps that assembly and its surviving fibre visible.  It therefore
leaves exactly two analytic estimates at the middle seam: one for
`A.frozenCoarse` and one for `finalFiberShading A k`.

V4 is a failed namespace draft and is not imported.
-/

/-- Once the two visible actual averages have separate analytic bounds, the
already-retained frozen product uses those bounds without changing data. -/
theorem sourceAverage_le_fourLoss_mul_outerInnerBounds
    {source loss outer fiber outerBound fiberBound : ENNReal}
    (hProduct : source <= (4 * loss) * (outer * fiber))
    (hOuter : outer <= outerBound)
    (hFiber : fiber <= fiberBound) :
    source <= (4 * loss) * (outerBound * fiberBound) := by
  exact hProduct.trans
    (mul_le_mul' le_rfl (mul_le_mul' hOuter hFiber))

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The canonical buffered assembly and one surviving actual fibre give the
direct source-to-tau parent-average product on the same identified witness.
No outer or fibre multiplicity estimate is assumed or manufactured here. -/
theorem exists_canonicalBuffered_sourceTau_frozenProduct
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D C S W.m).activeFine).shading.shadingMass ≠ 0) :
    let rho :=
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W
    let hbuffered : S.IsBuffered P.epsilon W.m rho :=
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius_isBuffered
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf
    let Y := sourceTauFullShading D C S W.m
    let U := bufferedIntervalCover D hD C S P.epsilon
      P.epsilon_pos.le W.m rho hbuffered
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        D hD C S P.epsilon P.epsilon_pos.le W.m rho hbuffered hsourceTau
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            D hD S P.epsilon_pos.le W.m rho hbuffered) Y hsource).asConvexFactorization
          Y 1,
      A.loss = frozenComparableLoss (bufferedLowerIndex D C S W.m)
        (Fin U.coarseCard) ∧
      ∃ k : Fin U.coarseCard, k ∈ U.activeCoarse ∧
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (parentAggregatedShading (sourceTauCover D C S W.m)
            D.shading).averageMultiplicity <=
          (4 * (frozenComparableLoss (bufferedLowerIndex D C S W.m)
            (Fin U.coarseCard) : ENNReal)) *
            (A.frozenCoarse.averageMultiplicity *
              (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  obtain ⟨A, hLoss, hRetained, k, hk, hFiberVolume, hRefinement⟩ :=
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.exists_canonicalBuffered_sourceTau_frozenAssembly
      D hD C S P W hepsilonHalf hsourceTau
  refine ⟨A, hLoss, k, hk, hFiberVolume, ?_⟩
  exact sourceAverage_le_fourLoss_mul_outerFiber hRetained hRefinement

#print axioms exists_canonicalBuffered_sourceTau_frozenProduct

end Witness

#print axioms sourceAverage_le_fourLoss_mul_outerInnerBounds

end

end Family8IdentifiedDividingWitnessSourceTauFrozenProductV5
