import Family8Grounding.Family8IdentifiedDividingWitnessSourceTauFrozenProductV5
import Family8Grounding.Family8FullRefinementActualDatumV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessSourceTauFrozenProductV6

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
open Family8FullRefinementActualDatumV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# Original nonzero mass supplies the canonical source-tau product

Installing full refinement metadata changes neither the tubes nor the
shading.  It makes every source index active, so the original nonzero shading
mass automatically discharges the only structural mass premise of the
canonical source-to-tau frozen-product theorem.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- On the full-refinement copy of the original datum, nonzero original mass
automatically produces one canonical assembly and its direct source-to-tau
outer/fibre product. -/
theorem exists_fullRefinement_canonicalBuffered_sourceTau_frozenProduct
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hmass : D.shading.shadingMass ≠ 0) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let rho :=
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius W
    let hbuffered : S.IsBuffered P.epsilon W.m rho :=
      Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness.canonicalBufferedRadius_isBuffered
        W hE.delta_pos P.epsilon_pos.le hepsilonHalf
    let Y := sourceTauFullShading E C S W.m
    let U := bufferedIntervalCover E hE C S P.epsilon
      P.epsilon_pos.le W.m rho hbuffered
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        E hE C S P.epsilon P.epsilon_pos.le W.m rho hbuffered
          (Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
            D C S W.m hmass)
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            E hE S P.epsilon_pos.le W.m rho hbuffered) Y hsource).asConvexFactorization
          Y 1,
      A.loss = frozenComparableLoss (bufferedLowerIndex E C S W.m)
        (Fin U.coarseCard) ∧
      ∃ k : Fin U.coarseCard, k ∈ U.activeCoarse ∧
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (parentAggregatedShading (sourceTauCover E C S W.m)
            E.shading).averageMultiplicity <=
          (4 * (frozenComparableLoss (bufferedLowerIndex E C S W.m)
            (Fin U.coarseCard) : ENNReal)) *
            (A.frozenCoarse.averageMultiplicity *
              (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  have hsourceTau :
      (IndexedShadingRefinement.restrictTo (fullRefinementDatum D).shading
        (sourceTauCover (fullRefinementDatum D) C S W.m).activeFine).shading.shadingMass ≠
          0 :=
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
      D C S W.m hmass
  exact
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV5.Witness.exists_canonicalBuffered_sourceTau_frozenProduct
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P W hepsilonHalf hsourceTau

#print axioms
  exists_fullRefinement_canonicalBuffered_sourceTau_frozenProduct

end Witness

end

end Family8IdentifiedDividingWitnessSourceTauFrozenProductV6
