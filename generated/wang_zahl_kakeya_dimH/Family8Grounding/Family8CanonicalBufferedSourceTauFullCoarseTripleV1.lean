import Family8Grounding.Family8CanonicalBufferedGlobalLongIntervalMiddleFactorV1
import Family8Grounding.Family8IdentifiedDividingWitnessSourceTauFrozenProductV5
import Family8Grounding.Family8ExactAssemblySameDataFiberBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedSourceTauFullCoarseTripleV1

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
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyActiveCoarseFullDatumV1
open Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness
open Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly

noncomputable section

/-!
# Insert the literal global `T_b` average into the actual source-tau product

The canonical full coarse shading has nonzero union and hence average
multiplicity at least one.  Consequently the already-constructed source-tau
frozen product can contain this exact same `T_b` average as an additional
middle factor.  This produces the structural triple consumed by Eq. (66)
without identifying the global full shading with the frozen assembly
shading (those averages are not definitionally equal).
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem one_le_canonicalBufferedGlobalFullCoarse_averageMultiplicity
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    1 <=
      (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos P.epsilon_pos.le
          hepsilonHalf).shading.averageMultiplicity := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hcoarse : G.activeCoarse.Nonempty :=
    canonicalBufferedGlobalCover_activeCoarse_nonempty W hD.delta_pos
      P.epsilon_pos.le hepsilonHalf hfine
  obtain ⟨k, hk⟩ := hcoarse
  let kk : {k // k ∈ G.activeCoarse} := ⟨k, hk⟩
  have hb : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have htube : 0 < volume (G.coarse.tubes k).carrier :=
    (G.coarse.tubes k).volume_pos hb
  have hsubset :
      (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos P.epsilon_pos.le hepsilonHalf).shading.carrier kk <=
      (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos P.epsilon_pos.le hepsilonHalf).shading.shadedUnion := by
    exact Set.subset_iUnion (fun j =>
      (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos P.epsilon_pos.le hepsilonHalf).shading.carrier j) kk
  have hcarrier : 0 < volume
      ((canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos P.epsilon_pos.le hepsilonHalf).shading.carrier kk) := by
    simpa only [canonicalBufferedGlobalFullCoarseDatum,
      activeCoarseFullDatum_shading_carrier, kk, G] using htube
  have hunion : 0 < volume
      (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
        hD.delta_pos P.epsilon_pos.le
          hepsilonHalf).shading.shadedUnion :=
    hcarrier.trans_le (measure_mono hsubset)
  exact one_le_averageMultiplicity_of_volume_shadedUnion_ne_zero _ hunion.ne'

theorem exists_canonicalBuffered_sourceTau_fullCoarse_frozenTriple
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D Cmulti Sseq W.m).activeFine).shading.shadingMass ≠ 0) :
    let rho := canonicalBufferedRadius W
    let hbuffered : Sseq.IsBuffered P.epsilon W.m rho :=
      canonicalBufferedRadius_isBuffered
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf
    let Y := sourceTauFullShading D Cmulti Sseq W.m
    let U := bufferedIntervalCover D hD Cmulti Sseq P.epsilon
      P.epsilon_pos.le W.m rho hbuffered
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        D hD Cmulti Sseq P.epsilon P.epsilon_pos.le W.m rho hbuffered hsourceTau
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            D hD Sseq P.epsilon_pos.le W.m rho hbuffered) Y hsource).asConvexFactorization
          Y 1,
      A.loss = frozenComparableLoss
          (bufferedLowerIndex D Cmulti Sseq W.m) (Fin U.coarseCard) /\
      exists k : Fin U.coarseCard, k ∈ U.activeCoarse /\
        0 < volume (finalFiberShading A k).shadedUnion /\
        (parentAggregatedShading (sourceTauCover D Cmulti Sseq W.m)
            D.shading).averageMultiplicity <=
          (4 * (frozenComparableLoss
            (bufferedLowerIndex D Cmulti Sseq W.m)
              (Fin U.coarseCard) : ENNReal)) *
            ((canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
                hD.delta_pos P.epsilon_pos.le
                  hepsilonHalf).shading.averageMultiplicity *
              (A.frozenCoarse.averageMultiplicity *
                (finalFiberShading A k).averageMultiplicity)) := by
  dsimp only
  obtain ⟨A, hLoss, k, hk, hFiber, hProduct⟩ :=
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV5.Witness.exists_canonicalBuffered_sourceTau_frozenProduct
      D hD Cmulti Sseq P W hepsilonHalf hsourceTau
  refine ⟨A, hLoss, k, hk, hFiber, hProduct.trans ?_⟩
  have hone := one_le_canonicalBufferedGlobalFullCoarse_averageMultiplicity
    D hD Cmulti Sseq P W hepsilonHalf hfine
  apply mul_le_mul' le_rfl
  calc
    A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity =
        1 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) := by rw [one_mul]
    _ <=
        (canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
            hD.delta_pos P.epsilon_pos.le
              hepsilonHalf).shading.averageMultiplicity *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) :=
      mul_le_mul' hone le_rfl

#print axioms one_le_canonicalBufferedGlobalFullCoarse_averageMultiplicity
#print axioms exists_canonicalBuffered_sourceTau_fullCoarse_frozenTriple

end Witness
end
end Family8CanonicalBufferedSourceTauFullCoarseTripleV1
