import Family8Grounding.Family8CanonicalBufferedGlobalKatzTaoBoundedFrozenAssemblyV1
import Family8Grounding.Family8FullRefinementActualDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalBufferedGlobalSourceAverageIdentityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyBoundedFiberPartitionCoreV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8AllFrostmanStickyUnionProducerV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2
open Family8FullRefinementActualDatumV1

noncomputable section

/-!
# Source average on the canonical global bounded partition

The global buffered cover of the full-refinement datum is full-active.  Its
active-fine reindexing is therefore a universe, as is the fine index of the
bounded partition.  Consequently the source restriction named by the frozen
assembly has exactly the original datum's average multiplicity.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

theorem canonicalBufferedGlobal_bounded_sourceAverage_eq
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTsource : IsKatzTao CKT D.family.bodyFamily)
    {etaF : Real} (hFsource : FrostmanHypotheses D etaF) :
    let E := fullRefinementDatum D
    let G := canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover G
    let Y := activeFineRestrictedShading G E.shading
    let M := Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
      delta (canonicalBufferedRadius W) CKT
    let hsource0 :
        (IndexedShadingRefinement.restrictTo E.shading
          G.activeFine).shading.shadingMass ≠ 0 := by
      have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
          D.shading.shadingMass :=
        delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
      have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
        ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
          ENNReal.coe_ne_top
      have hmass : E.shading.shadingMass ≠ 0 := by
        rw [fullRefinementDatum_shadingMass]
        exact ne_of_gt (hpositive.trans_le hfloor)
      have hactive : G.activeFine = Finset.univ := by
        rw [G.activeFine_eq_refined, fullRefinementDatum_refined]
      rw [hactive, restrictTo_univ_shadingMass]
      exact hmass
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      activeFineRestrictedSourceMass_ne_zero G E.shading hsource0
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        G hD.delta_pos hD.delta_le_half
          (canonicalBufferedRadius_le_one W hD.delta_pos
            hepsilon hepsilonHalf)
          hCKTfinite hKTsource
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      ((Sseq.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon))
      hcoarse M hM
    (IndexedShadingRefinement.restrictTo Y
      Pcoarse.asConvexFactorization.index.fine).shading.averageMultiplicity =
        D.shading.averageMultiplicity := by
  dsimp only
  let E := fullRefinementDatum D
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover G
  let Y := activeFineRestrictedShading G E.shading
  let M := Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
    delta (canonicalBufferedRadius W) CKT
  have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
  have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  have hactive : G.activeFine = Finset.univ := by
    rw [G.activeFine_eq_refined, fullRefinementDatum_refined]
  have hsource0 :
      (IndexedShadingRefinement.restrictTo E.shading
        G.activeFine).shading.shadingMass ≠ 0 := by
    rw [hactive, restrictTo_univ_shadingMass,
      fullRefinementDatum_shadingMass]
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero G E.shading hsource0
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      G hD.delta_pos hD.delta_le_half
        (canonicalBufferedRadius_le_one W hD.delta_pos
          hepsilon hepsilonHalf)
        hCKTfinite hKTsource
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    ((Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon))
    hcoarse M hM
  have hfine : Pcoarse.asConvexFactorization.index.fine = Finset.univ := rfl
  calc
    (IndexedShadingRefinement.restrictTo Y
        Pcoarse.asConvexFactorization.index.fine).shading.averageMultiplicity =
        Y.averageMultiplicity := by
      rw [hfine, restrictTo_univ_averageMultiplicity]
    _ = (activeFineShading G E.shading).averageMultiplicity :=
      activeFineRestrictedShading_averageMultiplicity G E.shading
    _ = E.shading.averageMultiplicity := by
      unfold Shading.averageMultiplicity
      rw [Family8AllFrostmanStickyUnionProducerV1.activeFineShading_shadingMass_eq_of_activeFine_eq_univ
          G E.shading hactive,
        Family8AllFrostmanStickyUnionProducerV1.activeFineShading_shadedUnion_eq_of_activeFine_eq_univ
          G E.shading hactive]
    _ = D.shading.averageMultiplicity :=
      fullRefinementDatum_averageMultiplicity D

#print axioms canonicalBufferedGlobal_bounded_sourceAverage_eq

end Witness
end
end Family8CanonicalBufferedGlobalSourceAverageIdentityV1
