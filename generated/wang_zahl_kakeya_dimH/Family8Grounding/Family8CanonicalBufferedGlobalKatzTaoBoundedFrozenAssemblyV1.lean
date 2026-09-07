import Family8Grounding.Family8CanonicalBufferedGlobalBoundedSourceFloorV1
import Family8Grounding.Family8StickyActiveKatzTaoBoundedFrozenAssemblyScaleV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedGlobalKatzTaoBoundedFrozenAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8FullRefinementActualDatumV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyActiveKatzTaoBoundedFrozenAssemblyScaleV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8CanonicalBufferedGlobalBoundedSourceFloorV1.Witness
open Family8AllFrostmanStickyUnionProducerV1

noncomputable section

/-!
# Canonical global bounded assembly with its lossless source floor

This specializes the scale-only Katz--Tao assembly producer to the literal
global `delta -> b` cover.  The returned assembly and the source-floor
statement use the same bounded partition object.  In contrast with the
tau-active aggregation route, no source fibre cap occurs.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

theorem exists_fullRefinement_canonicalBufferedGlobal_boundedFrozenAssembly
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    {etaF : Real} (hFsource : FrostmanHypotheses D etaF)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTsource : IsKatzTao CKT D.family.bodyFamily) :
    let E := fullRefinementDatum D
    let G := canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover G
    let Y := activeFineRestrictedShading G E.shading
    let M := katzTaoDoubledFiberNatCap delta
      (canonicalBufferedRadius W) CKT
    let hsource0 :
        (IndexedShadingRefinement.restrictTo E.shading
          G.activeFine).shading.shadingMass ≠ 0 := by
      have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
          D.shading.shadingMass :=
        delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
      have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
        ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
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
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ G.activeFine}
          (Fin U.coarseCard) /\
      (delta : ENNReal) ^ (2 * etaF) <=
        (sourceActiveFineShading
          Pcoarse.asConvexFactorization Y).shadingMass /\
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass <=
        ((A.loss : ENNReal) * (M : ENNReal)) *
          A.frozenCoarse.shadingMass /\
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingDensity *
          familyVolume (sourceActiveFineFamily Pcoarse.asConvexFactorization) <=
        ((A.loss : ENNReal) * (M : ENNReal)) *
          (A.frozenCoarse.shadingDensity * familyVolume U.coarse.bodyFamily) /\
      ∃ k ∈ Pcoarse.coarseIndices,
        0 < volume (finalFiberShading A k).shadedUnion /\
        (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  let E := fullRefinementDatum D
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon hepsilonHalf
  have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
  have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  have hmass : E.shading.shadingMass ≠ 0 := by
    rw [fullRefinementDatum_shadingMass]
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hactive : G.activeFine = Finset.univ := by
    rw [G.activeFine_eq_refined, fullRefinementDatum_refined]
  have hsource0 :
      (IndexedShadingRefinement.restrictTo E.shading
        G.activeFine).shading.shadingMass ≠ 0 := by
    rw [hactive, restrictTo_univ_shadingMass]
    exact hmass
  have hassembly :=
    exists_activeKatzTaoBounded_frozenComparableAssembly_of_scale
      E G hD.delta_pos hD.delta_le_half
        ((Sseq.delta_le_tau W.m).trans
          (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon))
        (canonicalBufferedRadius_le_one W hD.delta_pos
          hepsilon hepsilonHalf)
        hCKTfinite hKTsource 1 (by norm_num) hsource0
  obtain ⟨A, hAloss, hmassA, hdensityA, hproductA⟩ := hassembly
  refine ⟨A, hAloss, ?_, hmassA, hdensityA, hproductA⟩
  exact fullRefinement_canonicalBufferedGlobal_bounded_sourceMass_lower
    D hD Cmulti Sseq W hepsilon hepsilonHalf hFsource
      hCKTfinite hKTsource

#print axioms
  exists_fullRefinement_canonicalBufferedGlobal_boundedFrozenAssembly

end Witness
end
end Family8CanonicalBufferedGlobalKatzTaoBoundedFrozenAssemblyV1
