import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8StickyKatzTaoBoundedFiberPartitionV4
import Family8Grounding.Family8StickyBoundedFiberSourceMassIdentityV2
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedGlobalBoundedSourceFloorV1

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
open Family8StickyBoundedFiberSourceMassIdentityV2
open Family8AllFrostmanStickyUnionProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3

noncomputable section

/-!
# Lossless source floor on the canonical global `delta -> b` cover

Unlike the tau-parent aggregation route, the canonical global cover acts on
the full-refinement copy of the original datum.  Its active fine set is the
whole source index type.  Reindexing it and replacing the partition's
branching fields by the exact Katz--Tao cap therefore preserves the original
source shading mass exactly; no source fibre cap divides the Frostman floor.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

theorem fullRefinement_canonicalBufferedGlobal_bounded_sourceMass_lower
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
    (delta : ENNReal) ^ (2 * etaF) <=
      (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass := by
  dsimp only
  let E := fullRefinementDatum D
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover G
  let Y := activeFineRestrictedShading G E.shading
  let M := katzTaoDoubledFiberNatCap delta
    (canonicalBufferedRadius W) CKT
  have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
  have hGactive : G.activeFine = Finset.univ := by
    rw [G.activeFine_eq_refined, fullRefinementDatum_refined]
  have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  have hsource0 :
      (IndexedShadingRefinement.restrictTo E.shading
        G.activeFine).shading.shadingMass ≠ 0 := by
    rw [hGactive, restrictTo_univ_shadingMass,
      fullRefinementDatum_shadingMass]
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero G E.shading hsource0
  have hKTfull : IsKatzTao CKT E.family.bodyFamily := hKTsource
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      G hD.delta_pos hD.delta_le_half
        (canonicalBufferedRadius_le_one W hD.delta_pos
          hepsilon hepsilonHalf)
        hCKTfinite hKTfull
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    ((Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon))
    hcoarse M hM
  have hsourceEq :=
    boundedFiberCoarseTubePartition_sourceActiveFineShading_mass_eq
      U ((Sseq.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon))
      hcoarse M hM Y
  have hUactive : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine G
  calc
    (delta : ENNReal) ^ (2 * etaF) <= D.shading.shadingMass := hfloor
    _ = E.shading.shadingMass := (fullRefinementDatum_shadingMass D).symm
    _ = (activeFineShading G E.shading).shadingMass :=
      (activeFineShading_shadingMass_eq_of_activeFine_eq_univ
        G E.shading hGactive).symm
    _ = Y.shadingMass :=
      (activeFineRestrictedShading_shadingMass G E.shading).symm
    _ = (activeFineShading U Y).shadingMass :=
      (activeFineShading_shadingMass_eq_of_activeFine_eq_univ
        U Y hUactive).symm
    _ = (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass := hsourceEq.symm

#print axioms
  fullRefinement_canonicalBufferedGlobal_bounded_sourceMass_lower

end Witness
end
end Family8CanonicalBufferedGlobalBoundedSourceFloorV1
