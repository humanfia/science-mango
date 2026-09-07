import Family8Grounding.Family8NormalizedLongCoreSourceTauParentFloorV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveBoundedFrozenAssemblyV2
import Family8Grounding.Family8StickyBoundedFiberSourceMassIdentityV2
import Mathlib.Tactic

/-!
# Exact-cap source floor on the core-native bounded tau partition, V5

V1 omitted a namespace; V2--V4 were malformed generation drafts. None is imported.
This transports the genuine source-to-`tau` Frostman/Katz--Tao mass floor
through the canonical active reindexing and the literal bounded-fibre
partition.  The divisor is exactly the first-outer doubled-fibre cap.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreTauActiveBoundedSourceFloorV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8FullRefinementActualDatumV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreSourceTauParentFloorV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberSourceMassIdentityV2
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The exact Frostman source floor on the bounded core-native `tau -> b`
partition used by the later same-assembly middle endpoint. -/
theorem fullRefinement_canonicalBufferedTauActive_bounded_sourceMass_lower_exactCap
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {etaF etaKT : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTEvery : C.base.IsKatzTaoAtEveryScale CKT) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let M := katzTaoDoubledFiberNatCap
      (S.tau W.m) (canonicalBufferedRadius W) CKT
    let hsource0 :
        (IndexedShadingRefinement.restrictTo Dtau.shading
          U0.activeFine).shading.shadingMass ≠ 0 := by
      have hsourceTau :
          (IndexedShadingRefinement.restrictTo E.shading
            (tauScaleCover E C S W).activeFine).shading.shadingMass ≠ 0 := by
        rw [(tauScaleCover E C S W).activeFine_eq_refined]
        exact fullRefinementDatum_restricted_shadingMass_ne_zero_of_frostman
          D hD hFsource
      exact canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E hE C S P W hepsilonHalf hsourceTau
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        U0
          (hD.delta_pos.trans_le (S.delta_le_tau W.m))
          ((tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
            (hbufferedSixteenth.trans (by
              change (1 : Real) / 16 <= (2 : Real)⁻¹
              norm_num)))
          (hbufferedSixteenth.trans (by
            change (1 : Real) / 16 <= (1 : Real)
            norm_num))
          hCKTfinite
          (tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
            E C S P W
              (hKTEvery (S.tau W.m)
                (S.delta_le_tau W.m)
                ((S.tau_le_theta W.m).trans (S.theta_le_one W.m))))
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse M hM
    (delta : ENNReal) ^ (2 * etaF) /
        (katzTaoDoubledFiberNatCap delta (S.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) <=
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  let M := katzTaoDoubledFiberNatCap
    (S.tau W.m) (canonicalBufferedRadius W) CKT
  have hsourceTau :
      (IndexedShadingRefinement.restrictTo E.shading
        (tauScaleCover E C S W).activeFine).shading.shadingMass ≠ 0 := by
    rw [(tauScaleCover E C S W).activeFine_eq_refined]
    exact fullRefinementDatum_restricted_shadingMass_ne_zero_of_frostman
      D hD hFsource
  have hsource0 :
      (IndexedShadingRefinement.restrictTo Dtau.shading
        U0.activeFine).shading.shadingMass ≠ 0 :=
    canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE C S P W hepsilonHalf hsourceTau
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ :=
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
      (hbufferedSixteenth.trans (by
        change (1 : Real) / 16 <= (2 : Real)⁻¹
        norm_num))
  have hrhoOne : canonicalBufferedRadius W <= 1 :=
    hbufferedSixteenth.trans (by
      change (1 : Real) / 16 <= (1 : Real)
      norm_num)
  have hKTtau : IsKatzTao CKT Dtau.family.bodyFamily :=
    tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
      E C S P W
        (hKTEvery (S.tau W.m)
          (S.delta_le_tau W.m)
          ((S.tau_le_theta W.m).trans (S.theta_le_one W.m)))
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      U0 (hD.delta_pos.trans_le (S.delta_le_tau W.m))
        htauHalf hrhoOne hCKTfinite hKTtau
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
    hcoarse M hM
  have hparent :=
    fullRefinement_sourceTau_parentAggregated_mass_lower_exactCap
      D hD C S W hFsource hKTsource
  have hsourceEq :=
    boundedFiberCoarseTubePartition_sourceActiveFineShading_mass_eq
      U (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hcoarse M hM Y
  have hU0active : U0.activeFine = Finset.univ :=
    canonicalBufferedTauActiveCover_activeFine
      E hE C S W P.epsilon_pos.le hepsilonHalf
  have hUactive : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine U0
  calc
    (delta : ENNReal) ^ (2 * etaF) /
        (katzTaoDoubledFiberNatCap delta (S.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) <=
        (parentAggregatedShading
          (tauScaleCover E C S W) E.shading).shadingMass := hparent
    _ = Dtau.shading.shadingMass := by rfl
    _ = (activeFineShading U0 Dtau.shading).shadingMass :=
      (activeFineShading_shadingMass_eq_of_activeFine_eq_univ
        U0 Dtau.shading hU0active).symm
    _ = Y.shadingMass :=
      (activeFineRestrictedShading_shadingMass U0 Dtau.shading).symm
    _ = (activeFineShading U Y).shadingMass :=
      (activeFineShading_shadingMass_eq_of_activeFine_eq_univ
        U Y hUactive).symm
    _ = (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass :=
      hsourceEq.symm

#print axioms
  fullRefinement_canonicalBufferedTauActive_bounded_sourceMass_lower_exactCap

end
end Family8NormalizedLongCoreTauActiveBoundedSourceFloorV5
