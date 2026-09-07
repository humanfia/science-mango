import Family8Grounding.Family8StickyActiveKatzTaoBoundedFrozenAssemblyScaleV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8FullRefinementActualDatumV1
import Mathlib.Tactic

/-!
# Compact core-native bounded frozen assembly on the tau interval, V2

Only the assembly, its literal loss identity, and one positive final fiber
are retained.  This is the smallest choice consumed by the positive-middle
and same-assembly endpoints.  V1 had a malformed dependent existential and
is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreTauActiveBoundedFrozenAssemblyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyActiveKatzTaoBoundedFrozenAssemblyScaleV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- A compact canonical assembly choice on the true `tau -> b` interval. -/
theorem exists_fullRefinement_canonicalBufferedTauActive_boundedFrozenAssembly
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {etaF : Real} (hFsource : FrostmanHypotheses D etaF)
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
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) /\
      ∃ k ∈ Pcoarse.coarseIndices,
        0 < volume (finalFiberShading A k).shadedUnion := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  have htauPos : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
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
  obtain ⟨A, hLoss, _hMass, _hDensity, k, hk, hpositive, _hproduct⟩ :=
    exists_activeKatzTaoBounded_frozenComparableAssembly_of_scale
      Dtau U0 htauPos htauHalf
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hrhoOne hCKTfinite hKTtau 1 (by norm_num) hsource0
  exact ⟨A, hLoss, k, hk, hpositive⟩

#print axioms
  exists_fullRefinement_canonicalBufferedTauActive_boundedFrozenAssembly

end
end Family8NormalizedLongCoreTauActiveBoundedFrozenAssemblyV2
