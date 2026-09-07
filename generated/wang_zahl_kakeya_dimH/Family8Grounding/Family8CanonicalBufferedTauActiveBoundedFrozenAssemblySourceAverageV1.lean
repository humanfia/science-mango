import Family8Grounding.Family8StickyActiveKatzTaoBoundedFrozenAssemblySourceAverageV3
import Family8Grounding.Family8CanonicalBufferedTauActiveKatzTaoBoundedFrozenAssemblyV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveBoundedFrozenAssemblySourceAverageV1

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
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8IdentifiedDividingWitnessTauActivePowerProductV3.Witness
open Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8FullRefinementActualDatumV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8TauActiveNativeKatzTaoTransportV4.Witness
open Family8StickyActiveKatzTaoBoundedFrozenAssemblySourceAverageV3

noncomputable section

/-!
# Canonical tau-active bounded source-average product

Every scale and dependent-family input of the generic bounded producer is
discharged from the identified witness and the coherent every-scale
Katz--Tao certificate.  The resulting source average is the literal
tau-active parent average, and the same `Pcoarse/A/k` is ready for the frozen
outer third-factor estimate.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem exists_fullRefinement_canonicalBufferedTauActive_bounded_sourceAverageProduct
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W ≤ (1 / 16 : NNReal))
    {etaF : Real} (hFsource : FrostmanHypotheses D etaF)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U0 := canonicalBufferedTauActiveCover E hE Cmulti Sseq W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E Cmulti Sseq W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let M := katzTaoDoubledFiberNatCap
      (Sseq.tau W.m) (canonicalBufferedRadius W) CKT
    let hsource0 :
        (IndexedShadingRefinement.restrictTo Dtau.shading
          U0.activeFine).shading.shadingMass ≠ 0 := by
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤
            D.shading.shadingMass :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
        have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
        exact ne_of_gt (hpositive.trans_le hfloor)
      exact canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E hE Cmulti Sseq P W hepsilonHalf
          (fullRefinement_sourceTau_activeMass_ne_zero
            D Cmulti Sseq W.m hmass)
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
    let hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        U0
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          ((tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
            (hbufferedSixteenth.trans (by
              change (1 : Real) / 16 ≤ (2 : Real)⁻¹
              norm_num)))
          (hbufferedSixteenth.trans (by
            change (1 : Real) / 16 ≤ (1 : Real)
            norm_num))
          hCKTfinite
          (tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
            (fullRefinementDatum D) Cmulti Sseq W
              (hKTEvery (Sseq.tau W.m)
                (Sseq.delta_le_tau W.m)
                ((Sseq.tau_le_theta W.m).trans (Sseq.theta_le_one W.m))))
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse M hM
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) ∧
      ∃ k ∈ Pcoarse.coarseIndices,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) ∧
        Dtau.shading.averageMultiplicity ≤
          (4 * (A.loss : ENNReal)) *
            (A.frozenCoarse.averageMultiplicity *
              (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U0 := canonicalBufferedTauActiveCover E hE Cmulti Sseq W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E Cmulti Sseq W
  have htauPos : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hsixteenHalf : (1 / 16 : NNReal) ≤ (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 ≤ (2 : Real)⁻¹
    norm_num
  have htauHalf : Sseq.tau W.m ≤ (2 : NNReal)⁻¹ :=
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
      (hbufferedSixteenth.trans hsixteenHalf)
  have hsixteenOne : (1 / 16 : NNReal) ≤ 1 := by
    change (1 : Real) / 16 ≤ (1 : Real)
    norm_num
  have hrhoOne : canonicalBufferedRadius W ≤ 1 :=
    hbufferedSixteenth.trans hsixteenOne
  have hKTtau : IsKatzTao CKT Dtau.family.bodyFamily :=
    tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
      E Cmulti Sseq W
        (hKTEvery (Sseq.tau W.m)
          (Sseq.delta_le_tau W.m)
          ((Sseq.tau_le_theta W.m).trans (Sseq.theta_le_one W.m)))
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤ D.shading.shadingMass :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
    have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsourceTau := fullRefinement_sourceTau_activeMass_ne_zero
    D Cmulti Sseq W.m hmass
  have hsource0 :
      (IndexedShadingRefinement.restrictTo Dtau.shading
        U0.activeFine).shading.shadingMass ≠ 0 :=
    canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE Cmulti Sseq P W hepsilonHalf hsourceTau
  obtain ⟨A, hAloss, k, hk, hkpositive, hproduct, hsourceProduct⟩ :=
    exists_activeKatzTaoBounded_frozenComparable_sourceAverageProduct
      Dtau U0 htauPos htauHalf
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hrhoOne hCKTfinite hKTtau 1 (by norm_num) hsource0
  have hactiveAverage :=
    canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
      E hE Cmulti Sseq P W hepsilonHalf
  rw [hactiveAverage] at hsourceProduct
  exact ⟨A, hAloss, k, hk, hkpositive, hproduct, hsourceProduct⟩

#print axioms
  exists_fullRefinement_canonicalBufferedTauActive_bounded_sourceAverageProduct

end Witness
end
end Family8CanonicalBufferedTauActiveBoundedFrozenAssemblySourceAverageV1
