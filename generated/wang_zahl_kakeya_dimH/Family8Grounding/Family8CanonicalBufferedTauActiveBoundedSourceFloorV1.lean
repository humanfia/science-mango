import Family8Grounding.Family8CanonicalBufferedTauActiveKatzTaoBoundedFrozenAssemblyV4
import Family8Grounding.Family8FullRefinementSourceTauParentFloorV3
import Family8Grounding.Family8StickyBoundedFiberSourceMassIdentityV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveBoundedSourceFloorV1

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
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8TauActiveNativeKatzTaoTransportV4.Witness
open Family8FullRefinementSourceTauParentFloorV3.Witness
open Family8StickyBoundedFiberSourceMassIdentityV2

noncomputable section

/-!
# The source-to-tau floor on the literal bounded frozen partition

The exact source-to-tau parent floor is transported through the canonical
tau-active reindexing and then through the bounded-fibre partition without
any additional loss. The resulting lower bound names precisely the source
shading of the same partition used by the canonical bounded frozen assembly.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem fullRefinement_canonicalBufferedTauActive_bounded_sourceMass_lower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W ≤ (1 / 16 : NNReal))
    {etaF etaKT : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
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
    (delta : ENNReal) ^ (2 * etaF) /
        ((katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) + 1 : Nat) : ENNReal) ≤
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U0 := canonicalBufferedTauActiveCover E hE Cmulti Sseq W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E Cmulti Sseq W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  let M := katzTaoDoubledFiberNatCap
    (Sseq.tau W.m) (canonicalBufferedRadius W) CKT
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaF) ≤
        D.shading.shadingMass :=
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
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
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
  have hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      U0 (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        htauHalf hrhoOne hCKTfinite hKTtau
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
    hcoarse M hM
  have hparent :=
    fullRefinement_sourceTau_parentAggregated_mass_lower
      D hD Cmulti Sseq W hFsource hKTsource
  have hsourceEq :=
    boundedFiberCoarseTubePartition_sourceActiveFineShading_mass_eq
      U (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hcoarse M hM Y
  have hU0active : U0.activeFine = Finset.univ :=
    canonicalBufferedTauActiveCover_activeFine
      E hE Cmulti Sseq W P.epsilon_pos.le hepsilonHalf
  have hUactive : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine U0
  calc
    (delta : ENNReal) ^ (2 * etaF) /
        ((katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) + 1 : Nat) : ENNReal) ≤
        (parentAggregatedShading
          (tauScaleCover E Cmulti Sseq W) E.shading).shadingMass := hparent
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
  fullRefinement_canonicalBufferedTauActive_bounded_sourceMass_lower

end Witness
end
end Family8CanonicalBufferedTauActiveBoundedSourceFloorV1
