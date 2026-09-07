import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Family8Grounding.Family8EndpointIdentityNoKTSourceCardPowerV3
import Family8Grounding.Family8SelectedFineFiberCardCapTransportV2
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Family8Grounding.Family8StickySelectedFineAssemblyFiberBridgeV1
import Family8Grounding.Family8StickySelectedFineSubtypeScaleCoverV1
import Mathlib.Tactic

/-!
# Direct selected-fine card powers for the endpoint singleton assembly

Unlike the older transport, this theorem stops at the literal selected-fine
cover used by the mass-popular and Frostman producers.  It therefore keeps
the parent `q` definitionally identical throughout the middle construction.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentitySingletonAssemblySelectedFineDirectCardPowerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8ContractedJohnActualTubeProxyV1
open Family8EndpointIdentityNoKTSourceCardPowerV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8SelectedFineFiberCardCapTransportV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Any two uniform old-fibre bounds survive the literal selected-fine
subtype, without adding the later active-restriction reindexing. -/
theorem selectedFine_dualCardPower_of_parent
    (S : StickyScaleCover fine rho)
    (selected : Finset index) (hselected : selected ⊆ S.activeFine)
    {Bproxy Brelative : ENNReal}
    (hparent : ∀ q : {q // q ∈ S.activeCoarse},
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤ Bproxy ∧
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤ Brelative) :
    let T := selectedFineScaleCover S selected hselected
    ∀ q : {q // q ∈ T.activeCoarse},
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤ Bproxy ∧
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤ Brelative := by
  dsimp only
  let T := selectedFineScaleCover S selected hselected
  intro q
  let old : Fin S.coarseCard :=
    ((selectedFineParentValues S selected).equivFin.symm q.1).1
  have hold : old ∈ S.activeCoarse := by
    dsimp only [old]
    exact selectedFineScaleCover_parent_mem_activeCoarse
      S selected hselected q.1
  let oldq : {q // q ∈ S.activeCoarse} := ⟨old, hold⟩
  have hselectedCard :
      Fintype.card {i // i ∈ T.fiber q.1} ≤
        Fintype.card {i // i ∈ S.fiber old} := by
    simpa only [Fintype.card_coe, T, old] using
      selectedFineScaleCover_fiber_card_le_parent_fiber
        S selected hselected q.1
  have hselectedCardENN :
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
        (Fintype.card {i // i ∈ S.fiber old} : ENNReal) := by
    exact_mod_cast hselectedCard
  obtain ⟨hproxy, hrelative⟩ := hparent oldq
  constructor
  · exact hselectedCardENN.trans (by simpa only [oldq] using hproxy)
  · exact hselectedCardENN.trans (by simpa only [oldq] using hrelative)

variable {index0 : Type} [Fintype index0] [DecidableEq index0]
  {epsilon0 beta gamma : Real}

/-- The exact selected-fine object of the endpoint `M=1` assembly carries
both card powers used by the fresh low-CF producer. -/
theorem endpointLongCore_identity_singletonAssembly_selectedFine_directDualCardPower
    (D : ActualTubeDatum delta index0) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {etaSource cardExp kappa : Real}
    (hF : FrostmanHypotheses D etaSource)
    (hcardExp : 0 ≤ cardExp) (hcountExp : 0 < 2 + kappa) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
        rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf]
        have hfloor :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
        exact ne_of_gt ((ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
      rw [shadingMass_restrictTo_eq_sum]
      exact hOn
    let hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ 1 := by
      intro k _hk
      simpa only [Fintype.card_coe] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse 1 hM
    ∀ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      let hindices := assembly_indices_subset_activeFine U Y 1 A
      let T := selectedFineScaleCover U A.refinement.indices hindices
      ∀ q : {q // q ∈ T.activeCoarse},
        (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
            (((contractedJohnProxyRadius (S.tau W.m)
              (canonicalBufferedRadius W) / 8 : NNReal) : ENNReal) ^
                (-cardExp)) ∧
          (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
            1 * ((((S.tau W.m : NNReal) : ENNReal) /
              (canonicalBufferedRadius W : ENNReal)) ^ (-(2 + kappa))) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
    rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
      D hD P W hepsilonHalf]
    have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    rw [shadingMass_restrictTo_eq_sum]
    exact hOn
  have hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf k
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  have hscale : S.tau W.m ≤ canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse 1 hM
  intro A
  let hindices := assembly_indices_subset_activeFine U Y 1 A
  apply selectedFine_dualCardPower_of_parent
    U A.refinement.indices hindices
  intro q
  simpa only [U, U0] using
    identityCore_canonicalBufferedTauActiveRestricted_dualPower
      E hE S W P.epsilon_pos.le hepsilonHalf
        hcardExp hcountExp q

#print axioms selectedFine_dualCardPower_of_parent
#print axioms
  endpointLongCore_identity_singletonAssembly_selectedFine_directDualCardPower

end
end Family8EndpointIdentitySingletonAssemblySelectedFineDirectCardPowerV2
