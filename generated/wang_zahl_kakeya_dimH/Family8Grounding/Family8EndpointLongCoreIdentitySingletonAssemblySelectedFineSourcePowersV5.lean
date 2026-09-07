import Family8Grounding.Family8EndpointLongCoreTauActiveSingletonBoundedFrozenAssemblyV4
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Family8Grounding.Family8StickySelectedFineAssemblyDenseProductV1
import Family8Grounding.Family8SourceMassDividedFloorPowerV3
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Mathlib.Tactic

/-!
# Endpoint singleton-assembly selected-fine source powers, V5

V1--V4 are failed drafts and are not imported.  V3 exposed only a redundant
tactic after an already closed full-set mass identity and a costly dependent
rewrite of the final active set.  This successor removes the redundant tactic
and transports that active set with an explicit `congrArg` equality.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8SourceMassDividedFloorPowerV3
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberPartitionFineIndexV3
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySelectedFineAssemblyDenseProductV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-! ## Thin exact density transports -/

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Selecting a literal full finite set changes neither the numerator nor the
family-volume denominator of shading density. -/
theorem sourceActiveFineShading_density_eq_of_fine_eq_univ
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {W : ConvexFamily kappa}
    (P : ConvexFactorization fine.bodyFamily W)
    (Y : Shading fine.bodyFamily)
    (hfine : P.index.fine = Finset.univ) :
    (sourceActiveFineShading P Y).shadingDensity = Y.shadingDensity := by
  have hmass : (sourceActiveFineShading P Y).shadingMass = Y.shadingMass := by
    rw [sourceActiveFineShading_shadingMass, hfine,
      shadingMass_restrictTo_eq_sum, Shading.shadingMass]
  have hvolume : familyVolume (sourceActiveFineFamily P) =
      familyVolume fine.bodyFamily := by
    unfold sourceActiveFineFamily
    rw [selectedCoarseFamily_volume, hfine]
    unfold familyVolume
    simp
  unfold Shading.shadingDensity
  rw [hmass, hvolume]

/-- The active-restricted representation has the same density whenever the
old active set is the full finite family. -/
theorem activeFineRestrictedShading_density_eq_of_activeFine_eq_univ
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ) :
    (activeFineRestrictedShading S Y).shadingDensity = Y.shadingDensity := by
  have hmass : (activeFineRestrictedShading S Y).shadingMass =
      Y.shadingMass := by
    rw [activeFineRestrictedShading_shadingMass,
      activeFineShading_shadingMass_eq_of_activeFine_eq_univ S Y hactive]
  have hvolume : familyVolume (activeFineRestrictedFamily S).bodyFamily =
      familyVolume fine.bodyFamily := by
    unfold familyVolume
    let e : {i // i ∈ S.activeFine} ≃ iota :=
      { toFun := Subtype.val
        invFun := fun i => ⟨i, by rw [hactive]; exact Finset.mem_univ i⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold Shading.shadingDensity
  rw [hmass, hvolume]

/-- The multiplicity-counted mass on the full index set is total shading
mass. -/
theorem shadingMassOn_univ
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {r : NNReal} {G : UniformTubeFamily r alpha}
    (Y : Shading G.bodyFamily) :
    shadingMassOn Y (Finset.univ : Finset alpha) = Y.shadingMass := by
  unfold shadingMassOn Shading.shadingMass
  simp

variable {index : Type} [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Consequently the endpoint parent-aggregated tau shading has exactly the
source density, not merely the already-known exact mass and average. -/
theorem endpointLongCore_identity_tauActive_shadingDensity_eq_source
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))) :
    (tauActiveCoarseDatum (fullRefinementDatum D)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) W).shading.shadingDensity =
      D.shading.shadingDensity := by
  unfold Shading.shadingDensity
  rw [endpointLongCore_tauActive_shadingMass_eq_source D hD P W,
    endpointLongCore_identity_tauActive_familyVolume_eq_source D hD P W]

/-! ## The same literal singleton assembly -/

/-- The selected-fine active restriction of the endpoint `M = 1` frozen
assembly has both powers consumed by the no-KT low-CF selector. -/
theorem endpointLongCore_identity_singletonAssembly_selectedFine_sourcePowers
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {etaSource lossExp massEta densityEta : Real}
    (hF : FrostmanHypotheses D etaSource) :
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
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
      intro k _hk
      simpa only [Fintype.card_coe] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse 1 hM
    forall A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) ->
      (A.loss : ENNReal) <= (delta : ENNReal) ^ (-lossExp) ->
      2 * etaSource + lossExp <= 2 * massEta ->
      etaSource + lossExp <= 2 * densityEta ->
      let hindices := assembly_indices_subset_activeFine U Y 1 A
      let T0 := selectedFineScaleCover U A.refinement.indices hindices
      let Z0 := selectedFineShading U A.refinement.indices
        A.refinement.shading
      let T := activeFineRestrictedScaleCover T0
      let Z := activeFineRestrictedShading T0 Z0
      (delta : ENNReal) ^ (2 * massEta) <=
          shadingMassOn Z T.activeFine /\
        (delta : ENNReal) ^ (2 * densityEta) <= Z.shadingDensity := by
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
  have hsourceMassPower : (delta : ENNReal) ^ (2 * etaSource) <=
      shadingMassOn Y U.activeFine := by
    calc
      (delta : ENNReal) ^ (2 * etaSource) <= D.shading.shadingMass :=
        delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
      _ = shadingMassOn Y U.activeFine :=
        (endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf).symm
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    rw [shadingMass_restrictTo_eq_sum]
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le
        hsourceMassPower)
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf k
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  have hscale : S.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse 1 hM
  intro A hAloss hLossPower hMassBudget hDensityBudget
  let hindices := assembly_indices_subset_activeFine U Y 1 A
  let T0 := selectedFineScaleCover U A.refinement.indices hindices
  let Z0 := selectedFineShading U A.refinement.indices A.refinement.shading
  let T := activeFineRestrictedScaleCover T0
  let Z := activeFineRestrictedShading T0 Z0
  have hfine : Pcoarse.asConvexFactorization.index.fine = U.activeFine := by
    simpa only [Pcoarse] using
      boundedFiberCoarseTubePartition_asConvexFactorization_fine
        U hscale hcoarse 1 hM
  have hU : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine U0
  have hU0 : U0.activeFine = Finset.univ :=
    canonicalBufferedTauActiveCover_activeFine
      E hE C S W P.epsilon_pos.le hepsilonHalf
  have hsourceDensity :
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingDensity =
        D.shading.shadingDensity := by
    calc
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingDensity =
          Y.shadingDensity :=
        sourceActiveFineShading_density_eq_of_fine_eq_univ
          Pcoarse.asConvexFactorization Y (hfine.trans hU)
      _ = Dtau.shading.shadingDensity :=
        activeFineRestrictedShading_density_eq_of_activeFine_eq_univ
          U0 Dtau.shading hU0
      _ = D.shading.shadingDensity :=
        endpointLongCore_identity_tauActive_shadingDensity_eq_source D hD P W
  have hsourceMass :
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass =
        D.shading.shadingMass := by
    rw [sourceActiveFineShading_shadingMass, hfine, hU,
      restrictTo_univ_shadingMass]
    calc
      Y.shadingMass = shadingMassOn Y U.activeFine := by
        rw [hU, shadingMassOn_univ]
      _ = D.shading.shadingMass :=
        endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf
  have hactualMassFloor : (delta : ENNReal) ^ (2 * etaSource) /
      (A.loss : ENNReal) <= (actualRefinementShading A).shadingMass := by
    apply ENNReal.div_le_of_le_mul'
    calc
      (delta : ENNReal) ^ (2 * etaSource) <= D.shading.shadingMass :=
        delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
      _ = (sourceActiveFineShading
          Pcoarse.asConvexFactorization Y).shadingMass := hsourceMass.symm
      _ <= (A.loss : ENNReal) *
          (actualRefinementShading A).shadingMass :=
        sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
  have hactualDensityFloor : (delta : ENNReal) ^ etaSource /
      (A.loss : ENNReal) <= (actualRefinementShading A).shadingDensity := by
    calc
      (delta : ENNReal) ^ etaSource / (A.loss : ENNReal) <=
          (sourceActiveFineShading
            Pcoarse.asConvexFactorization Y).shadingDensity /
              (A.loss : ENNReal) := ENNReal.div_le_div_right (hF.1.trans_eq
                hsourceDensity.symm) _
      _ <= (actualRefinementShading A).shadingDensity :=
        sourceActiveFineShading_density_div_loss_le_actualRefinementShading A
  have hLossPos : 0 < A.loss := by
    rw [hAloss]
    unfold frozenComparableLoss
    positivity
  have hactualMassPower : (delta : ENNReal) ^ (2 * massEta) <=
      (actualRefinementShading A).shadingMass :=
    sourceMass_power_of_divided_floor_and_natCap_power
      hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hLossPos
      hactualMassFloor hLossPower hMassBudget
  have hactualDensityPower : (delta : ENNReal) ^ (2 * densityEta) <=
      (actualRefinementShading A).shadingDensity := by
    apply sourceMass_power_of_divided_floor_and_natCap_power
      (etaSmall := etaSource / 2) (capExponent := lossExp)
      hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hLossPos
    · convert hactualDensityFloor using 1 ; ring
    · exact hLossPower
    · linarith
  have hT0 : T0.activeFine = Finset.univ := rfl
  have hZ0Mass : Z0.shadingMass =
      (actualRefinementShading A).shadingMass := by
    change (actualRefinementShading A).shadingMass =
      (actualRefinementShading A).shadingMass
    rfl
  have hZ0Density : Z0.shadingDensity =
      (actualRefinementShading A).shadingDensity := by
    change (actualRefinementShading A).shadingDensity =
      (actualRefinementShading A).shadingDensity
    rfl
  have hactiveEq : T.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine T0
  have hmassOnEq :
      shadingMassOn Z T.activeFine = shadingMassOn Z Finset.univ :=
    congrArg (fun s => shadingMassOn Z s) hactiveEq
  have hZMass : shadingMassOn Z T.activeFine =
      (actualRefinementShading A).shadingMass := by
    calc
      shadingMassOn Z T.activeFine = shadingMassOn Z Finset.univ := hmassOnEq
      _ = Z.shadingMass := shadingMassOn_univ Z
      _ = (activeFineShading T0 Z0).shadingMass :=
        activeFineRestrictedShading_shadingMass T0 Z0
      _ = Z0.shadingMass :=
        activeFineShading_shadingMass_eq_of_activeFine_eq_univ T0 Z0 hT0
      _ = (actualRefinementShading A).shadingMass := hZ0Mass
  have hZDensity : Z.shadingDensity =
      (actualRefinementShading A).shadingDensity := by
    calc
      Z.shadingDensity = Z0.shadingDensity :=
        activeFineRestrictedShading_density_eq_of_activeFine_eq_univ
          T0 Z0 hT0
      _ = (actualRefinementShading A).shadingDensity := hZ0Density
  exact ⟨hactualMassPower.trans_eq hZMass.symm,
    hactualDensityPower.trans_eq hZDensity.symm⟩

#print axioms sourceActiveFineShading_density_eq_of_fine_eq_univ
#print axioms activeFineRestrictedShading_density_eq_of_activeFine_eq_univ
#print axioms shadingMassOn_univ
#print axioms endpointLongCore_identity_tauActive_shadingDensity_eq_source
#print axioms
  endpointLongCore_identity_singletonAssembly_selectedFine_sourcePowers

end
end Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV5
