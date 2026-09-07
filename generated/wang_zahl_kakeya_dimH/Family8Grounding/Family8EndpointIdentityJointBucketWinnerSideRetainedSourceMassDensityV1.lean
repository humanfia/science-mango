import Family8Grounding.Family8EndpointIdentityExactSameCoreHighPayloadJointBucketAdapterV1
import Family8Grounding.Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

/-!
# Endpoint joint-bucket winner-side retained-source mass and density

The joint fibre/density bucket and the weighted winner-side bucket are two
successive restrictions of one literal tau-active shading.  Their mass
payments therefore compose before any later Equation-(32) or DSO input is
available.  At the identity endpoint, tau-active mass and family volume are
both exactly those of the original datum, so the same composed loss gives a
direct, division-free density comparison with the original source density.

The statements below keep the actual joint bucket, its fine shading, the
winner-side label, and `winnerSideRetainedSource`; no shading or occurrence
set is reselected.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityJointBucketWinnerSideRetainedSourceMassDensityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8CoreHighPrefixFiberDensityBucketFineShadingV1
open Family8EndpointIdentityCorrelatedSameCoreHighCloserDatumAdapterV1
open Family8EndpointIdentityExactSameCoreHighPayloadJointBucketAdapterV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceWeightedWinnerSideBucketV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-! ## Division-free same-family algebra -/

/-- On one fixed finite convex family, mass retention gives the direct
density comparison with the same loss.  This is the multiplication form of
the density payment and needs no nonzero or non-top hypothesis on `loss`. -/
theorem sameFamily_shadingDensity_le_loss_mul_of_shadingMass_le
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota}
    (Y Z : Shading F) (loss : ENNReal)
    (hmass : Y.shadingMass <= loss * Z.shadingMass) :
    Y.shadingDensity <= loss * Z.shadingDensity := by
  by_cases hzero : familyVolume F = 0
  · have hYmass : Y.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp
        (Y.shadingMass_le_familyVolume.trans_eq hzero)
    have hZmass : Z.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp
        (Z.shadingMass_le_familyVolume.trans_eq hzero)
    simp [Shading.shadingDensity, hzero, hYmass, hZmass]
  · rw [<- ENNReal.mul_le_mul_iff_right hzero
      (familyVolume_ne_top F)]
    calc
      familyVolume F * Y.shadingDensity = Y.shadingMass := by
        rw [mul_comm, shadingDensity_mul_familyVolume]
      _ <= loss * Z.shadingMass := hmass
      _ = loss * (Z.shadingDensity * familyVolume F) := by
        rw [shadingDensity_mul_familyVolume]
      _ = familyVolume F * (loss * Z.shadingDensity) := by ac_rfl

/-! ## The literal winner-side source -/

/-- Compose an arbitrary joint-bucket mass payment with the mass payment
stored in the literal winner-side selection payload.  Both conclusions use
the exact `winnerSideRetainedSource` occurring in that payload. -/
theorem source_mass_density_le_winnerSideRetainedSource_of_joint_winner
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hrho : 0 < rho)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (outerLabel : Fin 3 -> Int)
    (source : Shading S.activeCoarseFamily)
    (jointLoss : ENNReal)
    (hjoint : source.shadingMass <= jointLoss *
      (winnerSideBucketSource D S Y fineBucket).shadingMass)
    (hselection : WinnerSideSelectionPayload
      D S P hrho R Y fineBucket outerLabel) :
    source.shadingMass <=
        (jointLoss * (winnerSideBucketLoss rho : ENNReal)) *
          (winnerSideRetainedSource
            D S P hrho R Y fineBucket outerLabel).shadingMass /\
      source.shadingDensity <=
        (jointLoss * (winnerSideBucketLoss rho : ENNReal)) *
          (winnerSideRetainedSource
            D S P hrho R Y fineBucket outerLabel).shadingDensity := by
  let retained := winnerSideRetainedSource
    D S P hrho R Y fineBucket outerLabel
  have hwinner : (winnerSideBucketSource D S Y fineBucket).shadingMass <=
      (winnerSideBucketLoss rho : ENNReal) * retained.shadingMass :=
    hselection.2.2.2.2.1
  have hmass : source.shadingMass <=
      (jointLoss * (winnerSideBucketLoss rho : ENNReal)) *
        retained.shadingMass := by
    calc
      source.shadingMass <= jointLoss *
          (winnerSideBucketSource D S Y fineBucket).shadingMass := hjoint
      _ <= jointLoss *
          ((winnerSideBucketLoss rho : ENNReal) * retained.shadingMass) :=
        mul_le_mul' le_rfl hwinner
      _ = (jointLoss * (winnerSideBucketLoss rho : ENNReal)) *
          retained.shadingMass := by ac_rfl
  refine ⟨by simpa only [retained] using hmass, ?_⟩
  simpa only [retained] using
    (sameFamily_shadingDensity_le_loss_mul_of_shadingMass_le
      source retained
        (jointLoss * (winnerSideBucketLoss rho : ENNReal)) hmass)

/-! ## Exact endpoint packaging -/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The object-preserving endpoint output.  It records the definitional
identity of the joint fine shading with `winnerSideBucketSource`, both
successive selection payloads, and the composed division-free mass/density
comparison with the original datum. -/
def EndpointIdentityJointWinnerSideRetainedSourceMassDensityAt
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (rFrozen : Real) (r : NNReal) (hr : 0 < r) : Prop :=
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let hrho : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  let M := Nat.log 2 (Fintype.card (ActiveParentIndex T))
  let jointLoss : ENNReal :=
    ((2 * prop51JointOccurrenceLoss (ActiveParentIndex T) M : Nat) : ENNReal)
  exists P : GreedyDensityPartition Dtau.family.bodyFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex T)))
      (hullContainer Dtau.family.bodyFamily) Finset.univ,
    exists selected : Finset (ActiveParentIndex T),
      exists hcover : (forall i, i ∈ selected ->
        exists q : Fin (blocks Dtau.family.bodyFamily P).length,
          i ∈ (blockAt Dtau.family.bodyFamily P q).fiber /\
            CoreHighConcentrationOccurrence Dtau P A q),
        exists b : Fin (Nat.log 2 (Fintype.card (ActiveParentIndex T)) + 1) ×
            Fin (M + 1),
          let R := coreHighFiberDensityOccurrenceBucket
            Dtau P A A M selected hcover b
          let fineBucket := coreHighFiberDensityFineBucket
            Dtau P A A M selected hcover b
          let Yjoint := coreHighFiberDensityFineShading
            Dtau P A A M selected hcover b
          exists outerLabel : Fin 3 -> Int,
            let retained := winnerSideRetainedSource
              E T P hrho R Dtau.shading fineBucket outerLabel
            Yjoint = winnerSideBucketSource E T Dtau.shading fineBucket /\
            Dtau.shading.shadingMass <= jointLoss * Yjoint.shadingMass /\
            WinnerSideSelectionPayload
              E T P hrho R Dtau.shading fineBucket outerLabel /\
            WinnerSideLocalBlockPositiveCarrierPaymentPayload E T P
              (winnerSideRetainedOccurrences E T P hrho R outerLabel)
              retained rFrozen hrho r hr /\
            D.shading.shadingMass <=
              (jointLoss * (winnerSideBucketLoss (S.tau W.m) : ENNReal)) *
                retained.shadingMass /\
            D.shading.shadingDensity <=
              (jointLoss * (winnerSideBucketLoss (S.tau W.m) : ENNReal)) *
                retained.shadingDensity

/-- Any already-constructed exact joint-density-first winner-side payment
has the original-source mass and density comparison on its very same
retained source. -/
theorem endpointIdentity_jointWinnerSideRetainedSource_massDensity_of_payment
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (hpayment : EndpointIdentityJointDensityFirstWinnerSideSameQPaymentAt
      D hD L W A rFrozen r hr) :
    EndpointIdentityJointWinnerSideRetainedSourceMassDensityAt
      D hD L W A rFrozen r hr := by
  classical
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let hrho : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  let M := Nat.log 2 (Fintype.card (ActiveParentIndex T))
  let jointLoss : ENNReal :=
    ((2 * prop51JointOccurrenceLoss (ActiveParentIndex T) M : Nat) : ENNReal)
  unfold EndpointIdentityJointDensityFirstWinnerSideSameQPaymentAt at hpayment
  dsimp only at hpayment
  obtain ⟨P, selected, hcover, b, _hRnonempty, _hRsubset,
      _hfineBucket, _hcore, _hband, _hcomparable, hmass, _havg,
      hwinner⟩ := hpayment
  let R := coreHighFiberDensityOccurrenceBucket
    Dtau P A A M selected hcover b
  let fineBucket := coreHighFiberDensityFineBucket
    Dtau P A A M selected hcover b
  let Yjoint := coreHighFiberDensityFineShading
    Dtau P A A M selected hcover b
  unfold WinnerSideLocalBlockPositiveCarrierPaymentConclusion at hwinner
  obtain ⟨outerLabel, hselection, hlocal⟩ := hwinner
  let retained := winnerSideRetainedSource
    E T P hrho R Dtau.shading fineBucket outerLabel
  have hYjoint : Yjoint =
      winnerSideBucketSource E T Dtau.shading fineBucket := rfl
  have hjoint : Dtau.shading.shadingMass <= jointLoss *
      (winnerSideBucketSource E T Dtau.shading fineBucket).shadingMass := by
    rw [<- hYjoint]
    convert hmass using 1
    rfl
  have hcomparison :=
    source_mass_density_le_winnerSideRetainedSource_of_joint_winner
      E T P hrho R Dtau.shading fineBucket outerLabel Dtau.shading
        jointLoss hjoint hselection
  have hmassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
    change (tauActiveCoarseDatum E C S W).shading.shadingMass =
      D.shading.shadingMass
    simpa only [E, C, S] using
      (endpointLongCore_tauActive_shadingMass_eq_source D hD L W)
  have hvolumeEq : familyVolume Dtau.family.bodyFamily =
      familyVolume D.family.bodyFamily := by
    change familyVolume
        (tauActiveCoarseDatum E C S W).family.bodyFamily =
      familyVolume D.family.bodyFamily
    simpa only [E, C, S] using
      (endpointLongCore_identity_tauActive_familyVolume_eq_source D hD L W)
  have hdensityEq : Dtau.shading.shadingDensity =
      D.shading.shadingDensity := by
    unfold Shading.shadingDensity
    rw [hmassEq, hvolumeEq]
  have hsourceMass : D.shading.shadingMass <=
      (jointLoss * (winnerSideBucketLoss (S.tau W.m) : ENNReal)) *
        retained.shadingMass := by
    rw [<- hmassEq]
    convert hcomparison.1 using 1
    rfl
  have hsourceDensity : D.shading.shadingDensity <=
      (jointLoss * (winnerSideBucketLoss (S.tau W.m) : ENNReal)) *
        retained.shadingDensity := by
    rw [<- hdensityEq]
    convert hcomparison.2 using 1
    rfl
  unfold EndpointIdentityJointWinnerSideRetainedSourceMassDensityAt
  dsimp only
  refine ⟨P, selected, hcover, b, outerLabel, ?_⟩
  exact ⟨hYjoint, by simpa only [jointLoss, Yjoint] using hmass,
    by simpa only [R, fineBucket] using hselection,
    by simpa only [R, fineBucket, retained] using hlocal,
    by simpa only [jointLoss, R, fineBucket, retained] using hsourceMass,
    by simpa only [jointLoss, R, fineBucket, retained] using hsourceDensity⟩

/-- Direct endpoint-high corollary.  Its hypotheses are exactly those of the
existing joint-bucket/winner-side producer; no Equation-(32) or DSO premise
is added. -/
theorem endpointIdentity_jointWinnerSideRetainedSource_massDensity_of_exactSameCoreHighPayload
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (hA : 1 <= A)
    (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (r : NNReal) (hr : 0 < r) (KT : ENNReal)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hHigh : EndpointIdentityExactSameCoreHighPayloadAt
      D hD L W A r hr KT) :
    EndpointIdentityJointWinnerSideRetainedSourceMassDensityAt
      D hD L W A rFrozen r hr := by
  apply endpointIdentity_jointWinnerSideRetainedSource_massDensity_of_payment
    D hD L W A rFrozen r hr
  exact
    endpointIdentity_jointDensityFirst_winnerSide_sameQ_payment_of_exactSameCoreHighPayload
      D hD L W A hA rFrozen hrFrozen r hr KT hsource0 hHigh

#print axioms sameFamily_shadingDensity_le_loss_mul_of_shadingMass_le
#print axioms
  source_mass_density_le_winnerSideRetainedSource_of_joint_winner
#print axioms EndpointIdentityJointWinnerSideRetainedSourceMassDensityAt
#print axioms
  endpointIdentity_jointWinnerSideRetainedSource_massDensity_of_payment
#print axioms
  endpointIdentity_jointWinnerSideRetainedSource_massDensity_of_exactSameCoreHighPayload

end
end Family8EndpointIdentityJointBucketWinnerSideRetainedSourceMassDensityV1
