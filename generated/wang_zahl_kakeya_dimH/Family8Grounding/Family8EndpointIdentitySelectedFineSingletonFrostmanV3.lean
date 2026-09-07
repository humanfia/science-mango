import Family8Grounding.Family8IdentityCoreTauActiveSingletonFiberV4
import Family8Grounding.Family8SelectedFineFiberCardCapTransportV2
import Family8Grounding.Family8StickySelectedFineSubtypeScaleCoverV1
import FamilyStickyGrounding.FamilyStickyCapturedTubeBoxWidthCleanV2
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import FamilyStickyGrounding.FamilyStickyFrostmanFiberNormalizerAdapterV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
import Mathlib.Tactic

/-!
# Endpoint identity selected-fine singleton Frostman control, V3

V1 and V2 are frozen.  This clean successor imports the two direct symbol
owners and makes the selected-fibre cardinal coercion explicit.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentitySelectedFineSingletonFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8SelectedFineFiberCardCapTransportV2
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyFrostmanFiberNormalizerAdapterV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat → Real}

/-- Every selected-fine subtype of the identity tau-active cover remains
Frostman with the literal captured-tube loss. -/
theorem identityCore_selectedFineTauActiveCover_isFrostmanAtScale
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (selected : Finset {i // i ∈
      (canonicalBufferedTauActiveCover D hD
        (identityRadiusCoherentCover D.family) S W
          hepsilon hepsilonHalf).activeFine})
    (hselected : selected ⊆
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD
          (identityRadiusCoherentCover D.family) S W
            hepsilon hepsilonHalf)).activeFine) :
    let U0 := canonicalBufferedTauActiveCover D hD
      (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    let T := selectedFineScaleCover U selected hselected
    T.IsFrostmanAtScale
      (capturedTubeBoxLoss (S.tau W.m) (canonicalBufferedRadius W)) := by
  dsimp only
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let T := selectedFineScaleCover U selected hselected
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hepsilon
  apply StickyScaleCover.isFrostmanAtScale_of_fiberKatzTao_and_normalizer
    T (fun _ ↦ 1)
      (capturedTubeBoxLoss (S.tau W.m) (canonicalBufferedRadius W))
  · intro q _hq
    apply isKatzTao_iff_concentration_le.mpr
    intro K
    have hselectedCard :
        Fintype.card {i // i ∈ T.fiber q} ≤
          Fintype.card {i // i ∈ U.fiber
            ((selectedFineParentValues U selected).equivFin.symm q).1} := by
      simpa only [Fintype.card_coe] using
        selectedFineScaleCover_fiber_card_le_parent_fiber
          U selected hselected q
    have holdCard :
        Fintype.card {i // i ∈ U.fiber
          ((selectedFineParentValues U selected).equivFin.symm q).1} ≤ 1 := by
      simpa only [U, U0] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          D hD S W hepsilon hepsilonHalf
            ((selectedFineParentValues U selected).equivFin.symm q).1
    calc
      concentration (T.fiberFamily q) K ≤
          maximalConcentration (T.fiberFamily q) :=
        concentration_le_maximalConcentration _ _
      _ ≤ (Fintype.card {i // i ∈ T.fiber q} : ENNReal) :=
        maximalConcentration_le_card _
      _ ≤ 1 := by
        exact_mod_cast hselectedCard.trans holdCard
  · intro q hq
    exact one_le_capturedTubeBoxLoss_mul_parentConcentration
      T htau hrho q hq

/-- The preceding scale certificate on the exact selected-fine fibre, in the
`IsFrostmanIn` form consumed by the fresh low-CF selector. -/
theorem identityCore_selectedFineTauActive_fiber_isFrostmanIn
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (selected : Finset {i // i ∈
      (canonicalBufferedTauActiveCover D hD
        (identityRadiusCoherentCover D.family) S W
          hepsilon hepsilonHalf).activeFine})
    (hselected : selected ⊆
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD
          (identityRadiusCoherentCover D.family) S W
            hepsilon hepsilonHalf)).activeFine)
    (q : {q // q ∈
      (selectedFineScaleCover
        (activeFineRestrictedScaleCover
          (canonicalBufferedTauActiveCover D hD
            (identityRadiusCoherentCover D.family) S W
              hepsilon hepsilonHalf)) selected hselected).activeCoarse}) :
    let U0 := canonicalBufferedTauActiveCover D hD
      (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    let T := selectedFineScaleCover U selected hselected
    IsFrostmanIn
      (capturedTubeBoxLoss (S.tau W.m) (canonicalBufferedRadius W))
      (T.fiberFamily q.1) (T.activeCoarseFamily q) := by
  dsimp only
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let T := selectedFineScaleCover U selected hselected
  have hAt : T.IsFrostmanAtScale
      (capturedTubeBoxLoss (S.tau W.m) (canonicalBufferedRadius W)) := by
    simpa only [T, U, U0] using
      identityCore_selectedFineTauActiveCover_isFrostmanAtScale
        D hD S W hepsilon hepsilonHalf selected hselected
  apply isFrostmanIn_iff_concentration_le.mpr
  exact ⟨T.fiber_carrier_subset_parent q.1, hAt q.1 q.2⟩

#print axioms identityCore_selectedFineTauActiveCover_isFrostmanAtScale
#print axioms identityCore_selectedFineTauActive_fiber_isFrostmanIn

end
end Family8EndpointIdentitySelectedFineSingletonFrostmanV3
