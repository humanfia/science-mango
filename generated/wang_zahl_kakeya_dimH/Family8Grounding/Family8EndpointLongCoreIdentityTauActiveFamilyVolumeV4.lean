import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Mathlib.Tactic

/-!
# Endpoint identity tau-active family volume, V4

V1--V3 are failed drafts and are not imported.  V3 reduced the goal to a
single finite sum, but used a nonexistent `Finset.sum_univ` name.  This
successor discharges the remaining reindexing explicitly with the inverse law
for `Fintype.equivFin`; changing a tube to its already certified radius is then
definitionally invisible to its body.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The endpoint tau-active parent family has exactly the source family
volume. -/
theorem endpointLongCore_identity_tauActive_familyVolume_eq_source
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))) :
    familyVolume
        (tauActiveCoarseDatum (fullRefinementDatum D)
          (identityRadiusCoherentCover (fullRefinementDatum D).family)
          (endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))) W).family.bodyFamily =
      familyVolume D.family.bodyFamily := by
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W
  change familyVolume
      (selectedCoarseFamily
        (tauScaleCover E C S W).coarse.bodyFamily
        (tauScaleCover E C S W).activeCoarse) =
    familyVolume D.family.bodyFamily
  rw [selectedCoarseFamily_volume]
  unfold familyVolume
  dsimp only [tauScaleCover, C, identityRadiusCoherentCover,
    identityRadiusScaleCover]
  rw [Finset.sum_map]
  simp only [UniformTubeFamily.bodyFamily,
    UniformTubeFamily.reindex_tubes, UniformTubeFamily.changeRadius_tubes]
  rw [htau]
  have hindex (x : index) :
      (Fintype.equivFin index).symm
          ((Fintype.equivFin index).toEmbedding x) = x :=
    (Fintype.equivFin index).symm_apply_apply x
  simp_rw [hindex]
  rfl

#print axioms endpointLongCore_identity_tauActive_familyVolume_eq_source

end
end Family8EndpointLongCoreIdentityTauActiveFamilyVolumeV4
