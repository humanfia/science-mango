import Family8Grounding.Family8PlankLongTubeAmbientB2SupportV1
import Family8Grounding.Family8GeneralizedFrostmanMultiplicityV1
import Family8Grounding.Family8FiniteRandomRigidMotionIncidenceV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlCenteredLongTubeClusterV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PlankLongTubeAmbientB2SupportV1
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlLongTubeClusterDatumV2

noncomputable section

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

def centeredThickenedPlankClusterLongTubeDatum
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    ActualTubeDatum b
      (Unit × {j // j ∈ thickenedPlankIndices D theta i}) :=
  let G := thickenedPlankCluster D theta i
  indexedRigidCopyDatum
    (fun _ : Unit =>
      translationRigidMotion (-(ambientPlankCertificate G).box.center))
    (thickenedPlankClusterLongTubeDatum D theta i)

theorem centeredThickenedPlankClusterLongTubeDatum_B2
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (hb : b ≤ (2 : NNReal)⁻¹) :
    ∀ p : Unit × {j // j ∈ thickenedPlankIndices D theta i},
      ((centeredThickenedPlankClusterLongTubeDatum D theta i).family.tubes p).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro p x hx
  let G := thickenedPlankCluster D theta i
  let R := translationRigidMotion (-(ambientPlankCertificate G).box.center)
  change x ∈ (rigidTube R
    ((thickenedPlankClusterLongTubeDatum D theta i).family.tubes p.2)).carrier at hx
  rw [rigidTube_carrier] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hraw := longTubeCover_subset_closedBall_ambientCenter_two G hb p.2 hy
  rw [Metric.mem_closedBall] at hraw ⊢
  simpa [R, translationRigidMotion_apply, dist_eq_norm, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hraw

theorem centeredThickenedPlankClusterLongTubeDatum_shadingMass
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (centeredThickenedPlankClusterLongTubeDatum D theta i).shading.shadingMass =
      (thickenedPlankClusterLongTubeDatum D theta i).shading.shadingMass := by
  let G := thickenedPlankCluster D theta i
  let motion : Unit → RigidMotion := fun _ =>
    translationRigidMotion (-(ambientPlankCertificate G).box.center)
  change (indexedRigidCopyShading motion
      (thickenedPlankClusterLongTubeDatum D theta i).family
      (thickenedPlankClusterLongTubeDatum D theta i).shading).shadingMass = _
  simpa [motion] using indexedRigidCopyShading_shadingMass motion
    (thickenedPlankClusterLongTubeDatum D theta i).family
    (thickenedPlankClusterLongTubeDatum D theta i).shading

theorem centeredThickenedPlankClusterLongTubeDatum_actualFamilyVolume
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (centeredThickenedPlankClusterLongTubeDatum D theta i).actualFamilyVolume =
      (thickenedPlankClusterLongTubeDatum D theta i).actualFamilyVolume := by
  let G := thickenedPlankCluster D theta i
  let motion : Unit → RigidMotion := fun _ =>
    translationRigidMotion (-(ambientPlankCertificate G).box.center)
  change familyVolume
      (indexedRigidCopyTubeFamily motion
        (thickenedPlankClusterLongTubeDatum D theta i).family).bodyFamily = _
  simpa [motion, ActualTubeDatum.actualFamilyVolume] using
    indexedRigidCopyTubeFamily_familyVolume motion
      (thickenedPlankClusterLongTubeDatum D theta i).family

theorem centeredThickenedPlankClusterLongTubeDatum_shadedUnionVolume
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    volume
        (centeredThickenedPlankClusterLongTubeDatum D theta i).shading.shadedUnion =
      volume
        (thickenedPlankClusterLongTubeDatum D theta i).shading.shadedUnion := by
  let G := thickenedPlankCluster D theta i
  let motion : Unit → RigidMotion := fun _ =>
    translationRigidMotion (-(ambientPlankCertificate G).box.center)
  change volume
      (indexedRigidCopyShading motion
        (thickenedPlankClusterLongTubeDatum D theta i).family
        (thickenedPlankClusterLongTubeDatum D theta i).shading).shadedUnion = _
  rw [indexedRigidCopyShading_shadedUnion]
  have hunion :
      (⋃ j : Unit,
        motion j ''
          (thickenedPlankClusterLongTubeDatum D theta i).shading.shadedUnion) =
        motion () ''
          (thickenedPlankClusterLongTubeDatum D theta i).shading.shadedUnion := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      simpa [motion] using hj
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨(), hx⟩
  rw [hunion]
  exact volume_rigidMotion_image (motion ()) _

theorem centeredThickenedPlankClusterLongTubeDatum_averageMultiplicity
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (centeredThickenedPlankClusterLongTubeDatum D theta i).shading.averageMultiplicity =
      (thickenedPlankClusterLongTubeDatum D theta i).shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [centeredThickenedPlankClusterLongTubeDatum_shadingMass,
    centeredThickenedPlankClusterLongTubeDatum_shadedUnionVolume]

#print axioms centeredThickenedPlankClusterLongTubeDatum_B2
#print axioms centeredThickenedPlankClusterLongTubeDatum_shadingMass
#print axioms centeredThickenedPlankClusterLongTubeDatum_actualFamilyVolume
#print axioms centeredThickenedPlankClusterLongTubeDatum_shadedUnionVolume
#print axioms centeredThickenedPlankClusterLongTubeDatum_averageMultiplicity

end
end Family8PlankThickControlCenteredLongTubeClusterV4
