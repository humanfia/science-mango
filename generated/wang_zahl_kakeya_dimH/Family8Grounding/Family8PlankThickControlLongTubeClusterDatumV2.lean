import Family8Grounding.Family8PlankCertificateLongTubeCoverV2
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlLongTubeClusterDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankThickControlActualClusterV1

noncomputable section

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The literal `M`-controlled thickening cluster, covered by the genuine
same-index radius-`b` tubes selected from its actual plank certificates. -/
def thickenedPlankClusterLongTubeDatum
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    ActualTubeDatum b {j // j ∈ thickenedPlankIndices D theta i} where
  family := plankLongTubeCoverFamily (thickenedPlankCluster D theta i)
  shading := plankLongTubeCoverShading (thickenedPlankCluster D theta i)

@[simp] theorem thickenedPlankClusterLongTubeDatum_family
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (thickenedPlankClusterLongTubeDatum D theta i).family =
      plankLongTubeCoverFamily (thickenedPlankCluster D theta i) := rfl

@[simp] theorem thickenedPlankClusterLongTubeDatum_shading_carrier
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (j : {j // j ∈ thickenedPlankIndices D theta i}) :
    (thickenedPlankClusterLongTubeDatum D theta i).shading.carrier j =
      D.shading.carrier j.1 := rfl

theorem thickenedPlankCluster_body_subset_longTube
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (j : {j // j ∈ thickenedPlankIndices D theta i}) :
    (D.family j.1 : Set Space) ⊆
      ((thickenedPlankClusterLongTubeDatum D theta i).family.tubes j).carrier :=
  sourcePlank_subset_longTubeCover (thickenedPlankCluster D theta i) j

theorem thickenedPlankClusterLongTubeDatum_nonempty
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    Nonempty {j // j ∈ thickenedPlankIndices D theta i} :=
  thickenedPlankCluster_nonempty D theta i

theorem thickenedPlankClusterLongTubeDatum_card_le
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal) (i : iota)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b ≤ theta) (htheta : theta ≤ 1) :
    (Fintype.card {j // j ∈ thickenedPlankIndices D theta i} : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal) :=
  thickenedPlankCluster_card_le D M theta i hthick hatheta htheta

theorem thickenedPlankClusterLongTubeDatum_shadingMass
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (thickenedPlankClusterLongTubeDatum D theta i).shading.shadingMass =
      (thickenedPlankCluster D theta i).shading.shadingMass :=
  plankLongTubeCoverShading_shadingMass (thickenedPlankCluster D theta i)

theorem thickenedPlankClusterLongTubeDatum_shadedUnion
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (thickenedPlankClusterLongTubeDatum D theta i).shading.shadedUnion =
      (thickenedPlankCluster D theta i).shading.shadedUnion :=
  plankLongTubeCoverShading_shadedUnion (thickenedPlankCluster D theta i)

theorem thickenedPlankClusterLongTubeDatum_averageMultiplicity
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (thickenedPlankClusterLongTubeDatum D theta i).shading.averageMultiplicity =
      (thickenedPlankCluster D theta i).shading.averageMultiplicity :=
  plankLongTubeCoverShading_averageMultiplicity
    (thickenedPlankCluster D theta i)

theorem thickenedPlankCluster_familyVolume_le_longTubeDatum
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    familyVolume (thickenedPlankCluster D theta i).family ≤
      (thickenedPlankClusterLongTubeDatum D theta i).actualFamilyVolume :=
  source_familyVolume_le_longTubeCover (thickenedPlankCluster D theta i)

/-- The actual tube volume of one `M`-aware cluster has the explicit
`M * theta * 8 b^2` envelope. -/
theorem thickenedPlankClusterLongTubeDatum_actualFamilyVolume_le
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal) (i : iota)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b ≤ theta) (htheta : theta ≤ 1)
    (hb : b ≤ (2 : NNReal)⁻¹) :
    (thickenedPlankClusterLongTubeDatum D theta i).actualFamilyVolume ≤
      ((M : ENNReal) * (theta : ENNReal)) *
        (8 * (b : ENNReal) ^ 2) := by
  calc
    (thickenedPlankClusterLongTubeDatum D theta i).actualFamilyVolume ≤
        (Fintype.card {j // j ∈ thickenedPlankIndices D theta i} : ENNReal) *
          (8 * (b : ENNReal) ^ 2) :=
      longTubeCover_familyVolume_le_card_mul_eight_sq
        (thickenedPlankCluster D theta i) hb
    _ ≤ ((M : ENNReal) * (theta : ENNReal)) *
          (8 * (b : ENNReal) ^ 2) := by
      gcongr
      exact thickenedPlankCluster_card_le D M theta i hthick hatheta htheta

#print axioms thickenedPlankClusterLongTubeDatum_family
#print axioms thickenedPlankClusterLongTubeDatum_shading_carrier
#print axioms thickenedPlankCluster_body_subset_longTube
#print axioms thickenedPlankClusterLongTubeDatum_nonempty
#print axioms thickenedPlankClusterLongTubeDatum_card_le
#print axioms thickenedPlankClusterLongTubeDatum_shadingMass
#print axioms thickenedPlankClusterLongTubeDatum_shadedUnion
#print axioms thickenedPlankClusterLongTubeDatum_averageMultiplicity
#print axioms thickenedPlankCluster_familyVolume_le_longTubeDatum
#print axioms thickenedPlankClusterLongTubeDatum_actualFamilyVolume_le

end
end Family8PlankThickControlLongTubeClusterDatumV2
