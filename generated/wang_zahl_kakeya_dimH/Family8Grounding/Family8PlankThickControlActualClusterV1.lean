import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlActualClusterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6AffinePlankAnalyticHypothesesStableV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Actual thickening clusters from the `M`-aware plank control

The thickened-plank control already singles out a literal finite collection
of source planks.  This file packages that collection as a genuine
`ShadedConvexPlankFamily` on the subtype, without replacing any body or
shading.  Thus its cardinality, shading mass, family volume, and carrier
containment can be used by a later geometric selector on the same datum.
-/

/-- The actual subfamily of planks lying in the prescribed thickening of one
source plank.  No surrogate bodies or conclusion-valued fields are added. -/
def thickenedPlankCluster
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    ShadedConvexPlankFamily {j // j ∈ thickenedPlankIndices D theta i} a b where
  family := selectedCoarseFamily D.family (thickenedPlankIndices D theta i)
  shading := selectedCoarseShading D.shading (thickenedPlankIndices D theta i)
  comparisonConstant := D.comparisonConstant
  all_isPlank j := D.all_isPlank j.1
  ambient := D.ambient
  ambientComparisonConstant := D.ambientComparisonConstant
  ambient_is_unit_scale := D.ambient_is_unit_scale
  contained_in_ambient j := D.contained_in_ambient j.1

@[simp] theorem thickenedPlankCluster_family_apply
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (j : {j // j ∈ thickenedPlankIndices D theta i}) :
    (thickenedPlankCluster D theta i).family j = D.family j.1 := rfl

@[simp] theorem thickenedPlankCluster_shading_carrier
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (j : {j // j ∈ thickenedPlankIndices D theta i}) :
    (thickenedPlankCluster D theta i).shading.carrier j =
      D.shading.carrier j.1 := rfl

@[simp] theorem mem_thickenedPlankIndices_iff
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i j : iota) :
    j ∈ thickenedPlankIndices D theta i ↔
      (D.family j : Set Space) ⊆
        Metric.cthickening ((theta * b : NNReal) : Real)
          (D.family i : Set Space) := by
  simp only [thickenedPlankIndices,
    Family6AffinePlankAnalyticHypothesesStableV1.containedIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem source_mem_thickenedPlankIndices
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    i ∈ thickenedPlankIndices D theta i := by
  rw [mem_thickenedPlankIndices_iff]
  exact Metric.self_subset_cthickening _

theorem thickenedPlankCluster_nonempty
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    Nonempty {j // j ∈ thickenedPlankIndices D theta i} :=
  ⟨⟨i, source_mem_thickenedPlankIndices D theta i⟩⟩

theorem thickenedPlankCluster_card_eq
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    Fintype.card {j // j ∈ thickenedPlankIndices D theta i} =
      (thickenedPlankIndices D theta i).card := by
  exact Fintype.card_coe _

/-- The source `M`-aware thickening estimate becomes the literal cardinality
bound for the actual restricted plank datum. -/
theorem thickenedPlankCluster_card_le
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal) (i : iota)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b ≤ theta) (htheta : theta ≤ 1) :
    (Fintype.card {j // j ∈ thickenedPlankIndices D theta i} : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal) := by
  simpa only [Fintype.card_coe] using hthick.2 theta hatheta htheta i

theorem thickenedPlankCluster_shadingMass
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (thickenedPlankCluster D theta i).shading.shadingMass =
      ∑ j ∈ thickenedPlankIndices D theta i,
        volume (D.shading.carrier j) := by
  exact selectedCoarseShading_mass D.shading
    (thickenedPlankIndices D theta i)

theorem thickenedPlankCluster_shadingMass_le
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (thickenedPlankCluster D theta i).shading.shadingMass ≤
      D.shading.shadingMass := by
  rw [thickenedPlankCluster_shadingMass]
  unfold Shading.shadingMass
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem thickenedPlankCluster_familyVolume
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    familyVolume (thickenedPlankCluster D theta i).family =
      ∑ j ∈ thickenedPlankIndices D theta i,
        volume (D.family j : Set Space) := by
  exact selectedCoarseFamily_volume D.family
    (thickenedPlankIndices D theta i)

theorem thickenedPlankCluster_familyVolume_le
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    familyVolume (thickenedPlankCluster D theta i).family ≤
      familyVolume D.family := by
  rw [thickenedPlankCluster_familyVolume]
  unfold familyVolume
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Every body in the actual cluster is contained in the very thickening used
by `FrostmanThickenedPlankControl`. -/
theorem thickenedPlankCluster_family_subset_thickening
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (j : {j // j ∈ thickenedPlankIndices D theta i}) :
    ((thickenedPlankCluster D theta i).family j : Set Space) ⊆
      Metric.cthickening ((theta * b : NNReal) : Real)
        (D.family i : Set Space) := by
  rw [thickenedPlankCluster_family_apply]
  exact (mem_thickenedPlankIndices_iff D theta i j.1).1 j.2

theorem thickenedPlankCluster_shadedUnion_subset
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (thickenedPlankCluster D theta i).shading.shadedUnion ⊆
      D.shading.shadedUnion := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨j.1, hj⟩

#print axioms thickenedPlankCluster_family_apply
#print axioms thickenedPlankCluster_shading_carrier
#print axioms mem_thickenedPlankIndices_iff
#print axioms source_mem_thickenedPlankIndices
#print axioms thickenedPlankCluster_nonempty
#print axioms thickenedPlankCluster_card_eq
#print axioms thickenedPlankCluster_card_le
#print axioms thickenedPlankCluster_shadingMass
#print axioms thickenedPlankCluster_shadingMass_le
#print axioms thickenedPlankCluster_familyVolume
#print axioms thickenedPlankCluster_familyVolume_le
#print axioms thickenedPlankCluster_family_subset_thickening
#print axioms thickenedPlankCluster_shadedUnion_subset

end
end Family8PlankThickControlActualClusterV1
