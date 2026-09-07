import Family8Grounding.Family8PlankThickControlActualClusterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlActualCopyFamilyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlActualClusterV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The actual `M`-aware copied plank family, V2

Indexing by all pairs `(seed, member of the seed thickening cluster)` gives a
literal copied version of the source plank datum.  The diagonal occurrences
retain the full source mass and geometric union.  Summing the source
thick-control bounds the total number of copies by `|D| M theta`.
-/

/-- An occurrence records a seed plank and an actual source plank contained
in the seed's `theta*b` thickening. -/
abbrev ThickenedPlankOccurrence
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :=
  Σ i : iota, {j // j ∈ thickenedPlankIndices D theta i}

/-- The literal copied plank datum indexed by all thickening occurrences.
Every copy keeps the original convex body and the original shaded carrier. -/
def thickenedPlankCopyFamily
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    ShadedConvexPlankFamily (ThickenedPlankOccurrence D theta) a b where
  family p := D.family p.2.1
  shading := {
    carrier := fun p => D.shading.carrier p.2.1
    measurable_carrier := fun p => D.shading.measurable_carrier p.2.1
    carrier_subset := fun p => D.shading.carrier_subset p.2.1 }
  comparisonConstant := D.comparisonConstant
  all_isPlank p := D.all_isPlank p.2.1
  ambient := D.ambient
  ambientComparisonConstant := D.ambientComparisonConstant
  ambient_is_unit_scale := D.ambient_is_unit_scale
  contained_in_ambient p := D.contained_in_ambient p.2.1

@[simp] theorem thickenedPlankCopyFamily_family_apply
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    (thickenedPlankCopyFamily D theta).family p = D.family p.2.1 := rfl

@[simp] theorem thickenedPlankCopyFamily_shading_carrier
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    (thickenedPlankCopyFamily D theta).shading.carrier p =
      D.shading.carrier p.2.1 := rfl

theorem thickenedPlankOccurrence_card_eq
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    Fintype.card (ThickenedPlankOccurrence D theta) =
      ∑ i : iota, (thickenedPlankIndices D theta i).card := by
  simp only [ThickenedPlankOccurrence, Fintype.card_sigma, Fintype.card_coe]

/-- Summing the pointwise thick-control estimate bounds the number of actual
copies. -/
theorem thickenedPlankOccurrence_card_le
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b ≤ theta) (htheta : theta ≤ 1) :
    (Fintype.card (ThickenedPlankOccurrence D theta) : ENNReal) ≤
      (Fintype.card iota : ENNReal) *
        ((M : ENNReal) * (theta : ENNReal)) := by
  calc
    (Fintype.card (ThickenedPlankOccurrence D theta) : ENNReal) =
        ∑ i : iota, ((thickenedPlankIndices D theta i).card : ENNReal) := by
      simp only [thickenedPlankOccurrence_card_eq, Nat.cast_sum]
    _ ≤ ∑ _i : iota, (M : ENNReal) * (theta : ENNReal) := by
      exact Finset.sum_le_sum fun i _hi => hthick.2 theta hatheta htheta i
    _ = (Fintype.card iota : ENNReal) *
        ((M : ENNReal) * (theta : ENNReal)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

theorem thickenedPlankCopyFamily_shadingMass
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (thickenedPlankCopyFamily D theta).shading.shadingMass =
      ∑ i : iota, ∑ j ∈ thickenedPlankIndices D theta i,
        volume (D.shading.carrier j) := by
  unfold Shading.shadingMass
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Finset.sum_coe_sort (thickenedPlankIndices D theta i)
    (fun j => volume (D.shading.carrier j))

/-- Diagonal occurrences retain every source shading piece, so the copied
datum retains at least the entire source shading mass. -/
theorem source_shadingMass_le_thickenedPlankCopyFamily
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    D.shading.shadingMass ≤
      (thickenedPlankCopyFamily D theta).shading.shadingMass := by
  rw [thickenedPlankCopyFamily_shadingMass]
  unfold Shading.shadingMass
  apply Finset.sum_le_sum
  intro i _hi
  refine Finset.single_le_sum
    (s := thickenedPlankIndices D theta i)
    (f := fun j => volume (D.shading.carrier j)) ?_ ?_
  · intro j hj
    exact bot_le
  · exact source_mem_thickenedPlankIndices D theta i

theorem thickenedPlankCopyFamily_familyVolume
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    familyVolume (thickenedPlankCopyFamily D theta).family =
      ∑ i : iota, ∑ j ∈ thickenedPlankIndices D theta i,
        volume (D.family j : Set Space) := by
  unfold familyVolume
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Finset.sum_coe_sort (thickenedPlankIndices D theta i)
    (fun j => volume (D.family j : Set Space))

theorem source_familyVolume_le_thickenedPlankCopyFamily
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    familyVolume D.family ≤
      familyVolume (thickenedPlankCopyFamily D theta).family := by
  rw [thickenedPlankCopyFamily_familyVolume]
  unfold familyVolume
  apply Finset.sum_le_sum
  intro i _hi
  refine Finset.single_le_sum
    (s := thickenedPlankIndices D theta i)
    (f := fun j => volume (D.family j : Set Space)) ?_ ?_
  · intro j hj
    exact bot_le
  · exact source_mem_thickenedPlankIndices D theta i

/-- Copying changes multiplicity but not the geometric shaded union: every
copy comes from the source and every source index has its diagonal copy. -/
theorem thickenedPlankCopyFamily_shadedUnion_eq
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (thickenedPlankCopyFamily D theta).shading.shadedUnion =
      D.shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨p.2.1, hp⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    let p : ThickenedPlankOccurrence D theta :=
      ⟨i, ⟨i, source_mem_thickenedPlankIndices D theta i⟩⟩
    exact Set.mem_iUnion.mpr ⟨p, hi⟩

theorem source_averageMultiplicity_le_thickenedPlankCopyFamily
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    D.shading.averageMultiplicity ≤
      (thickenedPlankCopyFamily D theta).shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [thickenedPlankCopyFamily_shadedUnion_eq]
  gcongr
  exact source_shadingMass_le_thickenedPlankCopyFamily D theta

/-- Each copied body is contained in the thickening attached to its literal
seed coordinate. -/
theorem thickenedPlankCopyFamily_subset_seedThickening
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    ((thickenedPlankCopyFamily D theta).family p : Set Space) ⊆
      Metric.cthickening ((theta * b : NNReal) : Real)
        (D.family p.1 : Set Space) := by
  rw [thickenedPlankCopyFamily_family_apply]
  exact (mem_thickenedPlankIndices_iff D theta p.1 p.2.1).1 p.2.2

#print axioms thickenedPlankCopyFamily_family_apply
#print axioms thickenedPlankCopyFamily_shading_carrier
#print axioms thickenedPlankOccurrence_card_eq
#print axioms thickenedPlankOccurrence_card_le
#print axioms thickenedPlankCopyFamily_shadingMass
#print axioms source_shadingMass_le_thickenedPlankCopyFamily
#print axioms thickenedPlankCopyFamily_familyVolume
#print axioms source_familyVolume_le_thickenedPlankCopyFamily
#print axioms thickenedPlankCopyFamily_shadedUnion_eq
#print axioms source_averageMultiplicity_le_thickenedPlankCopyFamily
#print axioms thickenedPlankCopyFamily_subset_seedThickening

end
end Family8PlankThickControlActualCopyFamilyV2
