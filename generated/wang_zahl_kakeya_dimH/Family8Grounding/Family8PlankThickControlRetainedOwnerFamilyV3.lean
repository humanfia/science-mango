import Family8Grounding.Family8PlankThickControlOwnerFiberLogBucketV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlRetainedOwnerFamilyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The actual source plank refinement retained by one owner-cardinality bucket

V1 and V2 were failed drafts and are not imported.\n\nThe selected owner bucket is pulled back along the constructed owner map.
Restricting the original family to that literal finite set produces a genuine
`ShadedConvexPlankFamily`: bodies and shaded carriers are unchanged.  Its
shaded mass is exactly the sum of the retained owner-fibre masses, so the
logarithmic retention theorem becomes an actual-datum statement.
-/

/-- Source indices whose constructed owner belongs to the selected
logarithmic seed bucket. -/
def retainedOwnerSourceIndices
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : Finset iota :=
  Finset.univ.filter fun i ↦ C.owner i ∈ selectedOwnerLogBucket C q

@[simp] theorem mem_retainedOwnerSourceIndices
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) (i : iota) :
    i ∈ retainedOwnerSourceIndices C q ↔
      C.owner i ∈ selectedOwnerLogBucket C q := by
  simp [retainedOwnerSourceIndices]

/-- The genuine restricted source plank datum carried by one owner bucket. -/
def retainedOwnerPlankFamily
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    ShadedConvexPlankFamily {i // i ∈ retainedOwnerSourceIndices C q} a b where
  family := selectedCoarseFamily D.family (retainedOwnerSourceIndices C q)
  shading := selectedCoarseShading D.shading (retainedOwnerSourceIndices C q)
  comparisonConstant := D.comparisonConstant
  all_isPlank i := D.all_isPlank i.1
  ambient := D.ambient
  ambientComparisonConstant := D.ambientComparisonConstant
  ambient_is_unit_scale := D.ambient_is_unit_scale
  contained_in_ambient i := D.contained_in_ambient i.1

@[simp] theorem retainedOwnerPlankFamily_family_apply
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (i : {i // i ∈ retainedOwnerSourceIndices C q}) :
    (retainedOwnerPlankFamily D C q).family i = D.family i.1 := rfl

@[simp] theorem retainedOwnerPlankFamily_shading_carrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (i : {i // i ∈ retainedOwnerSourceIndices C q}) :
    (retainedOwnerPlankFamily D C q).shading.carrier i =
      D.shading.carrier i.1 := rfl

/-- On a retained seed, its owner fibre is exactly the corresponding fibre
inside the pullback source refinement. -/
theorem retained_filter_owner_eq
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {s : iota} (hs : s ∈ selectedOwnerLogBucket C q) :
    (retainedOwnerSourceIndices C q).filter (fun i ↦ C.owner i = s) =
      ownerFiber C s := by
  ext i
  simp only [Finset.mem_filter, mem_retainedOwnerSourceIndices,
    mem_ownerFiber]
  constructor
  · exact fun h ↦ h.2
  · intro hi
    exact ⟨hi ▸ hs, hi⟩

/-- Exact finite reindexing of the retained source mass by selected owners. -/
theorem sum_retained_eq_sum_ownerFiberMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (∑ i ∈ retainedOwnerSourceIndices C q,
        volume (D.shading.carrier i)) =
      ∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s := by
  have hmaps :
      ((retainedOwnerSourceIndices C q : Finset iota) : Set iota).MapsTo
        C.owner (selectedOwnerLogBucket C q) := by
    intro i hi
    exact (mem_retainedOwnerSourceIndices C q i).1 hi
  calc
    (∑ i ∈ retainedOwnerSourceIndices C q,
        volume (D.shading.carrier i)) =
        ∑ s ∈ selectedOwnerLogBucket C q,
          ∑ i ∈ (retainedOwnerSourceIndices C q).filter
            (fun i ↦ C.owner i = s), volume (D.shading.carrier i) :=
      (Finset.sum_fiberwise_of_maps_to hmaps
        (fun i ↦ volume (D.shading.carrier i))).symm
    _ = ∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [retained_filter_owner_eq C q hs]
      rfl

/-- The restricted actual plank datum has precisely the bucketed owner-fibre
shaded mass. -/
theorem retainedOwnerPlankFamily_shadingMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (retainedOwnerPlankFamily D C q).shading.shadingMass =
      ∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s := by
  change (selectedCoarseShading D.shading
    (retainedOwnerSourceIndices C q)).shadingMass = _
  rw [selectedCoarseShading_mass D.shading (retainedOwnerSourceIndices C q)]
  exact sum_retained_eq_sum_ownerFiberMass C q

/-- Positive retained mass makes the actual restricted index type nonempty. -/
theorem retainedOwnerSourceIndices_nonempty_of_mass_ne_zero
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    (retainedOwnerSourceIndices C q).Nonempty := by
  by_contra hempty
  have hindices : retainedOwnerSourceIndices C q = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hzero :
      (retainedOwnerPlankFamily D C q).shading.shadingMass = 0 := by
    change (selectedCoarseShading D.shading
      (retainedOwnerSourceIndices C q)).shadingMass = 0
    rw [selectedCoarseShading_mass D.shading (retainedOwnerSourceIndices C q),
      hindices]
    simp
  exact hmass hzero

/-- Actual-datum version of the M-aware logarithmic owner selection. -/
theorem exists_retainedOwnerPlankFamily_mass_card_thickControl
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal)
    (C : MutualThickeningClustering D theta)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b ≤ theta) (htheta : theta ≤ 1) :
    ∃ q : Fin (Nat.log 2 (Fintype.card iota) + 1),
      D.shading.shadingMass ≤
        (Nat.log 2 (Fintype.card iota) + 1 : Nat) *
          (retainedOwnerPlankFamily D C q).shading.shadingMass ∧
      0 < ownerBucketBranching q ∧
      ∀ s ∈ selectedOwnerLogBucket C q,
        ownerBucketBranching q ≤ (ownerFiber C s).card ∧
        (ownerFiber C s).card < 2 * ownerBucketBranching q ∧
        ((ownerFiber C s).card : ENNReal) ≤
          (M : ENNReal) * (theta : ENNReal) := by
  obtain ⟨q, hmass, hNpos, hbounds⟩ :=
    exists_selectedOwnerLogBucket_mass_card_thickControl
      D M theta C hthick hatheta htheta
  refine ⟨q, ?_, hNpos, hbounds⟩
  simpa only [retainedOwnerPlankFamily_shadingMass] using hmass

#print axioms mem_retainedOwnerSourceIndices
#print axioms retainedOwnerPlankFamily_family_apply
#print axioms retainedOwnerPlankFamily_shading_carrier
#print axioms retained_filter_owner_eq
#print axioms sum_retained_eq_sum_ownerFiberMass
#print axioms retainedOwnerPlankFamily_shadingMass
#print axioms retainedOwnerSourceIndices_nonempty_of_mass_ne_zero
#print axioms exists_retainedOwnerPlankFamily_mass_card_thickControl

end
end Family8PlankThickControlRetainedOwnerFamilyV3
