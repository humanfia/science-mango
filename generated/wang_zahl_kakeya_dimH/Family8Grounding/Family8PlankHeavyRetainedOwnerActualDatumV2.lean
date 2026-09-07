import Family8Grounding.Family8PlankRetainedOwnerHeavyMassSelectionV3
import Family8Grounding.Family8PlankRetainedOwnerThickenedInducedShadingV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankHeavyRetainedOwnerActualDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankRetainedOwnerHeavyMassSelectionV3

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The actual source datum carried by the heavy retained owners

The half-average selection is pulled back along the already constructed owner
map before any cell or slab selection.  Thus this is a literal restricted
plank datum, not a final-row filter.  Its mass is exactly the sum of the heavy
owner-fibre masses and it retains the previous logarithmic owner datum with
loss two.  Grouping it by the same heavy owners gives an actual thickened
coarse shading with exactly the same shaded union.

This is the object on which the common CubeWeight/cell construction can be
rerun while preserving the rowwise half-average lower bound.
-/

/-- Source indices whose constructed owner survives the half-average heavy
selection. -/
def heavyRetainedOwnerSourceIndices
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : Finset iota :=
  Finset.univ.filter fun i => C.owner i ∈ heavyRetainedOwners C q

@[simp] theorem mem_heavyRetainedOwnerSourceIndices
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) (i : iota) :
    i ∈ heavyRetainedOwnerSourceIndices C q ↔
      C.owner i ∈ heavyRetainedOwners C q := by
  simp [heavyRetainedOwnerSourceIndices]

/-- The genuine source plank family obtained by retaining complete fibres of
the heavy owners. -/
def heavyRetainedOwnerPlankFamily
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    ShadedConvexPlankFamily
      {i // i ∈ heavyRetainedOwnerSourceIndices C q} a b where
  family := selectedCoarseFamily D.family
    (heavyRetainedOwnerSourceIndices C q)
  shading := selectedCoarseShading D.shading
    (heavyRetainedOwnerSourceIndices C q)
  comparisonConstant := D.comparisonConstant
  all_isPlank i := D.all_isPlank i.1
  ambient := D.ambient
  ambientComparisonConstant := D.ambientComparisonConstant
  ambient_is_unit_scale := D.ambient_is_unit_scale
  contained_in_ambient i := D.contained_in_ambient i.1

@[simp] theorem heavyRetainedOwnerPlankFamily_family_apply
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (i : {i // i ∈ heavyRetainedOwnerSourceIndices C q}) :
    (heavyRetainedOwnerPlankFamily D C q).family i = D.family i.1 := rfl

@[simp] theorem heavyRetainedOwnerPlankFamily_shading_carrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (i : {i // i ∈ heavyRetainedOwnerSourceIndices C q}) :
    (heavyRetainedOwnerPlankFamily D C q).shading.carrier i =
      D.shading.carrier i.1 := rfl

theorem heavyRetained_filter_owner_eq
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {s : iota} (hs : s ∈ heavyRetainedOwners C q) :
    (heavyRetainedOwnerSourceIndices C q).filter
        (fun i => C.owner i = s) = ownerFiber C s := by
  ext i
  simp only [Finset.mem_filter, mem_heavyRetainedOwnerSourceIndices,
    mem_ownerFiber]
  constructor
  · exact fun h => h.2
  · intro hi
    exact ⟨hi ▸ hs, hi⟩

/-- Exact finite reindexing of the heavy restricted source mass. -/
theorem sum_heavyRetained_eq_heavyRetainedOwnerMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (∑ i ∈ heavyRetainedOwnerSourceIndices C q,
        volume (D.shading.carrier i)) = heavyRetainedOwnerMass C q := by
  have hmaps :
      ((heavyRetainedOwnerSourceIndices C q : Finset iota) : Set iota).MapsTo
        C.owner (heavyRetainedOwners C q) := by
    intro i hi
    exact (mem_heavyRetainedOwnerSourceIndices C q i).1 hi
  calc
    (∑ i ∈ heavyRetainedOwnerSourceIndices C q,
        volume (D.shading.carrier i)) =
        ∑ s ∈ heavyRetainedOwners C q,
          ∑ i ∈ (heavyRetainedOwnerSourceIndices C q).filter
            (fun i => C.owner i = s), volume (D.shading.carrier i) :=
      (Finset.sum_fiberwise_of_maps_to hmaps
        (fun i => volume (D.shading.carrier i))).symm
    _ = ∑ s ∈ heavyRetainedOwners C q, ownerFiberMass C s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [heavyRetained_filter_owner_eq C q hs]
      rfl
    _ = heavyRetainedOwnerMass C q := rfl

/-- The actual heavy source datum has exactly the selected heavy fibre mass. -/
theorem heavyRetainedOwnerPlankFamily_shadingMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass =
      heavyRetainedOwnerMass C q := by
  change (selectedCoarseShading D.shading
    (heavyRetainedOwnerSourceIndices C q)).shadingMass = _
  rw [selectedCoarseShading_mass D.shading
    (heavyRetainedOwnerSourceIndices C q)]
  exact sum_heavyRetained_eq_heavyRetainedOwnerMass C q

/-- Pulling the heavy rows back to source indices preserves the proved
factor-two mass retention literally. -/
theorem retainedOwnerPlankFamily_mass_le_two_mul_heavyActualMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (retainedOwnerPlankFamily D C q).shading.shadingMass ≤
      2 * (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass := by
  rw [heavyRetainedOwnerPlankFamily_shadingMass]
  exact retainedOwnerPlankFamily_mass_le_two_mul_heavyRetainedOwnerMass
    D C q

/-- Any earlier source-to-retained mass comparison composes with the honest
heavy restriction without a conclusion-valued field. -/
theorem sourceMass_le_two_mul_loss_mul_heavyActualMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (loss : ENNReal)
    (hretained : D.shading.shadingMass ≤
      loss * (retainedOwnerPlankFamily D C q).shading.shadingMass) :
    D.shading.shadingMass ≤
      (2 * loss) *
        (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass := by
  calc
    D.shading.shadingMass ≤
        loss * (retainedOwnerPlankFamily D C q).shading.shadingMass := hretained
    _ ≤ loss *
        (2 * (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass) :=
      mul_le_mul' le_rfl
        (retainedOwnerPlankFamily_mass_le_two_mul_heavyActualMass D C q)
    _ = (2 * loss) *
        (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass := by
      ring

/-- Positive retained mass gives a genuine nonempty heavy source index type. -/
theorem heavyRetainedOwnerSourceIndices_nonempty_of_retainedMass_ne_zero
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    (heavyRetainedOwnerSourceIndices C q).Nonempty := by
  obtain ⟨s, hs⟩ :=
    heavyRetainedOwners_nonempty_of_retainedMass_pos D C q (bot_lt_iff_ne_bot.mpr hmass)
  have hsBucket : s ∈ selectedOwnerLogBucket C q :=
    (mem_heavyRetainedOwners C q s).1 hs |>.1
  have hsSelected : s ∈ C.selected :=
    (mem_selectedOwnerLogBucket C q s).1 hsBucket |>.1
  refine ⟨s, (mem_heavyRetainedOwnerSourceIndices C q s).2 ?_⟩
  simpa [owner_eq_self_of_selected C hsSelected] using hs

/-- Literal thickened bodies indexed only by the selected heavy owners. -/
def heavyRetainedOwnerThickenedFamily
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    ConvexFamily {s // s ∈ heavyRetainedOwners C q} :=
  fun s => ownerThickenedBody D theta s.1

/-- The induced coarse shading groups complete original owner fibres, now
only over the heavy owner set. -/
def heavyRetainedOwnerThickenedShading
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    Shading (heavyRetainedOwnerThickenedFamily D C q) where
  carrier := fun s => ownerFiberInducedCarrier C s.1
  measurable_carrier := fun s =>
    measurableSet_ownerFiberInducedCarrier C s.1
  carrier_subset := fun s =>
    ownerFiberInducedCarrier_subset_ownerThickenedBody D theta C s.1

@[simp] theorem heavyRetainedOwnerThickenedShading_carrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (s : {s // s ∈ heavyRetainedOwners C q}) :
    (heavyRetainedOwnerThickenedShading D C q).carrier s =
      ownerFiberInducedCarrier C s.1 := rfl

/-- Grouping the heavy source family by its actual owners preserves exactly
the shaded point set. -/
theorem heavyRetainedOwnerThickenedShading_shadedUnion_eq
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (heavyRetainedOwnerThickenedShading D C q).shadedUnion =
      (heavyRetainedOwnerPlankFamily D C q).shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hsx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hix⟩ := Set.mem_iUnion.mp hsx
    have howner : C.owner i.1 = s.1 :=
      (mem_ownerFiber C s.1 i.1).1 i.2
    have hiHeavy : C.owner i.1 ∈ heavyRetainedOwners C q := by
      rw [howner]
      exact s.2
    exact Set.mem_iUnion.mpr
      ⟨⟨i.1, (mem_heavyRetainedOwnerSourceIndices C q i.1).2 hiHeavy⟩, hix⟩
  · intro hx
    obtain ⟨i, hix⟩ := Set.mem_iUnion.mp hx
    have howner : C.owner i.1 ∈ heavyRetainedOwners C q :=
      (mem_heavyRetainedOwnerSourceIndices C q i.1).1 i.2
    let s : {s // s ∈ heavyRetainedOwners C q} :=
      ⟨C.owner i.1, howner⟩
    have hiFiber : i.1 ∈ ownerFiber C s.1 :=
      (mem_ownerFiber C s.1 i.1).2 rfl
    exact Set.mem_iUnion.mpr
      ⟨s, Set.mem_iUnion.mpr ⟨⟨i.1, hiFiber⟩, hix⟩⟩

/-- Every coarse row in the actual heavy datum has the common lower mass
certificate produced before the cell construction. -/
theorem heavyRetainedOwner_row_mass_floor
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (s : {s // s ∈ heavyRetainedOwners C q}) :
    retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s.1 :=
  retainedOwnerHalfAverageFloor_le_ownerFiberMass C q s.2

#print axioms mem_heavyRetainedOwnerSourceIndices
#print axioms heavyRetainedOwnerPlankFamily_family_apply
#print axioms heavyRetainedOwnerPlankFamily_shading_carrier
#print axioms heavyRetained_filter_owner_eq
#print axioms sum_heavyRetained_eq_heavyRetainedOwnerMass
#print axioms heavyRetainedOwnerPlankFamily_shadingMass
#print axioms retainedOwnerPlankFamily_mass_le_two_mul_heavyActualMass
#print axioms sourceMass_le_two_mul_loss_mul_heavyActualMass
#print axioms heavyRetainedOwnerSourceIndices_nonempty_of_retainedMass_ne_zero
#print axioms heavyRetainedOwnerThickenedShading_carrier
#print axioms heavyRetainedOwnerThickenedShading_shadedUnion_eq
#print axioms heavyRetainedOwner_row_mass_floor

end
end Family8PlankHeavyRetainedOwnerActualDatumV2
