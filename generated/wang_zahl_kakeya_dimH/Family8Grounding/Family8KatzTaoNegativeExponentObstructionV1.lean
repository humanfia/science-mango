import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8KatzTaoNegativeExponentObstructionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# The negative Katz--Tao exponent obstruction

The first layer is independent of the later explicit tube grid: a finite
pairwise-disjoint convex family has Katz--Tao constant one, and its literal
full shading has density and average multiplicity one.
-/

/-- Literal full shading of every member of a convex family. -/
def fullShading {iota : Type} (F : ConvexFamily iota) : Shading F where
  carrier i := (F i : Set Space)
  measurable_carrier i := (F i).isCompact.measurableSet
  carrier_subset _i := Set.Subset.rfl

@[simp] theorem fullShading_carrier
    {iota : Type} (F : ConvexFamily iota) (i : iota) :
    (fullShading F).carrier i = (F i : Set Space) := rfl

theorem fullShading_shadingMass
    {iota : Type} [Fintype iota] (F : ConvexFamily iota) :
    (fullShading F).shadingMass = familyVolume F := by
  rfl

theorem fullShading_shadedUnion
    {iota : Type} (F : ConvexFamily iota) :
    (fullShading F).shadedUnion = familyUnion F := by
  rfl

/-- Finite pairwise-disjoint measurable members have additive union volume. -/
theorem volume_familyUnion_eq_familyVolume_of_pairwiseDisjoint
    {iota : Type} [Fintype iota]
    (F : ConvexFamily iota)
    (hdisjoint : Set.Pairwise (Set.univ : Set iota)
      (fun i j => Disjoint (F i : Set Space) (F j : Set Space))) :
    volume (familyUnion F) = familyVolume F := by
  classical
  unfold familyUnion familyVolume
  have hpair : PairwiseDisjoint
      (↑(Finset.univ : Finset iota) : Set iota)
      (fun i => (F i : Set Space)) := by
    intro i _hi j _hj hij
    exact hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij
  simpa using measure_biUnion_finset hpair
    (fun i _hi => (F i).isCompact.measurableSet)

/-- Pairwise-disjoint convex bodies obey the global Katz--Tao estimate with
constant one. -/
theorem isKatzTao_one_of_pairwiseDisjoint
    {iota : Type} [Fintype iota]
    (F : ConvexFamily iota)
    (hdisjoint : Set.Pairwise (Set.univ : Set iota)
      (fun i j => Disjoint (F i : Set Space) (F j : Set Space))) :
    IsKatzTao 1 F := by
  classical
  intro K
  unfold IsKatzTaoAt
  rw [one_mul]
  let s : Finset iota := containedIndices F K
  have hpair : PairwiseDisjoint (↑s : Set iota)
      (fun i => (F i : Set Space)) := by
    intro i _hi j _hj hij
    exact hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij
  have hmeasure :
      volume (⋃ i ∈ s, (F i : Set Space)) =
        ∑ i ∈ s, volume (F i : Set Space) :=
    measure_biUnion_finset hpair
      (fun i _hi => (F i).isCompact.measurableSet)
  calc
    containedMass F K = ∑ i ∈ s, volume (F i : Set Space) := by rfl
    _ = volume (⋃ i ∈ s, (F i : Set Space)) := hmeasure.symm
    _ ≤ volume (K : Set Space) := by
      apply measure_mono
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      obtain ⟨hi, hxi⟩ := hx
      exact (mem_containedIndices F K i).1 hi hxi

/-- Full shading has density one whenever the indexed family volume is
nonzero. -/
theorem fullShading_shadingDensity_eq_one
    {iota : Type} [Fintype iota] (F : ConvexFamily iota)
    (hvolume : familyVolume F ≠ 0) :
    (fullShading F).shadingDensity = 1 := by
  unfold Shading.shadingDensity
  rw [fullShading_shadingMass, ENNReal.div_self hvolume (familyVolume_ne_top F)]

/-- For a nonzero pairwise-disjoint family, literal full shading also has
average multiplicity exactly one. -/
theorem fullShading_averageMultiplicity_eq_one
    {iota : Type} [Fintype iota] (F : ConvexFamily iota)
    (hdisjoint : Set.Pairwise (Set.univ : Set iota)
      (fun i j => Disjoint (F i : Set Space) (F j : Set Space)))
    (hvolume : familyVolume F ≠ 0) :
    (fullShading F).averageMultiplicity = 1 := by
  unfold Shading.averageMultiplicity
  rw [fullShading_shadingMass, fullShading_shadedUnion,
    volume_familyUnion_eq_familyVolume_of_pairwiseDisjoint F hdisjoint,
    ENNReal.div_self hvolume (familyVolume_ne_top F)]

#print axioms volume_familyUnion_eq_familyVolume_of_pairwiseDisjoint
#print axioms isKatzTao_one_of_pairwiseDisjoint
#print axioms fullShading_shadingDensity_eq_one
#print axioms fullShading_averageMultiplicity_eq_one

end
end Family8KatzTaoNegativeExponentObstructionV1
