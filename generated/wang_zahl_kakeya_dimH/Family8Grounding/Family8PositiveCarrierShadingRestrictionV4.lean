import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV5

/-!
# Positive-carrier restriction of a finite shading, V4

Removing all zero-volume carrier pieces preserves shading mass and union
volume, hence average multiplicity.  A nonzero shading restricts to a
nonempty finite subtype with an automatically constructed positive finite
carrier-volume floor.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PositiveCarrierShadingRestrictionV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota] {F : ConvexFamily iota}

def positiveCarrierIndices (Y : Shading F) : Finset iota :=
  Finset.univ.filter fun i => volume (Y.carrier i) ≠ 0

abbrev positiveCarrierFamily (Y : Shading F) :
    ConvexFamily {i // i ∈ positiveCarrierIndices Y} :=
  selectedCoarseFamily F (positiveCarrierIndices Y)

def positiveCarrierShading (Y : Shading F) :
    Shading (positiveCarrierFamily Y) :=
  selectedCoarseShading Y (positiveCarrierIndices Y)

@[simp] theorem mem_positiveCarrierIndices (Y : Shading F) (i : iota) :
    i ∈ positiveCarrierIndices Y ↔ volume (Y.carrier i) ≠ 0 := by
  simp only [positiveCarrierIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]

@[simp] theorem positiveCarrierShading_carrier
    (Y : Shading F) (i : {i // i ∈ positiveCarrierIndices Y}) :
    (positiveCarrierShading Y).carrier i = Y.carrier i.1 := rfl

theorem positiveCarrierShading_shadingMass (Y : Shading F) :
    (positiveCarrierShading Y).shadingMass = Y.shadingMass := by
  rw [positiveCarrierShading, selectedCoarseShading_mass]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hnot
  by_contra hne
  exact hnot ((mem_positiveCarrierIndices Y i).2 hne)

def zeroCarrierUnion (Y : Shading F) : Set Space :=
  ⋃ i : {i // i ∉ positiveCarrierIndices Y}, Y.carrier i.1

theorem volume_zeroCarrierUnion (Y : Shading F) :
    volume (zeroCarrierUnion Y) = 0 := by
  unfold zeroCarrierUnion
  apply measure_iUnion_null
  intro i
  by_contra hne
  exact i.2 ((mem_positiveCarrierIndices Y i.1).2 hne)

theorem shadedUnion_eq_positiveCarrier_union_zeroCarrier
    (Y : Shading F) :
    Y.shadedUnion =
      (positiveCarrierShading Y).shadedUnion ∪ zeroCarrierUnion Y := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    by_cases hi : i ∈ positiveCarrierIndices Y
    · left
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    · right
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  · intro hx
    rcases hx with hx | hx
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i.1, hxi⟩
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i.1, hxi⟩

theorem positiveCarrierShading_shadedUnion_volume (Y : Shading F) :
    volume (positiveCarrierShading Y).shadedUnion =
      volume Y.shadedUnion := by
  have hnull :
      (((positiveCarrierShading Y).shadedUnion ∪ zeroCarrierUnion Y : Set Space))
          =ᵐ[volume]
        ((positiveCarrierShading Y).shadedUnion : Set Space) :=
    union_ae_eq_left_of_ae_eq_empty
      (ae_eq_empty.mpr (volume_zeroCarrierUnion Y))
  have hmeasure :
      volume ((positiveCarrierShading Y).shadedUnion ∪ zeroCarrierUnion Y) =
        volume (positiveCarrierShading Y).shadedUnion :=
    measure_congr hnull
  have hunion := congrArg volume
    (shadedUnion_eq_positiveCarrier_union_zeroCarrier Y)
  exact hmeasure.symm.trans hunion.symm

theorem positiveCarrierShading_averageMultiplicity (Y : Shading F) :
    (positiveCarrierShading Y).averageMultiplicity =
      Y.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [positiveCarrierShading_shadingMass,
    positiveCarrierShading_shadedUnion_volume]

theorem positiveCarrierIndices_nonempty_of_shadingMass_ne_zero
    (Y : Shading F) (hmass : Y.shadingMass ≠ 0) :
    (positiveCarrierIndices Y).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hmass
  rw [← positiveCarrierShading_shadingMass Y]
  rw [positiveCarrierShading, selectedCoarseShading_mass, hempty]
  simp

def positiveCarrierVolumeFloor (Y : Shading F)
    (hpos : (positiveCarrierIndices Y).Nonempty) : ENNReal :=
  (positiveCarrierIndices Y).inf' hpos
    (fun i => volume (Y.carrier i))

theorem positiveCarrierVolumeFloor_le
    (Y : Shading F) (hpos : (positiveCarrierIndices Y).Nonempty)
    (q : {i // i ∈ positiveCarrierIndices Y}) :
    positiveCarrierVolumeFloor Y hpos ≤
      volume ((positiveCarrierShading Y).carrier q) := by
  exact Finset.inf'_le (fun i => volume (Y.carrier i)) q.2

theorem positiveCarrierVolumeFloor_pos
    (Y : Shading F) (hpos : (positiveCarrierIndices Y).Nonempty) :
    0 < positiveCarrierVolumeFloor Y hpos := by
  apply Finset.inf'_mem (Set.Ioi (0 : ENNReal))
  · intro x hx y hy
    exact lt_min (show 0 < x from hx) (show 0 < y from hy)
  · intro i hi
    exact bot_lt_iff_ne_bot.mpr ((mem_positiveCarrierIndices Y i).1 hi)

theorem positiveCarrierVolumeFloor_ne_zero
    (Y : Shading F) (hpos : (positiveCarrierIndices Y).Nonempty) :
    positiveCarrierVolumeFloor Y hpos ≠ 0 :=
  (positiveCarrierVolumeFloor_pos Y hpos).ne'

theorem positiveCarrierVolumeFloor_ne_top
    (Y : Shading F) (hpos : (positiveCarrierIndices Y).Nonempty) :
    positiveCarrierVolumeFloor Y hpos ≠ ∞ := by
  let lower := positiveCarrierVolumeFloor Y hpos
  change lower ≠ ∞
  obtain ⟨i, hi⟩ := hpos
  have hle : lower ≤ volume (Y.carrier i) := by
    exact Finset.inf'_le (fun j => volume (Y.carrier j)) hi
  intro htop
  have hivol : volume (Y.carrier i) = ∞ :=
    top_unique (by simpa only [htop] using hle)
  exact (shadingPiece_volume_lt_top Y i).ne hivol

#print axioms positiveCarrierShading_shadingMass
#print axioms volume_zeroCarrierUnion
#print axioms positiveCarrierShading_shadedUnion_volume
#print axioms positiveCarrierShading_averageMultiplicity
#print axioms positiveCarrierIndices_nonempty_of_shadingMass_ne_zero
#print axioms positiveCarrierVolumeFloor_le
#print axioms positiveCarrierVolumeFloor_pos
#print axioms positiveCarrierVolumeFloor_ne_zero
#print axioms positiveCarrierVolumeFloor_ne_top

end

end Family8PositiveCarrierShadingRestrictionV4
