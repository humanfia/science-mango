import FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
import FamilyStickyRandomFiniteMaximalCellCodeV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Lemma57TubeCoefficientDedupV1

open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyRandomFiniteMaximalCellCodeV1
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Maximal reduced-coefficient deduplication of actual tubes

A finite tube family admits a maximal subfamily separated by the reduced
`(a,b,d)` coefficient distance.  Every discarded tube is assigned to a
selected center at coefficient distance strictly below the target scale.
Thus any independently proved local near-coefficient multiplicity cap gives
an exact cardinal-retention bound for the selected separated subfamily.
-/

/-- A tube together with its membership in one finite family. -/
abbrev TubeMember {radius : NNReal} (family : Finset (Tube radius)) :=
  {T // T ∈ family}

/-- Reduced-coordinate separation on family members. -/
def coefficientSeparated {radius : NNReal}
    (family : Finset (Tube radius)) (delta : Real)
    (T U : TubeMember family) : Prop :=
  delta <= tubePairCoefficientDistance T.1 U.1

/-- Reduced-coordinate separation is symmetric. -/
theorem coefficientSeparated_symm
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real) :
    Std.Symm (coefficientSeparated family delta) := by
  constructor
  intro T U hTU
  rw [coefficientSeparated, tubePairCoefficientDistance_comm]
  exact hTU

/-- One canonical maximal reduced-coordinate separated selection. -/
noncomputable def coefficientSelection
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real) :
    MaximalSeparatedCells (coefficientSeparated family delta) := by
  classical
  exact Classical.choice
    (exists_maximalSeparatedCells (coefficientSeparated family delta)
      (coefficientSeparated_symm family delta))

/-- The selected actual tubes, forgetting their family-membership proofs. -/
noncomputable def selectedTubes
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real) :
    Finset (Tube radius) := by
  classical
  exact (coefficientSelection family delta).cells.image Subtype.val

/-- Every selected tube belongs to the original family. -/
theorem selectedTubes_subset
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real) :
    selectedTubes family delta ⊆ family := by
  classical
  intro T hT
  rw [selectedTubes, Finset.mem_image] at hT
  obtain ⟨member, _hmember, rfl⟩ := hT
  exact member.2

/-- Forgetting membership proofs does not change the selected cardinality. -/
theorem selectedTubes_card
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real) :
    (selectedTubes family delta).card =
      (coefficientSelection family delta).cells.card := by
  classical
  rw [selectedTubes]
  apply Finset.card_image_iff.mpr
  intro T _hT U _hU hval
  exact Subtype.ext hval

/-- Distinct selected actual tubes are separated at the requested reduced
coefficient scale. -/
theorem selectedTubes_pairwise_separated
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real) :
    forall T, T ∈ selectedTubes family delta ->
      forall U, U ∈ selectedTubes family delta -> T ≠ U ->
        delta <= tubePairCoefficientDistance T U := by
  classical
  intro T hT U hU hTU
  rw [selectedTubes, Finset.mem_image] at hT hU
  obtain ⟨memberT, hmemberT, rfl⟩ := hT
  obtain ⟨memberU, hmemberU, rfl⟩ := hU
  have hmembers : memberT ≠ memberU := by
    intro h
    exact hTU (congrArg Subtype.val h)
  exact (coefficientSelection family delta).pairwise
    hmemberT hmemberU hmembers

/-- Canonical selected coefficient center, with classical equality hidden behind
the noncomputable definition. -/
noncomputable def coefficientCode
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real)
    (T : TubeMember family) :
    (coefficientSelection family delta).Cell := by
  classical
  exact (coefficientSelection family delta).code T

/-- Every family member is assigned to a selected center within strict
reduced coefficient distance `delta`. -/
theorem coefficientSelection_code_distance_lt
    {radius : NNReal} (family : Finset (Tube radius))
    {delta : Real} (hdelta : 0 < delta) (T : TubeMember family) :
    tubePairCoefficientDistance T.1
      (coefficientCode family delta T).1.1 < delta := by
  classical
  let C := coefficientSelection family delta
  change tubePairCoefficientDistance T.1 (C.code T).1.1 < delta
  rcases C.eq_or_not_separated_code T with heq | hnot
  · have hval : T.1 = (C.code T).1.1 := congrArg Subtype.val heq
    rw [hval]
    simp [tubePairCoefficientDistance, coefficientDistance,
      tubePairDeltaA, tubePairDeltaB, tubePairDeltaD]
    exact hdelta
  · exact lt_of_not_ge (by
      simpa only [coefficientSeparated, C] using hnot)

/-- A local near-coefficient multiplicity cap gives exact cardinal retention
for the maximal separated subfamily. -/
theorem family_card_le_mul_selectedTubes_card_of_near_cap
    {radius : NNReal} (family : Finset (Tube radius))
    {delta : Real} (hdelta : 0 < delta) (multiplicity : Nat)
    (hnearCap : forall center, center ∈ selectedTubes family delta ->
      (family.filter fun T =>
        tubePairCoefficientDistance T center < delta).card <= multiplicity) :
    family.card <= multiplicity * (selectedTubes family delta).card := by
  classical
  let C := coefficientSelection family delta
  have hfiber : forall center : C.Cell,
      (Finset.univ.filter fun T => C.code T = center).card <=
        multiplicity := by
    intro center
    let source := Finset.univ.filter fun T => C.code T = center
    let near := family.filter fun T =>
      tubePairCoefficientDistance T center.1.1 < delta
    let embed : ↥source -> ↥near := fun T => ⟨T.1.1, by
      change T.1.1 ∈ family.filter fun U =>
        tubePairCoefficientDistance U center.1.1 < delta
      rw [Finset.mem_filter]
      have hcode : C.code T.1 = center :=
        (Finset.mem_filter.mp T.2).2
      have hclose := coefficientSelection_code_distance_lt
        family hdelta T.1
      change tubePairCoefficientDistance T.1.1
        (C.code T.1).1.1 < delta at hclose
      rw [hcode] at hclose
      exact ⟨T.1.2, hclose⟩⟩
    have hinjective : Function.Injective embed := by
      intro T U hTU
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun V : ↥near => V.1) hTU
    calc
      source.card = Fintype.card ↥source := (Fintype.card_coe source).symm
      _ <= Fintype.card ↥near := Fintype.card_le_of_injective embed hinjective
      _ = near.card := Fintype.card_coe near
      _ <= multiplicity := hnearCap center.1 (by
        rw [selectedTubes, Finset.mem_image]
        exact ⟨center.1, center.2, rfl⟩)
  have hretention := C.card_le_of_fiber_bound multiplicity hfiber
  calc
    family.card = Fintype.card (TubeMember family) :=
      (Fintype.card_coe family).symm
    _ <= multiplicity * Fintype.card C.Cell := hretention
    _ = multiplicity * C.cells.card := by rw [Fintype.card_coe]
    _ = multiplicity * (selectedTubes family delta).card := by
      rw [selectedTubes_card]

/-- If the original family has at least `3*multiplicity` members, the
retained separated family has at least three. -/
theorem three_le_selectedTubes_card_of_near_cap
    {radius : NNReal} (family : Finset (Tube radius))
    {delta : Real} (hdelta : 0 < delta) {multiplicity : Nat}
    (hmultiplicity : 0 < multiplicity)
    (hlarge : 3 * multiplicity <= family.card)
    (hnearCap : forall center, center ∈ selectedTubes family delta ->
      (family.filter fun T =>
        tubePairCoefficientDistance T center < delta).card <= multiplicity) :
    3 <= (selectedTubes family delta).card := by
  have hretention := family_card_le_mul_selectedTubes_card_of_near_cap
    family hdelta multiplicity hnearCap
  have hmul : 3 * multiplicity <=
      multiplicity * (selectedTubes family delta).card :=
    hlarge.trans hretention
  rw [Nat.mul_comm 3 multiplicity] at hmul
  exact Nat.le_of_mul_le_mul_left hmul hmultiplicity

#print axioms coefficientSeparated_symm
#print axioms coefficientSelection
#print axioms selectedTubes_subset
#print axioms selectedTubes_card
#print axioms selectedTubes_pairwise_separated
#print axioms coefficientSelection_code_distance_lt
#print axioms family_card_le_mul_selectedTubes_card_of_near_cap
#print axioms three_le_selectedTubes_card_of_near_cap

end

end FamilyStickyCinematicL32Lemma57TubeCoefficientDedupV1
