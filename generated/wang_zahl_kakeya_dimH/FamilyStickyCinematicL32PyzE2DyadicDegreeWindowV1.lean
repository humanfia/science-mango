import FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# Natural degree window attached to the actual `E₂` dyadic cell

The continuum selector stores the real window
`upper / 2 < #(Y₁(x)) ≤ upper`.  Natural ceilings turn this into the exact
integer lower and upper degrees consumed by the finite good-pair
regularization.  The two endpoints differ by at most a factor of two.
-/

def pyzE2DegreeLower (label : Int) : Nat :=
  Nat.ceil (dyadicCeilUpper label / 2)

def pyzE2DegreeUpper (label : Int) : Nat :=
  Nat.ceil (dyadicCeilUpper label)

theorem pyzE2DegreeLower_pos (label : Int)
    (hupper : 0 < dyadicCeilUpper label) :
    0 < pyzE2DegreeLower label := by
  rw [pyzE2DegreeLower, Nat.ceil_pos]
  positivity

theorem pyzE2DegreeUpper_pos (label : Int)
    (hupper : 0 < dyadicCeilUpper label) :
    0 < pyzE2DegreeUpper label := by
  rw [pyzE2DegreeUpper, Nat.ceil_pos]
  exact hupper

theorem pyzE2DegreeUpper_le_two_mul_lower (label : Int) :
    pyzE2DegreeUpper label ≤ 2 * pyzE2DegreeLower label := by
  rw [pyzE2DegreeUpper, Nat.ceil_le]
  have hceil : dyadicCeilUpper label / 2 ≤
      (Nat.ceil (dyadicCeilUpper label / 2) : Real) :=
    Nat.le_ceil _
  push_cast
  dsimp only [pyzE2DegreeLower]
  linarith

theorem pyzE2DegreeLower_le_active_card_of_mem_cell
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (x : point) (hx : x ∈ projectedPositiveMultiplicityDyadicCell Z label)
    (hactive : (Z.activeAtPoint x).Nonempty) :
    pyzE2DegreeLower label ≤ (Z.activeAtPoint x).card := by
  have hlabelEq : dyadicCeilBucket (projectedActiveMultiplicity Z x) =
      label := by
    simpa [projectedPositiveMultiplicityDyadicCell,
      continuumCriticalSingleDyadicCell, measurableLabelCell] using hx.2
  have hscalePos : 0 < projectedActiveMultiplicity Z x := by
    change 0 < ((Z.activeAtPoint x).card : Real)
    exact_mod_cast Finset.card_pos.mpr hactive
  have hbin := dyadicCeilUpper_half_lt_and_le hscalePos
  rw [hlabelEq] at hbin
  rw [pyzE2DegreeLower, Nat.ceil_le]
  change dyadicCeilUpper label / 2 ≤ projectedActiveMultiplicity Z x
  exact hbin.1.le

theorem active_card_le_pyzE2DegreeUpper_of_mem_cell
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (x : point) (hx : x ∈ projectedPositiveMultiplicityDyadicCell Z label)
    (hactive : (Z.activeAtPoint x).Nonempty) :
    (Z.activeAtPoint x).card ≤ pyzE2DegreeUpper label := by
  have hlabelEq : dyadicCeilBucket (projectedActiveMultiplicity Z x) =
      label := by
    simpa [projectedPositiveMultiplicityDyadicCell,
      continuumCriticalSingleDyadicCell, measurableLabelCell] using hx.2
  have hscalePos : 0 < projectedActiveMultiplicity Z x := by
    change 0 < ((Z.activeAtPoint x).card : Real)
    exact_mod_cast Finset.card_pos.mpr hactive
  have hbin := dyadicCeilUpper_half_lt_and_le hscalePos
  rw [hlabelEq] at hbin
  have hceil : dyadicCeilUpper label ≤
      (Nat.ceil (dyadicCeilUpper label) : Real) := Nat.le_ceil _
  rw [pyzE2DegreeUpper]
  have hupper : ((Z.activeAtPoint x).card : Real) ≤
      dyadicCeilUpper label := by
    change projectedActiveMultiplicity Z x ≤ dyadicCeilUpper label
    exact hbin.2
  exact_mod_cast hupper.trans hceil

#print axioms pyzE2DegreeLower
#print axioms pyzE2DegreeUpper
#print axioms pyzE2DegreeLower_pos
#print axioms pyzE2DegreeUpper_pos
#print axioms pyzE2DegreeUpper_le_two_mul_lower
#print axioms pyzE2DegreeLower_le_active_card_of_mem_cell
#print axioms active_card_le_pyzE2DegreeUpper_of_mem_cell

end
end FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
