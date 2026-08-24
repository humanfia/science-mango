import FamilyStickyCinematicL32PyzLowMultiplicityDegreeCapCleanV1
import FamilyStickyCinematicL32FiniteIncidenceThreeHalfUpperV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteMeasureMultiplicityV1
open FamilyStickyCinematicL32FiniteIncidenceThreeHalfUpperV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzLowMultiplicityDegreeCapCleanV1

open scoped BigOperators ENNReal

noncomputable section

/-!
# The actual E₂-restricted low-multiplicity three-halves estimate

On the strict complement of the PYZ high-degree gate, restrict every literal
projected `Y₁` carrier to the actual dyadic set `E₂`.  The resulting global
finite incidence multiplicity vanishes off `E₂` and is at most
`48 * logCount` on `E₂`.  The generic finite-incidence `3/2` theorem therefore
gives an exact bound by the sum of these restricted carrier masses.

The final theorem exposes the one remaining geometric source obligation as
`hmass`: a uniform bound for `μ(E₂ ∩ carrier i)`.  It does not rename or
assume PYZ (5.24), and it does not supply the missing paper-parameter
transport `μ → μ₁ → μ₂`.
-/

/-- The literal `E₂` part of one projected `Y₁` carrier. -/
def pyzE2RestrictedCarrier
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (i : index) : Set point :=
  projectedPositiveMultiplicityDyadicCell Z label ∩ Z.carrier i

theorem measurableSet_projectedPositiveMultiplicityDyadicCell
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int) :
    MeasurableSet (projectedPositiveMultiplicityDyadicCell Z label) := by
  exact measurableSet_continuumCriticalSingleDyadicCell
    Z.measurable_base (measurable_projectedActiveMultiplicity Z) label

theorem pointMultiplicity_pyzE2RestrictedCarrier_eq_active_card_of_mem
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (x : point) (hx : x ∈ projectedPositiveMultiplicityDyadicCell Z label) :
    pointMultiplicity Z.ambient (pyzE2RestrictedCarrier Z label) x =
      (Z.activeAtPoint x).card := by
  classical
  simp [pointMultiplicity, pyzE2RestrictedCarrier, hx,
    FiniteProjectedShading.activeAtPoint,
    finiteIncidenceActiveAtPoint]

theorem pointMultiplicity_pyzE2RestrictedCarrier_eq_zero_of_not_mem
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (x : point) (hx : x ∉ projectedPositiveMultiplicityDyadicCell Z label) :
    pointMultiplicity Z.ambient (pyzE2RestrictedCarrier Z label) x = 0 := by
  classical
  simp [pointMultiplicity, pyzE2RestrictedCarrier, hx]

/-- The strict low-degree gate gives a global multiplicity cap after the
literal carriers are restricted to `E₂`. -/
theorem pointMultiplicity_pyzE2RestrictedCarrier_le_fortyEight_mul_logCount
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (logCount : Nat)
    (hactive : ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
      (Z.activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    ∀ x, pointMultiplicity Z.ambient
      (pyzE2RestrictedCarrier Z label) x ≤ 48 * logCount := by
  intro x
  by_cases hx : x ∈ projectedPositiveMultiplicityDyadicCell Z label
  · rw [pointMultiplicity_pyzE2RestrictedCarrier_eq_active_card_of_mem
      Z label x hx]
    exact active_card_le_fortyEight_mul_logCount_of_mem_pyzE2
      Z label logCount x hx (hactive x hx) hlow
  · rw [pointMultiplicity_pyzE2RestrictedCarrier_eq_zero_of_not_mem
      Z label x hx]
    omega

/-- The literal `E₂` `3/2` moment is exactly the global finite-incidence
moment of the restricted carriers. -/
theorem lintegral_active_rpow_three_halves_eq_restrictedMultiplicity
    {point index : Type*} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int) :
    (∫⁻ x in projectedPositiveMultiplicityDyadicCell Z label,
      ((Z.activeAtPoint x).card : ENNReal) ^ (3 / 2 : Real) ∂mu) =
    ∫⁻ x, finiteMultiplicityThreeHalfWeight
      (pointMultiplicity Z.ambient (pyzE2RestrictedCarrier Z label) x) ∂mu := by
  let E2 := projectedPositiveMultiplicityDyadicCell Z label
  have hE2 : MeasurableSet E2 :=
    measurableSet_projectedPositiveMultiplicityDyadicCell Z label
  calc
    (∫⁻ x in E2,
      ((Z.activeAtPoint x).card : ENNReal) ^ (3 / 2 : Real) ∂mu) =
        ∫⁻ x in E2,
          finiteMultiplicityThreeHalfWeight (Z.activeAtPoint x).card ∂mu := by
      congr 1
      funext x
      exact (finiteMultiplicityThreeHalfWeight_eq_rpow
        (Z.activeAtPoint x).card).symm
    _ = ∫⁻ x, E2.indicator
        (fun x => finiteMultiplicityThreeHalfWeight
          (Z.activeAtPoint x).card) x ∂mu :=
      (lintegral_indicator hE2 _).symm
    _ = ∫⁻ x, finiteMultiplicityThreeHalfWeight
        (pointMultiplicity Z.ambient
          (pyzE2RestrictedCarrier Z label) x) ∂mu := by
      congr 1
      funext x
      by_cases hx : x ∈ E2
      · simp only [Set.indicator, hx, if_true]
        rw [pointMultiplicity_pyzE2RestrictedCarrier_eq_active_card_of_mem
          Z label x hx]
      · simp only [Set.indicator, hx, if_false]
        rw [pointMultiplicity_pyzE2RestrictedCarrier_eq_zero_of_not_mem
          Z label x hx]
        simp [finiteMultiplicityThreeHalfWeight]

/-- Low-degree `E₂` `3/2` moment bound with the actual sum of restricted
carrier measures retained. -/
theorem lintegral_active_rpow_three_halves_le_lowCap_sum_restricted_measure
    {point index : Type*} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int) (logCount : Nat)
    (hactive : ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
      (Z.activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    (∫⁻ x in projectedPositiveMultiplicityDyadicCell Z label,
      ((Z.activeAtPoint x).card : ENNReal) ^ (3 / 2 : Real) ∂mu) ≤
    ((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
      ∑ i ∈ Z.ambient, mu (pyzE2RestrictedCarrier Z label i) := by
  rw [lintegral_active_rpow_three_halves_eq_restrictedMultiplicity
    mu Z label]
  apply lintegral_threeHalfWeight_le_sqrtCap_mul_sum_measure
  · intro i hi
    exact (measurableSet_projectedPositiveMultiplicityDyadicCell Z label).inter
      (Z.measurable_carrier i hi)
  · exact pointMultiplicity_pyzE2RestrictedCarrier_le_fortyEight_mul_logCount
      Z label logCount hactive hlow

/-- Low-degree `E₂` `3/2` moment bound after a genuine one-carrier mass
estimate is supplied.  This is the last purely finite/measurable connector
before the missing geometric mass and paper-parameter inputs. -/
theorem lintegral_active_rpow_three_halves_le_lowCap_card_mul_pieceMass
    {point index : Type*} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int) (logCount : Nat) (pieceMass : ENNReal)
    (hactive : ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
      (Z.activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount)
    (hmass : ∀ i ∈ Z.ambient,
      mu (pyzE2RestrictedCarrier Z label i) ≤ pieceMass) :
    (∫⁻ x in projectedPositiveMultiplicityDyadicCell Z label,
      ((Z.activeAtPoint x).card : ENNReal) ^ (3 / 2 : Real) ∂mu) ≤
    ((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
      ((Z.ambient.card : ENNReal) * pieceMass) := by
  rw [lintegral_active_rpow_three_halves_eq_restrictedMultiplicity
    mu Z label]
  apply lintegral_threeHalfWeight_le_sqrtCap_mul_card_mul_pieceMass
  · intro i hi
    exact (measurableSet_projectedPositiveMultiplicityDyadicCell Z label).inter
      (Z.measurable_carrier i hi)
  · exact pointMultiplicity_pyzE2RestrictedCarrier_le_fortyEight_mul_logCount
      Z label logCount hactive hlow
  · exact hmass

#print axioms pointMultiplicity_pyzE2RestrictedCarrier_eq_active_card_of_mem
#print axioms pointMultiplicity_pyzE2RestrictedCarrier_eq_zero_of_not_mem
#print axioms pointMultiplicity_pyzE2RestrictedCarrier_le_fortyEight_mul_logCount
#print axioms lintegral_active_rpow_three_halves_eq_restrictedMultiplicity
#print axioms lintegral_active_rpow_three_halves_le_lowCap_sum_restricted_measure
#print axioms lintegral_active_rpow_three_halves_le_lowCap_card_mul_pieceMass

end
end FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
