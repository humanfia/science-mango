import FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41FiniteProjectedShadingE2MassV1

open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteIncidenceThreeHalfUpperV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

noncomputable section

universe u v

/-!
# E2 mass charged to the actual finite projected carriers

Every point of a positive-multiplicity set belongs to at least one literal
projected carrier.  Finite subadditivity therefore charges the measure of
that set to the sum of its carrier restrictions.  On a genuine dyadic E2
cell the lower multiplicity endpoint gives the stronger first-moment
inequality with its exact degree factor.

These statements use no disjointness.  Pairwise-disjoint survivor shadings
and their containment in an enlarged owner rectangle are separate geometric
inputs in the Lemma 5.5 cluster-mass argument.
-/

/-- A set on which the literal active family is nonempty has measure at most
the sum of the measures of its restrictions to the projected carriers. -/
theorem measure_le_sum_restrictedCarrier
    {point : Type u} {index : Type v} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (E : Set point)
    (hactive : forall x, x ∈ E -> (Z.activeAtPoint x).Nonempty) :
    mu E <= ∑ i ∈ Z.ambient, mu (E ∩ Z.carrier i) := by
  classical
  have hsubset :
      E ⊆ ⋃ i ∈ (Z.ambient : Set index), E ∩ Z.carrier i := by
    intro x hx
    obtain ⟨i, hi⟩ := hactive x hx
    have hiData := (Z.mem_activeAtPoint x i).mp hi
    simp only [mem_iUnion]
    exact ⟨i, hiData.1, hx, hiData.2⟩
  calc
    mu E <= mu (⋃ i ∈ (Z.ambient : Set index), E ∩ Z.carrier i) :=
      measure_mono hsubset
    _ <= ∑ i ∈ Z.ambient, mu (E ∩ Z.carrier i) :=
      measure_biUnion_finset_le Z.ambient _

/-- The preceding union bound specialized to the literal E2-restricted
carriers already used by the low-multiplicity moment API. -/
theorem measure_projectedPositiveMultiplicityDyadicCell_le_sum_restrictedCarrier
    {point : Type u} {index : Type v} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int)
    (hactive : forall x,
      x ∈ projectedPositiveMultiplicityDyadicCell Z label ->
        (Z.activeAtPoint x).Nonempty) :
    mu (projectedPositiveMultiplicityDyadicCell Z label) <=
      ∑ i ∈ Z.ambient, mu (pyzE2RestrictedCarrier Z label i) := by
  simpa only [pyzE2RestrictedCarrier] using
    measure_le_sum_restrictedCarrier mu Z
      (projectedPositiveMultiplicityDyadicCell Z label) hactive

/-- Exact first-moment strengthening: the dyadic lower degree times the E2
measure is charged to the sum of the literal E2-restricted carrier masses. -/
theorem degreeLower_mul_measure_le_sum_restrictedCarrier
    {point : Type u} {index : Type v} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int)
    (hactive : forall x,
      x ∈ projectedPositiveMultiplicityDyadicCell Z label ->
        (Z.activeAtPoint x).Nonempty) :
    (pyzE2DegreeLower label : ENNReal) *
        mu (projectedPositiveMultiplicityDyadicCell Z label) <=
      ∑ i ∈ Z.ambient, mu (pyzE2RestrictedCarrier Z label i) := by
  let E2 := projectedPositiveMultiplicityDyadicCell Z label
  have hE2 : MeasurableSet E2 :=
    measurableSet_projectedPositiveMultiplicityDyadicCell Z label
  have hmeasurable : forall i, i ∈ Z.ambient ->
      MeasurableSet (pyzE2RestrictedCarrier Z label i) := by
    intro i hi
    exact hE2.inter (Z.measurable_carrier i hi)
  calc
    (pyzE2DegreeLower label : ENNReal) * mu E2 =
        ∫⁻ x, E2.indicator
          (fun _ => (pyzE2DegreeLower label : ENNReal)) x ∂mu :=
      (lintegral_indicator_const hE2 _).symm
    _ <= ∫⁻ x, (FamilyStickyCinematicL32FiniteMeasureMultiplicityV1.pointMultiplicity
          Z.ambient (pyzE2RestrictedCarrier Z label) x : ENNReal) ∂mu := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ E2
      · simp only [Set.indicator, hx, if_true]
        rw [pointMultiplicity_pyzE2RestrictedCarrier_eq_active_card_of_mem
          Z label x hx]
        exact_mod_cast pyzE2DegreeLower_le_active_card_of_mem_cell
          Z label x hx (hactive x hx)
      · simp only [Set.indicator, hx, if_false]
        exact bot_le
    _ = ∑ i ∈ Z.ambient, mu (pyzE2RestrictedCarrier Z label i) :=
      lintegral_pointMultiplicity_eq_sum_measure mu Z.ambient
        (pyzE2RestrictedCarrier Z label) hmeasurable

#print axioms measure_le_sum_restrictedCarrier
#print axioms measure_projectedPositiveMultiplicityDyadicCell_le_sum_restrictedCarrier
#print axioms degreeLower_mul_measure_le_sum_restrictedCarrier

end

end FamilyStickyCinematicL32Prop41FiniteProjectedShadingE2MassV1
