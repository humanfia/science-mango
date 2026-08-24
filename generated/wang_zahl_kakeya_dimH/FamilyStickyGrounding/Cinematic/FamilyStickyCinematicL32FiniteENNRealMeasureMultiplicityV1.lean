import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteMeasureMultiplicityV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteENNRealMeasureMultiplicityV1

open FamilyStickyCinematicL32FiniteMeasureMultiplicityV1

open scoped BigOperators ENNReal

noncomputable section

/-!
# Finite measure double counting with an ENNReal multiplicity bound

This variant of the previously frozen finite double count accepts a real or
extended-real pointwise multiplicity bound.  It is needed when separated
slope packing gives `#fiber <= C * lambda` without first rounding that
quantity to a natural number.
-/

/-- Finite measurable pieces of measure at least `area`, contained in one
target and with point multiplicity bounded by `B : ENNReal`, satisfy
`#pieces * area <= B * measure target`. -/
theorem card_mul_pieceMeasure_le_ennrealMultiplicity_mul_targetMeasure
    {alpha index : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (indices : Finset index)
    (pieces : index -> Set alpha) (target : Set alpha)
    {area B : ENNReal}
    (hmeasurable : forall i, i ∈ indices -> MeasurableSet (pieces i))
    (harea : forall i, i ∈ indices -> area <= mu (pieces i))
    (hsubset : forall i, i ∈ indices -> pieces i ⊆ target)
    (hmultiplicity : forall x, x ∈ target ->
      (pointMultiplicity indices pieces x : ENNReal) <= B) :
    (indices.card : ENNReal) * area <= B * mu target := by
  classical
  have hindicatorMeasurable : forall i, i ∈ indices ->
      Measurable ((pieces i).indicator (fun _ => (1 : ENNReal))) := by
    intro i hi
    exact measurable_const.indicator (hmeasurable i hi)
  have hpointwise : forall x,
      (∑ i ∈ indices,
        (pieces i).indicator (fun _ => (1 : ENNReal)) x) <=
      target.indicator (fun _ => B) x := by
    intro x
    by_cases hx : x ∈ target
    · rw [sum_indicator_one_eq_pointMultiplicity]
      simp only [Set.indicator, hx, if_true]
      exact hmultiplicity x hx
    · simp only [Set.indicator, hx, if_false, nonpos_iff_eq_zero]
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      exact fun hxpiece => hx (hsubset i hi hxpiece)
  calc
    (indices.card : ENNReal) * area = ∑ _i ∈ indices, area := by
      simp [nsmul_eq_mul]
    _ <= ∑ i ∈ indices, mu (pieces i) := by
      exact Finset.sum_le_sum harea
    _ = ∑ i ∈ indices,
        ∫⁻ x, (pieces i).indicator (fun _ => (1 : ENNReal)) x ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_indicator_const (hmeasurable i hi)]
      simp
    _ = ∫⁻ x, ∑ i ∈ indices,
        (pieces i).indicator (fun _ => (1 : ENNReal)) x ∂mu := by
      exact (lintegral_finsetSum indices hindicatorMeasurable).symm
    _ <= ∫⁻ x, target.indicator (fun _ => B) x ∂mu := by
      exact lintegral_mono hpointwise
    _ <= B * mu target := lintegral_indicator_const_le target B

#print axioms card_mul_pieceMeasure_le_ennrealMultiplicity_mul_targetMeasure

end

end FamilyStickyCinematicL32FiniteENNRealMeasureMultiplicityV1
