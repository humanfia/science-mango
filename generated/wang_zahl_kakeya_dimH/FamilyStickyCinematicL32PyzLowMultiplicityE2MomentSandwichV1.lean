import FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzLowMultiplicityE2MomentSandwichV1

open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

open scoped BigOperators ENNReal

noncomputable section

/-!
# Lower/upper three-halves moment sandwich on the actual PYZ E₂ cell

The dyadic lower endpoint is a pointwise lower bound for the literal active
`Y₁` multiplicity on `E₂`.  Integrating its `3/2` power and combining with
the separately proved low-multiplicity upper moment gives the denominator-
free weak estimate in this module.

This is still not PYZ (5.24): the right-hand carrier mass and the paper's
`μ`, `μ₁`, `μ₂` scale relations remain explicit source obligations.
-/

/-- The lower endpoint of the actual dyadic multiplicity window controls
the `E₂` measure through the literal `3/2` moment. -/
theorem degreeLower_rpow_mul_measure_le_active_threeHalfMoment
    {point index : Type*} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int)
    (hactive : ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
      (Z.activeAtPoint x).Nonempty) :
    (pyzE2DegreeLower label : ENNReal) ^ (3 / 2 : Real) *
        mu (projectedPositiveMultiplicityDyadicCell Z label) ≤
      ∫⁻ x in projectedPositiveMultiplicityDyadicCell Z label,
        ((Z.activeAtPoint x).card : ENNReal) ^ (3 / 2 : Real) ∂mu := by
  let E2 := projectedPositiveMultiplicityDyadicCell Z label
  have hE2 : MeasurableSet E2 :=
    measurableSet_projectedPositiveMultiplicityDyadicCell Z label
  calc
    (pyzE2DegreeLower label : ENNReal) ^ (3 / 2 : Real) * mu E2 =
        ∫⁻ x, E2.indicator (fun _ =>
          (pyzE2DegreeLower label : ENNReal) ^ (3 / 2 : Real)) x ∂mu :=
      (lintegral_indicator_const hE2 _).symm
    _ ≤ ∫⁻ x, E2.indicator (fun x =>
        ((Z.activeAtPoint x).card : ENNReal) ^ (3 / 2 : Real)) x ∂mu := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ E2
      · simp only [Set.indicator, hx, if_true]
        apply ENNReal.rpow_le_rpow
        · exact_mod_cast pyzE2DegreeLower_le_active_card_of_mem_cell
            Z label x hx (hactive x hx)
        · norm_num
      · simp [Set.indicator, hx]
    _ = ∫⁻ x in E2,
        ((Z.activeAtPoint x).card : ENNReal) ^ (3 / 2 : Real) ∂mu :=
      lintegral_indicator hE2 _

/-- Denominator-free low-degree estimate retaining the exact sum of
restricted carrier masses. -/
theorem degreeLower_rpow_mul_measure_le_lowCap_sum_restricted_measure
    {point index : Type*} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int) (logCount : Nat)
    (hactive : ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
      (Z.activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    (pyzE2DegreeLower label : ENNReal) ^ (3 / 2 : Real) *
        mu (projectedPositiveMultiplicityDyadicCell Z label) ≤
      ((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
        ∑ i ∈ Z.ambient, mu (pyzE2RestrictedCarrier Z label i) := by
  exact (degreeLower_rpow_mul_measure_le_active_threeHalfMoment
    mu Z label hactive).trans
      (lintegral_active_rpow_three_halves_le_lowCap_sum_restricted_measure
        mu Z label logCount hactive hlow)

/-- Denominator-free low-degree estimate after a genuine uniform bound for
the actual restricted carriers is supplied. -/
theorem degreeLower_rpow_mul_measure_le_lowCap_card_mul_pieceMass
    {point index : Type*} [MeasurableSpace point]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (label : Int) (logCount : Nat) (pieceMass : ENNReal)
    (hactive : ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
      (Z.activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount)
    (hmass : ∀ i ∈ Z.ambient,
      mu (pyzE2RestrictedCarrier Z label i) ≤ pieceMass) :
    (pyzE2DegreeLower label : ENNReal) ^ (3 / 2 : Real) *
        mu (projectedPositiveMultiplicityDyadicCell Z label) ≤
      ((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
        ((Z.ambient.card : ENNReal) * pieceMass) := by
  exact (degreeLower_rpow_mul_measure_le_active_threeHalfMoment
    mu Z label hactive).trans
      (lintegral_active_rpow_three_halves_le_lowCap_card_mul_pieceMass
        mu Z label logCount pieceMass hactive hlow hmass)

#print axioms degreeLower_rpow_mul_measure_le_active_threeHalfMoment
#print axioms degreeLower_rpow_mul_measure_le_lowCap_sum_restricted_measure
#print axioms degreeLower_rpow_mul_measure_le_lowCap_card_mul_pieceMass

end
end FamilyStickyCinematicL32PyzLowMultiplicityE2MomentSandwichV1
