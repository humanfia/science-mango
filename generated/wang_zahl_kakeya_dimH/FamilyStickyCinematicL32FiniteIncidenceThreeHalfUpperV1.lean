import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteMeasureMultiplicityV1
import FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteIncidenceThreeHalfUpperV1

open FamilyStickyCinematicL32FiniteMeasureMultiplicityV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1

open scoped BigOperators ENNReal

noncomputable section

/-!
# Finite-incidence three-halves upper bound

This is the measure-theoretic algebra needed at the entrance to the weak
low-multiplicity alternative in Pramanik--Yang--Zahl, Section 5.  A pointwise
multiplicity cap bounds the `3/2` moment by the square root of that cap times
the first moment; finite incidence double counting identifies the first
moment with the sum of the carrier measures.

This module does **not** assert PYZ (5.24).  Applying it there still requires
the geometric one-carrier mass estimate for the actual `Y₁` pieces and the
quantitative transport of the paper parameters `μ`, `μ₁`, and `μ₂`.
-/

/-- The exact `3/2` weight of a finite multiplicity, written in a form that
separates its first moment from its square-root factor. -/
def finiteMultiplicityThreeHalfWeight (n : Nat) : ENNReal :=
  (n : ENNReal) * (n : ENNReal) ^ (1 / 2 : Real)

theorem finiteMultiplicityThreeHalfWeight_eq_rpow (n : Nat) :
    finiteMultiplicityThreeHalfWeight n =
      (n : ENNReal) ^ (3 / 2 : Real) := by
  rw [show (3 / 2 : Real) = 1 + 1 / 2 by norm_num,
    ENNReal.rpow_add_of_nonneg (1 : Real) (1 / 2 : Real)
      (by norm_num) (by norm_num),
    ENNReal.rpow_one]
  rfl

/-- A pointwise cap turns the finite `3/2` weight into the first moment times
the square root of the cap. -/
theorem finiteMultiplicityThreeHalfWeight_le
    {n M : Nat} (h : n ≤ M) :
    finiteMultiplicityThreeHalfWeight n ≤
      (M : ENNReal) ^ (1 / 2 : Real) * (n : ENNReal) := by
  have hcast : (n : ENNReal) ≤ (M : ENNReal) := by
    exact_mod_cast h
  have hrpow : (n : ENNReal) ^ (1 / 2 : Real) ≤
      (M : ENNReal) ^ (1 / 2 : Real) :=
    ENNReal.rpow_le_rpow hcast (by norm_num)
  calc
    finiteMultiplicityThreeHalfWeight n =
        (n : ENNReal) * (n : ENNReal) ^ (1 / 2 : Real) := rfl
    _ ≤ (n : ENNReal) * (M : ENNReal) ^ (1 / 2 : Real) :=
      mul_le_mul_right hrpow _
    _ = (M : ENNReal) ^ (1 / 2 : Real) * (n : ENNReal) := mul_comm _ _

/-- The first moment of a finite measurable incidence multiplicity is the
sum of the measures of its carriers. -/
theorem lintegral_pointMultiplicity_eq_sum_measure
    {alpha index : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (indices : Finset index)
    (pieces : index → Set alpha)
    (hmeasurable : ∀ i ∈ indices, MeasurableSet (pieces i)) :
    (∫⁻ x, (pointMultiplicity indices pieces x : ENNReal) ∂mu) =
      ∑ i ∈ indices, mu (pieces i) := by
  classical
  have hindicatorMeasurable : ∀ i ∈ indices,
      Measurable ((pieces i).indicator (fun _ => (1 : ENNReal))) := by
    intro i hi
    exact measurable_const.indicator (hmeasurable i hi)
  calc
    (∫⁻ x, (pointMultiplicity indices pieces x : ENNReal) ∂mu) =
        ∫⁻ x, ∑ i ∈ indices,
          (pieces i).indicator (fun _ => (1 : ENNReal)) x ∂mu := by
      congr 1
      funext x
      exact (sum_indicator_one_eq_pointMultiplicity indices pieces x).symm
    _ = ∑ i ∈ indices,
        ∫⁻ x, (pieces i).indicator (fun _ => (1 : ENNReal)) x ∂mu :=
      lintegral_finsetSum indices hindicatorMeasurable
    _ = ∑ i ∈ indices, mu (pieces i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_indicator_const (hmeasurable i hi)]
      simp

/-- Abstract finite-incidence low-multiplicity estimate: a pointwise cap
controls the `3/2` moment by the summed carrier mass. -/
theorem lintegral_threeHalfWeight_le_sqrtCap_mul_sum_measure
    {alpha index : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (indices : Finset index)
    (pieces : index → Set alpha) (M : Nat)
    (hmeasurable : ∀ i ∈ indices, MeasurableSet (pieces i))
    (hcap : ∀ x, pointMultiplicity indices pieces x ≤ M) :
    (∫⁻ x, finiteMultiplicityThreeHalfWeight
        (pointMultiplicity indices pieces x) ∂mu) ≤
      (M : ENNReal) ^ (1 / 2 : Real) *
        ∑ i ∈ indices, mu (pieces i) := by
  have hmultiplicityMeasurable : Measurable (fun x =>
      (pointMultiplicity indices pieces x : ENNReal)) := by
    have hpattern := measurable_finiteIncidencePatternValue indices
      (fun i x => x ∈ pieces i) hmeasurable
      (fun active => (active.card : ENNReal))
    simpa [pointMultiplicity, finiteIncidenceActiveAtPoint] using hpattern
  calc
    (∫⁻ x, finiteMultiplicityThreeHalfWeight
        (pointMultiplicity indices pieces x) ∂mu) ≤
        ∫⁻ x, (M : ENNReal) ^ (1 / 2 : Real) *
          (pointMultiplicity indices pieces x : ENNReal) ∂mu := by
      exact lintegral_mono fun x =>
        finiteMultiplicityThreeHalfWeight_le (hcap x)
    _ = (M : ENNReal) ^ (1 / 2 : Real) *
        ∫⁻ x, (pointMultiplicity indices pieces x : ENNReal) ∂mu :=
      lintegral_const_mul _ hmultiplicityMeasurable
    _ = (M : ENNReal) ^ (1 / 2 : Real) *
        ∑ i ∈ indices, mu (pieces i) := by
      rw [lintegral_pointMultiplicity_eq_sum_measure
        mu indices pieces hmeasurable]

/-- If every carrier has mass at most `pieceMass`, the summed-mass term is
bounded by the literal family cardinality times that mass. -/
theorem lintegral_threeHalfWeight_le_sqrtCap_mul_card_mul_pieceMass
    {alpha index : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (indices : Finset index)
    (pieces : index → Set alpha) (M : Nat) (pieceMass : ENNReal)
    (hmeasurable : ∀ i ∈ indices, MeasurableSet (pieces i))
    (hcap : ∀ x, pointMultiplicity indices pieces x ≤ M)
    (hmass : ∀ i ∈ indices, mu (pieces i) ≤ pieceMass) :
    (∫⁻ x, finiteMultiplicityThreeHalfWeight
        (pointMultiplicity indices pieces x) ∂mu) ≤
      (M : ENNReal) ^ (1 / 2 : Real) *
        ((indices.card : ENNReal) * pieceMass) := by
  refine (lintegral_threeHalfWeight_le_sqrtCap_mul_sum_measure
    mu indices pieces M hmeasurable hcap).trans ?_
  apply mul_le_mul_right
  calc
    (∑ i ∈ indices, mu (pieces i)) ≤ ∑ _i ∈ indices, pieceMass :=
      Finset.sum_le_sum hmass
    _ = (indices.card : ENNReal) * pieceMass := by
      simp [nsmul_eq_mul]

#print axioms finiteMultiplicityThreeHalfWeight_eq_rpow
#print axioms finiteMultiplicityThreeHalfWeight_le
#print axioms lintegral_pointMultiplicity_eq_sum_measure
#print axioms lintegral_threeHalfWeight_le_sqrtCap_mul_sum_measure
#print axioms lintegral_threeHalfWeight_le_sqrtCap_mul_card_mul_pieceMass

end
end FamilyStickyCinematicL32FiniteIncidenceThreeHalfUpperV1
