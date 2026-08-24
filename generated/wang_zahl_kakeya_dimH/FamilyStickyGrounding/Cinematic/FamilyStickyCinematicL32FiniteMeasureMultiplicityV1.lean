import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteMeasureMultiplicityV1

open scoped BigOperators ENNReal

noncomputable section

/-!
# Finite measure double counting with bounded point multiplicity

This is the measure-theoretic counting step in the proof of
Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.15.  Once rectangle
geometry supplies a lower area bound, containment in one enlarged
rectangle, and a pointwise multiplicity bound (obtained there from slope
packing), the global rectangle count follows by integrating the finite
incidence multiplicity.

No rectangle-count or cinematic `L^{3/2}` conclusion is assumed here.
-/

/-- The number of members of a finite set family containing a point. -/
noncomputable def pointMultiplicity {alpha index : Type*}
    (indices : Finset index) (pieces : index -> Set alpha) (x : alpha) : Nat := by
  classical
  exact (indices.filter fun i => x ∈ pieces i).card

/-- The sum of `ENNReal` indicator functions is exactly the cast of the
finite point multiplicity. -/
theorem sum_indicator_one_eq_pointMultiplicity
    {alpha index : Type*} (indices : Finset index)
    (pieces : index -> Set alpha) (x : alpha) :
    (∑ i ∈ indices, (pieces i).indicator (fun _ => (1 : ENNReal)) x) =
      (pointMultiplicity indices pieces x : ENNReal) := by
  classical
  simp [pointMultiplicity, Set.indicator]

/-- A finite measurable family with piece measure at least `area`, contained
in `target`, and point multiplicity at most `M`, satisfies
`#family * area <= M * measure target`.

The target need not be measurable: the final indicator integral inequality
holds for arbitrary sets. -/
theorem card_mul_pieceMeasure_le_multiplicity_mul_targetMeasure
    {alpha index : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (indices : Finset index)
    (pieces : index -> Set alpha) (target : Set alpha)
    {area : ENNReal} (M : Nat)
    (hmeasurable : forall i, i ∈ indices -> MeasurableSet (pieces i))
    (harea : forall i, i ∈ indices -> area <= mu (pieces i))
    (hsubset : forall i, i ∈ indices -> pieces i ⊆ target)
    (hmultiplicity : forall x, x ∈ target ->
      pointMultiplicity indices pieces x <= M) :
    (indices.card : ENNReal) * area <= (M : ENNReal) * mu target := by
  classical
  have hindicatorMeasurable : forall i, i ∈ indices ->
      Measurable ((pieces i).indicator (fun _ => (1 : ENNReal))) := by
    intro i hi
    exact measurable_const.indicator (hmeasurable i hi)
  have hpointwise : forall x,
      (∑ i ∈ indices,
        (pieces i).indicator (fun _ => (1 : ENNReal)) x) <=
      target.indicator (fun _ => (M : ENNReal)) x := by
    intro x
    by_cases hx : x ∈ target
    · rw [sum_indicator_one_eq_pointMultiplicity]
      simp only [Set.indicator, hx, if_true]
      exact_mod_cast hmultiplicity x hx
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
    _ <= ∫⁻ x, target.indicator (fun _ => (M : ENNReal)) x ∂mu := by
      exact lintegral_mono hpointwise
    _ <= (M : ENNReal) * mu target :=
      lintegral_indicator_const_le target (M : ENNReal)

#print axioms sum_indicator_one_eq_pointMultiplicity
#print axioms card_mul_pieceMeasure_le_multiplicity_mul_targetMeasure

end

end FamilyStickyCinematicL32FiniteMeasureMultiplicityV1
