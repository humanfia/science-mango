import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosThreeKindAggregationV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1.LensListEncoding

/-! Pure aggregation of the three Marcus--Tardos neighbor-list kinds. -/

theorem properLensKind_card : Fintype.card ProperLensKind = 3 := by
  decide

theorem three_kind_total_list_length_le
    {curve : Type*} [Fintype curve] [Nonempty curve] [DecidableEq curve]
    (lists : ProperLensKind → curve → DistinctCyclicSequence curve)
    (hreverse : ∀ k, PairwiseIntersectionReverse (lists k)) :
    (∑ k : ProperLensKind, ∑ c : curve,
        ((lists k c).order.length : Real)) ≤
      3 * (16 * (canonicalDepth curve : Real) *
          (Fintype.card curve : Real) *
            Real.sqrt (Fintype.card curve : Real) +
        105 * (Fintype.card curve : Real) *
          Real.sqrt (Fintype.card curve : Real)) := by
  calc
    (∑ k : ProperLensKind, ∑ c : curve,
        ((lists k c).order.length : Real)) ≤
      ∑ _k : ProperLensKind,
        (16 * (canonicalDepth curve : Real) *
            (Fintype.card curve : Real) *
              Real.sqrt (Fintype.card curve : Real) +
          105 * (Fintype.card curve : Real) *
            Real.sqrt (Fintype.card curve : Real)) := by
      exact Finset.sum_le_sum fun k hk ↦
        nonuniform_total_length_canonicalDepth (lists k) (hreverse k)
    _ = 3 * (16 * (canonicalDepth curve : Real) *
          (Fintype.card curve : Real) *
            Real.sqrt (Fintype.card curve : Real) +
        105 * (Fintype.card curve : Real) *
          Real.sqrt (Fintype.card curve : Real)) := by
      simp [properLensKind_card]
      ring

theorem lensListEncoding_card_le_explicit
    {curve lens : Type*} [Fintype curve] [Nonempty curve]
    [DecidableEq curve] [Fintype lens]
    (E : LensListEncoding curve lens)
    (hreverse : E.ListsPairwiseIntersectionReverse) :
    (Fintype.card lens : Real) ≤ (Fintype.card curve : Real) +
      3 * (16 * (canonicalDepth curve : Real) *
          (Fintype.card curve : Real) *
            Real.sqrt (Fintype.card curve : Real) +
        105 * (Fintype.card curve : Real) *
          Real.sqrt (Fintype.card curve : Real)) := by
  have hcardNat := E.card_lens_le_curve_add_sum_list_length
  have hcardReal : (Fintype.card lens : Real) ≤
      (Fintype.card curve : Real) +
        ∑ k : ProperLensKind, ∑ c : curve,
          ((E.lists k c).order.length : Real) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans (add_le_add_right
    (three_kind_total_list_length_le E.lists hreverse) _)

#print axioms properLensKind_card
#print axioms three_kind_total_list_length_le
#print axioms lensListEncoding_card_le_explicit

end FamilyStickyCinematicL32Prop41MarcusTardosThreeKindAggregationV1
