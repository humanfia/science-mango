import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteENNRealFiberFubiniV3

open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# Finite ENNReal weights regrouped by a literal finite fibre

This is the elementary Fubini identity needed before a geometric degree
estimate. It keeps the exact fibre multiplicities rather than replacing them
by the cardinality of the ambient family. V1 and V2 were failed proof/linter
drafts and are not imported.
-/

/-- A finite weighted sum is the sum of its exact label-fibre cardinalities
times the corresponding label weight. -/
theorem finiteENNRealWeight_eq_sum_card_filter_mul
    {alpha : Type u} {beta : Type v} [DecidableEq alpha] [DecidableEq beta]
    (items : Finset alpha) (labels : Finset beta) (labelAt : alpha -> beta)
    (weight : beta -> ENNReal)
    (hlabel : forall a, a ∈ items -> labelAt a ∈ labels) :
    finiteENNRealWeight items (fun a => weight (labelAt a)) =
      ∑ b ∈ labels,
        ((items.filter fun a => labelAt a = b).card : ENNReal) * weight b := by
  classical
  unfold finiteENNRealWeight
  calc
    (∑ a ∈ items, weight (labelAt a)) =
        ∑ a ∈ items,
          ∑ b ∈ labels, if labelAt a = b then weight b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [eq_comm, Finset.sum_ite_eq', hlabel a ha, if_true]
    _ = ∑ b ∈ labels,
        ∑ a ∈ items, if labelAt a = b then weight b else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ labels,
        ((items.filter fun a => labelAt a = b).card : ENNReal) * weight b := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [← Finset.sum_filter]
      simp

#print axioms finiteENNRealWeight_eq_sum_card_filter_mul

end

end FamilyStickyCinematicL32FiniteENNRealFiberFubiniV3
