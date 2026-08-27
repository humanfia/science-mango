import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
import Mathlib.Data.ENNReal.Basic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairENNRealSelectionV1

open scoped BigOperators ENNReal

open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

noncomputable section

/-!
# ENNReal-weighted finite selection of a rich separated pair

The existing selector is real-valued.  This companion keeps infinite masses
honest and supplies the denominator-free form used by first-hit volume
weights.
-/

/-- Total `ENNReal` weight of all admissible ordered centre pairs. -/
noncomputable def richSeparatedPairENNRealWeightTotal {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> ENNReal) : ENNReal := by
  classical
  exact ∑ pair ∈ richSeparatedCenterPairs centers separated goodPair,
    pairWeight pair.1 pair.2

/-- One admissible pair carries the total `ENNReal` weight up to the exact
number of admissible pairs.  No finiteness assumption on the weights is
needed. -/
theorem exists_richSeparated_pair_totalENNRealWeight_le_card_mul
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> ENNReal)
    (hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          richSeparatedPairENNRealWeightTotal centers separated goodPair
              pairWeight <=
            ((richSeparatedCenterPairs centers separated goodPair).card :
                ENNReal) * pairWeight left right := by
  classical
  let pairs := richSeparatedCenterPairs centers separated goodPair
  rcases Finset.exists_max_image pairs
      (fun pair => pairWeight pair.1 pair.2) hpairs with
    ⟨pair, hpair, hmax⟩
  have hsum :
      richSeparatedPairENNRealWeightTotal centers separated goodPair
          pairWeight <=
        (pairs.card : ENNReal) * pairWeight pair.1 pair.2 := by
    have hsum' := Finset.sum_le_card_nsmul pairs
      (fun candidate => pairWeight candidate.1 candidate.2)
      (pairWeight pair.1 pair.2) hmax
    simpa only [richSeparatedPairENNRealWeightTotal, pairs,
      nsmul_eq_mul] using hsum'
  have hpairData :=
    (mem_richSeparatedCenterPairs_iff (left := pair.1)
      (right := pair.2)).mp hpair
  exact ⟨pair.1, hpairData.1, pair.2, hpairData.2.1,
    hpairData.2.2.1, hpairData.2.2.2, by simpa only [pairs] using hsum⟩

/-- A positive weighted lower bound also certifies that the admissible pair
carrier is nonempty. -/
theorem exists_richSeparated_pair_of_pos_totalENNRealWeight_lower
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> ENNReal)
    {lowerBound : ENNReal} (hlowerBound : 0 < lowerBound)
    (htotal : lowerBound <=
      richSeparatedPairENNRealWeightTotal centers separated goodPair
        pairWeight) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          lowerBound <=
            ((richSeparatedCenterPairs centers separated goodPair).card :
                ENNReal) * pairWeight left right := by
  classical
  have hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty := by
    by_contra hpairs
    have hpairsEmpty :
        richSeparatedCenterPairs centers separated goodPair = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hpairs
    have hlowerBoundZero : lowerBound <= 0 := by
      simpa [richSeparatedPairENNRealWeightTotal, hpairsEmpty] using htotal
    exact (not_le_of_gt hlowerBound) hlowerBoundZero
  obtain ⟨left, hleft, right, hright, hseparated, hgood, hselected⟩ :=
    exists_richSeparated_pair_totalENNRealWeight_le_card_mul
      centers separated goodPair pairWeight hpairs
  exact ⟨left, hleft, right, hright, hseparated, hgood,
    htotal.trans hselected⟩

#print axioms richSeparatedPairENNRealWeightTotal
#print axioms exists_richSeparated_pair_totalENNRealWeight_le_card_mul
#print axioms exists_richSeparated_pair_of_pos_totalENNRealWeight_lower

end

end FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairENNRealSelectionV1
