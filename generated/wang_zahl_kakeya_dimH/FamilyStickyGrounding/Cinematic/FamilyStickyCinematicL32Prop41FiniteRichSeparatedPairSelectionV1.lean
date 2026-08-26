import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

open scoped BigOperators

noncomputable section

/-!
# Finite selection of a rich separated pair

This is the purely combinatorial averaging step needed before an application
of PYZ Proposition 4.1.  Both geometric inputs are explicit predicates:
`separated` records the required separation of two centres, while `goodPair`
records any additional incidence or richness condition already proved by a
caller.  The lemmas below only select a pair from the resulting finite set.

In particular, this module does not construct coarse rectangles, prove that
two metric balls are rich, or manufacture the global pair-mass lower bound.
-/

/-- Ordered centre pairs satisfying both the supplied separation and good-pair
predicates. -/
noncomputable def richSeparatedCenterPairs {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop) : Finset (center × center) := by
  classical
  exact (centers.product centers).filter fun pair =>
    separated pair.1 pair.2 ∧ goodPair pair.1 pair.2

@[simp]
theorem mem_richSeparatedCenterPairs_iff {center : Type*}
    {centers : Finset center}
    {separated goodPair : center -> center -> Prop}
    {left right : center} :
    (left, right) ∈ richSeparatedCenterPairs centers separated goodPair ↔
      left ∈ centers ∧ right ∈ centers ∧
        separated left right ∧ goodPair left right := by
  classical
  simp [richSeparatedCenterPairs, and_assoc]

/-- The admissible ordered-pair count never exceeds the square of the centre
count. -/
theorem richSeparatedCenterPairs_card_le_sq {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop) :
    (richSeparatedCenterPairs centers separated goodPair).card <=
      centers.card * centers.card := by
  classical
  exact (Finset.card_filter_le (centers.product centers)
    (fun pair : center × center =>
      separated pair.1 pair.2 ∧ goodPair pair.1 pair.2)).trans_eq
        (Finset.card_product centers centers)

/-- Sum of an arbitrary real mass over all rich separated ordered pairs. -/
noncomputable def richSeparatedPairWeightTotal {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> Real) : Real := by
  classical
  exact ∑ pair ∈ richSeparatedCenterPairs centers separated goodPair,
    pairWeight pair.1 pair.2

/-- Exact denominator-free finite averaging: one admissible pair carries at
least total pair weight divided by the number of admissible pairs. -/
theorem exists_richSeparated_pair_totalWeight_le_card_mul
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> Real)
    (hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          richSeparatedPairWeightTotal centers separated goodPair pairWeight <=
            ((richSeparatedCenterPairs centers separated goodPair).card : Real) *
              pairWeight left right := by
  classical
  let pairs := richSeparatedCenterPairs centers separated goodPair
  rcases Finset.exists_max_image pairs
      (fun pair => pairWeight pair.1 pair.2) hpairs with
    ⟨pair, hpair, hmax⟩
  have hsum :
      richSeparatedPairWeightTotal centers separated goodPair pairWeight <=
        (pairs.card : Real) * pairWeight pair.1 pair.2 := by
    have hsum' := Finset.sum_le_card_nsmul pairs
      (fun candidate => pairWeight candidate.1 candidate.2)
      (pairWeight pair.1 pair.2) hmax
    simpa only [richSeparatedPairWeightTotal, pairs, nsmul_eq_mul] using hsum'
  have hpairData :=
    (mem_richSeparatedCenterPairs_iff (left := pair.1)
      (right := pair.2)).mp hpair
  exact ⟨pair.1, hpairData.1, pair.2, hpairData.2.1,
    hpairData.2.2.1, hpairData.2.2.2, by simpa only [pairs] using hsum⟩

/-- Division-form version of finite averaging for real pair weights. -/
theorem exists_richSeparated_pair_weight_ge_average
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> Real)
    (hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          richSeparatedPairWeightTotal centers separated goodPair pairWeight /
              (richSeparatedCenterPairs centers separated goodPair).card <=
            pairWeight left right := by
  classical
  rcases exists_richSeparated_pair_totalWeight_le_card_mul
      centers separated goodPair pairWeight hpairs with
    ⟨left, hleft, right, hright, hseparated, hgood, htotal⟩
  have hcardNat :
      0 < (richSeparatedCenterPairs centers separated goodPair).card :=
    Finset.card_pos.mpr hpairs
  have hcardReal :
      (0 : Real) < (richSeparatedCenterPairs centers separated goodPair).card := by
    exact_mod_cast hcardNat
  refine ⟨left, hleft, right, hright, hseparated, hgood, ?_⟩
  exact (div_le_iff₀ hcardReal).2 (by simpa [mul_comm] using htotal)

/-- A supplied lower bound for the global admissible pair mass transfers to
the selected pair, with exactly the admissible-pair cardinality loss. -/
theorem exists_richSeparated_pair_of_totalWeight_lower
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> Real)
    {lowerBound : Real}
    (hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty)
    (htotal : lowerBound <=
      richSeparatedPairWeightTotal centers separated goodPair pairWeight) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          lowerBound <=
            ((richSeparatedCenterPairs centers separated goodPair).card : Real) *
              pairWeight left right := by
  rcases exists_richSeparated_pair_totalWeight_le_card_mul
      centers separated goodPair pairWeight hpairs with
    ⟨left, hleft, right, hright, hseparated, hgood, hselected⟩
  exact ⟨left, hleft, right, hright, hseparated, hgood,
    htotal.trans hselected⟩

/-- A positive global pair-mass lower bound itself certifies that the
admissible pair set is nonempty, so no separate existence input is needed. -/
theorem exists_richSeparated_pair_of_pos_totalWeight_lower
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairWeight : center -> center -> Real)
    {lowerBound : Real} (hlowerBound : 0 < lowerBound)
    (htotal : lowerBound <=
      richSeparatedPairWeightTotal centers separated goodPair pairWeight) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          lowerBound <=
            ((richSeparatedCenterPairs centers separated goodPair).card : Real) *
              pairWeight left right := by
  classical
  have hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty := by
    by_contra hpairs
    have hpairsEmpty :
        richSeparatedCenterPairs centers separated goodPair = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hpairs
    have hlowerBoundZero : lowerBound <= 0 := by
      simpa [richSeparatedPairWeightTotal, hpairsEmpty] using htotal
    exact (not_le_of_gt hlowerBound) hlowerBoundZero
  exact exists_richSeparated_pair_of_totalWeight_lower
    centers separated goodPair pairWeight hpairs htotal

/-- Sum of an arbitrary natural-number count over the admissible ordered
pairs.  This is useful when the mass is literally an incidence count. -/
noncomputable def richSeparatedPairCountTotal {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairCount : center -> center -> Nat) : Nat := by
  classical
  exact ∑ pair ∈ richSeparatedCenterPairs centers separated goodPair,
    pairCount pair.1 pair.2

/-- Natural-number version of the denominator-free average selection. -/
theorem exists_richSeparated_pair_totalCount_le_card_mul
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairCount : center -> center -> Nat)
    (hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          richSeparatedPairCountTotal centers separated goodPair pairCount <=
            (richSeparatedCenterPairs centers separated goodPair).card *
              pairCount left right := by
  classical
  let pairs := richSeparatedCenterPairs centers separated goodPair
  rcases Finset.exists_max_image pairs
      (fun pair => pairCount pair.1 pair.2) hpairs with
    ⟨pair, hpair, hmax⟩
  have hsum :
      richSeparatedPairCountTotal centers separated goodPair pairCount <=
        pairs.card * pairCount pair.1 pair.2 := by
    have hsum' := Finset.sum_le_card_nsmul pairs
      (fun candidate => pairCount candidate.1 candidate.2)
      (pairCount pair.1 pair.2) hmax
    simpa only [richSeparatedPairCountTotal, pairs, Nat.nsmul_eq_mul] using hsum'
  have hpairData :=
    (mem_richSeparatedCenterPairs_iff (left := pair.1)
      (right := pair.2)).mp hpair
  exact ⟨pair.1, hpairData.1, pair.2, hpairData.2.1,
    hpairData.2.2.1, hpairData.2.2.2, by simpa only [pairs] using hsum⟩

/-- A positive lower bound for the total admissible incidence count selects a
pair attaining the corresponding denominator-free average. -/
theorem exists_richSeparated_pair_of_pos_totalCount_lower
    {center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (pairCount : center -> center -> Nat)
    {lowerBound : Nat} (hlowerBound : 0 < lowerBound)
    (htotal : lowerBound <=
      richSeparatedPairCountTotal centers separated goodPair pairCount) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          lowerBound <=
            (richSeparatedCenterPairs centers separated goodPair).card *
              pairCount left right := by
  classical
  have hpairs :
      (richSeparatedCenterPairs centers separated goodPair).Nonempty := by
    by_contra hpairs
    have hpairsEmpty :
        richSeparatedCenterPairs centers separated goodPair = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hpairs
    have hlowerBoundZero : lowerBound <= 0 := by
      simpa [richSeparatedPairCountTotal, hpairsEmpty] using htotal
    exact (Nat.not_succ_le_zero 0) ((Nat.succ_le_iff).mpr
      (hlowerBound.trans_le hlowerBoundZero))
  rcases exists_richSeparated_pair_totalCount_le_card_mul
      centers separated goodPair pairCount hpairs with
    ⟨left, hleft, right, hright, hseparated, hgood, hselected⟩
  exact ⟨left, hleft, right, hright, hseparated, hgood,
    htotal.trans hselected⟩

/-- The finite items incident to one centre under an arbitrary incidence
predicate. -/
noncomputable def centerIncidenceFiber {item center : Type*}
    (items : Finset item) (incident : item -> center -> Prop)
    (selectedCenter : center) : Finset item := by
  classical
  exact items.filter fun item => incident item selectedCenter

@[simp]
theorem mem_centerIncidenceFiber_iff {item center : Type*}
    {items : Finset item} {incident : item -> center -> Prop}
    {selectedCenter : center} {x : item} :
    x ∈ centerIncidenceFiber items incident selectedCenter ↔
      x ∈ items ∧ incident x selectedCenter := by
  classical
  simp [centerIncidenceFiber]

/-- Product of the two incidence-fiber cardinalities at an ordered pair of
centres. -/
noncomputable def centerCrossIncidenceCount
    {leftItem rightItem center : Type*}
    (leftItems : Finset leftItem) (rightItems : Finset rightItem)
    (leftIncident : leftItem -> center -> Prop)
    (rightIncident : rightItem -> center -> Prop)
    (left right : center) : Nat :=
  (centerIncidenceFiber leftItems leftIncident left).card *
    (centerIncidenceFiber rightItems rightIncident right).card

/-- Global cross-incidence count over all rich separated ordered pairs. -/
noncomputable def richSeparatedCrossIncidenceTotal
    {leftItem rightItem center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (leftItems : Finset leftItem) (rightItems : Finset rightItem)
    (leftIncident : leftItem -> center -> Prop)
    (rightIncident : rightItem -> center -> Prop) : Nat :=
  richSeparatedPairCountTotal centers separated goodPair
    (centerCrossIncidenceCount leftItems rightItems
      leftIncident rightIncident)

/-- Main incidence specialization: a positive global cross-incidence lower
bound selects two admissible centres whose product of incidence counts reaches
the exact denominator-free average. -/
theorem exists_richSeparated_pair_of_pos_crossIncidence_lower
    {leftItem rightItem center : Type*}
    (centers : Finset center)
    (separated goodPair : center -> center -> Prop)
    (leftItems : Finset leftItem) (rightItems : Finset rightItem)
    (leftIncident : leftItem -> center -> Prop)
    (rightIncident : rightItem -> center -> Prop)
    {lowerBound : Nat} (hlowerBound : 0 < lowerBound)
    (htotal : lowerBound <=
      richSeparatedCrossIncidenceTotal centers separated goodPair
        leftItems rightItems leftIncident rightIncident) :
    exists left, left ∈ centers ∧
      exists right, right ∈ centers ∧
        separated left right ∧ goodPair left right ∧
          lowerBound <=
            (richSeparatedCenterPairs centers separated goodPair).card *
              centerCrossIncidenceCount leftItems rightItems
                leftIncident rightIncident left right := by
  exact exists_richSeparated_pair_of_pos_totalCount_lower
    centers separated goodPair
      (centerCrossIncidenceCount leftItems rightItems
        leftIncident rightIncident)
      hlowerBound htotal

#print axioms richSeparatedCenterPairs
#print axioms mem_richSeparatedCenterPairs_iff
#print axioms richSeparatedCenterPairs_card_le_sq
#print axioms richSeparatedPairWeightTotal
#print axioms exists_richSeparated_pair_totalWeight_le_card_mul
#print axioms exists_richSeparated_pair_weight_ge_average
#print axioms exists_richSeparated_pair_of_totalWeight_lower
#print axioms exists_richSeparated_pair_of_pos_totalWeight_lower
#print axioms richSeparatedPairCountTotal
#print axioms exists_richSeparated_pair_totalCount_le_card_mul
#print axioms exists_richSeparated_pair_of_pos_totalCount_lower
#print axioms centerIncidenceFiber
#print axioms mem_centerIncidenceFiber_iff
#print axioms centerCrossIncidenceCount
#print axioms richSeparatedCrossIncidenceTotal
#print axioms exists_richSeparated_pair_of_pos_crossIncidence_lower

end

end FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
