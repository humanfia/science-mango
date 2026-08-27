import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ENNRealSeventyTwoWeightedRetentionV1

noncomputable section

universe u v w x

/-!
# Package-free weighted retention with the honest factor 72

This module composes the three losses used by the actual Family 7
construction:

* random sampling retains one eighth of the original mass;
* the staggered C-grid loses a factor at most three;
* the trace-shift fibre loses a factor at most three.

All masses take values in `ENNReal`.  In particular, none of the statements
assumes that a mass is finite, and the proofs do not pass through `toReal`.
The small sum-transport lemmas below make the same algebra usable when one or
more stages are represented by attached or nested subtypes.
-/

/-- The algebraic `8 * 3 * 3 = 72` retention core for extended-real mass.

The hypotheses themselves force every necessary comparison in the
infinite-mass case; no `≠ ∞` premise on any of the four masses is needed. -/
theorem ennreal_le_seventyTwo_mul_of_eighth_three_three
    (total sampled grid final : ENNReal)
    (hsampling : total / 8 <= sampled)
    (hgrid : sampled <= 3 * grid)
    (htrace : grid <= 3 * final) :
    total <= 72 * final := by
  have hsampling' : total <= sampled * 8 :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp hsampling
  calc
    total <= sampled * 8 := hsampling'
    _ <= (3 * grid) * 8 := by
      gcongr
    _ <= (3 * (3 * final)) * 8 := by
      gcongr
    _ = 72 * final := by ring

/-- The form used when the grid and trace choices have already been combined
into a factor-nine estimate. -/
theorem ennreal_le_seventyTwo_mul_of_eighth_nine
    (total sampled final : ENNReal)
    (hsampling : total / 8 <= sampled)
    (hnine : sampled <= 9 * final) :
    total <= 72 * final := by
  have hsampling' : total <= sampled * 8 :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp hsampling
  calc
    total <= sampled * 8 := hsampling'
    _ <= (9 * final) * 8 := by
      gcongr
    _ = 72 * final := by ring

/-- Pulling a weight back along a label map on an attached subtype does not
change its finite sum.  This is the standard bridge from a literal label
finset to the corresponding survivor subtype. -/
theorem sum_subtype_univ_labelWeight_eq_finset
    {alpha : Type u} [DecidableEq alpha]
    {label : Type v}
    (items : Finset alpha) (labelAt : alpha -> label)
    (labelWeight : label -> ENNReal) :
    (∑ a : {a // a ∈ items}, labelWeight (labelAt a.1)) =
      ∑ a ∈ items, labelWeight (labelAt a) := by
  exact Finset.sum_attach items (fun a => labelWeight (labelAt a))

/-- Explicit two-level version of `sum_subtype_univ_labelWeight_eq_finset`.
It rewrites the sum over a subtype attached to a finset whose elements are
themselves attached to an outer finset. -/
theorem sum_nestedSubtype_univ_labelWeight_eq_finset
    {alpha : Type u} [DecidableEq alpha]
    {label : Type v}
    (outer : Finset alpha)
    (inner : Finset {a // a ∈ outer})
    (labelAt : alpha -> label) (labelWeight : label -> ENNReal) :
    (∑ a : {a // a ∈ inner}, labelWeight (labelAt a.1.1)) =
      ∑ a ∈ inner, labelWeight (labelAt a.1) := by
  exact Finset.sum_attach inner (fun a => labelWeight (labelAt a.1))

/-- Label-pulled finite sums on possibly different carrier types satisfy the
same factor-72 conclusion.  This version is convenient when grid or trace
selection is represented by a nested subtype rather than a subfinset of the
sample carrier. -/
theorem finsetLabelWeight_le_seventyTwo_mul_of_eighth_three_three
    {label : Type u} [DecidableEq label]
    {sampleItem : Type v} [DecidableEq sampleItem]
    {gridItem : Type w} [DecidableEq gridItem]
    {finalItem : Type x} [DecidableEq finalItem]
    (sourceLabels : Finset label)
    (sampleItems : Finset sampleItem)
    (gridItems : Finset gridItem)
    (finalItems : Finset finalItem)
    (labelWeight : label -> ENNReal)
    (sampleLabel : sampleItem -> label)
    (gridLabel : gridItem -> label)
    (finalLabel : finalItem -> label)
    (hsampling :
      (∑ r ∈ sourceLabels, labelWeight r) / 8 <=
        ∑ a ∈ sampleItems, labelWeight (sampleLabel a))
    (hgrid :
      (∑ a ∈ sampleItems, labelWeight (sampleLabel a)) <=
        3 * ∑ a ∈ gridItems, labelWeight (gridLabel a))
    (htrace :
      (∑ a ∈ gridItems, labelWeight (gridLabel a)) <=
        3 * ∑ a ∈ finalItems, labelWeight (finalLabel a)) :
    (∑ r ∈ sourceLabels, labelWeight r) <=
      72 * ∑ a ∈ finalItems, labelWeight (finalLabel a) := by
  exact ennreal_le_seventyTwo_mul_of_eighth_three_three
    (∑ r ∈ sourceLabels, labelWeight r)
    (∑ a ∈ sampleItems, labelWeight (sampleLabel a))
    (∑ a ∈ gridItems, labelWeight (gridLabel a))
    (∑ a ∈ finalItems, labelWeight (finalLabel a))
    hsampling hgrid htrace

/-- Actual-ready form: the sampled carrier is a finite type and the later
stages are literal finsets of that same type. -/
theorem fintypeLabelWeight_le_seventyTwo_mul_of_eighth_three_three
    {label : Type u} [DecidableEq label]
    {item : Type v} [Fintype item] [DecidableEq item]
    (sourceLabels : Finset label)
    (gridItems finalItems : Finset item)
    (labelWeight : label -> ENNReal) (labelAt : item -> label)
    (hsampling :
      (∑ r ∈ sourceLabels, labelWeight r) / 8 <=
        ∑ a : item, labelWeight (labelAt a))
    (hgrid :
      (∑ a : item, labelWeight (labelAt a)) <=
        3 * ∑ a ∈ gridItems, labelWeight (labelAt a))
    (htrace :
      (∑ a ∈ gridItems, labelWeight (labelAt a)) <=
        3 * ∑ a ∈ finalItems, labelWeight (labelAt a)) :
    (∑ r ∈ sourceLabels, labelWeight r) <=
      72 * ∑ a ∈ finalItems, labelWeight (labelAt a) := by
  exact ennreal_le_seventyTwo_mul_of_eighth_three_three
    (∑ r ∈ sourceLabels, labelWeight r)
    (∑ a : item, labelWeight (labelAt a))
    (∑ a ∈ gridItems, labelWeight (labelAt a))
    (∑ a ∈ finalItems, labelWeight (labelAt a))
    hsampling hgrid htrace

/-- Actual-ready corollary for an already-combined grid-plus-trace factor
nine estimate. -/
theorem fintypeLabelWeight_le_seventyTwo_mul_of_eighth_nine
    {label : Type u} [DecidableEq label]
    {item : Type v} [Fintype item] [DecidableEq item]
    (sourceLabels : Finset label) (finalItems : Finset item)
    (labelWeight : label -> ENNReal) (labelAt : item -> label)
    (hsampling :
      (∑ r ∈ sourceLabels, labelWeight r) / 8 <=
        ∑ a : item, labelWeight (labelAt a))
    (hnine :
      (∑ a : item, labelWeight (labelAt a)) <=
        9 * ∑ a ∈ finalItems, labelWeight (labelAt a)) :
    (∑ r ∈ sourceLabels, labelWeight r) <=
      72 * ∑ a ∈ finalItems, labelWeight (labelAt a) := by
  exact ennreal_le_seventyTwo_mul_of_eighth_nine
    (∑ r ∈ sourceLabels, labelWeight r)
    (∑ a : item, labelWeight (labelAt a))
    (∑ a ∈ finalItems, labelWeight (labelAt a))
    hsampling hnine

#print axioms ennreal_le_seventyTwo_mul_of_eighth_three_three
#print axioms ennreal_le_seventyTwo_mul_of_eighth_nine
#print axioms sum_subtype_univ_labelWeight_eq_finset
#print axioms sum_nestedSubtype_univ_labelWeight_eq_finset
#print axioms finsetLabelWeight_le_seventyTwo_mul_of_eighth_three_three
#print axioms fintypeLabelWeight_le_seventyTwo_mul_of_eighth_three_three
#print axioms fintypeLabelWeight_le_seventyTwo_mul_of_eighth_nine

end

end FamilyStickyCinematicL32Prop41ENNRealSeventyTwoWeightedRetentionV1
