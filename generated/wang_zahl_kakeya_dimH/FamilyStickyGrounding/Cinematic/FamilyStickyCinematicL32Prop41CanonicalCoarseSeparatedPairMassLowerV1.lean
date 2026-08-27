import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1

open scoped BigOperators

noncomputable section

universe u v w

/-!
# Producing the actual separated-pair mass lower bound

For a coarse rectangle `R`, the paper first counts all ordered pairs in
`F(R)²` and then subtracts pairs whose centres are closer than `10r`.
This file formalizes that subtraction and the subsequent `G'` double count.

The inputs retained by the final theorem are source-level quantities:

* a selected coarse subfamily and a lower bound for its retained `G'` mass;
* the upper half of the paper's `q`-uniform coarse degree window;
* a lower richness bound for every selected coarse fibre;
* the scalar inequality making the canonical `10r` ball contain at most
  `nearCap` centres.

No separated-pair total, rich pair, or synonym of either is accepted as an
input.  The explicit loss is `richness - nearCap`; if `nearCap >= richness`,
the construction honestly gives only the zero lower bound.
-/

/-- The part of the literal coarse fibre lying in the canonical norm family.
This intersection is needed because the global pair total only sums centres
from `N.family`. -/
noncomputable def canonicalCoarseActiveFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    Finset iota :=
  D.coarseCurveIndexFiber keep R ∩ N.family

/-- Ordered `10r`-separated centre pairs inside one active coarse fibre. -/
noncomputable def canonicalCoarseSeparatedPairsAt
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle) : Finset (iota × iota) := by
  classical
  exact ((canonicalCoarseActiveFiber N D keep R) ×ˢ
    (canonicalCoarseActiveFiber N D keep R)).filter fun pair =>
      canonicalTenRadiusSeparated N ballRadius pair.1 pair.2

/-- The non-separated right endpoints in one active coarse fibre, for a
fixed left endpoint. -/
noncomputable def canonicalCoarseNearRightFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle) (left : iota) : Finset iota := by
  classical
  exact (canonicalCoarseActiveFiber N D keep R).filter fun right =>
    ¬canonicalTenRadiusSeparated N ballRadius left right

/-- All non-separated ordered pairs in one active coarse fibre. -/
noncomputable def canonicalCoarseNearPairsAt
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle) : Finset (iota × iota) := by
  classical
  exact ((canonicalCoarseActiveFiber N D keep R) ×ˢ
    (canonicalCoarseActiveFiber N D keep R)).filter fun pair =>
      ¬canonicalTenRadiusSeparated N ballRadius pair.1 pair.2

/-- The retained `G'` incidences assigned to a selected coarse subfamily. -/
noncomputable def retainedGoodPairsOver
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle) : Finset (iota × fineLabel) := by
  classical
  exact (D.retainedGoodPairs keep).filter fun pair =>
    D.coarseRectangleAt pair.2 ∈ rectangles

@[simp]
theorem mem_retainedGoodPairsOver_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle) {pair : iota × fineLabel} :
    pair ∈ retainedGoodPairsOver D keep rectangles <->
      pair ∈ D.retainedGoodPairs keep ∧
        D.coarseRectangleAt pair.2 ∈ rectangles := by
  classical
  simp [retainedGoodPairsOver]

/-- Exact partition of the selected retained `G'` mass by coarse rectangle. -/
theorem retainedGoodPairsOver_card_eq_sum_coarseIncidencePairs
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle) :
    (retainedGoodPairsOver D keep rectangles).card =
      ∑ R ∈ rectangles, (D.coarseIncidencePairs keep R).card := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := retainedGoodPairsOver D keep rectangles)
    (t := rectangles) (f := fun pair => D.coarseRectangleAt pair.2)
    (fun pair hpair =>
      ((mem_retainedGoodPairsOver_iff D keep rectangles).mp hpair).2)
  calc
    (retainedGoodPairsOver D keep rectangles).card =
        ∑ R ∈ rectangles,
          ((retainedGoodPairsOver D keep rectangles).filter fun pair =>
            D.coarseRectangleAt pair.2 = R).card := hpartition
    _ = ∑ R ∈ rectangles, (D.coarseIncidencePairs keep R).card := by
      apply Finset.sum_congr rfl
      intro R hR
      congr 1
      ext pair
      simp only [Finset.mem_filter, mem_retainedGoodPairsOver_iff,
        D.mem_coarseIncidencePairs_iff, D.mem_retainedGoodPairs_iff]
      constructor
      · rintro ⟨⟨hgood, _hselected⟩, hcoarse⟩
        exact ⟨hgood.1, hgood.2, hcoarse⟩
      · rintro ⟨hgood, hkeep, hcoarse⟩
        exact ⟨⟨⟨hgood, hkeep⟩, by simpa [hcoarse] using hR⟩, hcoarse⟩

/-- The global canonical total is exactly the sum, over all literal coarse
rectangles, of separated ordered-pair counts in their active fibres.  This is
the central Fubini identity; the `CoarseGoodPair` filter does not lose mass,
because an empty common fibre contributes cardinality zero. -/
theorem canonicalCoarseRichSeparatedPairCountTotal_eq_sum_separatedPairsAt
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real) :
    canonicalCoarseRichSeparatedPairCountTotal N D keep ballRadius =
      ∑ R ∈ D.coarseRectangleFamily,
        (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card := by
  classical
  simp only [canonicalCoarseRichSeparatedPairCountTotal,
    richSeparatedPairCountTotal, richSeparatedCenterPairs,
    Finset.sum_filter]
  calc
    (∑ pair ∈ N.family.product N.family,
        if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
            D.CoarseGoodPair keep pair.1 pair.2 then
          D.coarseCrossIncidenceCount keep pair.1 pair.2 else 0) =
      ∑ pair ∈ N.family.product N.family,
        if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 then
          D.coarseCrossIncidenceCount keep pair.1 pair.2 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      by_cases hseparated :
          canonicalTenRadiusSeparated N ballRadius pair.1 pair.2
      · by_cases hcommon :
          (D.commonCoarseRectangleFiber keep pair.1 pair.2).Nonempty
        · have hgood : D.CoarseGoodPair keep pair.1 pair.2 := hcommon
          simp [hseparated, hgood]
        · have hempty :
            D.commonCoarseRectangleFiber keep pair.1 pair.2 = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hcommon
          simp only [hseparated, true_and,
            CoarseRectangleIncidenceData.CoarseGoodPair,
            CoarseRectangleIncidenceData.coarseCrossIncidenceCount,
            hempty, Finset.not_nonempty_empty, Finset.card_empty, if_false, if_true]
      · simp [hseparated]
    _ = ∑ pair ∈ N.family.product N.family,
        ∑ R ∈ D.coarseRectangleFamily,
          if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
              pair.1 ∈ D.coarseCurveIndexFiber keep R ∧
              pair.2 ∈ D.coarseCurveIndexFiber keep R then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      by_cases hseparated :
          canonicalTenRadiusSeparated N ballRadius pair.1 pair.2
      · simp only [hseparated, if_true,
          CoarseRectangleIncidenceData.coarseCrossIncidenceCount,
          CoarseRectangleIncidenceData.commonCoarseRectangleFiber]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        simp only [true_and]
      · simp [hseparated]
    _ = ∑ R ∈ D.coarseRectangleFamily,
        ∑ pair ∈ N.family.product N.family,
          if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
              pair.1 ∈ D.coarseCurveIndexFiber keep R ∧
              pair.2 ∈ D.coarseCurveIndexFiber keep R then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ R ∈ D.coarseRectangleFamily,
        (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [Finset.card_eq_sum_ones]
      simp only [canonicalCoarseSeparatedPairsAt, Finset.sum_filter]
      symm
      have hactiveSubset : canonicalCoarseActiveFiber N D keep R ⊆ N.family := by
        exact Finset.inter_subset_right
      apply Finset.sum_subset_zero_on_sdiff
        (Finset.product_subset_product hactiveSubset hactiveSubset)
      · intro pair hpair
        have hpairData := Finset.mem_sdiff.mp hpair
        have hnotActive :
            ¬(pair.1 ∈ canonicalCoarseActiveFiber N D keep R ∧
              pair.2 ∈ canonicalCoarseActiveFiber N D keep R) := by
          intro hactive
          exact hpairData.2 (Finset.mem_product.mpr hactive)
        have hnotCoarse :
            ¬(pair.1 ∈ D.coarseCurveIndexFiber keep R ∧
              pair.2 ∈ D.coarseCurveIndexFiber keep R) := by
          intro hcoarse
          have hN := Finset.mem_product.mp hpairData.1
          exact hnotActive ⟨Finset.mem_inter.mpr ⟨hcoarse.1, hN.1⟩,
            Finset.mem_inter.mpr ⟨hcoarse.2, hN.2⟩⟩
        simp only [hnotCoarse, and_false, if_false]
      · intro pair hpair
        have hactive := Finset.mem_product.mp hpair
        have hcoarseLeft :=
          (Finset.mem_inter.mp hactive.1).1
        have hcoarseRight :=
          (Finset.mem_inter.mp hactive.2).1
        by_cases hseparated :
            canonicalTenRadiusSeparated N ballRadius pair.1 pair.2
        · simp only [hseparated, hcoarseLeft, hcoarseRight, and_self,
            if_true]
        · simp only [hseparated, false_and, if_false]

/-- Fubini for the near pairs in one coarse fibre. -/
theorem canonicalCoarseNearPairsAt_card_eq_sum_nearRightFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle) :
    (canonicalCoarseNearPairsAt N D keep ballRadius R).card =
      ∑ left ∈ canonicalCoarseActiveFiber N D keep R,
        (canonicalCoarseNearRightFiber N D keep ballRadius R left).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  simp only [canonicalCoarseNearPairsAt, Finset.sum_filter]
  rw [Finset.sum_product (canonicalCoarseActiveFiber N D keep R)
    (canonicalCoarseActiveFiber N D keep R)
    (fun pair => if
      ¬canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 then 1 else 0)]
  apply Finset.sum_congr rfl
  intro left hleft
  change
    (∑ right ∈ canonicalCoarseActiveFiber N D keep R,
      if ¬canonicalTenRadiusSeparated N ballRadius left right then 1 else 0) =
    ((canonicalCoarseActiveFiber N D keep R).filter fun right =>
      ¬canonicalTenRadiusSeparated N ballRadius left right).card
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]

/-- A pointwise near-right cap gives the expected `#F(R) * nearCap`
upper bound for all near ordered pairs. -/
theorem canonicalCoarseNearPairsAt_card_le
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle) (nearCap : Nat)
    (hcap : forall left, left ∈ canonicalCoarseActiveFiber N D keep R ->
      (canonicalCoarseNearRightFiber N D keep ballRadius R left).card <=
        nearCap) :
    (canonicalCoarseNearPairsAt N D keep ballRadius R).card <=
      (canonicalCoarseActiveFiber N D keep R).card * nearCap := by
  rw [canonicalCoarseNearPairsAt_card_eq_sum_nearRightFiber]
  calc
    (∑ left ∈ canonicalCoarseActiveFiber N D keep R,
        (canonicalCoarseNearRightFiber N D keep ballRadius R left).card) <=
      ∑ _left ∈ canonicalCoarseActiveFiber N D keep R, nearCap :=
        Finset.sum_le_sum fun left hleft => hcap left hleft
    _ = (canonicalCoarseActiveFiber N D keep R).card * nearCap := by
      simp

/-- Separated and near pairs partition the full ordered square exactly. -/
theorem canonicalCoarseSeparated_card_add_near_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle) :
    (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card +
        (canonicalCoarseNearPairsAt N D keep ballRadius R).card =
      (canonicalCoarseActiveFiber N D keep R).card *
        (canonicalCoarseActiveFiber N D keep R).card := by
  classical
  simpa only [canonicalCoarseSeparatedPairsAt,
    canonicalCoarseNearPairsAt, Finset.card_product] using
    ((canonicalCoarseActiveFiber N D keep R) ×ˢ
      (canonicalCoarseActiveFiber N D keep R)).card_filter_add_card_filter_not
        (fun pair => canonicalTenRadiusSeparated N ballRadius pair.1 pair.2)

/-- Explicit near-pair subtraction in one coarse fibre. -/
theorem activeFiber_card_mul_tsub_nearCap_le_separatedPairsAt_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (R : C2GraphRectangle) (nearCap : Nat)
    (hcap : forall left, left ∈ canonicalCoarseActiveFiber N D keep R ->
      (canonicalCoarseNearRightFiber N D keep ballRadius R left).card <=
        nearCap) :
    (canonicalCoarseActiveFiber N D keep R).card *
        ((canonicalCoarseActiveFiber N D keep R).card - nearCap) <=
      (canonicalCoarseSeparatedPairsAt N D keep ballRadius R).card := by
  have hnear := canonicalCoarseNearPairsAt_card_le
    N D keep ballRadius R nearCap hcap
  have hpartition := canonicalCoarseSeparated_card_add_near_card
    N D keep ballRadius R
  rw [Nat.mul_sub_left_distrib]
  have hsub := Nat.sub_le_sub_left hnear
    ((canonicalCoarseActiveFiber N D keep R).card *
      (canonicalCoarseActiveFiber N D keep R).card)
  omega

#print axioms retainedGoodPairsOver_card_eq_sum_coarseIncidencePairs
#print axioms canonicalCoarseRichSeparatedPairCountTotal_eq_sum_separatedPairsAt
#print axioms canonicalCoarseNearPairsAt_card_eq_sum_nearRightFiber
#print axioms canonicalCoarseNearPairsAt_card_le
#print axioms canonicalCoarseSeparated_card_add_near_card
#print axioms activeFiber_card_mul_tsub_nearCap_le_separatedPairsAt_card

end

end FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1
