import FamilyStickyGrounding.FamilyStickyHierarchySelectedLevelZeroDescendantProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped NNReal BigOperators

namespace FamilyStickyHierarchyTerminalSourceChartBucketUnitBallNormalizedProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyHierarchySelectedLevelZeroDescendantProducerV1

noncomputable section

universe u

/-!
# Unit-ball-normalized terminal source bucket selection

The public output of the existing chart/bucket selectors remembers only that
the selected indices lie in `levelZeroSource`.  Consequently the weakest
family-wide unit-ball input that can be transported through those selectors
without changing their API is containment for the carriers indexed by that
literal source.  Requiring containment for every `Index 0` would be stronger
than necessary.

The companion theorems below call the existing selectors, keep their exact
retention facts for the same witness `S`, and add
`SelectedLevelZeroUnitBallNormalized S`.  Cardinal and weighted selection
remain separate because their maximizing buckets need not coincide.
-/

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type u}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- Unit-ball normalization on exactly the active level-zero source used by
the terminal chart/bucket selectors. -/
def LevelZeroSourceUnitBallNormalized : Prop :=
  ∀ i, i ∈ levelZeroSource (H := H) →
    ((H.effectiveFamily 0).tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1

/-- Any selected terminal geometry inherits unit-ball normalization from the
whole level-zero source, using its actual selected-subset certificate. -/
theorem selectedLevelZeroUnitBallNormalized_of_source
    (hunit : LevelZeroSourceUnitBallNormalized (H := H))
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    SelectedLevelZeroUnitBallNormalized S := by
  apply selectedLevelZeroUnitBallNormalized_of_original S
  intro i hi
  exact hunit i (S.selected_subset_source hi)

/-- The cardinal-retaining fixed-chart selector, with unit-ball
normalization added for the same selected witness. -/
theorem exists_cardinalRetaining_levelZeroChartBucket_and_unitBallNormalized
    (hdelta : 0 < H.effectiveRadius 0)
    (hchart : (levelZeroFixedVerticalChart (H := H)).Nonempty)
    (hunit : LevelZeroSourceUnitBallNormalized (H := H)) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      ((levelZeroFixedVerticalChart (H := H)).card ≤
          (levelZeroOccupiedGraphCBuckets (H := H)).card * S.selected.card ∧
        (levelZeroOccupiedGraphCBuckets (H := H)).card ≤
          graphCBucketLoss
            (((H.effectiveRadius 0 : NNReal) : Real) / 2) ∧
        (levelZeroFixedVerticalChart (H := H)).card ≤
          graphCBucketLoss
              (((H.effectiveRadius 0 : NNReal) : Real) / 2) *
            S.selected.card) ∧
      SelectedLevelZeroUnitBallNormalized S := by
  obtain ⟨S, hactual, hcount, hexplicit⟩ :=
    exists_cardinalRetaining_levelZeroChartBucket (H := H) hdelta hchart
  exact ⟨S, ⟨hactual, hcount, hexplicit⟩,
    selectedLevelZeroUnitBallNormalized_of_source hunit S⟩

/-- The cardinal-retaining whole-source selector under fixed-chart
provenance, with unit-ball normalization added for the same witness. -/
theorem exists_cardinalRetaining_levelZeroSourceBucket_and_unitBallNormalized
    (hdelta : 0 < H.effectiveRadius 0)
    (hsource : (levelZeroSource (H := H)).Nonempty)
    (hvertical : ∀ i, i ∈ levelZeroSource (H := H) →
      (1 / 2 : Real) ≤
        |((H.effectiveFamily 0).tubes i).axis.direction 2|)
    (hunit : LevelZeroSourceUnitBallNormalized (H := H)) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      ((levelZeroSource (H := H)).card ≤
          (levelZeroOccupiedGraphCBuckets (H := H)).card * S.selected.card ∧
        (levelZeroSource (H := H)).card ≤
          graphCBucketLoss
              (((H.effectiveRadius 0 : NNReal) : Real) / 2) *
            S.selected.card) ∧
      SelectedLevelZeroUnitBallNormalized S := by
  obtain ⟨S, hactual, hexplicit⟩ :=
    exists_cardinalRetaining_levelZeroSourceBucket_of_vertical_half
      (H := H) hdelta hsource hvertical
  exact ⟨S, ⟨hactual, hexplicit⟩,
    selectedLevelZeroUnitBallNormalized_of_source hunit S⟩

/-- The weight-retaining fixed-chart selector, with unit-ball normalization
added for the same selected witness. -/
theorem exists_weightRetaining_levelZeroChartBucket_and_unitBallNormalized
    (hdelta : 0 < H.effectiveRadius 0)
    (hchart : (levelZeroFixedVerticalChart (H := H)).Nonempty)
    (weight : Index 0 → NNReal)
    (hunit : LevelZeroSourceUnitBallNormalized (H := H)) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      ((∑ i ∈ levelZeroFixedVerticalChart (H := H), weight i) ≤
          (levelZeroOccupiedGraphCBuckets (H := H)).card •
            ∑ i ∈ S.selected, weight i ∧
        (∑ i ∈ levelZeroFixedVerticalChart (H := H), weight i) ≤
          graphCBucketLoss
              (((H.effectiveRadius 0 : NNReal) : Real) / 2) •
            ∑ i ∈ S.selected, weight i) ∧
      SelectedLevelZeroUnitBallNormalized S := by
  obtain ⟨S, hactual, hexplicit⟩ :=
    exists_weightRetaining_levelZeroChartBucket
      (H := H) hdelta hchart weight
  exact ⟨S, ⟨hactual, hexplicit⟩,
    selectedLevelZeroUnitBallNormalized_of_source hunit S⟩

/-- The weight-retaining whole-source selector under fixed-chart provenance,
with unit-ball normalization added for the same selected witness. -/
theorem exists_weightRetaining_levelZeroSourceBucket_and_unitBallNormalized
    (hdelta : 0 < H.effectiveRadius 0)
    (hsource : (levelZeroSource (H := H)).Nonempty)
    (hvertical : ∀ i, i ∈ levelZeroSource (H := H) →
      (1 / 2 : Real) ≤
        |((H.effectiveFamily 0).tubes i).axis.direction 2|)
    (weight : Index 0 → NNReal)
    (hunit : LevelZeroSourceUnitBallNormalized (H := H)) :
    ∃ S : SelectedTerminalSourceChartBucketGeometry (H := H),
      ((∑ i ∈ levelZeroSource (H := H), weight i) ≤
          (levelZeroOccupiedGraphCBuckets (H := H)).card •
            ∑ i ∈ S.selected, weight i ∧
        (∑ i ∈ levelZeroSource (H := H), weight i) ≤
          graphCBucketLoss
              (((H.effectiveRadius 0 : NNReal) : Real) / 2) •
            ∑ i ∈ S.selected, weight i) ∧
      SelectedLevelZeroUnitBallNormalized S := by
  obtain ⟨S, hactual, hexplicit⟩ :=
    exists_weightRetaining_levelZeroSourceBucket_of_vertical_half
      (H := H) hdelta hsource hvertical weight
  exact ⟨S, ⟨hactual, hexplicit⟩,
    selectedLevelZeroUnitBallNormalized_of_source hunit S⟩

#print axioms selectedLevelZeroUnitBallNormalized_of_source
#print axioms exists_cardinalRetaining_levelZeroChartBucket_and_unitBallNormalized
#print axioms exists_cardinalRetaining_levelZeroSourceBucket_and_unitBallNormalized
#print axioms exists_weightRetaining_levelZeroChartBucket_and_unitBallNormalized
#print axioms exists_weightRetaining_levelZeroSourceBucket_and_unitBallNormalized

end
end FamilyStickyHierarchyTerminalSourceChartBucketUnitBallNormalizedProducerV1
