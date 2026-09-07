import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPAggregationV3
import FamilyStickyCinematicL32PyzActualWeightedPositiveCenterOverlapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
open FamilyStickyCinematicL32PyzActualProjectedNormThreeBallIndexedOverlapV1
open FamilyStickyCinematicL32PyzActualWeightedPositiveCenterOverlapV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# The true three-ball coefficient budget on the native high centers

V1 and V2 were failed namespace/linter drafts and are deliberately not
imported.  The normalized family inside each concrete Q/P package is
definitionally the indexed projected `3B` family at that global center.  Its
rich ordered-pair count is bounded by the square of the actual `3B`
cardinality, while summing one copy over the high centers costs only
`19^3 * ambient.card`.
-/

/-- The literal local norm-family cardinality at a native high center. -/
def nativeHighNormFamilyCard
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) : Nat :=
  (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale c.1.1).card

/-- The local norm index family is exactly the actual projected `3B` index
family used by the bounded-overlap theorem. -/
theorem nativeHighNormFamily_eq_threeBallIndices
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    actualGlobalNormIndexFamily D.S.family D.physical D.globalScale c.1.1 =
      actualProjectedNormThreeBallIndices D.S.family D.ambient D.globalScale
        c.1.1 := by
  rfl

/-- The actual rich-pair count in one explicit Q/P right-hand side is at
most the square of that center's indexed `3B` cardinality. -/
theorem concreteRichPair_card_le_nativeHighNormFamilyCard_sq
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    (richSeparatedCenterPairs
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).family
        (canonicalTenRadiusSeparated
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)) (G.ballRadius c))
        (fun _ _ => True)).card <=
      nativeHighNormFamilyCard D c * nativeHighNormFamilyCard D c := by
  simpa only [positiveCenterHighPayloadGlobalNormData_family,
    nativeHighNormFamilyCard] using
      richSeparatedCenterPairs_card_le_sq
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).family
        (canonicalTenRadiusSeparated
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)) (G.ballRadius c))
        (fun _ _ => True)

/-- Each local `3B` index family is a literal subfamily of the ambient
indices. -/
theorem nativeHighNormFamilyCard_le_ambient_card
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    nativeHighNormFamilyCard D c <= D.ambient.card := by
  unfold nativeHighNormFamilyCard actualGlobalNormIndexFamily
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The selected high-center subtype inherits the dimension-only global
`3B` overlap bound. -/
theorem sum_nativeHighNormFamilyCard_le
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (hpair : Set.Pairwise (D.ambient : Set iota) fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)) :
    (∑ c : D.HighCenter, nativeHighNormFamilyCard D c) <=
      19 ^ 3 * D.ambient.card := by
  classical
  have hhighAttach :
      (∑ c : D.HighCenter,
        (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
          c.1.1).card) =
        ∑ c ∈ D.high,
          (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
            c.1).card := by
    simpa only [Finset.univ_eq_attach] using
      Finset.sum_attach D.high (fun c =>
        (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
          c.1).card)
  calc
    (∑ c : D.HighCenter, nativeHighNormFamilyCard D c) =
        ∑ c ∈ D.high,
          (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
            c.1).card := by
      simpa only [nativeHighNormFamilyCard] using hhighAttach
    _ <= ∑ c : D.PositiveCenter,
        (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
          c.1).card := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ center ∈ actualAllCenterPositiveCenters volume D.centers D.cell,
        (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
          center).card := by
      simpa only [Finset.univ_eq_attach] using
        Finset.sum_attach
          (actualAllCenterPositiveCenters volume D.centers D.cell)
          (fun center =>
            (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
              center).card)
    _ <= ∑ center ∈ D.centers,
        (actualGlobalNormIndexFamily D.S.family D.physical D.globalScale
          center).card := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ center ∈ D.centers,
        (actualProjectedNormThreeBallIndices D.S.family D.ambient
          D.globalScale center).card := by
      apply Finset.sum_congr rfl
      intro center _hcenter
      rfl
    _ <= 19 ^ 3 * D.ambient.card := by
      simpa only [NativeBranchCore.centers, nativeCenters] using
        sum_actualProjectedNormThreeBallIndices_card_le D.S.family D.ambient
          D.hradius hpair D.hglobalScale

/-- ENNReal form used directly by the concrete-Q/P aggregation consumer. -/
theorem sum_nativeHighNormFamilyCard_cast_le
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (hpair : Set.Pairwise (D.ambient : Set iota) fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j)) :
    (∑ c : D.HighCenter, (nativeHighNormFamilyCard D c : ENNReal)) <=
      ((19 ^ 3 * D.ambient.card : Nat) : ENNReal) := by
  exact_mod_cast sum_nativeHighNormFamilyCard_le D hpair

#print axioms nativeHighNormFamily_eq_threeBallIndices
#print axioms concreteRichPair_card_le_nativeHighNormFamilyCard_sq
#print axioms nativeHighNormFamilyCard_le_ambient_card
#print axioms sum_nativeHighNormFamilyCard_le
#print axioms sum_nativeHighNormFamilyCard_cast_le

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
