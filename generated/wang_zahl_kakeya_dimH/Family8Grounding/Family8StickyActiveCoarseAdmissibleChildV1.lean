import Family8Grounding.Family8StickyActiveCoarseB2SupportV5
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Mathlib.Tactic

/-!
# A genuine admissible child of the active coarse family

Given an actual datum `D` and a Sticky cover of `D.family`, this module uses
the literal parent-aggregated shading on the actual active coarse tubes.  At
radius at most `1/16`, the existing geometry puts every active parent in
`B(0,2)`.  Eighth-normalization and the existing fresh greedy selector then
produce a genuine admissible actual datum.

The conflict threshold, source Katz--Tao constant, and every card, mass, and
average-multiplicity loss remain explicit.  No selection or successor
callback is stored in the interface.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveCoarseAdmissibleChildV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8StickyActiveCoarseB2SupportV5
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- The actual active coarse tubes with the literal parent-aggregated source
shading.  Unlike the full-shading coarse datum, this object retains the
shading supplied by `D`, grouped inside its actual Sticky parents. -/
def activeCoarseAggregatedDatum
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho) :
    ActualTubeDatum rho {k // k ∈ S.activeCoarse} where
  family := S.coarse.restrictTo S.activeCoarse
  shading := parentAggregatedShading S D.shading

@[simp]
theorem activeCoarseAggregatedDatum_family_tubes
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (k : {k // k ∈ S.activeCoarse}) :
    (activeCoarseAggregatedDatum D S).family.tubes k =
      S.coarse.tubes k.1 :=
  rfl

@[simp]
theorem activeCoarseAggregatedDatum_shading_carrier
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (k : {k // k ∈ S.activeCoarse}) :
    (activeCoarseAggregatedDatum D S).shading.carrier k =
      (parentAggregatedShading S D.shading).carrier k :=
  rfl

/-- The sharp active-parent support theorem supplies exactly the B2 premise
needed by eighth-normalization. -/
theorem activeCoarseAggregatedDatum_contained_in_B2
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrhoSixteenth : rho <= (1 / 16 : NNReal)) :
    forall k,
      ((activeCoarseAggregatedDatum D S).family.tubes k).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro k
  change (S.activeCoarseFamily k : Set Space) ⊆
    Metric.closedBall (0 : Space) 2
  exact activeCoarseFamily_body_subset_closedBall_two
    D hD S hrhoSixteenth k

/-- The cover's literal active-coarse Katz--Tao estimate is the estimate on
the actual aggregated datum; shading does not alter the indexed family. -/
theorem activeCoarseAggregatedDatum_isKatzTao
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    IsKatzTao C (activeCoarseAggregatedDatum D S).family.bodyFamily := by
  apply isKatzTao_iff_concentration_le.mpr
  intro K
  exact hKT K

/-- The actual normalized fresh child on a selected subtype of the active
coarse parent occurrences.  Its literal radius is `rho / 8`. -/
def activeCoarseFreshChildDatum
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (selected : Finset {k // k ∈ S.activeCoarse}) :
    ActualTubeDatum (rho / 8) {k // k ∈ selected} :=
  restrictActualTubeDatum
    (eighthNormalizedDatum (activeCoarseAggregatedDatum D S)) selected

/-- Callback-free construction of a genuine admissible active-coarse child.

The source conflict cap and source KT estimate are explicit inputs.  The
output repeats the exact greedy loss `conflictThreshold + 1` independently
in the card, normalized-mass, and source-average comparisons. -/
theorem exists_activeCoarse_admissibleChild
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrhoPos : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hrhoSixteenth : rho <= (1 / 16 : NNReal))
    (hactive : S.activeCoarse.Nonempty)
    {conflictThreshold : Nat}
    (hconflict : forall a : {k // k ∈ S.activeCoarse},
      (normalizedConflictIndices
        (activeCoarseAggregatedDatum D S) a).card <= conflictThreshold)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    exists selected : Finset {k // k ∈ S.activeCoarse},
      selected.Nonempty /\
      (activeCoarseFreshChildDatum D S selected).IsAdmissible /\
      (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) /\
      (eighthNormalizedDatum
        (activeCoarseAggregatedDatum D S)).shading.shadingMass <=
          (conflictThreshold + 1 : Nat) *
            (activeCoarseFreshChildDatum D S selected).shading.shadingMass /\
      IsKatzTao (128 * C)
        (activeCoarseFreshChildDatum D S selected).family.bodyFamily /\
      (activeCoarseAggregatedDatum D S).shading.averageMultiplicity <=
        (conflictThreshold + 1 : Nat) *
          (activeCoarseFreshChildDatum D S selected).shading.averageMultiplicity := by
  have hB2 : forall k,
      ((activeCoarseAggregatedDatum D S).family.tubes k).carrier ⊆
        Metric.closedBall (0 : Space) 2 :=
    activeCoarseAggregatedDatum_contained_in_B2 D hD S hrhoSixteenth
  have hsourceKT : IsKatzTao C
      (activeCoarseAggregatedDatum D S).family.bodyFamily :=
    activeCoarseAggregatedDatum_isKatzTao D S hKT
  simpa only [activeCoarseFreshChildDatum] using
    (@exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
      {k // k ∈ S.activeCoarse}
      inferInstance
      ⟨⟨hactive.choose, hactive.choose_spec⟩⟩
      inferInstance
      rho conflictThreshold
      (activeCoarseAggregatedDatum D S)
      hrhoPos hrhoHalf hB2 hconflict C hsourceKT)

#print axioms activeCoarseAggregatedDatum
#print axioms activeCoarseAggregatedDatum_family_tubes
#print axioms activeCoarseAggregatedDatum_shading_carrier
#print axioms activeCoarseAggregatedDatum_contained_in_B2
#print axioms activeCoarseAggregatedDatum_isKatzTao
#print axioms activeCoarseFreshChildDatum
#print axioms exists_activeCoarse_admissibleChild

end
end Family8StickyActiveCoarseAdmissibleChildV1
