import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Family8Grounding.Family8SharpKatzTaoOrGreedyHighConcentrationV1
import Family8Grounding.Family8FiniteRandomRigidMotionRefinementV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ActualDatumDirectFreshGreedyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1

noncomputable section

/-!
# Direct fresh greedy extraction for an actual tube datum

Unlike the earlier B2 selector, this version does not normalize the tubes a
second time.  It runs the finite weighted greedy theorem on the literal
equal-radius tubes of an `ActualTubeDatum`.  Thus an explicit conflict-degree
cap is the only geometric input; scale, support, subtype admissibility,
cardinality retention, shading-mass retention, density retention, and the
average-multiplicity comparison are discharged mechanically.
-/

/-- Literal failure of essential distinctness in an actual datum. -/
def directConflict
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (a b : index) : Prop :=
  ¬ EssentiallyDistinct (D.family.tubes a) (D.family.tubes b)

/-- The full finite conflict neighbourhood used by the producer interface. -/
def directConflictIndices
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (a : index) : Finset index := by
  classical
  exact Finset.univ.filter fun b => directConflict D b a

theorem directConflict_symm
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) : Std.Symm (directConflict D) := by
  constructor
  intro a b hab hba
  apply hab
  exact (essentiallyDistinct_comm
    (D.family.tubes a) (D.family.tubes b)).mpr hba

/-- Closed conflict neighbourhood, including its anchor. -/
def directClosedNeighbourhood
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (a : index) : Finset index := by
  classical
  exact Finset.univ.filter fun b => b = a ∨ directConflict D a b

theorem directClosedNeighbourhood_card_le
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    {conflictThreshold : Nat} (D : ActualTubeDatum delta index)
    (hconflict : forall a,
      (directConflictIndices D a).card <= conflictThreshold)
    (a : index) :
    (directClosedNeighbourhood D a).card <= conflictThreshold + 1 := by
  classical
  have hsubset : directClosedNeighbourhood D a ⊆
      insert a (directConflictIndices D a) := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    rcases hb'.2 with hba | hconf
    · exact Finset.mem_insert.mpr (Or.inl hba)
    · apply Finset.mem_insert.mpr
      apply Or.inr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ b, ?_⟩
      exact (directConflict_symm D).symm a b hconf
  calc
    (directClosedNeighbourhood D a).card <=
        (insert a (directConflictIndices D a)).card :=
      Finset.card_le_card hsubset
    _ <= (directConflictIndices D a).card + 1 :=
      Finset.card_insert_le _ _
    _ <= conflictThreshold + 1 :=
      Nat.add_le_add_right (hconflict a) 1

/-- Weighted fresh extraction on the literal actual tubes. -/
theorem exists_direct_greedyRefinement
    {delta : NNReal} {index : Type} [Fintype index] [Nonempty index]
    [DecidableEq index] {conflictThreshold : Nat}
    (D : ActualTubeDatum delta index)
    (hconflict : forall a,
      (directConflictIndices D a).card <= conflictThreshold) :
    exists selected : Finset index,
      selected.Nonempty ∧
      Set.Pairwise (selected : Set index) (fun a b =>
        EssentiallyDistinct (D.family.tubes a) (D.family.tubes b)) ∧
      (Fintype.card index : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) ∧
      D.shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum D selected).shading.shadingMass := by
  classical
  let weight : index -> ENNReal := fun i => volume (D.shading.carrier i)
  have hneighbour : forall a, a ∈ (Finset.univ : Finset index) ->
      (((Finset.univ : Finset index).filter fun b =>
          b = a ∨ directConflict D a b).card : ENNReal) <=
        (conflictThreshold + 1 : Nat) := by
    intro a _ha
    exact_mod_cast directClosedNeighbourhood_card_le D hconflict a
  obtain ⟨selected, _hselected, hselectedNonempty, hpair,
      hcard, hmass⟩ :=
    exists_greedy_pairwise_not_relation
      (Finset.univ : Finset index) (directConflict D)
      (directConflict_symm D) weight
      (conflictThreshold + 1 : Nat) hneighbour
  have hunivNonempty : (Finset.univ : Finset index).Nonempty :=
    Finset.univ_nonempty
  have hpairED : Set.Pairwise (selected : Set index) (fun a b =>
      EssentiallyDistinct (D.family.tubes a) (D.family.tubes b)) := by
    intro a ha b hb hab
    have hp := hpair ha hb hab
    simpa [directConflict] using hp
  have hcard' :
      (Fintype.card index : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) := by
    simpa using hcard
  have hfullMass :
      (∑ i ∈ (Finset.univ : Finset index), weight i) =
        D.shading.shadingMass := by
    simp [weight, Shading.shadingMass]
  have hselectedMass :
      (∑ i ∈ selected, weight i) =
        (restrictActualTubeDatum D selected).shading.shadingMass := by
    rw [restrictActualTubeDatum_shadingMass]
  rw [hfullMass, hselectedMass] at hmass
  exact ⟨selected, hselectedNonempty hunivNonempty, hpairED, hcard', hmass⟩

/-- Pairwise output plus the literal scale/support fields give actual paper
admissibility, without requiring the unselected source to be admissible. -/
theorem directRestricted_isAdmissible_of_scale_support
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsupport : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (selected : Finset index)
    (hpair : Set.Pairwise (selected : Set index) (fun a b =>
      EssentiallyDistinct (D.family.tubes a) (D.family.tubes b))) :
    (restrictActualTubeDatum D selected).IsAdmissible := by
  refine
    { delta_pos := hdeltaPos
      delta_le_half := hdeltaHalf
      contained_in_unit_ball := ?_
      pairwise_essentiallyDistinct := ?_ }
  · intro i
    exact hsupport i.1
  · intro i _hi j _hj hij
    apply hpair i.property j.property
    intro hv
    apply hij
    exact Subtype.ext hv

/-- Complete direct fresh-selection endpoint.  The only non-mechanical input
is the displayed finite conflict-degree cap. -/
theorem exists_direct_refinement_admissible
    {delta : NNReal} {index : Type} [Fintype index] [Nonempty index]
    [DecidableEq index] {conflictThreshold : Nat}
    (D : ActualTubeDatum delta index)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsupport : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hconflict : forall a,
      (directConflictIndices D a).card <= conflictThreshold) :
    exists selected : Finset index,
      selected.Nonempty ∧
      (restrictActualTubeDatum D selected).IsAdmissible ∧
      (Fintype.card index : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) ∧
      D.shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum D selected).shading.shadingMass ∧
      D.shading.shadingDensity / (conflictThreshold + 1 : Nat) <=
        (restrictActualTubeDatum D selected).shading.shadingDensity ∧
      D.shading.averageMultiplicity <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum D selected).shading.averageMultiplicity := by
  obtain ⟨selected, hselected, hpair, hcard, hmass⟩ :=
    exists_direct_greedyRefinement D hconflict
  refine ⟨selected, hselected, ?_, hcard, hmass, ?_, ?_⟩
  · exact directRestricted_isAdmissible_of_scale_support
      D hdeltaPos hdeltaHalf hsupport selected hpair
  · exact source_shadingDensity_div_loss_le_restrictActualTubeDatum
      D selected (conflictThreshold + 1 : Nat) hmass
  · exact source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
      D selected (conflictThreshold + 1 : Nat) hmass

#print axioms directConflictIndices
#print axioms directClosedNeighbourhood_card_le
#print axioms exists_direct_greedyRefinement
#print axioms directRestricted_isAdmissible_of_scale_support
#print axioms exists_direct_refinement_admissible

end

end Family8ActualDatumDirectFreshGreedyV1
