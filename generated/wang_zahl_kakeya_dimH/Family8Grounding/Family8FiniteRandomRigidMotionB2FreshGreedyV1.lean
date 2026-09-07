import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Family8Grounding.Family8FiniteRandomRigidMotionRefinementV1
import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2FreshGreedyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1

noncomputable section

/-!
# Fresh greedy selection after B2 normalization

Axis extension need not preserve the source family's essential distinctness.
This module therefore forms the literal conflict graph of the normalized
tubes and applies the existing weighted finite greedy theorem again.  The
selected subtype is admissible, keeps both cardinality and actual shading
mass up to the explicit closed-neighbourhood loss, and inherits the honest
normalized Katz--Tao bound.
-/

def normalizedConflict
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (a b : iota) : Prop :=
  ¬ EssentiallyDistinct
    ((eighthNormalizedDatum D).family.tubes a)
    ((eighthNormalizedDatum D).family.tubes b)

def normalizedConflictIndices
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (a : iota) : Finset iota := by
  classical
  exact Finset.univ.filter fun b => normalizedConflict D b a

theorem normalizedConflict_symm
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota) :
    Std.Symm (normalizedConflict D) := by
  constructor
  intro a b hab hba
  apply hab
  exact (essentiallyDistinct_comm
    ((eighthNormalizedDatum D).family.tubes a)
    ((eighthNormalizedDatum D).family.tubes b)).mpr hba

def normalizedClosedNeighbourhood
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (a : iota) : Finset iota := by
  classical
  exact Finset.univ.filter fun b => b = a ∨ normalizedConflict D a b

theorem normalizedClosedNeighbourhood_card_le
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {conflictThreshold : Nat}
    (D : ActualTubeDatum delta iota)
    (hconflict : forall a,
      (normalizedConflictIndices D a).card <= conflictThreshold)
    (a : iota) :
    (normalizedClosedNeighbourhood D a).card <= conflictThreshold + 1 := by
  classical
  have hsubset : normalizedClosedNeighbourhood D a ⊆
      insert a (normalizedConflictIndices D a) := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    rcases hb'.2 with hba | hconf
    · exact Finset.mem_insert.mpr (Or.inl hba)
    · apply Finset.mem_insert.mpr
      apply Or.inr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ b, ?_⟩
      exact (normalizedConflict_symm D).symm a b hconf
  calc
    (normalizedClosedNeighbourhood D a).card <=
        (insert a (normalizedConflictIndices D a)).card :=
      Finset.card_le_card hsubset
    _ <= (normalizedConflictIndices D a).card + 1 :=
      Finset.card_insert_le _ _
    _ <= conflictThreshold + 1 :=
      Nat.add_le_add_right (hconflict a) 1

theorem exists_normalized_greedyRefinement
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {delta : NNReal} {conflictThreshold : Nat}
    (D : ActualTubeDatum delta iota)
    (hconflict : forall a,
      (normalizedConflictIndices D a).card <= conflictThreshold) :
    exists selected : Finset iota,
      selected.Nonempty ∧
      Set.Pairwise (selected : Set iota) (fun a b =>
        EssentiallyDistinct
          ((eighthNormalizedDatum D).family.tubes a)
          ((eighthNormalizedDatum D).family.tubes b)) ∧
      (Fintype.card iota : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass := by
  classical
  let weight : iota -> ENNReal := fun i =>
    volume ((eighthNormalizedDatum D).shading.carrier i)
  have hneighbour : forall a, a ∈ (Finset.univ : Finset iota) ->
      (((Finset.univ : Finset iota).filter fun b =>
          b = a ∨ normalizedConflict D a b).card : ENNReal) <=
        (conflictThreshold + 1 : Nat) := by
    intro a _ha
    exact_mod_cast normalizedClosedNeighbourhood_card_le D hconflict a
  obtain ⟨selected, _hselected, hselectedNonempty, hpair,
      hcard, hmass⟩ :=
    exists_greedy_pairwise_not_relation
      (Finset.univ : Finset iota)
      (normalizedConflict D)
      (normalizedConflict_symm D)
      weight (conflictThreshold + 1 : Nat) hneighbour
  have hunivNonempty : (Finset.univ : Finset iota).Nonempty :=
    Finset.univ_nonempty
  have hpairED :
      Set.Pairwise (selected : Set iota) (fun a b =>
        EssentiallyDistinct
          ((eighthNormalizedDatum D).family.tubes a)
          ((eighthNormalizedDatum D).family.tubes b)) := by
    intro a ha b hb hab
    have hp := hpair ha hb hab
    simpa [normalizedConflict] using hp
  have hcard' :
      (Fintype.card iota : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) := by
    simpa using hcard
  have hfullMass :
      (∑ i ∈ (Finset.univ : Finset iota), weight i) =
        (eighthNormalizedDatum D).shading.shadingMass := by
    simp [weight, Shading.shadingMass]
  have hselectedMass :
      (∑ i ∈ selected, weight i) =
        (restrictActualTubeDatum (eighthNormalizedDatum D)
          selected).shading.shadingMass := by
    rw [restrictActualTubeDatum_shadingMass]
  rw [hfullMass, hselectedMass] at hmass
  exact ⟨selected, hselectedNonempty hunivNonempty, hpairED, hcard', hmass⟩

theorem normalizedRestricted_isAdmissible
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (selected : Finset iota)
    (hpair : Set.Pairwise (selected : Set iota) (fun a b =>
      EssentiallyDistinct
        ((eighthNormalizedDatum D).family.tubes a)
        ((eighthNormalizedDatum D).family.tubes b))) :
    (restrictActualTubeDatum
      (eighthNormalizedDatum D) selected).IsAdmissible := by
  refine
    { delta_pos := div_pos hD.delta_pos (by norm_num)
      delta_le_half :=
        (div_le_self (show 0 <= delta from bot_le)
          (by norm_num : (1 : NNReal) <= 8)).trans hD.delta_le_half
      contained_in_unit_ball := ?_
      pairwise_essentiallyDistinct := ?_ }
  · intro a
    change ((eighthNormalizedDatum D).family.tubes a.1).carrier ⊆
      Metric.closedBall (0 : Space) 1
    exact eighthNormalizedDatum_contained_in_unit_ball
      D hD.delta_le_half hB2 a.1
  · intro a _ha b _hb hab
    apply hpair a.property b.property
    intro hv
    apply hab
    exact Subtype.ext hv

theorem restrictActualTubeDatum_isKatzTao
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (selected : Finset iota) {C : ENNReal}
    (hfull : IsKatzTao C D.family.bodyFamily) :
    IsKatzTao C
      (restrictActualTubeDatum D selected).family.bodyFamily := by
  intro K
  unfold IsKatzTaoAt
  rw [restrictActualTubeDatum_containedMass]
  exact hfull.on selected K

theorem restrict_eighthNormalizedDatum_isKatzTao
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (selected : Finset iota) {C : ENNReal}
    (hKT : IsKatzTao C D.family.bodyFamily) :
    IsKatzTao (128 * C)
      (restrictActualTubeDatum (eighthNormalizedDatum D)
        selected).family.bodyFamily := by
  apply restrictActualTubeDatum_isKatzTao
  exact eighthNormalizedDatum_isKatzTao D hdeltaHalf hKT

theorem source_averageMultiplicity_le_loss_mul_normalizedRestricted
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (D : ActualTubeDatum delta iota)
    (selected : Finset iota) (loss : Nat)
    (hmass :
      (eighthNormalizedDatum D).shading.shadingMass <=
        (loss : ENNReal) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass) :
    D.shading.averageMultiplicity <=
      (loss : ENNReal) *
        (restrictActualTubeDatum (eighthNormalizedDatum D)
          selected).shading.averageMultiplicity := by
  rw [← eighthNormalizedDatum_averageMultiplicity D]
  let normalized := eighthNormalizedDatum D
  let refined := restrictActualTubeDatum normalized selected
  have hunion : refined.shading.shadedUnion ⊆
      normalized.shading.shadedUnion :=
    restrictActualTubeDatum_shadedUnion_subset normalized selected
  unfold Shading.averageMultiplicity
  calc
    normalized.shading.shadingMass /
          volume normalized.shading.shadedUnion <=
        ((loss : ENNReal) * refined.shading.shadingMass) /
          volume normalized.shading.shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ <= ((loss : ENNReal) * refined.shading.shadingMass) /
          volume refined.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = (loss : ENNReal) *
          (refined.shading.shadingMass /
            volume refined.shading.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Combined callback-free fresh-greedy seam.  Its only new geometric input
is the explicit finite normalized conflict cap; every property of the
existential selected subtype is discharged internally. -/
theorem exists_normalized_refinement_admissible_isKatzTao
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {delta : NNReal} {conflictThreshold : Nat}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (hconflict : forall a,
      (normalizedConflictIndices D a).card <= conflictThreshold)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily) :
    exists selected : Finset iota,
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card iota : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum (eighthNormalizedDatum D)
          selected).family.bodyFamily ∧
      D.shading.averageMultiplicity <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.averageMultiplicity := by
  obtain ⟨selected, hselected, hpair, hcard, hmass⟩ :=
    exists_normalized_greedyRefinement D hconflict
  refine ⟨selected, hselected, ?_, hcard, hmass, ?_, ?_⟩
  · exact normalizedRestricted_isAdmissible D hD hB2 selected hpair
  · exact restrict_eighthNormalizedDatum_isKatzTao
      D hD.delta_le_half selected hKT
  · exact source_averageMultiplicity_le_loss_mul_normalizedRestricted
      D selected (conflictThreshold + 1) hmass

#print axioms normalizedClosedNeighbourhood_card_le
#print axioms exists_normalized_greedyRefinement
#print axioms normalizedRestricted_isAdmissible
#print axioms restrict_eighthNormalizedDatum_isKatzTao
#print axioms source_averageMultiplicity_le_loss_mul_normalizedRestricted
#print axioms exists_normalized_refinement_admissible_isKatzTao

end
end Family8FiniteRandomRigidMotionB2FreshGreedyV1
