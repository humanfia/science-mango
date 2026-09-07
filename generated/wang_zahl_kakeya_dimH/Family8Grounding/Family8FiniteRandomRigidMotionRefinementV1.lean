import Family8Grounding.Family8FiniteRandomRigidMotionIncidenceV1
import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionRefinementV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1

noncomputable section

/-!
# From random rigid conflict caps to an actual refinement

The preceding incidence module produces a literal product family with a
uniform bound on every cross-copy conflict neighbourhood.  Here the generic
finite greedy theorem constructs a genuine pairwise essentially-distinct
subfamily.  Both indexed cardinality and actual shaded mass are retained up
to the same explicit `conflictThreshold + 1` loss.

The refined datum is a real subtype of the moved product family.  Its
admissibility is proved from the selected pairwise relation and the local
unit-ball containment of the moved tubes; neither conclusion is stored in a
package or passed as a callback.
-/

/-- `EssentiallyDistinct` is symmetric, directly from its intersection/max
definition. -/
theorem essentiallyDistinct_comm {delta : NNReal} (T U : Tube delta) :
    EssentiallyDistinct T U ↔ EssentiallyDistinct U T := by
  unfold EssentiallyDistinct
  rw [inter_comm, max_comm]

/-- Consequently the rigid-copy conflict relation is symmetric. -/
theorem rigidCopyConflict_symm
    {tau iota : Type}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : tau -> RigidMotion)
    (F : UniformTubeFamily delta iota) :
    Std.Symm (rigidCopyConflict motion F) := by
  constructor
  intro a b hab hba
  apply hab
  exact (essentiallyDistinct_comm
    ((indexedRigidCopyTubeFamily motion F).tubes a)
    ((indexedRigidCopyTubeFamily motion F).tubes b)).mpr hba

/-- The closed conflict neighbourhood used by the greedy selector. -/
def rigidCopyClosedNeighbourhood
    {tau iota : Type}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : tau -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (a : tau × iota) : Finset (tau × iota) := by
  classical
  exact Finset.univ.filter fun b =>
    b = a ∨ rigidCopyConflict motion F a b

/-- A cap for the open conflict set gives a cap one larger for the closed
neighbourhood required by greedy selection. -/
theorem rigidCopyClosedNeighbourhood_card_le
    {tau iota : Type}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {conflictThreshold : Nat}
    (motion : tau -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (hconflict : forall a,
      (rigidCopyConflictIndices motion F a).card <= conflictThreshold)
    (a : tau × iota) :
    (rigidCopyClosedNeighbourhood motion F a).card <=
      conflictThreshold + 1 := by
  classical
  have hsubset : rigidCopyClosedNeighbourhood motion F a ⊆
      insert a (rigidCopyConflictIndices motion F a) := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    rcases hb'.2 with hba | hconf
    · exact Finset.mem_insert.mpr (Or.inl hba)
    · apply Finset.mem_insert.mpr
      apply Or.inr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ b, ?_⟩
      exact (rigidCopyConflict_symm motion F).symm a b hconf
  calc
    (rigidCopyClosedNeighbourhood motion F a).card <=
        (insert a (rigidCopyConflictIndices motion F a)).card :=
      Finset.card_le_card hsubset
    _ <= (rigidCopyConflictIndices motion F a).card + 1 :=
      Finset.card_insert_le _ _
    _ <= conflictThreshold + 1 := Nat.add_le_add_right (hconflict a) 1

/-- A bounded conflict graph produces a genuine essentially-distinct
subtype, retaining both indexed cardinality and the actual shading mass.
The representatives are the literal moved tubes; no geometric structure is
rounded or reconstructed. -/
theorem exists_rigidCopy_greedyRefinement
    {tau iota : Type}
    [Fintype tau] [Nonempty tau] [DecidableEq tau]
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {delta : NNReal} {conflictThreshold : Nat}
    (motion : tau -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (hconflict : forall a,
      (rigidCopyConflictIndices motion D.family a).card <=
        conflictThreshold) :
    exists selected : Finset (tau × iota),
      selected.Nonempty ∧
      Set.Pairwise (selected : Set (tau × iota)) (fun a b =>
        EssentiallyDistinct
          ((indexedRigidCopyDatum motion D).family.tubes a)
          ((indexedRigidCopyDatum motion D).family.tubes b)) ∧
      (Fintype.card (tau × iota) : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (indexedRigidCopyDatum motion D).shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          (restrictActualTubeDatum
            (indexedRigidCopyDatum motion D) selected).shading.shadingMass := by
  classical
  let weight : tau × iota -> ENNReal := fun a =>
    volume ((indexedRigidCopyDatum motion D).shading.carrier a)
  have hneighbour : forall a, a ∈ (Finset.univ : Finset (tau × iota)) ->
      (((Finset.univ : Finset (tau × iota)).filter fun b =>
          b = a ∨ rigidCopyConflict motion D.family a b).card : ENNReal) <=
        (conflictThreshold + 1 : Nat) := by
    intro a _ha
    exact_mod_cast
      rigidCopyClosedNeighbourhood_card_le motion D.family hconflict a
  obtain ⟨selected, _hselected, hselectedNonempty, hpair,
      hcard, hmass⟩ :=
    exists_greedy_pairwise_not_relation
      (Finset.univ : Finset (tau × iota))
      (rigidCopyConflict motion D.family)
      (rigidCopyConflict_symm motion D.family)
      weight (conflictThreshold + 1 : Nat) hneighbour
  have hunivNonempty : (Finset.univ : Finset (tau × iota)).Nonempty :=
    Finset.univ_nonempty
  have hpairED :
      Set.Pairwise (selected : Set (tau × iota)) (fun a b =>
        EssentiallyDistinct
          ((indexedRigidCopyDatum motion D).family.tubes a)
          ((indexedRigidCopyDatum motion D).family.tubes b)) := by
    intro a ha b hb hab
    change EssentiallyDistinct
      (rigidTube (motion a.1) (D.family.tubes a.2))
      (rigidTube (motion b.1) (D.family.tubes b.2))
    have hp := hpair ha hb hab
    simpa [rigidCopyConflict] using hp
  have hcard' :
      (Fintype.card (tau × iota) : ENNReal) <=
        (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) := by
    simpa using hcard
  have hfullMass :
      (∑ a ∈ (Finset.univ : Finset (tau × iota)), weight a) =
        (indexedRigidCopyDatum motion D).shading.shadingMass := by
    simp [weight, Shading.shadingMass]
  have hselectedMass :
      (∑ a ∈ selected, weight a) =
        (restrictActualTubeDatum
          (indexedRigidCopyDatum motion D) selected).shading.shadingMass := by
    rw [restrictActualTubeDatum_shadingMass]
  rw [hfullMass, hselectedMass] at hmass
  exact ⟨selected, hselectedNonempty hunivNonempty, hpairED, hcard', hmass⟩

/-- The selected literal product subtype is an admissible actual datum once
the moved tubes satisfy the normalized unit-ball window. -/
theorem rigidCopyRestricted_isAdmissible
    {tau iota : Type}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : tau -> RigidMotion)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (selected : Finset (tau × iota))
    (hball : forall a : tau × iota,
      ((indexedRigidCopyDatum motion D).family.tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 1)
    (hpair : Set.Pairwise (selected : Set (tau × iota)) (fun a b =>
      EssentiallyDistinct
        ((indexedRigidCopyDatum motion D).family.tubes a)
        ((indexedRigidCopyDatum motion D).family.tubes b))) :
    (restrictActualTubeDatum
      (indexedRigidCopyDatum motion D) selected).IsAdmissible := by
  refine
    { delta_pos := hD.delta_pos
      delta_le_half := hD.delta_le_half
      contained_in_unit_ball := fun a => hball a.1
      pairwise_essentiallyDistinct := ?_ }
  intro a _ha b _hb hab
  apply hpair a.property b.property
  intro hv
  apply hab
  exact Subtype.ext hv

/-- Multiplicity returns from the greedy rigid-copy subtype with exactly the
same explicit mass-retention loss. -/
theorem source_averageMultiplicity_le_loss_mul_rigidCopyRestricted
    {tau iota : Type}
    [Fintype tau] [Nonempty tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : tau -> RigidMotion)
    (D : ActualTubeDatum delta iota)
    (selected : Finset (tau × iota)) (loss : Nat)
    (hmass :
      (indexedRigidCopyDatum motion D).shading.shadingMass <=
        (loss : ENNReal) *
          (restrictActualTubeDatum
            (indexedRigidCopyDatum motion D) selected).shading.shadingMass) :
    D.shading.averageMultiplicity <=
      (loss : ENNReal) *
        (restrictActualTubeDatum
          (indexedRigidCopyDatum motion D) selected).shading.averageMultiplicity := by
  let copied := indexedRigidCopyDatum motion D
  let refined := restrictActualTubeDatum copied selected
  have hsource := source_averageMultiplicity_le_indexedRigidCopy
    motion D.family D.shading
  have hunion : refined.shading.shadedUnion ⊆ copied.shading.shadedUnion :=
    restrictActualTubeDatum_shadedUnion_subset copied selected
  unfold Shading.averageMultiplicity at hsource ⊢
  calc
    D.shading.shadingMass / volume D.shading.shadedUnion <=
        copied.shading.shadingMass / volume copied.shading.shadedUnion := hsource
    _ <= ((loss : ENNReal) * refined.shading.shadingMass) /
          volume copied.shading.shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ <= ((loss : ENNReal) * refined.shading.shadingMass) /
          volume refined.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = (loss : ENNReal) *
          (refined.shading.shadingMass /
            volume refined.shading.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms essentiallyDistinct_comm
#print axioms rigidCopyClosedNeighbourhood_card_le
#print axioms exists_rigidCopy_greedyRefinement
#print axioms rigidCopyRestricted_isAdmissible
#print axioms source_averageMultiplicity_le_loss_mul_rigidCopyRestricted

end
end Family8FiniteRandomRigidMotionRefinementV1
