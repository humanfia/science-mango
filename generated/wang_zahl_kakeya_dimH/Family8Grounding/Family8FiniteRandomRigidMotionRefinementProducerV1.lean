import Family8Grounding.Family8FiniteRandomRigidMotionRefinementV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionRefinementProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionRefinementV1

noncomputable section

/-!
# One-shot finite random rigid refinement

This theorem composes the literal finite Chernoff selection with the proved
greedy conflict refinement.  Its premises are exactly the local finite-grid
geometry and the explicit numerical tail inequality.  Its outputs are an
actual tuple of rigid motions and an actual finite subtype, together with
admissibility, cardinality retention, shading-mass retention, and the
multiplicity comparison used by generalized Frostman.
-/

/-- A direct finite-random producer for the rigidly moved and refined datum.
No selected tuple, selected subset, or final geometric property is supplied
among the hypotheses. -/
theorem exists_finiteRandomRigidMotion_refinedDatum
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (choiceBudget : motionChoice × iota -> Nat)
    (repetitions conflictThreshold : Nat) [NeZero repetitions]
    {cap mean lambda : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hloadCap : forall anchor g,
      (rigidConflictLoadNat motion D.family anchor g : Real) <= cap)
    (hgrid : forall anchor i,
      rigidConflictChoiceCount motion D.family anchor i <=
        choiceBudget anchor)
    (hbalance : forall anchor,
      (Fintype.card iota : Real) * (choiceBudget anchor : Real) <=
        (Fintype.card motionChoice : Real) * mean)
    (hnumerical :
      (Fintype.card (motionChoice × iota) : Real) *
          ((Fintype.card motionChoice : Real) *
            (1 + (mean / cap) *
              (Real.exp (lambda * cap) - 1))) ^ repetitions <
        ((Finset.univ : Finset (Fin repetitions -> motionChoice)).card : Real) *
          Real.exp (lambda * (conflictThreshold : Real)))
    (hball : forall g i,
      (rigidTube (motion g) (D.family.tubes i)).carrier ⊆
        Metric.closedBall (0 : Space) 1) :
    exists omega : Fin repetitions -> motionChoice,
      exists selected : Finset (Fin repetitions × iota),
        selected.Nonempty ∧
        Set.Pairwise (selected : Set (Fin repetitions × iota)) (fun a b =>
          EssentiallyDistinct
            ((indexedRigidCopyDatum (fun j => motion (omega j)) D).family.tubes a)
            ((indexedRigidCopyDatum (fun j => motion (omega j)) D).family.tubes b)) ∧
        (restrictActualTubeDatum
          (indexedRigidCopyDatum (fun j => motion (omega j)) D)
          selected).IsAdmissible ∧
        (Fintype.card (Fin repetitions × iota) : ENNReal) <=
          (conflictThreshold + 1 : Nat) * (selected.card : ENNReal) ∧
        (indexedRigidCopyDatum
          (fun j => motion (omega j)) D).shading.shadingMass <=
          (conflictThreshold + 1 : Nat) *
            (restrictActualTubeDatum
              (indexedRigidCopyDatum (fun j => motion (omega j)) D)
              selected).shading.shadingMass ∧
        D.shading.averageMultiplicity <=
          (conflictThreshold + 1 : Nat) *
            (restrictActualTubeDatum
              (indexedRigidCopyDatum (fun j => motion (omega j)) D)
              selected).shading.averageMultiplicity := by
  obtain ⟨omega, hload⟩ := exists_rigidMotionTuple_conflictLoad_le
    motion D.family choiceBudget repetitions conflictThreshold
      hcap hlambda hloadCap hgrid hbalance hnumerical
  have hconflict : forall a : Fin repetitions × iota,
      (rigidCopyConflictIndices (fun j => motion (omega j)) D.family a).card <=
        conflictThreshold :=
    rigidCopyConflictIndices_card_le_of_tupleLoad
      motion D.family omega hload
  obtain ⟨selected, hselectedNonempty, hpair, hcard, hmass⟩ :=
    exists_rigidCopy_greedyRefinement
      (fun j => motion (omega j)) D hconflict
  have hballProduct : forall a : Fin repetitions × iota,
      ((indexedRigidCopyDatum
        (fun j => motion (omega j)) D).family.tubes a).carrier ⊆
          Metric.closedBall (0 : Space) 1 := by
    intro a
    change (rigidTube (motion (omega a.1))
      (D.family.tubes a.2)).carrier ⊆ Metric.closedBall (0 : Space) 1
    exact hball (omega a.1) a.2
  have hadmissible := rigidCopyRestricted_isAdmissible
    (fun j => motion (omega j)) D hD selected hballProduct hpair
  have hmultiplicity :=
    source_averageMultiplicity_le_loss_mul_rigidCopyRestricted
      (fun j => motion (omega j)) D selected (conflictThreshold + 1) hmass
  exact ⟨omega, selected, hselectedNonempty, hpair, hadmissible,
    hcard, hmass, hmultiplicity⟩

#print axioms exists_finiteRandomRigidMotion_refinedDatum

end
end Family8FiniteRandomRigidMotionRefinementProducerV1
