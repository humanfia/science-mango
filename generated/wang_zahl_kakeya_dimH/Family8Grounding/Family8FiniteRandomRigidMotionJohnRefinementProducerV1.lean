import Family8Grounding.Family8FiniteRandomRigidMotionJohnJointSelectionV1
import Family8Grounding.Family8FiniteRandomRigidMotionRefinementV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionJohnRefinementProducerV1

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
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8RigidCopyPolynomialJohnKatzTaoV1
open Family8FiniteRandomRigidMotionJohnJointSelectionV1

noncomputable section

/-!
# One-shot joint random rigid refinement with polynomial John control

This endpoint composes the joint conflict/catalogue Chernoff selector with
the exact conflict-count decomposition, greedy refinement, admissibility,
mass and cardinal retention, multiplicity recovery, and the polynomial
John all-convex adapter.  The selected tuple and selected subtype are both
produced by the proof.
-/

/-- One finite random construction simultaneously produces a genuine
essentially-distinct actual subtype and a Katz--Tao estimate for that same
subtype. -/
theorem exists_finiteRandomRigidMotion_refinedDatum_isKatzTao
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (repetitions conflictThreshold : Nat)
    [NeZero repetitions]
    (A johnCoefficient : Real)
    (conflictCap conflictMean : motionChoice × iota -> Real)
    (johnMean : CatalogueIndex delta hD.delta_pos -> Real)
    (hA : 0 <= A)
    (hconflictCap : forall anchor, 0 <= conflictCap anchor)
    (hconflictMean : forall anchor, 0 <= conflictMean anchor)
    (hjohnCoefficient : 0 <= johnCoefficient)
    (hjohnMean : forall q, 0 <= johnMean q)
    (hconflictLoadCap : forall anchor g,
      (rigidConflictLoadNat motion D.family anchor g : Real) <=
        conflictCap anchor)
    (hjohnLoadCap : forall q g,
      (rigidCopyPolynomialJohnLoad motion D.family hD.delta_pos q g).toReal <=
        johnCoefficient *
          (volume
            (representativeTestBody delta hD.delta_pos q : Set Space)).toReal)
    (hconflictSum : forall anchor,
      (∑ g : motionChoice,
        (rigidConflictLoadNat motion D.family anchor g : Real)) <=
          (Fintype.card motionChoice : Real) * conflictMean anchor)
    (hjohnSum : forall q,
      (∑ g : motionChoice,
        (rigidCopyPolynomialJohnLoad
          motion D.family hD.delta_pos q g).toReal) <=
          (Fintype.card motionChoice : Real) * johnMean q)
    (hconflictScale : forall anchor,
      (repetitions : Real) * conflictMean anchor <= conflictCap anchor)
    (hjohnScale : forall q,
      (repetitions : Real) * johnMean q <=
        johnCoefficient *
          (volume
            (representativeTestBody delta hD.delta_pos q : Set Space)).toReal)
    (htailRoom :
      (Fintype.card
          (RigidJohnJointTest delta motionChoice iota hD.delta_pos) : Real) *
          Real.exp (Real.exp 1 - 1) < Real.exp A)
    (hconflictThreshold : forall anchor,
      A * conflictCap anchor <= (conflictThreshold : Real))
    (hball : forall g i,
      (rigidTube (motion g) (D.family.tubes i)).carrier ⊆
        Metric.closedBall (0 : Space) 1) :
    exists omega : Fin repetitions -> motionChoice,
      exists selected : Finset (Fin repetitions × iota),
        selected.Nonempty ∧
        Set.Pairwise (selected : Set (Fin repetitions × iota)) (fun a b =>
          EssentiallyDistinct
            ((indexedRigidCopyDatum
              (fun j => motion (omega j)) D).family.tubes a)
            ((indexedRigidCopyDatum
              (fun j => motion (omega j)) D).family.tubes b)) ∧
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
              selected).shading.averageMultiplicity ∧
        IsKatzTao
          (ENNReal.ofReal (A * johnCoefficient) *
            johnCatalogueVolumeConstant)
          (restrictActualTubeDatum
            (indexedRigidCopyDatum (fun j => motion (omega j)) D)
            selected).family.bodyFamily := by
  obtain ⟨omega, hconflictReal, hjohnReal⟩ :=
    exists_rigidMotionTuple_joint_conflict_catalogue
      motion D.family hD.delta_pos repetitions A johnCoefficient
      conflictCap conflictMean johnMean
      hconflictCap hconflictMean hjohnCoefficient hjohnMean
      hconflictLoadCap hjohnLoadCap hconflictSum hjohnSum
      hconflictScale hjohnScale htailRoom
  have hloadNat : forall anchor : motionChoice × iota,
      (∑ j, rigidConflictLoadNat motion D.family anchor (omega j)) <=
        conflictThreshold := by
    intro anchor
    have hreal :
        (∑ j,
          (rigidConflictLoadNat motion D.family anchor (omega j) : Real)) <=
            (conflictThreshold : Real) :=
      (hconflictReal anchor).trans (hconflictThreshold anchor)
    exact_mod_cast hreal
  have hconflict : forall a : Fin repetitions × iota,
      (rigidCopyConflictIndices
        (fun j => motion (omega j)) D.family a).card <=
          conflictThreshold :=
    rigidCopyConflictIndices_card_le_of_tupleLoad
      motion D.family omega hloadNat
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
      (fun j => motion (omega j)) D selected
      (conflictThreshold + 1) hmass
  have hcoefficient : 0 <= A * johnCoefficient :=
    mul_nonneg hA hjohnCoefficient
  have hloads : forall q : CatalogueIndex delta hD.delta_pos,
      (∑ j, rigidCopyPolynomialJohnLoad
        (fun k => motion (omega k)) D.family hD.delta_pos q j) <=
          ENNReal.ofReal (A * johnCoefficient) *
            volume (representativeTestBody delta hD.delta_pos q : Set Space) := by
    intro q
    apply sum_rigidCopyPolynomialJohnLoad_le_of_toReal
      (fun k => motion (omega k)) D.family hD.delta_pos q
      (A * johnCoefficient) hcoefficient
    simpa only [rigidCopyPolynomialJohnLoad, mul_assoc] using hjohnReal q
  have hKT :=
    restrictIndexedRigidCopyDatum_isKatzTao_of_polynomialJohnLoads
      (fun j => motion (omega j)) D selected hD.delta_pos
      hballProduct (ENNReal.ofReal (A * johnCoefficient)) hloads
  exact ⟨omega, selected, hselectedNonempty, hpair, hadmissible,
    hcard, hmass, hmultiplicity, hKT⟩

#print axioms exists_finiteRandomRigidMotion_refinedDatum_isKatzTao

end
end Family8FiniteRandomRigidMotionJohnRefinementProducerV1
