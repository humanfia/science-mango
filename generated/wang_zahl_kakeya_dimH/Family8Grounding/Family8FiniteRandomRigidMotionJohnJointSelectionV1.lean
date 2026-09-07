import Family8Grounding.Family8RigidCopyPolynomialJohnKatzTaoV1
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionJohnJointSelectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8RigidCopyPolynomialJohnKatzTaoV1
open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTestDependentChernoffV1

noncomputable section

/-!
# One finite random tuple for conflicts and polynomial John tests

The test type is the disjoint union of every possible moved-tube conflict
anchor and every occupied John catalogue cell.  The existing test-dependent
finite Chernoff theorem then selects one tuple controlling both collections
simultaneously.  Caps and means remain test-dependent, as in the GWZ
appendix; no good tuple is supplied as input.
-/

/-- The finite joint test type used before the random tuple is chosen. -/
abbrev RigidJohnJointTest
    (delta : NNReal) (motionChoice iota : Type) (hdelta : 0 < delta) :=
  Sum (motionChoice × iota) (CatalogueIndex delta hdelta)

/-- Single-choice real load for either a conflict anchor or a John test. -/
def rigidJohnJointLoad
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta) :
    RigidJohnJointTest delta motionChoice iota hdelta ->
      motionChoice -> Real
  | Sum.inl anchor, g => (rigidConflictLoadNat motion F anchor g : Real)
  | Sum.inr q, g =>
      (rigidCopyPolynomialJohnLoad motion F hdelta q g).toReal

/-- Test-dependent cap.  John tests use `coefficient * test volume`. -/
def rigidJohnJointCap
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (hdelta : 0 < delta)
    (conflictCap : motionChoice × iota -> Real)
    (johnCoefficient : Real) :
    RigidJohnJointTest delta motionChoice iota hdelta -> Real
  | Sum.inl anchor => conflictCap anchor
  | Sum.inr q => johnCoefficient *
      (volume (representativeTestBody delta hdelta q : Set Space)).toReal

/-- Test-dependent mean for the joint finite Chernoff theorem. -/
def rigidJohnJointMean
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (hdelta : 0 < delta)
    (conflictMean : motionChoice × iota -> Real)
    (johnMean : CatalogueIndex delta hdelta -> Real) :
    RigidJohnJointTest delta motionChoice iota hdelta -> Real
  | Sum.inl anchor => conflictMean anchor
  | Sum.inr q => johnMean q

/-- A single finite random tuple simultaneously controls every literal
conflict anchor and every occupied polynomial John test. -/
theorem exists_rigidMotionTuple_joint_conflict_catalogue
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (repetitions : Nat) (A johnCoefficient : Real)
    (conflictCap conflictMean : motionChoice × iota -> Real)
    (johnMean : CatalogueIndex delta hdelta -> Real)
    (hconflictCap : forall anchor, 0 <= conflictCap anchor)
    (hconflictMean : forall anchor, 0 <= conflictMean anchor)
    (hjohnCoefficient : 0 <= johnCoefficient)
    (hjohnMean : forall q, 0 <= johnMean q)
    (hconflictLoadCap : forall anchor g,
      (rigidConflictLoadNat motion F anchor g : Real) <=
        conflictCap anchor)
    (hjohnLoadCap : forall q g,
      (rigidCopyPolynomialJohnLoad motion F hdelta q g).toReal <=
        johnCoefficient *
          (volume (representativeTestBody delta hdelta q : Set Space)).toReal)
    (hconflictSum : forall anchor,
      (∑ g : motionChoice,
        (rigidConflictLoadNat motion F anchor g : Real)) <=
          (Fintype.card motionChoice : Real) * conflictMean anchor)
    (hjohnSum : forall q,
      (∑ g : motionChoice,
        (rigidCopyPolynomialJohnLoad motion F hdelta q g).toReal) <=
          (Fintype.card motionChoice : Real) * johnMean q)
    (hconflictScale : forall anchor,
      (repetitions : Real) * conflictMean anchor <= conflictCap anchor)
    (hjohnScale : forall q,
      (repetitions : Real) * johnMean q <=
        johnCoefficient *
          (volume (representativeTestBody delta hdelta q : Set Space)).toReal)
    (htailRoom :
      (Fintype.card
          (RigidJohnJointTest delta motionChoice iota hdelta) : Real) *
          Real.exp (Real.exp 1 - 1) < Real.exp A) :
    exists omega : Fin repetitions -> motionChoice,
      (forall anchor : motionChoice × iota,
        (∑ j, (rigidConflictLoadNat motion F anchor (omega j) : Real)) <=
          A * conflictCap anchor) ∧
      (forall q : CatalogueIndex delta hdelta,
        (∑ j,
          (rigidCopyPolynomialJohnLoad motion F hdelta q (omega j)).toReal) <=
          A * (johnCoefficient *
            (volume (representativeTestBody delta hdelta q : Set Space)).toReal)) := by
  classical
  let tests : Finset
      (RigidJohnJointTest delta motionChoice iota hdelta) := Finset.univ
  obtain ⟨omega, homega⟩ :=
    exists_product_choice_load_le_A_mul_cap
      tests repetitions (rigidJohnJointLoad motion F hdelta)
      (rigidJohnJointCap hdelta conflictCap johnCoefficient)
      (rigidJohnJointMean hdelta conflictMean johnMean) A
      (by
        intro t _ht
        cases t with
        | inl anchor => exact hconflictCap anchor
        | inr q =>
            exact mul_nonneg hjohnCoefficient ENNReal.toReal_nonneg)
      (by
        intro t _ht
        cases t with
        | inl anchor => exact hconflictMean anchor
        | inr q => exact hjohnMean q)
      (by
        intro t _ht g
        cases t with
        | inl anchor => exact Nat.cast_nonneg _
        | inr q => exact ENNReal.toReal_nonneg)
      (by
        intro t _ht g
        cases t with
        | inl anchor => exact hconflictLoadCap anchor g
        | inr q => exact hjohnLoadCap q g)
      (by
        intro t _ht
        cases t with
        | inl anchor => exact hconflictSum anchor
        | inr q => exact hjohnSum q)
      (by
        intro t _ht
        cases t with
        | inl anchor => exact hconflictScale anchor
        | inr q => exact hjohnScale q)
      (by simpa [tests] using htailRoom)
  refine ⟨omega, ?_, ?_⟩
  · intro anchor
    have h := homega (Sum.inl anchor) (by simp [tests])
    simpa [rigidJohnJointLoad, rigidJohnJointCap,
      FamilyStickyRandomFiniteChernoffV3.productLoad] using h
  · intro q
    have h := homega (Sum.inr q) (by simp [tests])
    simpa [rigidJohnJointLoad, rigidJohnJointCap,
      FamilyStickyRandomFiniteChernoffV3.productLoad] using h

/-- A real catalogue-load bound converts back to the exact ENNReal bound
consumed by the all-convex John adapter. -/
theorem sum_rigidCopyPolynomialJohnLoad_le_of_toReal
    {tau iota : Type}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : tau -> RigidMotion) (F : UniformTubeFamily delta iota)
    (hdelta : 0 < delta) (q : CatalogueIndex delta hdelta)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (hreal :
      (∑ j,
        (rigidCopyPolynomialJohnLoad motion F hdelta q j).toReal) <=
        coefficient *
          (volume (representativeTestBody delta hdelta q : Set Space)).toReal) :
    (∑ j, rigidCopyPolynomialJohnLoad motion F hdelta q j) <=
      ENNReal.ofReal coefficient *
        volume (representativeTestBody delta hdelta q : Set Space) := by
  have hleftTop :
      (∑ j, rigidCopyPolynomialJohnLoad motion F hdelta q j) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro j _hj
    unfold rigidCopyPolynomialJohnLoad
    exact (containedMass_lt_top _ _).ne
  have hrightTop :
      ENNReal.ofReal coefficient *
          volume (representativeTestBody delta hdelta q : Set Space) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp)
      (representativeTestBody delta hdelta q).isCompact.measure_lt_top.ne
  apply (ENNReal.toReal_le_toReal hleftTop hrightTop).mp
  rw [ENNReal.toReal_sum]
  · simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoefficient] using hreal
  · intro j _hj
    unfold rigidCopyPolynomialJohnLoad
    exact (containedMass_lt_top _ _).ne

#print axioms exists_rigidMotionTuple_joint_conflict_catalogue
#print axioms sum_rigidCopyPolynomialJohnLoad_le_of_toReal

end
end Family8FiniteRandomRigidMotionJohnJointSelectionV1
