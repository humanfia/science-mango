import Family8Grounding.Family8GeneralizedFrostmanMultiplicityV1
import FamilyStickyGrounding.FamilyStickyActualTubeTranslationV1
import FamilyStickyGrounding.FamilyStickyRandomTranslationGridAdapterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionIncidenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8GeneralizedFrostmanMultiplicityV1
open FamilyStickyActualTubeTranslationV1
open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTranslationIncidenceV1
open FamilyStickyRandomTranslationGridAdapterV1

noncomputable section

/-!
# Finite random rigid-motion incidences

This is the finite probabilistic interface missing between the literal rigid
copies in `Family8GeneralizedFrostmanMultiplicityV1` and a quantitative
cross-copy refinement.  A test is an actual possible moved source tube.  Its
load under one further motion is the number of source tubes which fail the
repository's `EssentiallyDistinct` relation against that anchor.

The existing finite Chernoff engine is relation-generic despite its historic
`TranslationIncidenceModel` name.  We instantiate it with genuine affine
isometries.  Its hypotheses remain local: a one-motion load cap and, for each
fixed source tube/anchor, the number of grid motions producing a conflict.
No good tuple, refined family, or Frostman conclusion is supplied as data.
-/

/-- Ordinary translation is a special genuine rigid motion. -/
def translationRigidMotion (v : Space) : RigidMotion :=
  AffineIsometryEquiv.constVAdd Real Space v

@[simp] theorem translationRigidMotion_apply (v x : Space) :
    translationRigidMotion v x = v + x := by
  simp [translationRigidMotion]

/-- The generic rigid action exactly extends the repository's pre-existing
actual tube translation. -/
theorem rigidTube_translationRigidMotion_carrier
    {delta : NNReal} (T : Tube delta) (v : Space) :
    (rigidTube (translationRigidMotion v) T).carrier =
      (translateTube T v).carrier := by
  rw [rigidTube_carrier, translateTube_carrier]
  congr 1

/-- Number of source tubes moved by `g` that conflict with one fixed moved
anchor `(g0,i0)`. -/
def rigidConflictLoadNat
    {motionChoice iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) (g : motionChoice) : Nat := by
  classical
  exact ((Finset.univ : Finset iota).filter fun i =>
    ¬ EssentiallyDistinct
      (rigidTube (motion g) (F.tubes i))
      (rigidTube (motion anchor.1) (F.tubes anchor.2))).card

/-- Number of grid motions which make one fixed source tube conflict with a
fixed possible anchor.  This is the local geometric incidence quantity. -/
def rigidConflictChoiceCount
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) (i : iota) : Nat := by
  classical
  exact ((Finset.univ : Finset motionChoice).filter fun g =>
    ¬ EssentiallyDistinct
      (rigidTube (motion g) (F.tubes i))
      (rigidTube (motion anchor.1) (F.tubes anchor.2))).card

/-- The literal conflict relation as a finite incidence model. -/
def rigidConflictIncidenceModel
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) :
    TranslationIncidenceModel motionChoice iota (motionChoice × iota) := by
  classical
  exact
    { tubes := Finset.univ
      tests := Finset.univ
      hits := fun g i anchor => decide (¬ EssentiallyDistinct
        (rigidTube (motion g) (F.tubes i))
        (rigidTube (motion anchor.1) (F.tubes anchor.2))) }

@[simp] theorem rigidConflictIncidenceModel_tubes
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) :
    (rigidConflictIncidenceModel motion F).tubes = Finset.univ := rfl

@[simp] theorem rigidConflictIncidenceModel_tests
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) :
    (rigidConflictIncidenceModel motion F).tests = Finset.univ := rfl

/-- The abstract one-coordinate load is the actual rigid-conflict count. -/
theorem rigidConflictIncidenceModel_loadNat
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) (g : motionChoice) :
    (rigidConflictIncidenceModel motion F).loadNat anchor g =
      rigidConflictLoadNat motion F anchor g := by
  classical
  simp [TranslationIncidenceModel.loadNat,
    rigidConflictIncidenceModel, rigidConflictLoadNat]

theorem rigidConflictIncidenceModel_load
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) (g : motionChoice) :
    (rigidConflictIncidenceModel motion F).load anchor g =
      (rigidConflictLoadNat motion F anchor g : Real) := by
  rw [TranslationIncidenceModel.load,
    rigidConflictIncidenceModel_loadNat]

/-- The abstract per-source incidence count is the literal number of rigid
grid choices creating a conflict. -/
theorem rigidConflictIncidenceModel_gridHitsTube
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) (i : iota) :
    (rigidConflictIncidenceModel motion F).gridHitsTube anchor i =
      rigidConflictChoiceCount motion F anchor i := by
  classical
  simp [TranslationIncidenceModel.gridHitsTube,
    rigidConflictIncidenceModel, rigidConflictChoiceCount]

/-- A fully finite Chernoff selection of a tuple of actual rigid motions.
Every possible moved anchor is controlled simultaneously, so in particular
every tube which occurs in the selected tuple is controlled. -/
theorem exists_rigidMotionTuple_conflictLoad_le
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (choiceBudget : motionChoice × iota -> Nat)
    (repetitions conflictThreshold : Nat)
    {cap mean lambda : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hloadCap : forall anchor g,
      (rigidConflictLoadNat motion F anchor g : Real) <= cap)
    (hgrid : forall anchor i,
      rigidConflictChoiceCount motion F anchor i <= choiceBudget anchor)
    (hbalance : forall anchor,
      (Fintype.card iota : Real) * (choiceBudget anchor : Real) <=
        (Fintype.card motionChoice : Real) * mean)
    (hnumerical :
      (Fintype.card (motionChoice × iota) : Real) *
          ((Fintype.card motionChoice : Real) *
            (1 + (mean / cap) *
              (Real.exp (lambda * cap) - 1))) ^ repetitions <
        ((Finset.univ : Finset (Fin repetitions -> motionChoice)).card : Real) *
          Real.exp (lambda * (conflictThreshold : Real))) :
    exists omega : Fin repetitions -> motionChoice,
      forall anchor : motionChoice × iota,
        (∑ j, rigidConflictLoadNat motion F anchor (omega j)) <=
          conflictThreshold := by
  classical
  let M := rigidConflictIncidenceModel motion F
  obtain ⟨omega, homega⟩ :=
    FamilyStickyRandomTranslationGridAdapterV1.TranslationIncidenceModel.exists_product_choice_load_le_of_gridIncidence M
      choiceBudget repetitions hcap hlambda
      (fun anchor _hanchor g => by
        rw [rigidConflictIncidenceModel_load]
        exact hloadCap anchor g)
      (fun anchor _hanchor i _hi => by
        rw [rigidConflictIncidenceModel_gridHitsTube]
        exact hgrid anchor i)
      (fun anchor _hanchor => hbalance anchor)
      (by simpa [M] using hnumerical)
  refine ⟨omega, ?_⟩
  intro anchor
  have hreal := homega anchor (by simp [M])
  have hreal' :
      (∑ j, (rigidConflictLoadNat motion F anchor (omega j) : Real)) <=
        (conflictThreshold : Real) := by
    simpa [productLoad, M, rigidConflictIncidenceModel_load] using hreal
  exact_mod_cast hreal'

/-- Conflict relation on the product-indexed copied family. -/
def rigidCopyConflict
    {tau iota : Type}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : tau -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (a b : tau × iota) : Prop :=
  ¬ EssentiallyDistinct
    ((indexedRigidCopyTubeFamily motion F).tubes a)
    ((indexedRigidCopyTubeFamily motion F).tubes b)

/-- All conflicting product indices, without adding the anchor separately. -/
def rigidCopyConflictIndices
    {tau iota : Type}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : tau -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (a : tau × iota) : Finset (tau × iota) := by
  classical
  exact Finset.univ.filter fun b => rigidCopyConflict motion F b a

/-- Product conflict counts split exactly into the one-motion loads used by
the Chernoff selector. -/
theorem rigidCopyConflictIndices_card_eq_sum_load
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (omega : Fin repetitions -> motionChoice)
    (a : Fin repetitions × iota) :
    (rigidCopyConflictIndices (fun j => motion (omega j)) F a).card =
      ∑ j, rigidConflictLoadNat motion F (omega a.1, a.2) (omega j) := by
  classical
  unfold rigidCopyConflictIndices rigidConflictLoadNat rigidCopyConflict
  rw [Finset.card_eq_sum_ones]
  rw [← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  simp only [indexedRigidCopyTubeFamily_tubes]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : EssentiallyDistinct
      (rigidTube (motion (omega j)) (F.tubes i))
      (rigidTube (motion (omega a.1)) (F.tubes a.2)) <;> simp [h]

/-- The Chernoff output gives a uniform bound for every actual anchor in the
selected product family. -/
theorem rigidCopyConflictIndices_card_le_of_tupleLoad
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions conflictThreshold : Nat}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (omega : Fin repetitions -> motionChoice)
    (hload : forall anchor : motionChoice × iota,
      (∑ j, rigidConflictLoadNat motion F anchor (omega j)) <=
        conflictThreshold)
    (a : Fin repetitions × iota) :
    (rigidCopyConflictIndices (fun j => motion (omega j)) F a).card <=
      conflictThreshold := by
  rw [rigidCopyConflictIndices_card_eq_sum_load]
  exact hload (omega a.1, a.2)

#print axioms rigidTube_translationRigidMotion_carrier
#print axioms rigidConflictIncidenceModel_loadNat
#print axioms rigidConflictIncidenceModel_gridHitsTube
#print axioms exists_rigidMotionTuple_conflictLoad_le
#print axioms rigidCopyConflictIndices_card_eq_sum_load
#print axioms rigidCopyConflictIndices_card_le_of_tupleLoad

end
end Family8FiniteRandomRigidMotionIncidenceV1
