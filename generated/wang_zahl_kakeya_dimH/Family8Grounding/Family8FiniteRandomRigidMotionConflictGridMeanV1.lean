import Family8Grounding.Family8FiniteRandomRigidMotionAutomaticMeansV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionConflictGridMeanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionAutomaticMeansV1
open FamilyStickyRandomTranslationIncidenceV1

noncomputable section

/-!
# Conflict means from literal finite-grid incidence counts

The canonical conflict mean is controlled by a genuinely local geometric
quantity: for each source tube, how many finite rigid-grid choices make it
conflict with the fixed anchor.  This is exact finite double counting, not a
probabilistic callback.
-/

/-- Exact double count between loads per grid motion and conflicting grid
choices per source tube. -/
theorem sum_rigidConflictLoadNat_eq_sum_rigidConflictChoiceCount
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) :
    (∑ g : motionChoice, rigidConflictLoadNat motion F anchor g) =
      ∑ i : iota, rigidConflictChoiceCount motion F anchor i := by
  let M := rigidConflictIncidenceModel motion F
  have h := M.sum_loadNat_eq_sum_gridHitsTube anchor
  simpa only [M, rigidConflictIncidenceModel_tubes,
    rigidConflictIncidenceModel_loadNat,
    rigidConflictIncidenceModel_gridHitsTube] using h

/-- A uniform local choice-count bound gives the explicit canonical-mean
bound used by the one-shot random selector. -/
theorem rigidConflictFiniteMean_le_card_mul_choiceBudget_div_card
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (choiceBudget : motionChoice × iota -> Nat)
    (hgrid : forall anchor i,
      rigidConflictChoiceCount motion F anchor i <= choiceBudget anchor)
    (anchor : motionChoice × iota) :
    rigidConflictFiniteMean motion F anchor <=
      ((Fintype.card iota : Real) * (choiceBudget anchor : Real)) /
        (Fintype.card motionChoice : Real) := by
  have hsumNat :
      (∑ g : motionChoice, rigidConflictLoadNat motion F anchor g) <=
        Fintype.card iota * choiceBudget anchor := by
    rw [sum_rigidConflictLoadNat_eq_sum_rigidConflictChoiceCount]
    calc
      (∑ i : iota, rigidConflictChoiceCount motion F anchor i) <=
          ∑ _i : iota, choiceBudget anchor := by
        exact Finset.sum_le_sum fun i _hi => hgrid anchor i
      _ = Fintype.card iota * choiceBudget anchor := by simp
  have hsumReal :
      (∑ g : motionChoice,
        (rigidConflictLoadNat motion F anchor g : Real)) <=
          (Fintype.card iota : Real) * (choiceBudget anchor : Real) := by
    exact_mod_cast hsumNat
  have hcardPos : 0 < (Fintype.card motionChoice : Real) := by
    exact_mod_cast Fintype.card_pos
  unfold rigidConflictFiniteMean
  exact (div_le_div_iff_of_pos_right hcardPos).2 hsumReal

/-- A cross-multiplied local grid budget is sufficient for the conflict
scale premise of the automatic-mean Frostman producer. -/
theorem repetitions_mul_rigidConflictFiniteMean_le_of_gridBudget
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (choiceBudget : motionChoice × iota -> Nat)
    (repetitions : Nat) (conflictCap : motionChoice × iota -> Real)
    (hgrid : forall anchor i,
      rigidConflictChoiceCount motion F anchor i <= choiceBudget anchor)
    (hscale : forall anchor,
      (repetitions : Real) *
          (((Fintype.card iota : Real) * (choiceBudget anchor : Real)) /
            (Fintype.card motionChoice : Real)) <=
        conflictCap anchor) :
    forall anchor,
      (repetitions : Real) *
          rigidConflictFiniteMean motion F anchor <=
        conflictCap anchor := by
  intro anchor
  exact (mul_le_mul_of_nonneg_left
    (rigidConflictFiniteMean_le_card_mul_choiceBudget_div_card
      motion F choiceBudget hgrid anchor)
    (Nat.cast_nonneg repetitions)).trans (hscale anchor)

#print axioms sum_rigidConflictLoadNat_eq_sum_rigidConflictChoiceCount
#print axioms rigidConflictFiniteMean_le_card_mul_choiceBudget_div_card
#print axioms repetitions_mul_rigidConflictFiniteMean_le_of_gridBudget

end
end Family8FiniteRandomRigidMotionConflictGridMeanV1
