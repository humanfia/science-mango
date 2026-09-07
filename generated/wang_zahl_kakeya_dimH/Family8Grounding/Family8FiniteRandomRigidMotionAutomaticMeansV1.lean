import Family8Grounding.Family8FiniteRandomRigidMotionJohnFrostmanProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionAutomaticMeansV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8RigidCopyPolynomialJohnKatzTaoV1
open Family8FiniteRandomRigidMotionJohnFrostmanProducerV1

noncomputable section

/-!
# Canonical finite means for random rigid-motion tests

The random selector should not receive arbitrary `conflictMean` and
`johnMean` functions together with callbacks asserting that they dominate
the corresponding finite sums.  For a nonempty finite motion grid, the
canonical means below make both sum conditions exact identities.
-/

/-- Exact uniform-grid mean of the conflict load at one anchor. -/
def rigidConflictFiniteMean
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) : Real :=
  (∑ g : motionChoice,
    (rigidConflictLoadNat motion F anchor g : Real)) /
      (Fintype.card motionChoice : Real)

/-- Exact uniform-grid mean of the John catalogue load at one test. -/
def rigidJohnFiniteMean
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) : Real :=
  (∑ g : motionChoice,
    (rigidCopyPolynomialJohnLoad motion F hdelta q g).toReal) /
      (Fintype.card motionChoice : Real)

theorem rigidConflictFiniteMean_nonneg
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) :
    0 <= rigidConflictFiniteMean motion F anchor := by
  unfold rigidConflictFiniteMean
  positivity

theorem rigidJohnFiniteMean_nonneg
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) :
    0 <= rigidJohnFiniteMean motion F hdelta q := by
  unfold rigidJohnFiniteMean
  positivity

theorem sum_rigidConflictLoad_eq_card_mul_finiteMean
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota)
    (anchor : motionChoice × iota) :
    (∑ g : motionChoice,
      (rigidConflictLoadNat motion F anchor g : Real)) =
        (Fintype.card motionChoice : Real) *
          rigidConflictFiniteMean motion F anchor := by
  unfold rigidConflictFiniteMean
  have hcard : (Fintype.card motionChoice : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem sum_rigidJohnLoad_eq_card_mul_finiteMean
    {motionChoice iota : Type}
    [Fintype motionChoice] [Nonempty motionChoice]
    [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) :
    (∑ g : motionChoice,
      (rigidCopyPolynomialJohnLoad motion F hdelta q g).toReal) =
        (Fintype.card motionChoice : Real) *
          rigidJohnFiniteMean motion F hdelta q := by
  unfold rigidJohnFiniteMean
  have hcard : (Fintype.card motionChoice : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

#print axioms rigidConflictFiniteMean_nonneg
#print axioms rigidJohnFiniteMean_nonneg
#print axioms sum_rigidConflictLoad_eq_card_mul_finiteMean
#print axioms sum_rigidJohnLoad_eq_card_mul_finiteMean

end
end Family8FiniteRandomRigidMotionAutomaticMeansV1
