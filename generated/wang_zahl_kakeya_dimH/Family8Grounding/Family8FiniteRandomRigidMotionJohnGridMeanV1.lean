import Family8Grounding.Family8FiniteRandomRigidMotionAutomaticMeansV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionJohnGridMeanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8RigidCopyPolynomialJohnKatzTaoV1
open Family8FiniteRandomRigidMotionAutomaticMeansV1

noncomputable section

/-!
# John means from weighted finite-grid incidences

For a fixed catalogue body and source tube, count the grid motions whose
rigid image is contained in that body.  Double counting with the actual tube
volume as weight identifies the exact John mean used by the joint selector.
-/

/-- Number of finite rigid-grid choices which move one fixed source tube
inside a fixed polynomial John catalogue body. -/
def rigidJohnChoiceCount
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) (i : iota) : Nat := by
  classical
  exact ((Finset.univ : Finset motionChoice).filter fun g =>
    (rigidTube (motion g) (F.tubes i)).carrier ⊆
      (representativeTestBody delta hdelta q : Set Space)).card

/-- The exact grid-incidence mass for one John catalogue body. -/
def rigidJohnGridMass
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) : ENNReal :=
  ∑ i : iota,
    (rigidJohnChoiceCount motion F hdelta q i : ENNReal) *
      volume (F.tubes i).carrier

/-- Exact weighted double count: sum first over grid motions or first over
source tubes. -/
theorem sum_rigidCopyPolynomialJohnLoad_eq_rigidJohnGridMass
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) :
    (∑ g : motionChoice,
      rigidCopyPolynomialJohnLoad motion F hdelta q g) =
        rigidJohnGridMass motion F hdelta q := by
  classical
  let K := representativeTestBody delta hdelta q
  calc
    (∑ g : motionChoice,
        rigidCopyPolynomialJohnLoad motion F hdelta q g) =
        ∑ g : motionChoice, ∑ i : iota,
          if (rigidTube (motion g) (F.tubes i)).carrier ⊆ (K : Set Space)
          then volume (rigidTube (motion g) (F.tubes i)).carrier
          else 0 := by
      apply Finset.sum_congr rfl
      intro g _hg
      unfold rigidCopyPolynomialJohnLoad containedMass containedIndices
      rw [Finset.sum_filter]
      simp only [fixedRigidCopyBodyFamily_apply, Tube.coe_body, K]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl
    _ = ∑ i : iota, ∑ g : motionChoice,
          if (rigidTube (motion g) (F.tubes i)).carrier ⊆ (K : Set Space)
          then volume (rigidTube (motion g) (F.tubes i)).carrier
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : iota,
          (rigidJohnChoiceCount motion F hdelta q i : ENNReal) *
            volume (F.tubes i).carrier := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [rigidTube_volume]
      unfold rigidJohnChoiceCount
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl
    _ = rigidJohnGridMass motion F hdelta q := by
      rfl

/-- The real canonical John mean is exactly the to-real weighted grid mass
divided by the number of grid motions. -/
theorem rigidJohnFiniteMean_eq_gridMass_toReal_div_card
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) :
    rigidJohnFiniteMean motion F hdelta q =
      (rigidJohnGridMass motion F hdelta q).toReal /
        (Fintype.card motionChoice : Real) := by
  unfold rigidJohnFiniteMean
  congr 1
  rw [← ENNReal.toReal_sum]
  · rw [sum_rigidCopyPolynomialJohnLoad_eq_rigidJohnGridMass]
  · intro g _hg
    unfold rigidCopyPolynomialJohnLoad
    exact (containedMass_lt_top _ _).ne

/-- A uniform local John choice-count bound controls the exact weighted grid
mass by that count times the actual source-family volume. -/
theorem rigidJohnGridMass_le_budget_mul_familyVolume
    {motionChoice iota : Type}
    [Fintype motionChoice] [DecidableEq motionChoice]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (F : UniformTubeFamily delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) (choiceBudget : Nat)
    (hgrid : forall i,
      rigidJohnChoiceCount motion F hdelta q i <= choiceBudget) :
    rigidJohnGridMass motion F hdelta q <=
      (choiceBudget : ENNReal) * familyVolume F.bodyFamily := by
  unfold rigidJohnGridMass familyVolume
  calc
    (∑ i : iota,
        (rigidJohnChoiceCount motion F hdelta q i : ENNReal) *
          volume (F.tubes i).carrier) <=
        ∑ i : iota,
          (choiceBudget : ENNReal) * volume (F.tubes i).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      gcongr
      exact_mod_cast hgrid i
    _ = (choiceBudget : ENNReal) *
          ∑ i : iota, volume (F.bodyFamily i : Set Space) := by
      simp only [UniformTubeFamily.bodyFamily_apply, Tube.coe_body]
      rw [Finset.mul_sum]
    _ = (choiceBudget : ENNReal) *
          ∑ i : iota, volume (F.bodyFamily i : Set Space) := rfl

#print axioms sum_rigidCopyPolynomialJohnLoad_eq_rigidJohnGridMass
#print axioms rigidJohnFiniteMean_eq_gridMass_toReal_div_card
#print axioms rigidJohnGridMass_le_budget_mul_familyVolume

end
end Family8FiniteRandomRigidMotionJohnGridMeanV1
