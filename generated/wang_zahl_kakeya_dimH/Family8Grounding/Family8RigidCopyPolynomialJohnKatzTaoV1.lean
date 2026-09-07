import Family8Grounding.Family8FiniteRandomRigidMotionRefinementProducerV1
import Family8Grounding.Family8PolynomialJohnFrameBoxAllConvexV1
import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8RigidCopyPolynomialJohnKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GeneralizedFrostmanMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8FiniteRandomRigidMotionRefinementProducerV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8PolynomialJohnFrameBoxAllConvexV1
open Family8RestrictedActualDatumMassBridgeV1

noncomputable section

/-!
# Polynomial John tests for finite rigid copies

The pre-sampling occupied John catalogue is independent of the chosen rigid
motions.  This file identifies its test load on a literal product-indexed
rigid family with the sum of the loads of the individual copies.  Catalogue
control therefore upgrades to a genuine all-convex Katz--Tao estimate, and
that estimate descends exactly to every greedy-selected actual subtype.
-/

/-- Convex-body family of one rigidly moved copy. -/
def fixedRigidCopyBodyFamily
    {iota : Type} {delta : NNReal}
    [Fintype iota] [DecidableEq iota]
    (R : RigidMotion) (F : UniformTubeFamily delta iota) :
    ConvexFamily iota :=
  fun i => (rigidTube R (F.tubes i)).body

@[simp] theorem fixedRigidCopyBodyFamily_apply
    {iota : Type} {delta : NNReal}
    [Fintype iota] [DecidableEq iota]
    (R : RigidMotion) (F : UniformTubeFamily delta iota) (i : iota) :
    fixedRigidCopyBodyFamily R F i =
      (rigidTube R (F.tubes i)).body :=
  rfl

/-- Contained mass of the literal product family is exactly the sum of the
contained masses of its individual rigid copies. -/
theorem containedMass_indexedRigidCopyTubeFamily
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau -> RigidMotion) (F : UniformTubeFamily delta iota)
    (K : ConvexBody Space) :
    containedMass (indexedRigidCopyTubeFamily motion F).bodyFamily K =
      ∑ j, containedMass (fixedRigidCopyBodyFamily (motion j) F) K := by
  classical
  unfold containedMass containedIndices
  rw [← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  simp only [Finset.sum_filter]
  rfl

/-- Load of one rigid copy on one occupied John-catalogue test. -/
def rigidCopyPolynomialJohnLoad
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau -> RigidMotion) (F : UniformTubeFamily delta iota)
    (hdelta : 0 < delta) (q : CatalogueIndex delta hdelta) (j : tau) :
    ENNReal :=
  containedMass (fixedRigidCopyBodyFamily (motion j) F)
    (representativeTestBody delta hdelta q)

/-- The product load on a catalogue test is the sum of the per-copy loads. -/
theorem containedMass_catalogueTest_eq_sum_rigidCopyPolynomialJohnLoad
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau -> RigidMotion) (F : UniformTubeFamily delta iota)
    (hdelta : 0 < delta) (q : CatalogueIndex delta hdelta) :
    containedMass (indexedRigidCopyTubeFamily motion F).bodyFamily
        (representativeTestBody delta hdelta q) =
      ∑ j, rigidCopyPolynomialJohnLoad motion F hdelta q j := by
  rw [containedMass_indexedRigidCopyTubeFamily]
  rfl

/-- Uniform bounds for the polynomial catalogue loads imply all-convex
Katz--Tao control for the full product-indexed rigid family. -/
theorem isKatzTao_of_rigidCopy_polynomialJohnLoads
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau -> RigidMotion) (F : UniformTubeFamily delta iota)
    (hdelta : 0 < delta)
    (hunit : forall a : tau × iota,
      ((indexedRigidCopyTubeFamily motion F).tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 1)
    (A : ENNReal)
    (hloads : forall q : CatalogueIndex delta hdelta,
      (∑ j, rigidCopyPolynomialJohnLoad motion F hdelta q j) <=
        A * volume (representativeTestBody delta hdelta q : Set Space)) :
    IsKatzTao (A * johnCatalogueVolumeConstant)
      (indexedRigidCopyTubeFamily motion F).bodyFamily := by
  have hall := isKatzTao_of_polynomialJohnCatalogue hdelta
    (indexedRigidCopyTubeFamily motion F).tubes hunit A (by
      intro q
      change containedMass
          (indexedRigidCopyTubeFamily motion F).bodyFamily
          (representativeTestBody delta hdelta q) <=
        A * volume (representativeTestBody delta hdelta q : Set Space)
      rw [containedMass_catalogueTest_eq_sum_rigidCopyPolynomialJohnLoad]
      exact hloads q)
  exact hall

/-- Full-family Katz--Tao control descends with no further loss to the actual
subtype datum produced by greedy refinement. -/
theorem restrictIndexedRigidCopyDatum_isKatzTao
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau -> RigidMotion) (D : ActualTubeDatum delta iota)
    (selected : Finset (tau × iota)) (C : ENNReal)
    (hfull : IsKatzTao C
      (indexedRigidCopyTubeFamily motion D.family).bodyFamily) :
    IsKatzTao C
      (restrictActualTubeDatum (indexedRigidCopyDatum motion D)
        selected).family.bodyFamily := by
  intro K
  unfold IsKatzTaoAt
  rw [restrictActualTubeDatum_containedMass]
  exact hfull.on selected K

/-- The polynomial John load hypotheses can be consumed directly on the
greedy-selected actual datum. -/
theorem restrictIndexedRigidCopyDatum_isKatzTao_of_polynomialJohnLoads
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau -> RigidMotion) (D : ActualTubeDatum delta iota)
    (selected : Finset (tau × iota)) (hdelta : 0 < delta)
    (hunit : forall a : tau × iota,
      ((indexedRigidCopyTubeFamily motion D.family).tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 1)
    (A : ENNReal)
    (hloads : forall q : CatalogueIndex delta hdelta,
      (∑ j, rigidCopyPolynomialJohnLoad motion D.family hdelta q j) <=
        A * volume (representativeTestBody delta hdelta q : Set Space)) :
    IsKatzTao (A * johnCatalogueVolumeConstant)
      (restrictActualTubeDatum (indexedRigidCopyDatum motion D)
        selected).family.bodyFamily := by
  apply restrictIndexedRigidCopyDatum_isKatzTao motion D selected
  exact isKatzTao_of_rigidCopy_polynomialJohnLoads
    motion D.family hdelta hunit A hloads

#print axioms containedMass_indexedRigidCopyTubeFamily
#print axioms containedMass_catalogueTest_eq_sum_rigidCopyPolynomialJohnLoad
#print axioms isKatzTao_of_rigidCopy_polynomialJohnLoads
#print axioms restrictIndexedRigidCopyDatum_isKatzTao
#print axioms restrictIndexedRigidCopyDatum_isKatzTao_of_polynomialJohnLoads

end
end Family8RigidCopyPolynomialJohnKatzTaoV1
