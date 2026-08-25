import FamilyStickyGrounding.FamilyStickyHierarchyRandomMotionAdapterV1
import FamilyStickyGrounding.FamilyStickyRandomModelTubeCollisionGridV1

set_option autoImplicit false

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyCollisionTestGeometryProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.BoxCertifiedTestFamily
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyRandomModelTubeCollisionGridV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Automatic hierarchy geometry from actual collision-tube tests

For each literal parent fibre, start with the one-point zero-motion grid and
apply the already proved `collisionGrid` constructor.  Its finite tests are
exactly the bodies of the `100 delta` tubes obtained from the actual child
tubes in that fibre.  The aligned-frame theorem supplies their complete
two-sided `BoxDimensionsCertificate 2` data.

This removes the caller-supplied test catalogue, both transverse side lower
bounds, and the general box-dependent mean inequality.  The latter becomes
one explicit scalar hierarchy condition.  No load, random choice,
probability estimate, or desired endpoint is an input here.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- The literal hierarchy parent fibre, before adding collision tests.  Its
dummy test suite is empty; `collisionGrid` replaces that suite completely. -/
def hierarchyFiberSeedData
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    ActualTubeTestData (H.effectiveRadius k.1) (Index k.1) where
  tubes := (H.step k.1 k.2).combinatorics.index.fiber p
  tube := (H.effectiveFamily k.1).tubes
  testCard := 0
  testBody := fun K => Fin.elim0 K
  activeTests := ∅

/-- The one-point zero-motion grid on one actual hierarchy fibre. -/
def hierarchyFiberSeedGrid
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    ActualTubeTranslationGrid (H.effectiveRadius k.1) Unit (Index k.1) :=
  (hierarchyFiberSeedData H k p).seedGrid

@[simp] theorem hierarchyFiberSeedGrid_tubes
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    (hierarchyFiberSeedGrid H k p).tubes =
      (H.step k.1 k.2).combinatorics.index.fiber p := rfl

/-- Actual `100 delta` collision bodies, equipped with the explicit aligned
`2`-box certificates. -/
noncomputable def hierarchyCollisionTestFamily
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hsmall : hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹) :
    BoxCertifiedTestFamily where
  testCard := (collisionGrid (hierarchyFiberSeedGrid H k p)).testCard
  testBody := (collisionGrid (hierarchyFiberSeedGrid H k p)).testBody
  activeTests := (collisionGrid (hierarchyFiberSeedGrid H k p)).activeTests
  Cbox := 2
  side := collisionSide (hierarchyFiberSeedGrid H k p)
  certificate := fun K =>
    Classical.choice
      ((collisionGrid_hasBoxDimensions
        (hierarchyFiberSeedGrid H k p) hsmall K).nonempty_boxDimensionsCertificate)

@[simp] theorem hierarchyCollisionTestFamily_activeTests
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hsmall : hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹) :
    (hierarchyCollisionTestFamily H k p hsmall).activeTests = Finset.univ := rfl

@[simp] theorem hierarchyCollisionTestFamily_Cbox
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hsmall : hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹) :
    (hierarchyCollisionTestFamily H k p hsmall).Cbox = 2 := rfl

@[simp] theorem hierarchyCollisionTestFamily_side
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hsmall : hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹) :
    (hierarchyCollisionTestFamily H k p hsmall).side =
      collisionSide (hierarchyFiberSeedGrid H k p) := rfl

theorem childRadius_le_collisionSide_zero
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hsmall : hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹)
    (K : Fin (hierarchyCollisionTestFamily H k p hsmall).testCard) :
    H.effectiveRadius k.1 <=
      (hierarchyCollisionTestFamily H k p hsmall).side K 0 := by
  exact delta_le_collisionSide_zero (hierarchyFiberSeedGrid H k p) K

theorem childRadius_le_collisionSide_one
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hsmall : hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹)
    (K : Fin (hierarchyCollisionTestFamily H k p hsmall).testCard) :
    H.effectiveRadius k.1 <=
      (hierarchyCollisionTestFamily H k p hsmall).side K 1 := by
  exact delta_le_collisionSide_one (hierarchyFiberSeedGrid H k p) K

/-- After specializing the collision sides, the general Appendix mean
inequality reduces to this single source-level scalar comparison. -/
def HierarchyCollisionBranchingScale
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop :=
  forall k : Fin depth,
    1188 * ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
        (H.effectiveRadius k.1 : Real) ^ 2 <=
      (1 + 200 * (H.effectiveRadius k.1 : Real)) *
        (H.effectiveRadius (k.1 + 1) : Real) ^ 2

/-- Minimal compatibility input for the existing analytic hierarchy
certificate after choosing the collision-tube test catalogue internally. -/
structure HierarchyCollisionTestSourceGeometry
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) where
  childRadius_pos : forall k : Fin depth, 0 < H.effectiveRadius k.1
  hundredRadius_le_half : forall k : Fin depth,
    hundredRadius (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹
  parentRadius_le_one : forall k : Fin depth,
    H.effectiveRadius (k.1 + 1) <= 1
  branchingScale : HierarchyCollisionBranchingScale H

namespace HierarchyCollisionTestSourceGeometry

variable (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (S : HierarchyCollisionTestSourceGeometry H)

include S in
theorem childRadius_le_half (k : Fin depth) :
    H.effectiveRadius k.1 <= (2 : NNReal)⁻¹ := by
  calc
    H.effectiveRadius k.1 <= hundredRadius (H.effectiveRadius k.1) := by
      rw [hundredRadius]
      calc
        H.effectiveRadius k.1 = 1 * H.effectiveRadius k.1 := by simp
        _ <= 100 * H.effectiveRadius k.1 := by
          gcongr
          norm_num
    _ <= (2 : NNReal)⁻¹ :=
      HierarchyCollisionTestSourceGeometry.hundredRadius_le_half S k

/-- The explicit scalar condition is exactly the old box-dependent
`branchingMeanScale` after substituting sides
`200 delta, 200 delta, 1 + 200 delta`. -/
theorem branchingMeanScale
    (k : Fin depth) (p : Index (k.1 + 1))
    (_hp : p ∈ (H.step k.1 k.2).combinatorics.index.coarse)
    (K : Fin (hierarchyCollisionTestFamily H k p
      (S.hundredRadius_le_half k)).testCard)
    (_hK : K ∈ (hierarchyCollisionTestFamily H k p
      (S.hundredRadius_le_half k)).activeTests) :
    (297 *
      ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
      (((hierarchyCollisionTestFamily H k p
        (S.hundredRadius_le_half k)).side K 0) : Real) *
      (((hierarchyCollisionTestFamily H k p
        (S.hundredRadius_le_half k)).side K 1) : Real)) *
        ((H.effectiveRadius k.1 : Real) ^ 2 / 2) <=
      (((((hierarchyCollisionTestFamily H k p
        (S.hundredRadius_le_half k)).Cbox⁻¹ : NNReal) : Real) ^ 3 *
        ∏ i, (((hierarchyCollisionTestFamily H k p
          (S.hundredRadius_le_half k)).side K i) : Real)) *
        (H.effectiveRadius (k.1 + 1) : Real) ^ 2) := by
  have hscale := S.branchingScale k
  have hfactor :
      0 <= ((200 * (H.effectiveRadius k.1 : Real)) ^ 2 / 8) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hscale hfactor
  simp only [hierarchyCollisionTestFamily, collisionSide,
    Tube.frameBoxSides, hundredRadius, Fin.prod_univ_three, NNReal.coe_inv,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  norm_num
  ring_nf at hmul ⊢
  exact hmul

/-- Construct the existing hierarchy geometry object with the complete test
catalogue and side bounds filled automatically. -/
noncomputable def toHierarchyRandomMotionGeometry :
    HierarchyRandomMotionGeometry H where
  tests := fun k p =>
    hierarchyCollisionTestFamily H k p (S.hundredRadius_le_half k)
  childRadius_pos := S.childRadius_pos
  childRadius_le_half := childRadius_le_half H S
  parentRadius_le_one := S.parentRadius_le_one
  childRadius_le_side_zero := by
    intro k p hp K hK
    exact childRadius_le_collisionSide_zero H k p
      (S.hundredRadius_le_half k) K
  childRadius_le_side_one := by
    intro k p hp K hK
    exact childRadius_le_collisionSide_one H k p
      (S.hundredRadius_le_half k) K
  branchingMeanScale := branchingMeanScale H S

#print axioms hierarchyFiberSeedGrid_tubes
#print axioms hierarchyCollisionTestFamily_activeTests
#print axioms childRadius_le_collisionSide_zero
#print axioms childRadius_le_collisionSide_one
#print axioms childRadius_le_half
#print axioms branchingMeanScale
#print axioms toHierarchyRandomMotionGeometry

end HierarchyCollisionTestSourceGeometry

end
end FamilyStickyHierarchyCollisionTestGeometryProducerV1
