import FamilyStickyGrounding.FamilyStickyDependentMultiscaleAllParentRandomMotionV1
import Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyRandomMotionAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTestDataV1
open FamilyStickyBoxCertifiedTubeTestDataV1
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyPaperRandomMotionNondegeneracyV1.ActualTubeTestData
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Actual hierarchy adapter for shared random motion

For an honest `MultiscaleTubeHierarchy`, a layer parent is an active index at
level `k+1`, and its child family is the literal parent fiber in the supplied
adjacent-step factorization.  This module constructs those tube families and
the all-parent layer data automatically.

The remaining inputs are source-level rather than final random-motion or
sub-sticky callbacks: finitely many box-certified tests for each parent,
child/parent scale bounds, and the cross-multiplied Appendix mean inequality
with the hierarchy's certified branching factor.  The actual fiber-card
`SourceMeanScale` is then derived from `fiber_card_le_loss_mul_branching`.
-/

/-- Box-certified finite tests, without any tube family attached. -/
structure BoxCertifiedTestFamily where
  testCard : Nat
  testBody : Fin testCard -> ConvexBody Space
  activeTests : Finset (Fin testCard)
  Cbox : NNReal
  side : Fin testCard -> Fin 3 -> NNReal
  certificate : forall K,
    BoxDimensionsCertificate Cbox (side K) (testBody K)

namespace BoxCertifiedTestFamily

/-- Attach the literal child fiber of one hierarchy parent. -/
def attachHierarchyFiber
    {depth : Nat} {nominalRadius : Nat -> NNReal}
    {Index : Nat -> Type*} [forall l, DecidableEq (Index l)]
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) (p : Index (l + 1))
    (G : BoxCertifiedTestFamily) :
    BoxCertifiedTubeTestData (H.effectiveRadius l) (Index l) where
  data := {
    tubes := (H.step l hl).combinatorics.index.fiber p
    tube := (H.effectiveFamily l).tubes
    testCard := G.testCard
    testBody := G.testBody
    activeTests := G.activeTests }
  Cbox := G.Cbox
  side := G.side
  certificate := G.certificate

@[simp] theorem attachHierarchyFiber_tubes
    {depth : Nat} {nominalRadius : Nat -> NNReal}
    {Index : Nat -> Type*} [forall l, DecidableEq (Index l)]
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) (p : Index (l + 1))
    (G : BoxCertifiedTestFamily) :
    (G.attachHierarchyFiber H l hl p).data.tubes =
      (H.step l hl).combinatorics.index.fiber p := rfl

end BoxCertifiedTestFamily

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- The actual all-parent layer at hierarchy step `k`. -/
def hierarchyLayer
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (tests : forall k : Fin depth, Index (k.1 + 1) -> BoxCertifiedTestFamily)
    (k : Fin depth) :
    AllParentLayerData (H.effectiveRadius k.1)
      (Index (k.1 + 1)) (Index k.1) where
  activeParents :=
    (H.step k.1 k.2).combinatorics.index.coarse
  parentData := fun p =>
    (tests k p).attachHierarchyFiber H k.1 k.2 p

@[simp] theorem hierarchyLayer_activeParents
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (tests : forall k : Fin depth, Index (k.1 + 1) -> BoxCertifiedTestFamily)
    (k : Fin depth) :
    (hierarchyLayer H tests k).activeParents =
      (H.step k.1 k.2).combinatorics.index.coarse := rfl

@[simp] theorem hierarchyLayer_parent_tubes
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (tests : forall k : Fin depth, Index (k.1 + 1) -> BoxCertifiedTestFamily)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    ((hierarchyLayer H tests k).parentData p).data.tubes =
      (H.step k.1 k.2).combinatorics.index.fiber p := rfl

/-- Source data still genuinely needed after the hierarchy creates all
parent fibers.  The mean inequality uses the certified upper branching
factor, not the already desired actual load or probability conclusion. -/
structure HierarchyRandomMotionGeometry
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) where
  tests : forall k : Fin depth,
    Index (k.1 + 1) -> BoxCertifiedTestFamily
  childRadius_pos : forall k : Fin depth, 0 < H.effectiveRadius k.1
  childRadius_le_half : forall k : Fin depth,
    H.effectiveRadius k.1 <= (2 : NNReal)⁻¹
  parentRadius_le_one : forall k : Fin depth,
    H.effectiveRadius (k.1 + 1) <= 1
  childRadius_le_side_zero : forall (k : Fin depth)
      (p : Index (k.1 + 1)),
    p ∈ (H.step k.1 k.2).combinatorics.index.coarse ->
    forall K, K ∈ (tests k p).activeTests ->
      H.effectiveRadius k.1 <= (tests k p).side K 0
  childRadius_le_side_one : forall (k : Fin depth)
      (p : Index (k.1 + 1)),
    p ∈ (H.step k.1 k.2).combinatorics.index.coarse ->
    forall K, K ∈ (tests k p).activeTests ->
      H.effectiveRadius k.1 <= (tests k p).side K 1
  branchingMeanScale : forall (k : Fin depth)
      (p : Index (k.1 + 1)),
    p ∈ (H.step k.1 k.2).combinatorics.index.coarse ->
    forall K, K ∈ (tests k p).activeTests ->
      (297 *
        ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
        ((tests k p).side K 0 : Real) *
        ((tests k p).side K 1 : Real)) *
          ((H.effectiveRadius k.1 : Real) ^ 2 / 2) <=
        ((((tests k p).Cbox⁻¹ : NNReal) : Real) ^ 3 *
          ∏ i, ((tests k p).side K i : Real)) *
            (H.effectiveRadius (k.1 + 1) : Real) ^ 2

namespace HierarchyRandomMotionGeometry

variable (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)

/-- Branching control turns the source-level upper-card inequality into the
exact `SourceMeanScale` required by the random-motion endpoint. -/
theorem fiber_sourceMeanScale
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (H.step k.1 k.2).combinatorics.index.coarse)
    (K : Fin (G.tests k p).testCard)
    (hK : K ∈ (G.tests k p).activeTests) :
    SourceMeanScale
      ((G.tests k p).attachHierarchyFiber H k.1 k.2 p).data
      (G.tests k p).Cbox (G.tests k p).side
      (H.effectiveRadius (k.1 + 1)) K := by
  let C := (H.step k.1 k.2).combinatorics
  have hcardNat : (C.index.fiber p).card <= C.branchingFactor := by
    exact C.fiber_card_le_loss_mul_branching p hp
  have hcard : ((C.index.fiber p).card : Real) <=
      (C.branchingFactor : Real) := by
    exact_mod_cast hcardNat
  unfold SourceMeanScale
  change
    (297 * ((C.index.fiber p).card : Real) *
      ((G.tests k p).side K 0 : Real) *
      ((G.tests k p).side K 1 : Real)) *
        ((H.effectiveRadius k.1 : Real) ^ 2 / 2) <= _
  calc
    (297 * ((C.index.fiber p).card : Real) *
      ((G.tests k p).side K 0 : Real) *
      ((G.tests k p).side K 1 : Real)) *
        ((H.effectiveRadius k.1 : Real) ^ 2 / 2) <=
      (297 * (C.branchingFactor : Real) *
        ((G.tests k p).side K 0 : Real) *
        ((G.tests k p).side K 1 : Real)) *
          ((H.effectiveRadius k.1 : Real) ^ 2 / 2) := by
      gcongr
    _ <= _ := G.branchingMeanScale k p hp K hK

/-- Fully assembled dependent-index source data for all hierarchy steps. -/
def toDependentSource :
    DependentMultiscaleAllParentSourceData depth
      (fun k => Index (k.1 + 1)) (fun k => Index k.1) where
  delta := fun k => H.effectiveRadius k.1
  motionRadius := fun k => H.effectiveRadius (k.1 + 1)
  layer := hierarchyLayer H G.tests
  delta_le_half := G.childRadius_le_half
  delta_pos := G.childRadius_pos
  delta_le_motionRadius := fun k => H.effectiveRadius_step_le k.1 k.2
  delta_le_side_zero := by
    intro k q hq
    have hq' := ((hierarchyLayer H G.tests k).mem_activeTests_iff q).1 hq
    exact G.childRadius_le_side_zero k q.1 hq'.1 q.2 hq'.2
  delta_le_side_one := by
    intro k q hq
    have hq' := ((hierarchyLayer H G.tests k).mem_activeTests_iff q).1 hq
    exact G.childRadius_le_side_one k q.1 hq'.1 q.2 hq'.2
  sourceMeanScale := by
    intro k q hq
    have hq' := ((hierarchyLayer H G.tests k).mem_activeTests_iff q).1 hq
    exact fiber_sourceMeanScale H G k q.1 hq'.1 q.2 hq'.2

/-- The first hierarchy endpoint: all per-layer data and exact source means
are produced internally, then the dependent multiscale theorem is invoked. -/
theorem exists_output : Nonempty G.toDependentSource.Output :=
  DependentMultiscaleAllParentSourceData.exists_output G.toDependentSource

#print axioms fiber_sourceMeanScale
#print axioms toDependentSource
#print axioms exists_output

end HierarchyRandomMotionGeometry

end
end FamilyStickyHierarchyRandomMotionAdapterV1
