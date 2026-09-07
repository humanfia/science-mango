import Family8Grounding.Family8CellularActualDyadicRegularizationV1
import Family8Grounding.Family8CellularPositiveParentCellEdgeMassV1
import Mathlib.Tactic

/-!
# Apply numeric REG1/R2 to the genuine positive parent--cell graph

The positive graph has exactly the source shading mass.  Consequently a
positive source shading makes that graph nonempty, and every edge weight is
finite because it is bounded by the finite total shading mass.  Thus the
generic numeric REG1/R2 constructor applies without any additional bucket
or finiteness oracle.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CellularPositiveGraphActualRegularizationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CellularEqualVolumeEdgeMassV1
open Family8CellularJointFactoringFiniteCoreV1
open Family8CellularJointShadingFromEdgesV1
open Family8CellularPositiveParentCellEdgeMassV1
open Family8CellularActualDyadicRegularizationV1

noncomputable section

variable {child parent cell : Type*}
  [Fintype child] [DecidableEq child]
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]
  {F : ConvexFamily child}

/-- Positive total source mass forces the positive parent--cell graph to be
nonempty. -/
theorem positiveParentCellEdges_nonempty
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : forall i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q)
    (hmass : 0 < Y.shadingMass) :
    (positiveParentCellEdges Y C parentOf).Nonempty := by
  by_contra hnone
  have hempty : positiveParentCellEdges Y C parentOf = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnone
  have hweight := edgeWeight_positiveParentCellEdges_eq_shadingMass
    Y C parentOf hcover
  rw [hempty] at hweight
  simp only [edgeWeight, Finset.sum_empty] at hweight
  rw [← hweight] at hmass
  exact lt_irrefl 0 hmass

/-- Every weight in the genuine positive graph is finite, with the finite
source shading mass as a common upper bound. -/
theorem positiveParentCellEdge_weight_ne_top
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : forall i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q)
    (e : parent × cell)
    (he : e ∈ positiveParentCellEdges Y C parentOf) :
    parentCellWeight Y C parentOf e ≠ ∞ := by
  have hle : parentCellWeight Y C parentOf e <= Y.shadingMass := by
    rw [← edgeWeight_positiveParentCellEdges_eq_shadingMass
      Y C parentOf hcover]
    exact omega_le_edgeWeight
      (positiveParentCellEdges Y C parentOf)
      (parentCellWeight Y C parentOf) he
  intro htop
  rw [htop] at hle
  exact Submission.Kakeya.ConvexFactoring.CubeWeightUniformization.shadingMass_ne_top Y (top_unique hle)

/-- The real positive parent--cell graph admits the fully automatic numeric
REG1/R2 witness.  No weight or degree bucket is supplied by the caller. -/
theorem exists_positiveGraph_actualDyadicRegularization
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : forall i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q)
    (hmass : 0 < Y.shadingMass) :
    Nonempty (ActualDyadicRegularization
      (positiveParentCellEdges Y C parentOf)
      (parentCellWeight Y C parentOf)) := by
  apply exists_actualDyadicRegularization
  · exact positiveParentCellEdges_nonempty Y C parentOf hcover hmass
  · exact positiveParentCellEdges_weight_pos Y C parentOf
  · exact positiveParentCellEdge_weight_ne_top Y C parentOf hcover

/-- Direct P1 consumer bridge: the exact cellular shading-mass identity turns
the concrete numeric product loss into the same final-child-shading bound
that downstream code previously obtained from an abstract supplied-bucket
regularization. -/
theorem source_shadingMass_le_actualLoss_nsmul_final_shadingMass
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (source : Finset (parent × cell))
    (R : ActualDyadicRegularization source
      (parentCellWeight Y C parentOf)) :
    (selectedChildShading Y C parentOf source).shadingMass <=
      (weightLoss source * degreeLoss (parent := parent)) •
        (selectedChildShading Y C parentOf R.finalEdges).shadingMass := by
  rw [selectedChildShading_shadingMass_eq_edgeWeight,
    selectedChildShading_shadingMass_eq_edgeWeight]
  exact R.sourceWeight_le_final

#print axioms positiveParentCellEdges_nonempty
#print axioms positiveParentCellEdge_weight_ne_top
#print axioms exists_positiveGraph_actualDyadicRegularization
#print axioms source_shadingMass_le_actualLoss_nsmul_final_shadingMass

end
end Family8CellularPositiveGraphActualRegularizationV1
