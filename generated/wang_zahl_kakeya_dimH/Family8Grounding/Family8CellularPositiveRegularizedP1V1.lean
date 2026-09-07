import Family8Grounding.Family8CellularPositiveParentCellEdgeMassV1
import Family8Grounding.Family8CellularRegularizedShadingMassP1V1
import Mathlib.Tactic

/-!
# P1 from the genuine positive source graph and two-stage regularization

This module closes the mass-only path from a covered source shading to the
final edge set of a supplied two-stage regularization.  The positive
parent--cell graph has exactly the source mass; the finite weighted
pigeonholes then lose only the product of their two explicit label counts.

The label functions remain inputs.  Thus these statements establish P1 but
do not, by themselves, assert the numerical weight band or right-degree band
needed for P3--P5.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CellularPositiveRegularizedP1V1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CellularEqualVolumeEdgeMassV1
open Family8CellularJointFactoringRegularizationV1
open Family8CellularJointShadingFromEdgesV1
open Family8CellularPositiveParentCellEdgeMassV1
open Family8CellularUnitPartitionEqualVolumeCellsV1
open Family8CellularRegularizedShadingMassP1V1

noncomputable section

variable {child parent cell weightLabel degreeLabel : Type*}
  [Fintype child] [DecidableEq child]
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]
  [Fintype weightLabel] [DecidableEq weightLabel] [Nonempty weightLabel]
  [Fintype degreeLabel] [DecidableEq degreeLabel] [Nonempty degreeLabel]
  {F : ConvexFamily child}

/-- The exact positive-source identity turns the abstract regularization
bound into a P1 bound relative to the original shading. -/
theorem source_shadingMass_le_labelLoss_nsmul_positiveRegularized
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : forall i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q)
    (weightBucket : parent × cell -> weightLabel)
    (degreeBucket : cell -> degreeLabel)
    (R : TwoStageRegularization
      (positiveParentCellEdges Y C parentOf)
      (parentCellWeight Y C parentOf) weightBucket degreeBucket) :
    Y.shadingMass <=
      (Fintype.card weightLabel * Fintype.card degreeLabel) •
        (selectedChildShading Y C parentOf R.finalEdges).shadingMass := by
  rw [← selectedChildShading_positiveParentCellEdges_shadingMass_eq
    Y C parentOf hcover]
  exact source_shadingMass_le_labelLoss_nsmul_final_shadingMass
    Y C parentOf (positiveParentCellEdges Y C parentOf)
      weightBucket degreeBucket R

/-- The mass-retaining final edge set exists for every pair of finite label
functions; the quantitative band semantics of those labels can be supplied
separately. -/
theorem exists_positiveRegularization_with_sourceMass_le
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : forall i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q)
    (weightBucket : parent × cell -> weightLabel)
    (degreeBucket : cell -> degreeLabel) :
    exists R : TwoStageRegularization
        (positiveParentCellEdges Y C parentOf)
        (parentCellWeight Y C parentOf) weightBucket degreeBucket,
      Y.shadingMass <=
        (Fintype.card weightLabel * Fintype.card degreeLabel) •
          (selectedChildShading Y C parentOf R.finalEdges).shadingMass := by
  obtain ⟨R⟩ := exists_twoStageRegularization
    (positiveParentCellEdges Y C parentOf)
    (parentCellWeight Y C parentOf) weightBucket degreeBucket
  exact ⟨R, source_shadingMass_le_labelLoss_nsmul_positiveRegularized
    Y C parentOf hcover weightBucket degreeBucket R⟩

section UnitPartition

variable (n : Nat) [NeZero n]

/-- Genuine half-open cells give the same existence theorem from only
closed-unit-ball support of the source shading. -/
theorem exists_unitPartition_positiveRegularization_with_sourceMass_le
    (Y : Shading F) (parentOf : child -> parent)
    (hsupport : forall i,
      Y.carrier i ⊆ Metric.closedBall (0 : Space) 1)
    (weightBucket : parent ×
      UnitPartitionCell n unitSupportBox -> weightLabel)
    (degreeBucket : UnitPartitionCell n unitSupportBox -> degreeLabel) :
    exists R : TwoStageRegularization
        (positiveParentCellEdges Y
          (unitPartitionEqualVolumeCells n unitSupportBox) parentOf)
        (parentCellWeight Y
          (unitPartitionEqualVolumeCells n unitSupportBox) parentOf)
        weightBucket degreeBucket,
      Y.shadingMass <=
        (Fintype.card weightLabel * Fintype.card degreeLabel) •
          (selectedChildShading Y
            (unitPartitionEqualVolumeCells n unitSupportBox) parentOf
            R.finalEdges).shadingMass := by
  apply exists_positiveRegularization_with_sourceMass_le
  exact sourceShading_subset_unitPartitionCells n Y hsupport

end UnitPartition

#print axioms source_shadingMass_le_labelLoss_nsmul_positiveRegularized
#print axioms exists_positiveRegularization_with_sourceMass_le
#print axioms
  exists_unitPartition_positiveRegularization_with_sourceMass_le

end
end Family8CellularPositiveRegularizedP1V1
