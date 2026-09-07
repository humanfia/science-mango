import Family8Grounding.Family8CellularJointFactoringComposerV1
import Family8Grounding.Family8CellularPositiveParentCellEdgeMassV1

/-!
# Joint cellular factoring on the genuine half-open unit partition

This module specializes the generic cellular J1/P1--P5 composer to the
actual finite equal-volume unit-partition cells in `(-2,2]^3`.  The caller
only supplies closed-unit-ball support and positive shading mass; the cell
coverage hypothesis is discharged by the existing geometric coverage
theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CellularUnitPartitionJointFactoringComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CellularUnitPartitionEqualVolumeCellsV1
open Family8CellularPositiveParentCellEdgeMassV1
open Family8CellularJointFactoringComposerV1

noncomputable section

variable {child parent : Type*}
  [Fintype child] [DecidableEq child]
  [Fintype parent] [DecidableEq parent]
  {F : ConvexFamily child}

/-- The generic joint witness with its cell family fixed to the genuine
half-open unit partition of the support box. -/
abbrev UnitPartitionJointFactoringWitness
    (n : Nat) [NeZero n] (Y : Shading F)
    (parentOf : child -> parent) :=
  CellularJointFactoringWitness Y
    (unitPartitionEqualVolumeCells n unitSupportBox) parentOf

/-- Closed-unit-ball support and positive source mass produce the complete
cellular J1/P1--P5 witness on the genuine unit partition.  No abstract cell
cover, weight bucket, degree bucket, or finiteness oracle remains as input. -/
theorem exists_unitPartitionJointFactoringWitness
    (n : Nat) [NeZero n]
    (Y : Shading F) (parentOf : child -> parent)
    (hsupport : forall i,
      Y.carrier i ⊆ Metric.closedBall (0 : Space) 1)
    (hmass : 0 < Y.shadingMass) :
    Nonempty (UnitPartitionJointFactoringWitness n Y parentOf) := by
  apply exists_cellularJointFactoringWitness
  · exact sourceShading_subset_unitPartitionCells n Y hsupport
  · exact hmass

#print axioms UnitPartitionJointFactoringWitness
#print axioms exists_unitPartitionJointFactoringWitness

end
end Family8CellularUnitPartitionJointFactoringComposerV1
