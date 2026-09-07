import Family8Grounding.Family8CellularJointShadingFromEdgesV1
import Family8Grounding.Family8CellularUnitPartitionEqualVolumeCellsV1
import Mathlib.Tactic

/-!
# The positive parent--cell source graph preserves all shading mass

Given a finite pairwise-disjoint cell family covering every source shading,
this module starts with the complete labelled parent--cell graph.  Its edge
weight is the source shading mass inside that parent and cell.  The complete
graph therefore has exactly the total source shading mass.  Removing precisely
the zero-weight edges changes neither that total nor the selected child
shading mass.

The final theorem instantiates the construction with the genuine half-open
unit-partition cells in `(-2, 2]^3`.  It only asks that the source shadings lie
in the closed unit ball, which those cells cover.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CellularPositiveParentCellEdgeMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CellularEqualVolumeEdgeMassV1
open Family8CellularEqualVolumeEdgeMassV1.EqualVolumeCells
open Family8CellularJointFactoringFiniteCoreV1
open Family8CellularJointShadingFromEdgesV1
open Family8CellularUnitPartitionEqualVolumeCellsV1

noncomputable section

variable {child parent cell : Type*}
  [Fintype child] [DecidableEq child]
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]
  {F : ConvexFamily child}

/-- The complete labelled parent--cell graph. -/
def allParentCellEdges : Finset (parent × cell) :=
  Finset.univ

/-- The genuine source graph: retain exactly the complete-graph edges whose
source shading weight is strictly positive. -/
def positiveParentCellEdges (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) : Finset (parent × cell) :=
  allParentCellEdges.filter
    (fun e => 0 < parentCellWeight Y C parentOf e)

@[simp] theorem mem_allParentCellEdges (e : parent × cell) :
    e ∈ (allParentCellEdges : Finset (parent × cell)) := by
  simp [allParentCellEdges]

@[simp] theorem mem_positiveParentCellEdges_iff
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (e : parent × cell) :
    e ∈ positiveParentCellEdges Y C parentOf ↔
      0 < parentCellWeight Y C parentOf e := by
  simp [positiveParentCellEdges]

/-- Every positive source edge carries positive weight by construction. -/
theorem positiveParentCellEdges_weight_pos
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (e : parent × cell)
    (he : e ∈ positiveParentCellEdges Y C parentOf) :
    0 < parentCellWeight Y C parentOf e :=
  (mem_positiveParentCellEdges_iff Y C parentOf e).mp he

/-- The positive source graph packaged in the finite cellular-core API. -/
def positiveWeightedCellularEdges
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) : WeightedCellularEdges parent cell where
  edges := positiveParentCellEdges Y C parentOf
  omega := parentCellWeight Y C parentOf
  omega_pos := positiveParentCellEdges_weight_pos Y C parentOf

/-- A cell cover of the source shading puts each child shading inside the
complete cellular region of its labelled parent. -/
theorem carrier_subset_allParentCellRegion
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : ∀ i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q)
    (i : child) :
    Y.carrier i ⊆ C.parentRegion allParentCellEdges (parentOf i) := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp (hcover i hx)
  rw [parentRegion]
  apply Set.mem_iUnion.mpr
  refine ⟨⟨q, ?_⟩, hxq⟩
  simp [incidentCells, allParentCellEdges]

/-- Selecting the complete graph does not change the source shading mass
when the cells cover each source carrier. -/
theorem selectedChildShading_allParentCellEdges_shadingMass_eq
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : ∀ i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q) :
    (selectedChildShading Y C parentOf allParentCellEdges).shadingMass =
      Y.shadingMass := by
  unfold Shading.shadingMass
  apply Finset.sum_congr rfl
  intro i hi
  rw [selectedChildShading_carrier, inter_eq_left.mpr]
  exact carrier_subset_allParentCellRegion Y C parentOf hcover i

/-- Under source coverage, the complete parent--cell graph has exactly the
source shading mass. -/
theorem edgeWeight_allParentCellEdges_eq_shadingMass
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : ∀ i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q) :
    edgeWeight allParentCellEdges (parentCellWeight Y C parentOf) =
      Y.shadingMass := by
  rw [← selectedChildShading_allParentCellEdges_shadingMass_eq
    Y C parentOf hcover]
  exact (selectedChildShading_shadingMass_eq_edgeWeight
    Y C parentOf allParentCellEdges).symm

/-- Removing every zero-weight edge from the complete graph does not change
its total edge weight. -/
theorem edgeWeight_positiveParentCellEdges_eq_allParentCellEdges
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) :
    edgeWeight (positiveParentCellEdges Y C parentOf)
        (parentCellWeight Y C parentOf) =
      edgeWeight allParentCellEdges (parentCellWeight Y C parentOf) := by
  unfold edgeWeight
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro e heall henot
    have hnotpos : ¬ 0 < parentCellWeight Y C parentOf e := by
      intro hpos
      apply henot
      exact (mem_positiveParentCellEdges_iff Y C parentOf e).mpr hpos
    exact nonpos_iff_eq_zero.mp (not_lt.mp hnotpos)

/-- The positive source graph has exactly the source shading mass. -/
theorem edgeWeight_positiveParentCellEdges_eq_shadingMass
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : ∀ i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q) :
    edgeWeight (positiveParentCellEdges Y C parentOf)
        (parentCellWeight Y C parentOf) =
      Y.shadingMass := by
  rw [edgeWeight_positiveParentCellEdges_eq_allParentCellEdges]
  exact edgeWeight_allParentCellEdges_eq_shadingMass Y C parentOf hcover

/-- The child shading selected by the positive source graph retains all
source shading mass.  This is the exact P1 input before later regularization
loses a controlled fraction of the positive edge weight. -/
theorem selectedChildShading_positiveParentCellEdges_shadingMass_eq
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : ∀ i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q) :
    (selectedChildShading Y C parentOf
      (positiveParentCellEdges Y C parentOf)).shadingMass =
      Y.shadingMass := by
  rw [selectedChildShading_shadingMass_eq_edgeWeight]
  exact edgeWeight_positiveParentCellEdges_eq_shadingMass
    Y C parentOf hcover

section UnitPartition

variable (n : Nat) [NeZero n]

/-- The genuine half-open grid covers any source shading supported in the
closed unit ball. -/
theorem sourceShading_subset_unitPartitionCells
    (Y : Shading F)
    (hsupport : ∀ i, Y.carrier i ⊆ Metric.closedBall (0 : Space) 1)
    (i : child) :
    Y.carrier i ⊆
      ⋃ q : UnitPartitionCell n unitSupportBox,
        (unitPartitionEqualVolumeCells n unitSupportBox).carrier q := by
  exact (hsupport i).trans
    (closedBall_one_subset_equalVolumeCellsUnion n)

/-- For the genuine half-open grid, positive parent--cell edges have exactly
the source shading mass. -/
theorem unitPartition_positiveParentCellEdges_edgeWeight_eq_shadingMass
    (Y : Shading F) (parentOf : child -> parent)
    (hsupport : ∀ i, Y.carrier i ⊆ Metric.closedBall (0 : Space) 1) :
    edgeWeight
        (positiveParentCellEdges Y
          (unitPartitionEqualVolumeCells n unitSupportBox) parentOf)
        (parentCellWeight Y
          (unitPartitionEqualVolumeCells n unitSupportBox) parentOf) =
      Y.shadingMass := by
  apply edgeWeight_positiveParentCellEdges_eq_shadingMass
  exact sourceShading_subset_unitPartitionCells n Y hsupport

/-- The selected child shading of the genuine positive half-open grid
retains exactly the full source shading mass. -/
theorem unitPartition_selectedChildShading_positive_shadingMass_eq
    (Y : Shading F) (parentOf : child -> parent)
    (hsupport : ∀ i, Y.carrier i ⊆ Metric.closedBall (0 : Space) 1) :
    (selectedChildShading Y
      (unitPartitionEqualVolumeCells n unitSupportBox) parentOf
      (positiveParentCellEdges Y
        (unitPartitionEqualVolumeCells n unitSupportBox) parentOf)).shadingMass =
      Y.shadingMass := by
  apply selectedChildShading_positiveParentCellEdges_shadingMass_eq
  exact sourceShading_subset_unitPartitionCells n Y hsupport

end UnitPartition

#print axioms positiveWeightedCellularEdges
#print axioms edgeWeight_allParentCellEdges_eq_shadingMass
#print axioms edgeWeight_positiveParentCellEdges_eq_allParentCellEdges
#print axioms selectedChildShading_positiveParentCellEdges_shadingMass_eq
#print axioms unitPartition_positiveParentCellEdges_edgeWeight_eq_shadingMass
#print axioms unitPartition_selectedChildShading_positive_shadingMass_eq

end
end Family8CellularPositiveParentCellEdgeMassV1
