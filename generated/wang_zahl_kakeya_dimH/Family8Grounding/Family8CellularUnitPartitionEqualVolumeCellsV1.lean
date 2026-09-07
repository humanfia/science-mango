import Family8Grounding.Family8CellularEqualVolumeEdgeMassV1
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Genuine equal-volume half-open cells in ambient three-space

This file realizes `EqualVolumeCells` by pulling Mathlib's finite
`BoxIntegral.unitPartition` back from coordinate space `Fin 3 -> Real` to
`Space = EuclideanSpace Real (Fin 3)`.  The cells are full half-open boxes;
they are not intersected with a shading.  A separate coverage theorem shows
that the cells in the integral box `(-2, 2]^3` cover the closed unit ball.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CellularUnitPartitionEqualVolumeCellsV1

open LeanEval.Analysis.WangZahlKakeya
open Family8CellularEqualVolumeEdgeMassV1

noncomputable section

/-- The canonical coordinate map from ambient Euclidean space to the
ordinary function space carrying product Lebesgue measure. -/
abbrev spaceCoordinates : Space -> (Fin 3 -> Real) :=
  @WithLp.ofLp 2 (Fin 3 -> Real)

/-- The pullback to ambient Euclidean space of a coordinate box. -/
def euclideanBox (B : BoxIntegral.Box (Fin 3)) : Set Space :=
  spaceCoordinates ⁻¹' (B : Set (Fin 3 -> Real))

/-- The fixed integral box `(-2, 2]^3`.  The spare factor two avoids a
boundary problem at the negative face of the closed unit ball. -/
def unitSupportBox : BoxIntegral.Box (Fin 3) where
  lower := fun _ => -2
  upper := fun _ => 2
  lower_lt_upper := by
    intro i
    norm_num

/-- The fixed support box has integral vertices, as required by the exact
coverage theorem for `BoxIntegral.unitPartition`. -/
theorem unitSupportBox_hasIntegralVertices :
    BoxIntegral.hasIntegralVertices unitSupportBox := by
  refine ⟨fun _ => (-2 : Int), fun _ => (2 : Int), ?_, ?_⟩
  · intro i
    norm_num [unitSupportBox]
  · intro i
    norm_num [unitSupportBox]

/-- The finite type of mesh-`1 / n` cells contained in an ambient coordinate
box. -/
abbrev UnitPartitionCell (n : Nat) [NeZero n]
    (B : BoxIntegral.Box (Fin 3)) :=
  ↥(BoxIntegral.unitPartition.admissibleIndex n B)

/-- A coordinate unit-partition cell, pulled back to `Space`. -/
def unitPartitionCellCarrier (n : Nat) [NeZero n]
    (B : BoxIntegral.Box (Fin 3)) (q : UnitPartitionCell n B) : Set Space :=
  spaceCoordinates ⁻¹'
    ((BoxIntegral.unitPartition.box n q.1 : BoxIntegral.Box (Fin 3)) :
      Set (Fin 3 -> Real))

theorem measurableSet_unitPartitionCellCarrier
    (n : Nat) [NeZero n] (B : BoxIntegral.Box (Fin 3))
    (q : UnitPartitionCell n B) :
    MeasurableSet (unitPartitionCellCarrier n B q) := by
  exact
    (BoxIntegral.unitPartition.box n q.1).measurableSet_coe.preimage
      (PiLp.volume_preserving_ofLp (Fin 3)).measurable

/-- Pullback preserves the literal disjointness of distinct coordinate
unit-partition boxes. -/
theorem unitPartitionCellCarrier_pairwise_disjoint
    (n : Nat) [NeZero n] (B : BoxIntegral.Box (Fin 3)) :
    Pairwise (fun q q' : UnitPartitionCell n B =>
      Disjoint (unitPartitionCellCarrier n B q)
        (unitPartitionCellCarrier n B q')) := by
  intro q q' hqq'
  have hval : q.1 ≠ q'.1 := by
    intro h
    apply hqq'
    exact Subtype.ext h
  have hcoordinate :
      Disjoint
        ((BoxIntegral.unitPartition.box n q.1 : BoxIntegral.Box (Fin 3)) :
          Set (Fin 3 -> Real))
        ((BoxIntegral.unitPartition.box n q'.1 : BoxIntegral.Box (Fin 3)) :
          Set (Fin 3 -> Real)) :=
    BoxIntegral.unitPartition.disjoint.mp hval
  exact Disjoint.preimage spaceCoordinates hcoordinate

/-- The common finite volume of a three-dimensional mesh-`1 / n` cell. -/
def unitPartitionCellVolume (n : Nat) : NNReal :=
  (n : NNReal)⁻¹ ^ 3

theorem unitPartitionCellVolume_pos (n : Nat) [NeZero n] :
    0 < unitPartitionCellVolume n := by
  have hn : 0 < (n : NNReal) := by
    exact_mod_cast n.pos_of_neZero
  exact pow_pos (inv_pos.mpr hn) 3

/-- Product-coordinate volume is transported exactly to ambient Euclidean
volume by `WithLp.ofLp`. -/
theorem volume_unitPartitionCellCarrier
    (n : Nat) [NeZero n] (B : BoxIntegral.Box (Fin 3))
    (q : UnitPartitionCell n B) :
    volume (unitPartitionCellCarrier n B q) =
      (unitPartitionCellVolume n : ENNReal) := by
  calc
    volume (unitPartitionCellCarrier n B q) =
        volume
          ((BoxIntegral.unitPartition.box n q.1 :
            BoxIntegral.Box (Fin 3)) : Set (Fin 3 -> Real)) :=
      (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
        (BoxIntegral.unitPartition.box n q.1).measurableSet_coe.nullMeasurableSet
    _ = 1 / n ^ Fintype.card (Fin 3) :=
      BoxIntegral.unitPartition.volume_box n q.1
    _ = (unitPartitionCellVolume n : ENNReal) := by
      simp [unitPartitionCellVolume]

/-- Mathlib's coordinate unit partition gives a genuine finite family of
measurable, pairwise-disjoint, strictly positive equal-volume cells in
ambient Euclidean three-space. -/
def unitPartitionEqualVolumeCells
    (n : Nat) [NeZero n] (B : BoxIntegral.Box (Fin 3)) :
    EqualVolumeCells (UnitPartitionCell n B) where
  carrier := unitPartitionCellCarrier n B
  measurable_carrier := measurableSet_unitPartitionCellCarrier n B
  pairwise_disjoint := unitPartitionCellCarrier_pairwise_disjoint n B
  cellVolume := unitPartitionCellVolume n
  cellVolume_pos := unitPartitionCellVolume_pos n
  volume_carrier := volume_unitPartitionCellCarrier n B

/-- Every coordinate point in an integral box lies in the unit-partition
cell selected by `unitPartition.index`. -/
theorem euclideanBox_subset_unitPartitionCellUnion
    (n : Nat) [NeZero n] (B : BoxIntegral.Box (Fin 3))
    (hB : BoxIntegral.hasIntegralVertices B) :
    euclideanBox B ⊆
      ⋃ q : UnitPartitionCell n B, unitPartitionCellCarrier n B q := by
  intro x hx
  let nu : Fin 3 -> Int :=
    BoxIntegral.unitPartition.index n (spaceCoordinates x)
  have hnu : nu ∈ BoxIntegral.unitPartition.admissibleIndex n B := by
    apply BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box n hB
    exact hx
  apply Set.mem_iUnion.mpr
  refine ⟨⟨nu, hnu⟩, ?_⟩
  exact BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl

/-- Conversely, every admissible unit-partition cell is contained in its
bounding box. -/
theorem unitPartitionCellUnion_subset_euclideanBox
    (n : Nat) [NeZero n] (B : BoxIntegral.Box (Fin 3)) :
    (⋃ q : UnitPartitionCell n B, unitPartitionCellCarrier n B q) ⊆
      euclideanBox B := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  have hq :
      (BoxIntegral.unitPartition.box n q.1 : BoxIntegral.Box (Fin 3)) ≤ B :=
    BoxIntegral.unitPartition.mem_admissibleIndex_iff.mp q.2
  exact hq hxq

/-- For an integral coordinate box, the finite union of the pulled-back
cells is exactly its Euclidean pullback. -/
theorem unitPartitionCellUnion_eq_euclideanBox
    (n : Nat) [NeZero n] (B : BoxIntegral.Box (Fin 3))
    (hB : BoxIntegral.hasIntegralVertices B) :
    (⋃ q : UnitPartitionCell n B, unitPartitionCellCarrier n B q) =
      euclideanBox B := by
  exact Set.Subset.antisymm
    (unitPartitionCellUnion_subset_euclideanBox n B)
    (euclideanBox_subset_unitPartitionCellUnion n B hB)

/-- The closed unit ball is contained in the pullback of `(-2, 2]^3`. -/
theorem closedBall_one_subset_unitSupportEuclideanBox :
    Metric.closedBall (0 : Space) 1 ⊆ euclideanBox unitSupportBox := by
  intro x hx
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  change ∀ i, (-2 : Real) < x i ∧ x i ≤ 2
  intro i
  have hi : |x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le x i).trans hxnorm
  exact ⟨by linarith [neg_le_of_abs_le hi], by linarith [le_of_abs_le hi]⟩

/-- The genuine finite equal-volume cells in `(-2, 2]^3` cover the whole
closed unit ball. -/
theorem closedBall_one_subset_unitPartitionCellUnion
    (n : Nat) [NeZero n] :
    Metric.closedBall (0 : Space) 1 ⊆
      ⋃ q : UnitPartitionCell n unitSupportBox,
        unitPartitionCellCarrier n unitSupportBox q := by
  exact closedBall_one_subset_unitSupportEuclideanBox.trans
    (euclideanBox_subset_unitPartitionCellUnion n unitSupportBox
      unitSupportBox_hasIntegralVertices)

/-- The same coverage theorem stated through the constructed
`EqualVolumeCells` object. -/
theorem closedBall_one_subset_equalVolumeCellsUnion
    (n : Nat) [NeZero n] :
    Metric.closedBall (0 : Space) 1 ⊆
      ⋃ q : UnitPartitionCell n unitSupportBox,
        (unitPartitionEqualVolumeCells n unitSupportBox).carrier q := by
  exact closedBall_one_subset_unitPartitionCellUnion n

#print axioms unitSupportBox_hasIntegralVertices
#print axioms unitPartitionCellCarrier_pairwise_disjoint
#print axioms volume_unitPartitionCellCarrier
#print axioms unitPartitionEqualVolumeCells
#print axioms unitPartitionCellUnion_eq_euclideanBox
#print axioms closedBall_one_subset_equalVolumeCellsUnion

end

end Family8CellularUnitPartitionEqualVolumeCellsV1
