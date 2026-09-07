import Family8Grounding.Family8CellularPositiveGraphActualRegularizationV1
import Family8Grounding.Family8CellularCommonInnerLevelV1
import Family8Grounding.Family8CellularJointPointwiseP3P5BridgeV1
import Mathlib.Tactic

/-!
# One cellular witness carrying J1 and P1--P5

This file composes the already-grounded finite cellular ingredients.  Starting
from a positive source shading covered by finite equal-volume cells, it first
chooses the common inner multiplicity level (repair J1), then forms the genuine
positive parent--cell graph and applies the automatic numeric REG1/REG2
regularization.  The final child shading, parent regions, and degree bands all
use the same final edge set.

This is deliberately a cellular composer.  It does not construct the later
geometric nonidentity sticky cover or claim the full paper theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CellularJointFactoringComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ComparableMultiplicityBucketsV1
open Family8CellularCommonInnerLevelV1
open Family8CellularEqualVolumeEdgeMassV1
open Family8CellularJointFactoringFiniteCoreV1
open Family8CellularJointShadingFromEdgesV1
open Family8CellularPositiveParentCellEdgeMassV1
open Family8CellularActualDyadicRegularizationV1
open Family8CellularPositiveGraphActualRegularizationV1
open Family8CellularJointPointwiseP3P5BridgeV1

noncomputable section

variable {child parent cell : Type*}
  [Fintype child] [DecidableEq child]
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]
  {F : ConvexFamily child}

/-- Loss of the common inner multiplicity-level restriction. -/
def innerLevelLoss : Nat :=
  Nat.log 2 (Fintype.card child) + 2

/-- The genuine positive cellular graph after fixing the common inner label. -/
def innerPositiveEdges (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (b : Nat) : Finset (parent × cell) :=
  positiveParentCellEdges (commonInnerRestriction Y parentOf b) C parentOf

/-- The child shading selected by a final cellular edge set after J1. -/
def innerSelectedShading (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (b : Nat)
    (E : Finset (parent × cell)) : Shading F :=
  selectedChildShading (commonInnerRestriction Y parentOf b) C parentOf E

/-- The explicit combined J1, REG1, and REG2 loss. -/
def jointCellularLoss (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (b : Nat) : Nat :=
  innerLevelLoss (child := child) *
    (weightLoss (innerPositiveEdges Y C parentOf b) *
      degreeLoss (parent := parent))

/-- Membership in a cellular parent region produces a selected cell
containing the same point. -/
theorem exists_rightCell_of_mem_parentRegion
    (C : EqualVolumeCells cell) (E : Finset (parent × cell))
    (p : parent) (x : Space) (hx : x ∈ C.parentRegion E p) :
    ∃ q, q ∈ rightCells E ∧ x ∈ C.carrier q := by
  rw [Family8CellularEqualVolumeEdgeMassV1.EqualVolumeCells.parentRegion] at hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  refine ⟨q.1, ?_, hxq⟩
  exact (mem_rightCells_iff E q.1).2
    ⟨p, (Finset.mem_filter.mp q.2).2⟩

/-- Global P4: the cellwise degree identity applies at every point in the
union of final parent regions; no cell witness is required from the caller. -/
theorem parentRegionMultiplicity_positiveBand_of_mem_parentRegions
    (C : EqualVolumeCells cell) (E : Finset (parent × cell)) (d : Nat)
    (hband : HasRightDegreeBand E (rightCells E) d)
    (x : Space) (hx : x ∈ ⋃ p : parent, C.parentRegion E p) :
    d ≤ parentRegionMultiplicity C E x ∧
      parentRegionMultiplicity C E x < 2 * d := by
  obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
  obtain ⟨q, hq, hxq⟩ := exists_rightCell_of_mem_parentRegion C E p x hxp
  exact parentRegionMultiplicity_positiveBand
    C E (rightCells E) d hband q hq x hxq

/-- Global P5: every point of the final shaded union lies in a selected
parent region and hence in a selected cell, so the cellwise product bound
applies without an extra cell hypothesis. -/
theorem selectedChildShading_pointMultiplicity_lt_four_mul_of_mem_shadedUnion
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (E : Finset (parent × cell))
    (b d : Nat) (hbpos : 0 < comparableBase b)
    (hband : HasRightDegreeBand E (rightCells E) d)
    (x : Space)
    (hx : x ∈ (innerSelectedShading Y C parentOf b E).shadedUnion) :
    (innerSelectedShading Y C parentOf b E).pointMultiplicity x <
      4 * comparableBase b * d := by
  change x ∈ ⋃ i, (innerSelectedShading Y C parentOf b E).carrier i at hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  have hxp : x ∈ C.parentRegion E (parentOf i) :=
    selectedChild_mem_parentRegion
      (commonInnerRestriction Y parentOf b) C parentOf E i x hxi
  obtain ⟨q, hq, hxq⟩ :=
    exists_rightCell_of_mem_parentRegion C E (parentOf i) x hxp
  exact selectedChildShading_pointMultiplicity_lt_four_mul
    Y C parentOf E (rightCells E) b d hbpos hband q hq x hxq

/-- A single witness exposing the common-inner restriction, genuine automatic
dyadic regularization, and the resulting cellular P1--P5 conclusions. -/
structure CellularJointFactoringWitness
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) where
  innerLabel : Nat
  innerLabel_mem : innerLabel ∈
    Finset.range (innerLevelLoss (child := child))
  innerMass_pos :
    0 < (commonInnerRestriction Y parentOf innerLabel).shadingMass
  innerBase_pos : 0 < comparableBase innerLabel
  regularization : ActualDyadicRegularization
    (innerPositiveEdges Y C parentOf innerLabel)
    (parentCellWeight (commonInnerRestriction Y parentOf innerLabel)
      C parentOf)
  /-- P1: source mass survives the common level and the two actual dyadic
  regularizations with the explicit product loss. -/
  p1_mass : Y.shadingMass <=
    jointCellularLoss Y C parentOf innerLabel •
      (innerSelectedShading Y C parentOf innerLabel
        regularization.finalEdges).shadingMass
  /-- P2: every final child incidence lies in the parent region generated by
  the very same final edge set. -/
  p2_parentRegion : forall i x,
    x ∈ (innerSelectedShading Y C parentOf innerLabel
      regularization.finalEdges).carrier i ->
    x ∈ C.parentRegion regularization.finalEdges (parentOf i)
  /-- P3: the recomputed final parent-local child multiplicity lies in the
  common positive inner dyadic band. -/
  p3_innerBand : forall i x,
    x ∈ (innerSelectedShading Y C parentOf innerLabel
      regularization.finalEdges).carrier i ->
    comparableBase innerLabel <=
        parentLocalFiberMultiplicity
          (innerSelectedShading Y C parentOf innerLabel
            regularization.finalEdges) parentOf (parentOf i) x ∧
      parentLocalFiberMultiplicity
          (innerSelectedShading Y C parentOf innerLabel
            regularization.finalEdges) parentOf (parentOf i) x <
        2 * comparableBase innerLabel
  /-- P4, globally on the union of final parent regions: parent-region
  multiplicity is in the actual final right-degree band. -/
  p4_parentBand : forall x,
    x ∈ ⋃ p : parent, C.parentRegion regularization.finalEdges p ->
      regularization.d <=
          parentRegionMultiplicity C regularization.finalEdges x ∧
        parentRegionMultiplicity C regularization.finalEdges x <
          2 * regularization.d
  /-- P5, globally on the final shaded union: final point multiplicity has
  the joint product bound `4 * mu * d`. -/
  p5_pointMultiplicity : forall x,
    x ∈ (innerSelectedShading Y C parentOf innerLabel
      regularization.finalEdges).shadedUnion ->
      (innerSelectedShading Y C parentOf innerLabel
        regularization.finalEdges).pointMultiplicity x <
        4 * comparableBase innerLabel * regularization.d

namespace CellularJointFactoringWitness

/-- The final cellular edge set carried by the joint witness. -/
def finalEdges {Y : Shading F} {C : EqualVolumeCells cell}
    {parentOf : child -> parent}
    (W : CellularJointFactoringWitness Y C parentOf) :
    Finset (parent × cell) :=
  W.regularization.finalEdges

/-- The final fine shading carried by the joint witness. -/
def finalShading {Y : Shading F} {C : EqualVolumeCells cell}
    {parentOf : child -> parent}
    (W : CellularJointFactoringWitness Y C parentOf) : Shading F :=
  innerSelectedShading Y C parentOf W.innerLabel W.finalEdges

end CellularJointFactoringWitness

/-- Positive mass and finite cell coverage automatically produce one joint
cellular witness.  No weight bucket, degree bucket, or finiteness oracle is
supplied by the caller. -/
theorem exists_cellularJointFactoringWitness
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (hcover : forall i, Y.carrier i ⊆ ⋃ q : cell, C.carrier q)
    (hmass : 0 < Y.shadingMass) :
    Nonempty (CellularJointFactoringWitness Y C parentOf) := by
  obtain ⟨b, hb, hinnerMass, _hinnerBand⟩ :=
    exists_commonInnerRestriction_with_large_mass Y parentOf
  let Y0 := commonInnerRestriction Y parentOf b
  have hcover0 : forall i, Y0.carrier i ⊆ ⋃ q : cell, C.carrier q := by
    intro i x hx
    exact hcover i ((mem_commonInnerRestriction_carrier_iff
      Y parentOf b i x).1 hx).1
  have hinnerPos : 0 < Y0.shadingMass := by
    by_contra hnot
    have hzero : Y0.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hzero, nsmul_zero] at hinnerMass
    exact (not_le_of_gt hmass) hinnerMass
  have hbpos : 0 < comparableBase b := by
    have hsumPos : 0 < ∑ i : child, volume (Y0.carrier i) := by
      simpa only [Shading.shadingMass] using hinnerPos
    rw [Finset.sum_pos_iff] at hsumPos
    obtain ⟨i, _hi, hiPos⟩ := hsumPos
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hiPos.ne'
    exact (recomputed_parentLocalFiberMultiplicity_positiveBand
      Y parentOf b i x hx).1
  let source := innerPositiveEdges Y C parentOf b
  obtain ⟨R⟩ := exists_positiveGraph_actualDyadicRegularization
    Y0 C parentOf hcover0 hinnerPos
  have hsourceMass :
      (selectedChildShading Y0 C parentOf source).shadingMass =
        Y0.shadingMass := by
    exact selectedChildShading_positiveParentCellEdges_shadingMass_eq
      Y0 C parentOf hcover0
  have hregMass : Y0.shadingMass <=
      (weightLoss source * degreeLoss (parent := parent)) •
        (selectedChildShading Y0 C parentOf R.finalEdges).shadingMass := by
    rw [← hsourceMass]
    exact source_shadingMass_le_actualLoss_nsmul_final_shadingMass
      Y0 C parentOf source R
  have hjointMass : Y.shadingMass <=
      (innerLevelLoss (child := child) *
        (weightLoss source * degreeLoss (parent := parent))) •
          (selectedChildShading Y0 C parentOf R.finalEdges).shadingMass := by
    calc
      Y.shadingMass <=
          innerLevelLoss (child := child) • Y0.shadingMass := by
        simpa only [innerLevelLoss, Y0] using hinnerMass
      _ <= innerLevelLoss (child := child) •
          ((weightLoss source * degreeLoss (parent := parent)) •
            (selectedChildShading Y0 C parentOf R.finalEdges).shadingMass) := by
        exact nsmul_le_nsmul_right hregMass _
      _ = (innerLevelLoss (child := child) *
          (weightLoss source * degreeLoss (parent := parent))) •
            (selectedChildShading Y0 C parentOf R.finalEdges).shadingMass := by
        exact by
          simpa only [Nat.mul_comm] using (mul_nsmul
            (selectedChildShading Y0 C parentOf R.finalEdges).shadingMass
            (weightLoss source * degreeLoss (parent := parent))
            (innerLevelLoss (child := child))).symm
  refine ⟨{
    innerLabel := b
    innerLabel_mem := by simpa only [innerLevelLoss] using hb
    innerMass_pos := by simpa only [Y0] using hinnerPos
    innerBase_pos := hbpos
    regularization := R
    p1_mass := ?_
    p2_parentRegion := ?_
    p3_innerBand := ?_
    p4_parentBand := ?_
    p5_pointMultiplicity := ?_ }⟩
  · simpa only [jointCellularLoss, innerPositiveEdges,
      innerSelectedShading, source, Y0] using hjointMass
  · intro i x hx
    exact selectedChild_mem_parentRegion
      Y0 C parentOf R.finalEdges i x hx
  · intro i x hx
    exact (selectedChildShading_parentLocalFiberMultiplicity_positiveBand
      Y C parentOf R.finalEdges b i x hx).2
  · intro x hx
    exact parentRegionMultiplicity_positiveBand_of_mem_parentRegions
      C R.finalEdges R.d R.final_degreeBand x hx
  · intro x hx
    exact selectedChildShading_pointMultiplicity_lt_four_mul_of_mem_shadedUnion
      Y C parentOf R.finalEdges b R.d hbpos R.final_degreeBand x hx

#print axioms CellularJointFactoringWitness
#print axioms exists_rightCell_of_mem_parentRegion
#print axioms parentRegionMultiplicity_positiveBand_of_mem_parentRegions
#print axioms selectedChildShading_pointMultiplicity_lt_four_mul_of_mem_shadedUnion
#print axioms exists_cellularJointFactoringWitness

end
end Family8CellularJointFactoringComposerV1
