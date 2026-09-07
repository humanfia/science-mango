import Family8Grounding.Family8CellularJointFactoringRegularizationV1
import Family8Grounding.Family8CellularJointShadingFromEdgesV1
import Mathlib.Tactic

/-!
# Quantitative P1 mass for regularized cellular shadings

This file is a minimal composer.  A supplied two-stage finite
regularization selects a final parent--cell edge set.  The exact cellular
shading-mass identity then turns its finite weight conclusions into P1-type
mass bounds for the child shading selected by those same edges.

There are two complementary conclusions below.  The first records the
unconditional product loss from the two finite label spaces.  The second
uses the whole-incidence lift: a retained cardinality (or equal-volume
labelled-parent-mass) fraction inside one factor-two weight band gives a
`c / 2` retained child-shading-mass fraction.  No spatial grid, initial edge
graph, or cardinality-retention assertion is constructed in this module.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CellularRegularizedShadingMassP1V1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CellularEqualVolumeEdgeMassV1
open Family8CellularJointFactoringFiniteCoreV1
open Family8CellularJointFactoringRegularizationV1
open Family8CellularJointShadingFromEdgesV1

noncomputable section

variable {child parent cell weightLabel degreeLabel : Type*}
  [Fintype child] [DecidableEq child]
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]
  [Fintype weightLabel] [DecidableEq weightLabel] [Nonempty weightLabel]
  [Fintype degreeLabel] [DecidableEq degreeLabel] [Nonempty degreeLabel]
  {F : ConvexFamily child}

/-- The product of the two explicit finite label losses is already a P1
mass bound for the final selected child shading. -/
theorem source_shadingMass_le_labelLoss_nsmul_final_shadingMass
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (source : Finset (parent × cell))
    (weightBucket : parent × cell -> weightLabel)
    (degreeBucket : cell -> degreeLabel)
    (R : TwoStageRegularization source
      (parentCellWeight Y C parentOf) weightBucket degreeBucket) :
    (selectedChildShading Y C parentOf source).shadingMass <=
      (Fintype.card weightLabel * Fintype.card degreeLabel) •
        (selectedChildShading Y C parentOf R.finalEdges).shadingMass := by
  rw [selectedChildShading_shadingMass_eq_edgeWeight,
    selectedChildShading_shadingMass_eq_edgeWeight]
  exact R.sourceWeight_le

/-- Whole-incidence P1 in cardinality form.  The final set furnished by the
regularization is automatically a subedge of the source, so the only extra
inputs are the genuine geometric/numeric hypotheses required by the lift. -/
theorem cardFraction_mul_source_shadingMass_le_final_shadingMass
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (source : Finset (parent × cell))
    (weightBucket : parent × cell -> weightLabel)
    (degreeBucket : cell -> degreeLabel)
    (R : TwoStageRegularization source
      (parentCellWeight Y C parentOf) weightBucket degreeBucket)
    (w c : ENNReal)
    (hband : InHalfOpenWeightBand source
      (parentCellWeight Y C parentOf) w)
    (hcard : c * (source.card : ENNReal) <=
      (R.finalEdges.card : ENNReal)) :
    (c / 2) * (selectedChildShading Y C parentOf source).shadingMass <=
      (selectedChildShading Y C parentOf R.finalEdges).shadingMass := by
  rw [selectedChildShading_shadingMass_eq_edgeWeight,
    selectedChildShading_shadingMass_eq_edgeWeight]
  exact wholeIncidenceLift_half_fraction_mul_le source R.finalEdges
    (parentCellWeight Y C parentOf) w c R.finalEdges_subset_source hband hcard

/-- Equal-volume labelled-parent-mass form of the same P1 conclusion.  This
is the form used when the cellular construction controls retained parent
cell volume rather than edge cardinality directly. -/
theorem labelledParentMassFraction_mul_source_shadingMass_le_final_shadingMass
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent)
    (source : Finset (parent × cell))
    (weightBucket : parent × cell -> weightLabel)
    (degreeBucket : cell -> degreeLabel)
    (R : TwoStageRegularization source
      (parentCellWeight Y C parentOf) weightBucket degreeBucket)
    (w c cellVolume : ENNReal)
    (hband : InHalfOpenWeightBand source
      (parentCellWeight Y C parentOf) w)
    (hvolume0 : Not (cellVolume = 0))
      (hvolumeFinite : Exists fun r : NNReal => cellVolume = r)
    (hmass : c * labelledParentMass source cellVolume <=
      labelledParentMass R.finalEdges cellVolume) :
    (c / 2) * (selectedChildShading Y C parentOf source).shadingMass <=
      (selectedChildShading Y C parentOf R.finalEdges).shadingMass := by
  obtain ⟨r, rfl⟩ := hvolumeFinite
  rw [selectedChildShading_shadingMass_eq_edgeWeight,
    selectedChildShading_shadingMass_eq_edgeWeight]
  exact wholeIncidenceLift_of_labelledParentMass source R.finalEdges
    (parentCellWeight Y C parentOf) w c (r : ENNReal)
    R.finalEdges_subset_source hband hvolume0 ENNReal.coe_ne_top hmass

#print axioms source_shadingMass_le_labelLoss_nsmul_final_shadingMass
#print axioms cardFraction_mul_source_shadingMass_le_final_shadingMass
#print axioms labelledParentMassFraction_mul_source_shadingMass_le_final_shadingMass

end
end Family8CellularRegularizedShadingMassP1V1
