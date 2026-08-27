import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticToleranceV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1

noncomputable section

/-!
# Canonical external tolerance for finite reference families

Once the unperturbed reference budget has strict room, finiteness supplies a
canonical positive perturbation tolerance.  This removes both the tolerance
choice and its affine budget inequality from later geometric packages.
-/

/-- Spend the entire strict reference margin against the finite absolute
weight envelope, with `+ 1` keeping the denominator uniformly positive. -/
def finiteActualReferenceAutomaticTolerance
    {radius : NNReal} (referenceScale t : Real)
    (curves : Finset (Tube radius)) (weight : Tube radius -> Real) : Real :=
  (3 * t - 30 * referenceScale) /
    (finiteActualTubeFamilyWeightEnvelope curves weight + 1)

theorem finiteActualReferenceAutomaticTolerance_pos
    {radius : NNReal} {referenceScale t : Real}
    (curves : Finset (Tube radius)) (weight : Tube radius -> Real)
    (hmargin : 30 * referenceScale < 3 * t) :
    0 < finiteActualReferenceAutomaticTolerance
      referenceScale t curves weight := by
  unfold finiteActualReferenceAutomaticTolerance
  apply div_pos (sub_pos.mpr hmargin)
  linarith [finiteActualTubeFamilyWeightEnvelope_nonneg curves weight]

theorem finiteActualReferenceAutomaticTolerance_budget
    {radius : NNReal} {referenceScale t : Real}
    (curves : Finset (Tube radius)) (weight : Tube radius -> Real)
    (hmargin : 30 * referenceScale < 3 * t) :
    30 * referenceScale +
        finiteActualReferenceAutomaticTolerance referenceScale t curves weight *
          finiteActualTubeFamilyWeightEnvelope curves weight <=
      3 * t := by
  let envelope := finiteActualTubeFamilyWeightEnvelope curves weight
  have henvelope : 0 <= envelope := by
    exact finiteActualTubeFamilyWeightEnvelope_nonneg curves weight
  have hdenominator : 0 < envelope + 1 := by linarith
  have hmarginNonneg : 0 <= 3 * t - 30 * referenceScale := by
    linarith
  have hfraction :
      ((3 * t - 30 * referenceScale) / (envelope + 1)) * envelope <=
        3 * t - 30 * referenceScale := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hdenominator).2
    exact mul_le_mul_of_nonneg_left (by linarith) hmarginNonneg
  unfold finiteActualReferenceAutomaticTolerance
  change 30 * referenceScale +
      ((3 * t - 30 * referenceScale) / (envelope + 1)) * envelope <= 3 * t
  linarith

#print axioms finiteActualReferenceAutomaticTolerance
#print axioms finiteActualReferenceAutomaticTolerance_pos
#print axioms finiteActualReferenceAutomaticTolerance_budget

end

end FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticToleranceV1
