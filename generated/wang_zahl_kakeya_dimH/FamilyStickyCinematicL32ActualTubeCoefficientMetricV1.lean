import FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FamilyStickyCinematicL32ActualTubeCoefficientMetricV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1

noncomputable section

/-!
# The actual projected coefficient distance is an `l1` pseudometric

This is the thin algebraic source needed by the norm-critical-ball
construction.  It unfolds the three literal projected tube coefficients;
no packing, scale-selection, or tangency conclusion is assumed.
-/

theorem projectedTubePairCoefficientDistance_self
    {delta : NNReal} (T : Tube delta) :
    projectedTubePairCoefficientDistance T T = 0 := by
  simp [projectedTubePairCoefficientDistance, coefficientDistance,
    projectedTubePairDeltaA, projectedTubePairDeltaB,
    projectedTubePairDeltaD]

theorem projectedTubePairCoefficientDistance_nonneg
    {delta : NNReal} (T U : Tube delta) :
    0 ≤ projectedTubePairCoefficientDistance T U := by
  rw [projectedTubePairCoefficientDistance, coefficientDistance]
  exact add_nonneg
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

theorem projectedTubePairCoefficientDistance_triangle
    {delta : NNReal} (T U V : Tube delta) :
    projectedTubePairCoefficientDistance T V ≤
      projectedTubePairCoefficientDistance T U +
        projectedTubePairCoefficientDistance U V := by
  have hA :
      |projectedTubeGraphA T - projectedTubeGraphA V| ≤
        |projectedTubeGraphA T - projectedTubeGraphA U| +
          |projectedTubeGraphA U - projectedTubeGraphA V| := by
    calc
      |projectedTubeGraphA T - projectedTubeGraphA V| =
          |(projectedTubeGraphA T - projectedTubeGraphA U) +
            (projectedTubeGraphA U - projectedTubeGraphA V)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hB :
      |projectedTubeGraphB T - projectedTubeGraphB V| ≤
        |projectedTubeGraphB T - projectedTubeGraphB U| +
          |projectedTubeGraphB U - projectedTubeGraphB V| := by
    calc
      |projectedTubeGraphB T - projectedTubeGraphB V| =
          |(projectedTubeGraphB T - projectedTubeGraphB U) +
            (projectedTubeGraphB U - projectedTubeGraphB V)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hD :
      |projectedTubeGraphD T - projectedTubeGraphD V| ≤
        |projectedTubeGraphD T - projectedTubeGraphD U| +
          |projectedTubeGraphD U - projectedTubeGraphD V| := by
    calc
      |projectedTubeGraphD T - projectedTubeGraphD V| =
          |(projectedTubeGraphD T - projectedTubeGraphD U) +
            (projectedTubeGraphD U - projectedTubeGraphD V)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  simp only [projectedTubePairCoefficientDistance, coefficientDistance,
    projectedTubePairDeltaA, projectedTubePairDeltaB,
    projectedTubePairDeltaD]
  linarith

#print axioms projectedTubePairCoefficientDistance_self
#print axioms projectedTubePairCoefficientDistance_nonneg
#print axioms projectedTubePairCoefficientDistance_triangle

end

end FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
