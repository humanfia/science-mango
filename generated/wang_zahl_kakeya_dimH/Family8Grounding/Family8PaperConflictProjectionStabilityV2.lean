import Family8Grounding.Family8CommonPointTubePackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8PaperConflictProjectionStabilityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CommonPointTubePackingV1

noncomputable section

/-!
# Stability of transverse projection

This is the clean successor of the initial scratch module.  It contains only
the scale-free linear-algebra estimate needed by the constant paper-conflict
packing code.
-/

def transverseResidual (u d : Space) : Space :=
  d - ⟪u, d⟫_ℝ • u

theorem transverseResidual_neg (u d : Space) :
    transverseResidual (-u) d = transverseResidual u d := by
  simp [transverseResidual]

theorem tubePointTransverse_eq_transverseResidual
    {delta : NNReal} (x : Space) (T : Tube delta) :
    tubePointTransverse x T =
      transverseResidual T.axis.direction (tubeAxisMidpoint T - x) := by
  simp [tubePointTransverse, tubePointLongitudinal, transverseResidual]

theorem norm_transverseResidual_sub_le
    {u v d : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖transverseResidual u d - transverseResidual v d‖ ≤
      2 * ‖d‖ * ‖u - v‖ := by
  have hrewrite :
      transverseResidual u d - transverseResidual v d =
        ⟪v, d⟫_ℝ • (v - u) + ⟪v - u, d⟫_ℝ • u := by
    simp only [transverseResidual, inner_sub_left]
    module
  rw [hrewrite]
  calc
    ‖⟪v, d⟫_ℝ • (v - u) + ⟪v - u, d⟫_ℝ • u‖ ≤
        ‖⟪v, d⟫_ℝ • (v - u)‖ +
          ‖⟪v - u, d⟫_ℝ • u‖ := norm_add_le _ _
    _ = |⟪v, d⟫_ℝ| * ‖v - u‖ +
        |⟪v - u, d⟫_ℝ| * ‖u‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (‖v‖ * ‖d‖) * ‖v - u‖ +
        (‖v - u‖ * ‖d‖) * ‖u‖ := by
      gcongr
      · exact abs_real_inner_le_norm v d
      · exact abs_real_inner_le_norm (v - u) d
    _ = 2 * ‖d‖ * ‖u - v‖ := by
      rw [hu, hv, norm_sub_rev]
      ring

theorem norm_transverseResidual_sub_le_of_neg
    {u v d : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖transverseResidual u d - transverseResidual v d‖ ≤
      2 * ‖d‖ * ‖u + v‖ := by
  calc
    ‖transverseResidual u d - transverseResidual v d‖ =
        ‖transverseResidual u d - transverseResidual (-v) d‖ := by
      rw [transverseResidual_neg]
    _ ≤ 2 * ‖d‖ * ‖u - (-v)‖ :=
      norm_transverseResidual_sub_le hu (by simpa using hv)
    _ = 2 * ‖d‖ * ‖u + v‖ := by rw [sub_neg_eq_add]

#print axioms transverseResidual_neg
#print axioms tubePointTransverse_eq_transverseResidual
#print axioms norm_transverseResidual_sub_le
#print axioms norm_transverseResidual_sub_le_of_neg

end

end Family8PaperConflictProjectionStabilityV2
