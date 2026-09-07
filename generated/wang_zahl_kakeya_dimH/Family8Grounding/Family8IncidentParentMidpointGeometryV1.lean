import Family8Grounding.Family8PaperConflictAnisotropicBoundsV4
import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8IncidentParentMidpointGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1

noncomputable section

/-- The two midpoint definitions used by the elongated-body and paper
conflict modules are literally the same Euclidean point. -/
theorem tubeAxisMidpoint_eq_commonPointTubeAxisMidpoint
    {rho : NNReal} (T : Tube rho) :
    tubeAxisMidpoint T =
      Family8CommonPointTubePackingV1.tubeAxisMidpoint T := by
  simp only [tubeAxisMidpoint,
    Family8CommonPointTubePackingV1.tubeAxisMidpoint]
  norm_num

/-- A fine midpoint in a doubled parent is within distance two of the parent
midpoint throughout the normalized range. -/
theorem dist_fine_parent_midpoint_le_two_of_carrier_subset_twoFold
    {delta rho : NNReal} (I : Tube delta) (P : Tube rho)
    (hrho : rho ≤ (1 / 16 : NNReal))
    (hIP : I.carrier ⊆ twoFoldTubeCarrier P) :
    dist (tubeAxisMidpoint I) (tubeAxisMidpoint P) ≤ 2 := by
  have hmidI : tubeAxisMidpoint I ∈ I.carrier :=
    tubeAxisMidpoint_mem_carrier I
  obtain ⟨y, hy, hEq⟩ := hIP hmidI
  have hycenter0 :=
    Family8PaperConflictAnisotropicBoundsV4.dist_midpoint_le_half_add_radius
      P hy
  have hycenter : dist y (tubeAxisMidpoint P) ≤
      (2 : Real)⁻¹ + (rho : Real) := by
    rw [tubeAxisMidpoint_eq_commonPointTubeAxisMidpoint]
    exact hycenter0
  rw [← hEq, dist_eq_norm]
  have hcenter : tubeCenter P = tubeAxisMidpoint P := by
    simp only [tubeCenter, tubeAxisMidpoint]
    norm_num
  have hvec :
      (tubeCenter P + (2 : Real) • (y - tubeCenter P)) -
          tubeAxisMidpoint P =
        (2 : Real) • (y - tubeCenter P) := by
    rw [← hcenter]
    module
  rw [hvec, norm_smul, Real.norm_ofNat]
  have hrhoReal : (rho : Real) ≤ (1 : Real) / 16 := by
    exact_mod_cast hrho
  calc
    2 * ‖y - tubeCenter P‖ = 2 * dist y (tubeCenter P) := by rfl
    _ = 2 * dist y (tubeAxisMidpoint P) := by rw [hcenter]
    _ ≤ 2 * ((2 : Real)⁻¹ + (rho : Real)) := by gcongr
    _ ≤ 2 := by nlinarith

#print axioms tubeAxisMidpoint_eq_commonPointTubeAxisMidpoint
#print axioms dist_fine_parent_midpoint_le_two_of_carrier_subset_twoFold

end
end Family8IncidentParentMidpointGeometryV1
