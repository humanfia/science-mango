import Family8Grounding.Family8IncidentParentMidpointGeometryV1
import Family8Grounding.Family8UnequalRadiusDoubledDirectionCoherenceV1
import Family8Grounding.Family8PaperConflictOrientedCoreV1
import Family8Grounding.Family8PaperConflictProjectionStabilityV2
import Family8Grounding.Family8PaperConflictAnisotropicBoundsV4
import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8IncidentParentElongatedContainmentV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1
open Family8PaperConflictProjectionStabilityV2
open Family8PaperConflictOrientedCoreV1
open Family8UnequalRadiusDoubledDirectionCoherenceV1
open Family8IncidentParentMidpointGeometryV1
open FamilyStickySameRadiusTubeContainmentCompatibleV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# One common elongated test for all parents incident to one fine tube

Unequal-radius doubled containment controls both the midpoint and projective
direction of a parent.  The deterministic paper-conflict orientation then
puts the complete parent carrier in one honest elongated body centered and
aligned at the fixed fine tube.
-/

/-- The standard projective orientation of an incident parent is within
`8 rho` of the fine direction. -/
theorem norm_orientedParentDirection_sub_fine_le_eight_mul
    {delta rho : NNReal} (I : Tube delta) (P : Tube rho)
    (hIP : I.carrier ⊆ twoFoldTubeCarrier P) :
    ‖(paperConflictOrientedTube (I.changeRadius rho) P).axis.direction -
        I.axis.direction‖ ≤ 8 * (rho : Real) := by
  have hprojective :=
    unorientedDirectionClose_eight_mul_of_unequal_carrier_subset_twoFold
      I P hIP
  rw [paperConflictOrientedTube]
  split_ifs with hforward
  · rcases hprojective with hprojective | hprojective
    · simpa only [norm_sub_rev] using hprojective
    · exact hforward
  · rcases hprojective with hprojective | hprojective
    · exact (hforward (by
        simpa only [Tube.changeRadius_axis, norm_sub_rev] using hprojective)).elim
    · change ‖(-P.axis.direction) - I.axis.direction‖ ≤ _
      have heq :
          (-P.axis.direction) - I.axis.direction =
            -(P.axis.direction + I.axis.direction) := by module
      rw [heq, norm_neg]
      simpa only [add_comm] using hprojective

/-- Every incident parent lies in the same honest length-six elongated body
based at the fixed fine axis. -/
theorem parent_carrier_subset_fine_paperElongatedBody
    {delta rho : NNReal} (I : Tube delta) (P : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = I.axis.direction)
    (hrho : rho ≤ (1 / 16 : NNReal))
    (hIP : I.carrier ⊆ twoFoldTubeCarrier P) :
    P.carrier ⊆
      (paperElongatedBody (I.changeRadius rho) frame : Set Space) := by
  let anchor : Tube rho := I.changeRadius rho
  let V : Tube rho := paperConflictOrientedTube anchor P
  let d : Space := tubeAxisMidpoint P - tubeAxisMidpoint I
  have hd : ‖d‖ ≤ 2 := by
    have hdist :=
      dist_fine_parent_midpoint_le_two_of_carrier_subset_twoFold
        I P hrho hIP
    simpa only [d, dist_eq_norm, norm_sub_rev] using hdist
  have hprojective :=
    unorientedDirectionClose_eight_mul_of_unequal_carrier_subset_twoFold
      I P hIP
  have hmidI : tubeAxisMidpoint I ∈ I.carrier :=
    tubeAxisMidpoint_mem_carrier I
  have hparentResidual0 :=
    Family8PaperConflictAnisotropicBoundsV4.norm_transverseResidual_midpoint_le_four_mul_of_mem_twoFold
      P (hIP hmidI)
  have hparentResidual :
      ‖transverseResidual P.axis.direction d‖ ≤ 4 * (rho : Real) := by
    have hdneg : d = -(tubeAxisMidpoint I - tubeAxisMidpoint P) := by
      dsimp only [d]
      module
    rw [hdneg,
      Family8PaperConflictAnisotropicBoundsV4.transverseResidual_neg_argument,
      norm_neg]
    rw [tubeAxisMidpoint_eq_commonPointTubeAxisMidpoint P]
    exact hparentResidual0
  have hprojection :
      ‖transverseResidual I.axis.direction d -
          transverseResidual P.axis.direction d‖ ≤
        32 * (rho : Real) := by
    rcases hprojective with hforward | hreverse
    · calc
        ‖transverseResidual I.axis.direction d -
            transverseResidual P.axis.direction d‖ ≤
            2 * ‖d‖ * ‖I.axis.direction - P.axis.direction‖ :=
          norm_transverseResidual_sub_le
            I.axis.norm_direction P.axis.norm_direction
        _ ≤ 2 * 2 * (8 * (rho : Real)) := by gcongr
        _ = 32 * (rho : Real) := by ring
    · calc
        ‖transverseResidual I.axis.direction d -
            transverseResidual P.axis.direction d‖ ≤
            2 * ‖d‖ * ‖I.axis.direction + P.axis.direction‖ :=
          norm_transverseResidual_sub_le_of_neg
            I.axis.norm_direction P.axis.norm_direction
        _ ≤ 2 * 2 * (8 * (rho : Real)) := by gcongr
        _ = 32 * (rho : Real) := by ring
  have hanchorResidual :
      ‖transverseResidual I.axis.direction d‖ ≤ 36 * (rho : Real) := by
    calc
      ‖transverseResidual I.axis.direction d‖ ≤
          ‖transverseResidual I.axis.direction d -
              transverseResidual P.axis.direction d‖ +
            ‖transverseResidual P.axis.direction d‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le
            (transverseResidual I.axis.direction d -
              transverseResidual P.axis.direction d)
            (transverseResidual P.axis.direction d)
      _ ≤ 32 * (rho : Real) + 4 * (rho : Real) :=
        add_le_add hprojection hparentResidual
      _ = 36 * (rho : Real) := by ring
  have hdir :
      ‖V.axis.direction - I.axis.direction‖ ≤ 8 * (rho : Real) := by
    simpa only [V, anchor] using
      norm_orientedParentDirection_sub_fine_le_eight_mul I P hIP
  have hmidV : tubeAxisMidpoint V = tubeAxisMidpoint P := by
    rw [tubeAxisMidpoint_eq_commonPointTubeAxisMidpoint V,
      tubeAxisMidpoint_eq_commonPointTubeAxisMidpoint P]
    exact paperConflictOrientedTube_midpoint anchor P
  have hmidAnchor : tubeAxisMidpoint anchor = tubeAxisMidpoint I := by
    simp only [anchor, tubeAxisMidpoint, Tube.changeRadius_axis]
  have hbudget : ∀ k : Fin 3,
      (rho : Real) +
          |⟪frame k, tubeAxisMidpoint V - tubeAxisMidpoint anchor⟫_Real| +
          (2 : Real)⁻¹ * |⟪frame k, V.axis.direction⟫_Real| ≤
        ((paperElongatedSides rho k : NNReal) : Real) / 2 := by
    intro k
    rw [hmidV, hmidAnchor]
    change (rho : Real) + |⟪frame k, d⟫_Real| +
        (2 : Real)⁻¹ * |⟪frame k, V.axis.direction⟫_Real| ≤ _
    have hmidAll : |⟪frame k, d⟫_Real| ≤ 2 := by
      have hinner := abs_real_inner_le_norm (frame k) d
      rw [frame.norm_eq_one, one_mul] at hinner
      exact hinner.trans hd
    have hdirAll : |⟪frame k, V.axis.direction⟫_Real| ≤ 1 := by
      have hinner := abs_real_inner_le_norm (frame k) V.axis.direction
      rw [frame.norm_eq_one, one_mul, V.axis.norm_direction] at hinner
      exact hinner
    have hrhoReal : (rho : Real) ≤ (1 : Real) / 16 := by
      exact_mod_cast hrho
    fin_cases k
    · have horth : ⟪frame 0, I.axis.direction⟫_Real = 0 := by
        rw [← hframe]
        exact frame.inner_eq_zero (by decide)
      have hcoordEq :
          ⟪frame 0, d⟫_Real =
            ⟪frame 0, transverseResidual I.axis.direction d⟫_Real := by
        dsimp only [d]
        simp only [transverseResidual, inner_sub_right,
          real_inner_smul_right, horth, mul_zero, sub_zero]
      have hmidTrans : |⟪frame 0, d⟫_Real| ≤ 36 * (rho : Real) := by
        rw [hcoordEq]
        have hinner := abs_real_inner_le_norm
          (frame 0) (transverseResidual I.axis.direction d)
        rw [frame.norm_eq_one, one_mul] at hinner
        exact hinner.trans hanchorResidual
      have hdirEq :
          ⟪frame 0, V.axis.direction⟫_Real =
            ⟪frame 0, V.axis.direction - I.axis.direction⟫_Real := by
        rw [inner_sub_right, horth, sub_zero]
      have hdirTrans : |⟪frame 0, V.axis.direction⟫_Real| ≤
          8 * (rho : Real) := by
        rw [hdirEq]
        have hinner := abs_real_inner_le_norm
          (frame 0) (V.axis.direction - I.axis.direction)
        rw [frame.norm_eq_one, one_mul] at hinner
        exact hinner.trans hdir
      norm_num [paperElongatedSides] at ⊢
      nlinarith [NNReal.zero_le_coe (q := rho)]
    · have horth : ⟪frame 1, I.axis.direction⟫_Real = 0 := by
        rw [← hframe]
        exact frame.inner_eq_zero (by decide)
      have hcoordEq :
          ⟪frame 1, d⟫_Real =
            ⟪frame 1, transverseResidual I.axis.direction d⟫_Real := by
        dsimp only [d]
        simp only [transverseResidual, inner_sub_right,
          real_inner_smul_right, horth, mul_zero, sub_zero]
      have hmidTrans : |⟪frame 1, d⟫_Real| ≤ 36 * (rho : Real) := by
        rw [hcoordEq]
        have hinner := abs_real_inner_le_norm
          (frame 1) (transverseResidual I.axis.direction d)
        rw [frame.norm_eq_one, one_mul] at hinner
        exact hinner.trans hanchorResidual
      have hdirEq :
          ⟪frame 1, V.axis.direction⟫_Real =
            ⟪frame 1, V.axis.direction - I.axis.direction⟫_Real := by
        rw [inner_sub_right, horth, sub_zero]
      have hdirTrans : |⟪frame 1, V.axis.direction⟫_Real| ≤
          8 * (rho : Real) := by
        rw [hdirEq]
        have hinner := abs_real_inner_le_norm
          (frame 1) (V.axis.direction - I.axis.direction)
        rw [frame.norm_eq_one, one_mul] at hinner
        exact hinner.trans hdir
      norm_num [paperElongatedSides] at ⊢
      nlinarith [NNReal.zero_le_coe (q := rho)]
    · norm_num [paperElongatedSides] at ⊢
      norm_num at hrhoReal ⊢
      nlinarith
  have hV : V.carrier ⊆
      (paperElongatedBody anchor frame : Set Space) :=
    carrier_subset_paperElongatedBody_of_midpointDirectionBudget
      anchor V frame hbudget
  simpa only [V, anchor, paperConflictOrientedTube_carrier] using hV

#print axioms norm_orientedParentDirection_sub_fine_le_eight_mul
#print axioms parent_carrier_subset_fine_paperElongatedBody

end
end Family8IncidentParentElongatedContainmentV3
