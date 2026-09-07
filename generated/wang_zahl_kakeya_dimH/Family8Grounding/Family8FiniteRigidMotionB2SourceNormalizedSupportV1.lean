import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizationCoreV1
import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionB2SourceNormalizedSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalTranslationV2

noncomputable section

/-!
# Unit support after moving a B2 source and eighth-normalizing

The row long-tube source is naturally supported in `B(0,2)`, rather than in
the unit ball.  A sampled physical translation has norm at most one, so an
orthogonal rotation followed by that translation lies in `B(0,3)`.  The
existing eighth normalization still has ample room: its extended unit axis
lies in `B(0,7/8)`, and the normalized tube radius is at most `1/16`.

These lemmas remove the false need for source admissibility (whose unit-ball
field would also carry an unrelated essential-distinctness field).
-/

theorem orthogonalTranslationRigidMotion_mem_closedBall_three
    {U : OrthogonalThree} {t x : Space}
    (ht : ‖t‖ ≤ 1)
    (hx : x ∈ Metric.closedBall (0 : Space) 2) :
    orthogonalTranslationRigidMotion U t x ∈
      Metric.closedBall (0 : Space) 3 := by
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  rw [orthogonalTranslationRigidMotion_apply]
  calc
    ‖t + orthogonalThreeCLM U x‖ ≤
        ‖t‖ + ‖orthogonalThreeCLM U x‖ := norm_add_le _ _
    _ = ‖t‖ + ‖x‖ := by
      rw [← orthogonalThreeLinearIsometryEquiv_apply,
        orthogonalThreeLinearIsometryEquiv_norm]
    _ ≤ 3 := by linarith

theorem orthogonalTranslationRigidMotion_image_twoBall_subset_three
    {U : OrthogonalThree} {t : Space} (ht : ‖t‖ ≤ 1) :
    orthogonalTranslationRigidMotion U t ''
        Metric.closedBall (0 : Space) 2 ⊆
      Metric.closedBall (0 : Space) 3 := by
  rintro _ ⟨x, hx, rfl⟩
  exact orthogonalTranslationRigidMotion_mem_closedBall_three ht hx

theorem norm_tubeAxisMidpoint_le_three_of_carrier_subset
    {delta : NNReal} (T : Tube delta)
    (hB3 : T.carrier ⊆ Metric.closedBall (0 : Space) 3) :
    ‖tubeAxisMidpoint T‖ ≤ 3 := by
  have hm := hB3 (tubeAxisMidpoint_mem_carrier T)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hm

theorem eighthNormalizedAxis_carrier_subset_sevenEighthsBall
    {delta : NNReal} (T : Tube delta)
    (hB3 : T.carrier ⊆ Metric.closedBall (0 : Space) 3) :
    (eighthNormalizedAxis T).carrier ⊆
      Metric.closedBall (0 : Space) (7 / 8 : Real) := by
  intro x hx
  rw [UnitSegment.carrier_eq_image] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmid := norm_tubeAxisMidpoint_le_three_of_carrier_subset T hB3
  have hcenter :
      ‖eighthDilationPoint (tubeAxisMidpoint T)‖ ≤ (3 / 8 : Real) := by
    calc
      ‖eighthDilationPoint (tubeAxisMidpoint T)‖ =
          (1 / 8 : Real) * ‖tubeAxisMidpoint T‖ := by
        simp [eighthDilationPoint, norm_smul]
      _ ≤ (1 / 8 : Real) * 3 := by gcongr
      _ = (3 / 8 : Real) := by norm_num
  have hoffset :
      ‖(s - 1 / 2 : Real) • T.axis.direction‖ ≤ (1 / 2 : Real) := by
    rw [norm_smul, T.axis.norm_direction, mul_one, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hpoint :
      (eighthNormalizedAxis T).base +
          s • (eighthNormalizedAxis T).direction =
        eighthDilationPoint (tubeAxisMidpoint T) +
          (s - 1 / 2 : Real) • T.axis.direction := by
    simp only [eighthNormalizedAxis_base, eighthNormalizedAxis_direction]
    module
  change ‖(eighthNormalizedAxis T).base +
    s • (eighthNormalizedAxis T).direction‖ ≤ (7 / 8 : Real)
  rw [hpoint]
  calc
    ‖eighthDilationPoint (tubeAxisMidpoint T) +
        (s - 1 / 2 : Real) • T.axis.direction‖ ≤
        ‖eighthDilationPoint (tubeAxisMidpoint T)‖ +
          ‖(s - 1 / 2 : Real) • T.axis.direction‖ := norm_add_le _ _
    _ ≤ (3 / 8 : Real) + (1 / 2 : Real) := add_le_add hcenter hoffset
    _ = (7 / 8 : Real) := by norm_num

theorem eighthNormalizedTube_carrier_subset_unitBall_of_threeBall
    {delta : NNReal} (T : Tube delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hB3 : T.carrier ⊆ Metric.closedBall (0 : Space) 3) :
    (eighthNormalizedTube T).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  have haxis :=
    eighthNormalizedAxis_carrier_subset_sevenEighthsBall T hB3
  have hradius : ((delta / 8 : NNReal) : Real) ≤ (1 / 16 : Real) := by
    have hreal' : (delta : Real) ≤ (((2 : NNReal)⁻¹ : NNReal) : Real) :=
      NNReal.coe_le_coe.mpr hdeltaHalf
    have hreal : (delta : Real) ≤ (1 / 2 : Real) := by
      simpa using hreal'
    push_cast
    linarith
  change Metric.cthickening ((delta / 8 : NNReal) : Real)
      (eighthNormalizedAxis T).carrier ⊆ Metric.closedBall (0 : Space) 1
  refine (Metric.cthickening_subset_of_subset _ haxis).trans ?_
  rw [cthickening_closedBall (by positivity) (by norm_num)]
  exact Metric.closedBall_subset_closedBall (by linarith)

/-- The exact support statement used by the normalized product copy. -/
theorem eighthNormalized_orthogonalTranslation_carrier_subset_unitBall_of_B2
    {delta : NNReal} (T : Tube delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hB2 : T.carrier ⊆ Metric.closedBall (0 : Space) 2)
    (U : OrthogonalThree) (t : Space) (ht : ‖t‖ ≤ 1) :
    (eighthNormalizedTube
      (rigidTube (orthogonalTranslationRigidMotion U t) T)).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
  apply eighthNormalizedTube_carrier_subset_unitBall_of_threeBall _ hdeltaHalf
  rw [rigidTube_carrier]
  exact (Set.image_mono hB2).trans
    (orthogonalTranslationRigidMotion_image_twoBall_subset_three ht)

#print axioms orthogonalTranslationRigidMotion_mem_closedBall_three
#print axioms orthogonalTranslationRigidMotion_image_twoBall_subset_three
#print axioms norm_tubeAxisMidpoint_le_three_of_carrier_subset
#print axioms eighthNormalizedAxis_carrier_subset_sevenEighthsBall
#print axioms eighthNormalizedTube_carrier_subset_unitBall_of_threeBall
#print axioms
  eighthNormalized_orthogonalTranslation_carrier_subset_unitBall_of_B2

end
end Family8FiniteRigidMotionB2SourceNormalizedSupportV1
