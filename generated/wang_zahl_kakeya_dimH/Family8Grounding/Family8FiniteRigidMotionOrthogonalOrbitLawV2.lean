import Family8Grounding.Family8FiniteRigidMotionOrthogonalTransitiveV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace
open scoped Matrix.Norms.L2Operator

namespace Family8FiniteRigidMotionOrthogonalOrbitLawV2

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalOrbitV3
open Family8FiniteRigidMotionOrthogonalTransitiveV2

noncomputable section

/-!
# The normalized rotation-invariant direction law

Push normalized Haar measure on `O(3)` through the actual orbit of a fixed
vector.  Left Haar invariance and the proved action composition law make this
pushforward invariant under every orthogonal transformation.  In particular,
equal-radius balls with centers on the same sphere have equal probability.
-/

def orthogonalOrbitLaw (u : Space) : Measure Space :=
  Measure.map (orthogonalOrbit u) orthogonalThreeHaarProbability

@[simp] theorem orthogonalOrbitLaw_univ (u : Space) :
    orthogonalOrbitLaw u Set.univ = 1 := by
  rw [orthogonalOrbitLaw,
    Measure.map_apply (measurable_orthogonalOrbit u) MeasurableSet.univ]
  simp

theorem orthogonalOrbitLaw_map_action
    (u : Space) (U : OrthogonalThree) :
    Measure.map (orthogonalThreeCLM U) (orthogonalOrbitLaw u) =
      orthogonalOrbitLaw u := by
  have haction : Measurable (orthogonalThreeCLM U) :=
    (orthogonalThreeCLM U).continuous.measurable
  have hleft : Measurable (fun V : OrthogonalThree ↦ U * V) :=
    (continuous_const.mul continuous_id).measurable
  unfold orthogonalOrbitLaw
  calc
    Measure.map (orthogonalThreeCLM U)
        (Measure.map (orthogonalOrbit u) orthogonalThreeHaarProbability) =
      Measure.map (orthogonalThreeCLM U ∘ orthogonalOrbit u)
        orthogonalThreeHaarProbability :=
      Measure.map_map haction (measurable_orthogonalOrbit u)
    _ = Measure.map (orthogonalOrbit u ∘ fun V : OrthogonalThree ↦ U * V)
        orthogonalThreeHaarProbability := by
      apply Measure.map_congr
      filter_upwards with V
      exact (orthogonalOrbit_mul u U V).symm
    _ = Measure.map (orthogonalOrbit u)
        (Measure.map (fun V : OrthogonalThree ↦ U * V)
          orthogonalThreeHaarProbability) :=
      (Measure.map_map (measurable_orthogonalOrbit u) hleft).symm
    _ = Measure.map (orthogonalOrbit u) orthogonalThreeHaarProbability := by
      rw [orthogonalThreeHaarProbability_map_mul_left]

theorem preimage_ball_orthogonalThreeCLM
    (U : OrthogonalThree) (c : Space) (r : Real) :
    orthogonalThreeCLM U ⁻¹'
        Metric.ball (orthogonalThreeCLM U c) r =
      Metric.ball c r := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_ball]
  change dist (orthogonalThreeLinearIsometryEquiv U x)
      (orthogonalThreeLinearIsometryEquiv U c) < r ↔ dist x c < r
  rw [(orthogonalThreeLinearIsometryEquiv U).isometry.dist_eq]

theorem orthogonalOrbitLaw_ball_action
    (u c : Space) (U : OrthogonalThree) (r : Real) :
    orthogonalOrbitLaw u
        (Metric.ball (orthogonalThreeCLM U c) r) =
      orthogonalOrbitLaw u (Metric.ball c r) := by
  have hmap := congrArg
    (fun μ : Measure Space ↦
      μ (Metric.ball (orthogonalThreeCLM U c) r))
    (orthogonalOrbitLaw_map_action u U)
  rw [Measure.map_apply (orthogonalThreeCLM U).continuous.measurable
      measurableSet_ball,
    preimage_ball_orthogonalThreeCLM] at hmap
  exact hmap.symm

theorem orthogonalOrbitLaw_ball_eq_of_norm_eq
    (u c d : Space) (hcd : ‖c‖ = ‖d‖) (r : Real) :
    orthogonalOrbitLaw u (Metric.ball c r) =
      orthogonalOrbitLaw u (Metric.ball d r) := by
  let U := directionOrthogonal c d
  have hmaps : orthogonalThreeCLM U c = d :=
    directionOrthogonal_apply_of_norm_eq hcd
  simpa only [hmaps] using (orthogonalOrbitLaw_ball_action u c U r).symm

#print axioms orthogonalOrbitLaw_univ
#print axioms orthogonalOrbitLaw_map_action
#print axioms preimage_ball_orthogonalThreeCLM
#print axioms orthogonalOrbitLaw_ball_action
#print axioms orthogonalOrbitLaw_ball_eq_of_norm_eq

end
end Family8FiniteRigidMotionOrthogonalOrbitLawV2
