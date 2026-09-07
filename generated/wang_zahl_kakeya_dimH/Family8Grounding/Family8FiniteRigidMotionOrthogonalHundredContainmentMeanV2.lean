import Family8Grounding.Family8FiniteRigidMotionOrthogonalCapProbabilityV1
import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationV2
import FamilyStickyGrounding.FamilyStickyRandomWZLineParameterGeometryV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalHundredContainmentMeanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZLineParameterGeometryV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalOrbitV3
open Family8FiniteRigidMotionOrthogonalOrbitLawV2
open Family8FiniteRigidMotionOrthogonalCapProbabilityV1
open Family8FiniteRigidMotionOrthogonalTranslationV2

noncomputable section

/-!
# Uniform rotational mean for a literal paper `100 W` test

For every fixed translation, containment of a rotated source tube in a
literal `100 W` forces its moved direction to lie within `600 * delta` of
one of the two orientations of `W`.  The genuine Haar cap estimate bounds
those two alternatives by a quadratic quantity, uniformly in the translation.
-/

def orthogonalHundredContainmentEvent
    {delta : NNReal} (T W : Tube delta) (t : Space) : Set OrthogonalThree :=
  {U | (rigidTube (orthogonalTranslationRigidMotion U t) T).carrier ⊆
    (hundredTube W).carrier}

theorem orthogonalHundredContainmentEvent_subset_twoCaps
    {delta : NNReal} (T W : Tube delta) (t : Space)
    (hdelta : 0 < delta) :
    orthogonalHundredContainmentEvent T W t ⊆
      orthogonalOrbit T.axis.direction ⁻¹'
          Metric.ball W.axis.direction
            (((601 : NNReal) * delta : NNReal) : Real) ∪
        orthogonalOrbit T.axis.direction ⁻¹'
          Metric.ball (-W.axis.direction)
            (((601 : NNReal) * delta : NNReal) : Real) := by
  intro U hcontain
  obtain ⟨e, _hbase, hdir⟩ :=
    exists_orientation_componentwise_near_hundredContainer
      (rigidTube (orthogonalTranslationRigidMotion U t) T) W hcontain
  have hstrict :
      600 * (delta : Real) <
        (((601 : NNReal) * delta : NNReal) : Real) := by
    push_cast
    have hd : 0 < (delta : Real) := NNReal.coe_pos.mpr hdelta
    linarith
  cases e with
  | false =>
      apply Set.mem_union_left
      change dist (orthogonalOrbit T.axis.direction U)
          W.axis.direction <
        (((601 : NNReal) * delta : NNReal) : Real)
      rw [dist_eq_norm]
      have hdir' :
          ‖orthogonalOrbit T.axis.direction U - W.axis.direction‖ ≤
            600 * (delta : Real) := by
        simpa only [orientedLineParameter_false,
          rigidTube_orthogonalTranslation_direction] using hdir
      exact hdir'.trans_lt hstrict
  | true =>
      apply Set.mem_union_right
      change dist (orthogonalOrbit T.axis.direction U)
          (-W.axis.direction) <
        (((601 : NNReal) * delta : NNReal) : Real)
      rw [dist_eq_norm]
      have hdir' :
          ‖-(orthogonalOrbit T.axis.direction U) - W.axis.direction‖ ≤
            600 * (delta : Real) := by
        simpa only [orientedLineParameter_true,
          rigidTube_orthogonalTranslation_direction] using hdir
      have hnorm :
          ‖orthogonalOrbit T.axis.direction U - (-W.axis.direction)‖ =
            ‖-(orthogonalOrbit T.axis.direction U) - W.axis.direction‖ := by
        rw [show orthogonalOrbit T.axis.direction U - (-W.axis.direction) =
            -(-(orthogonalOrbit T.axis.direction U) - W.axis.direction) by
          module, norm_neg]
      rw [hnorm]
      exact hdir'.trans_lt hstrict

theorem orthogonalHundredContainmentEvent_toReal_le_ten_mul_sq
    {delta : NNReal} (T W : Tube delta) (t : Space)
    (hdelta : 0 < delta)
    (hsmall : (601 : NNReal) * delta ≤ 1 / 2) :
    (orthogonalThreeHaarProbability
        (orthogonalHundredContainmentEvent T W t)).toReal ≤
      10 * ((((601 : NNReal) * delta : NNReal) : Real) ^ 2) := by
  let mesh : NNReal := (601 : NNReal) * delta
  let A : Set OrthogonalThree :=
    orthogonalOrbit T.axis.direction ⁻¹'
      Metric.ball W.axis.direction (mesh : Real)
  let B : Set OrthogonalThree :=
    orthogonalOrbit T.axis.direction ⁻¹'
      Metric.ball (-W.axis.direction) (mesh : Real)
  have hsubset : orthogonalHundredContainmentEvent T W t ⊆ A ∪ B := by
    simpa only [A, B, mesh] using
      orthogonalHundredContainmentEvent_subset_twoCaps T W t hdelta
  have hmeasure :
      orthogonalThreeHaarProbability
          (orthogonalHundredContainmentEvent T W t) ≤
        orthogonalThreeHaarProbability A +
          orthogonalThreeHaarProbability B :=
    (measure_mono hsubset).trans (measure_union_le A B)
  have hA : orthogonalThreeHaarProbability A =
      orthogonalOrbitLaw T.axis.direction
        (Metric.ball W.axis.direction (mesh : Real)) := by
    rw [orthogonalOrbitLaw,
      Measure.map_apply (measurable_orthogonalOrbit T.axis.direction)
        measurableSet_ball]
  have hB : orthogonalThreeHaarProbability B =
      orthogonalOrbitLaw T.axis.direction
        (Metric.ball (-W.axis.direction) (mesh : Real)) := by
    rw [orthogonalOrbitLaw,
      Measure.map_apply (measurable_orthogonalOrbit T.axis.direction)
        measurableSet_ball]
  have hAne : orthogonalThreeHaarProbability A ≠ ∞ := by
    rw [hA]
    apply ne_of_lt
    calc
      orthogonalOrbitLaw T.axis.direction
          (Metric.ball W.axis.direction (mesh : Real)) ≤
          orthogonalOrbitLaw T.axis.direction Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := orthogonalOrbitLaw_univ T.axis.direction
      _ < ∞ := ENNReal.one_lt_top
  have hBne : orthogonalThreeHaarProbability B ≠ ∞ := by
    rw [hB]
    apply ne_of_lt
    calc
      orthogonalOrbitLaw T.axis.direction
          (Metric.ball (-W.axis.direction) (mesh : Real)) ≤
          orthogonalOrbitLaw T.axis.direction Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := orthogonalOrbitLaw_univ T.axis.direction
      _ < ∞ := ENNReal.one_lt_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hAne, hBne⟩) hmeasure
  rw [ENNReal.toReal_add hAne hBne, hA, hB] at hreal
  have hmeshPos : 0 < mesh := by
    exact mul_pos (by norm_num) hdelta
  have hcapA := orthogonalOrbitLaw_unitBall_toReal_le_five_mul_sq
    T.axis.direction W.axis.direction W.axis.norm_direction
      mesh hmeshPos (by simpa only [mesh] using hsmall)
  have hcapB := orthogonalOrbitLaw_unitBall_toReal_le_five_mul_sq
    T.axis.direction (-W.axis.direction)
      (by rw [norm_neg, W.axis.norm_direction])
      mesh hmeshPos (by simpa only [mesh] using hsmall)
  have hresult :
      (orthogonalThreeHaarProbability
          (orthogonalHundredContainmentEvent T W t)).toReal ≤
        10 * (mesh : Real) ^ 2 := by
    nlinarith
  simpa only [mesh] using hresult

#print axioms orthogonalHundredContainmentEvent_subset_twoCaps
#print axioms orthogonalHundredContainmentEvent_toReal_le_ten_mul_sq

end
end Family8FiniteRigidMotionOrthogonalHundredContainmentMeanV2
