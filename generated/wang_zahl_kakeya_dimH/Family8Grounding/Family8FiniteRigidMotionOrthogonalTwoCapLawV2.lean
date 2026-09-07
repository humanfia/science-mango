import Family8Grounding.Family8FiniteRigidMotionOrthogonalHundredContainmentMeanV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTwoCapLawV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalOrbitV3
open Family8FiniteRigidMotionOrthogonalOrbitLawV2
open Family8FiniteRigidMotionOrthogonalCapProbabilityV1
open Family8FiniteRigidMotionOrthogonalHundredContainmentMeanV2

noncomputable section

/-!
# Measurable two-cap events for the orthogonal Haar law

The literal hundred-containment event is contained in a union of two
direction caps.  Unlike containment itself, this cap union has an immediate
measurability proof and is therefore suitable for simultaneous finite
incidence-pattern sampling.
-/

noncomputable instance orthogonalThreeHaarProbability_isProbability :
    IsProbabilityMeasure orthogonalThreeHaarProbability :=
  ⟨orthogonalThreeHaarProbability_univ⟩

def orthogonalTwoCapEvent
    (u c : Space) (cap : NNReal) : Set OrthogonalThree :=
  orthogonalOrbit u ⁻¹' Metric.ball c (cap : Real) ∪
    orthogonalOrbit u ⁻¹' Metric.ball (-c) (cap : Real)

theorem measurableSet_orthogonalTwoCapEvent
    (u c : Space) (cap : NNReal) :
    MeasurableSet (orthogonalTwoCapEvent u c cap) := by
  exact
    ((measurable_orthogonalOrbit u) measurableSet_ball).union
      ((measurable_orthogonalOrbit u) measurableSet_ball)

theorem orthogonalTwoCapEvent_toReal_le_ten_mul_sq
    (u c : Space) (hc : ‖c‖ = 1)
    (cap : NNReal) (hcap : 0 < cap) (hcapHalf : cap ≤ 1 / 2) :
    (orthogonalThreeHaarProbability
        (orthogonalTwoCapEvent u c cap)).toReal ≤
      10 * (cap : Real) ^ 2 := by
  let A : Set OrthogonalThree :=
    orthogonalOrbit u ⁻¹' Metric.ball c (cap : Real)
  let B : Set OrthogonalThree :=
    orthogonalOrbit u ⁻¹' Metric.ball (-c) (cap : Real)
  have hmeasure :
      orthogonalThreeHaarProbability (A ∪ B) ≤
        orthogonalThreeHaarProbability A +
          orthogonalThreeHaarProbability B :=
    measure_union_le A B
  have hA :
      orthogonalThreeHaarProbability A =
        orthogonalOrbitLaw u (Metric.ball c (cap : Real)) := by
    rw [orthogonalOrbitLaw,
      Measure.map_apply (measurable_orthogonalOrbit u) measurableSet_ball]
  have hB :
      orthogonalThreeHaarProbability B =
        orthogonalOrbitLaw u (Metric.ball (-c) (cap : Real)) := by
    rw [orthogonalOrbitLaw,
      Measure.map_apply (measurable_orthogonalOrbit u) measurableSet_ball]
  have hAne : orthogonalThreeHaarProbability A ≠ ∞ := by
    rw [hA]
    apply ne_of_lt
    calc
      orthogonalOrbitLaw u (Metric.ball c (cap : Real)) ≤
          orthogonalOrbitLaw u Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := orthogonalOrbitLaw_univ u
      _ < ∞ := ENNReal.one_lt_top
  have hBne : orthogonalThreeHaarProbability B ≠ ∞ := by
    rw [hB]
    apply ne_of_lt
    calc
      orthogonalOrbitLaw u (Metric.ball (-c) (cap : Real)) ≤
          orthogonalOrbitLaw u Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := orthogonalOrbitLaw_univ u
      _ < ∞ := ENNReal.one_lt_top
  have hreal :=
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAne, hBne⟩) hmeasure
  rw [ENNReal.toReal_add hAne hBne, hA, hB] at hreal
  have hcapA :=
    orthogonalOrbitLaw_unitBall_toReal_le_five_mul_sq
      u c hc cap hcap hcapHalf
  have hcapB :=
    orthogonalOrbitLaw_unitBall_toReal_le_five_mul_sq
      u (-c) (by simpa using hc) cap hcap hcapHalf
  change
    (orthogonalThreeHaarProbability (A ∪ B)).toReal ≤
      10 * (cap : Real) ^ 2
  nlinarith

theorem orthogonalHundredContainmentEvent_subset_twoCapEvent
    {delta : NNReal} (T W : Tube delta) (t : Space)
    (hdelta : 0 < delta) :
    orthogonalHundredContainmentEvent T W t ⊆
      orthogonalTwoCapEvent T.axis.direction W.axis.direction
        ((601 : NNReal) * delta) := by
  simpa only [orthogonalTwoCapEvent] using
    orthogonalHundredContainmentEvent_subset_twoCaps T W t hdelta

#print axioms measurableSet_orthogonalTwoCapEvent
#print axioms orthogonalTwoCapEvent_toReal_le_ten_mul_sq
#print axioms orthogonalHundredContainmentEvent_subset_twoCapEvent

end
end Family8FiniteRigidMotionOrthogonalTwoCapLawV2
