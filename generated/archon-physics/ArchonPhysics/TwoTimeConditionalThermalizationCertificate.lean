import ArchonPhysics.ConditionalThermalizationCertificate
import ArchonPhysics.TwoTimeProbabilisticHittingTransfer

/-!
# Release-level microscopic thermalization certificate

The existing conditional certificate reaches the enhanced convergence to one
crossing constant.  For the first release root, the same microscopic error
fields need only a robust two-time kinetic window.  This module derives the
`HighProbabilityG2Bounds` structure directly, without passing through
`G2TeqConvergesInProbability`.
-/

namespace ArchonPhysics.TwoTimeConditionalThermalizationCertificate

open ArchonPhysics
open ArchonPhysics.ProbabilisticHittingTransfer
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.TwoTimeKineticHittingBounds
open ArchonPhysics.TwoTimeProbabilisticHittingTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-- A robust lower/upper kinetic window and the existing microscopic
certificate directly produce the first two-sided probabilistic release law.
-/
theorem ConditionalThermalizationCertificate.toHighProbabilityG2Bounds_of_twoTimeWindow
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (equilibrationTime : Nat -> Real -> Omega -> ENNReal)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta lower upper : Real)
    (certificate : ConditionalThermalizationCertificate probability
      equilibrationTime sizeCutoff kineticDistance delta)
    (window : RobustKineticHittingWindow
      kineticDistance delta lower upper) :
    HighProbabilityG2Bounds probability equilibrationTime
      sizeCutoff lower upper := by
  refine ⟨window.lower_pos, window.lower_le_upper,
    certificate.equilibrationTime_measurable, ?_⟩
  intro jointLimit
  have hwindow : Tendsto
      (fun j => probability
        (twoTimeHittingWindowEvent
          (fun j omega => certificate.scaledMicroscopicDistance
            (jointLimit.systemSize j) (jointLimit.coupling j) omega)
          delta lower upper j))
      atTop (nhds 1) := by
    exact random_local_uniform_error_implies_twoTime_hitting_window
      probability
      (fun j omega => certificate.scaledMicroscopicDistance
        (jointLimit.systemSize j) (jointLimit.coupling j) omega)
      (fun j omega => certificate.localUniformError upper
        (jointLimit.systemSize j) (jointLimit.coupling j) omega)
      delta lower upper window
      (certificate.localUniformError_convergesInProbability
        probability equilibrationTime sizeCutoff kineticDistance delta
        jointLimit upper
        (window.lower_pos.trans_le window.lower_le_upper))
      (fun eta heta j omega hsmall =>
        certificate.localUniformError_controls jointLimit upper eta
          (window.lower_pos.trans_le window.lower_le_upper) heta
          j omega hsmall)
  apply hwindow.congr'
  exact Eventually.of_forall fun j => by
    apply congrArg probability
    ext omega
    simp only [scalingWindowEvent, twoTimeHittingWindowEvent,
      Set.mem_preimage, Set.mem_Icc]
    rw [certificate.scaledEquilibrationTime_eq_hittingTime
      jointLimit j omega]
    rfl

/-- Initial separation, continuity at zero, and eventual kinetic relaxation
already yield some positive finite constants for the release law. -/
theorem ConditionalThermalizationCertificate.exists_highProbabilityG2Bounds_of_relaxation
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (equilibrationTime : Nat -> Real -> Omega -> ENNReal)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta : Real)
    (certificate : ConditionalThermalizationCertificate probability
      equilibrationTime sizeCutoff kineticDistance delta)
    (relaxation : RelaxationToTwoTimeWindow kineticDistance delta) :
    exists lower upper : Real,
      HighProbabilityG2Bounds probability equilibrationTime
        sizeCutoff lower upper := by
  obtain ⟨lower, upper, window⟩ :=
    relaxation.exists_robustKineticHittingWindow
  exact ⟨lower, upper,
    ConditionalThermalizationCertificate.toHighProbabilityG2Bounds_of_twoTimeWindow
      probability equilibrationTime sizeCutoff kineticDistance
      delta lower upper certificate window⟩

end

end ArchonPhysics.TwoTimeConditionalThermalizationCertificate
