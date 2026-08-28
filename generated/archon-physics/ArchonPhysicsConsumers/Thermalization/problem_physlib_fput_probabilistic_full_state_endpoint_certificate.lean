import ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate

/-!
# Consumer: probabilistic full-state FPUT endpoint certificate

This consumer checks that a quantitative full-state RPA coupling outside a
measurable bad event produces the existing restart certificate and retains
the exact second/fourth-moment bad-event costs.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTProbabilisticFullStateEndpointCertificate

open MeasureTheory
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} {M : Real}

def problem_probabilistic_full_state_endpoint_certificate
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    AmplitudeCouplingRestartCertificate mu M :=
  data.toAmplitudeCouplingRestartCertificate

theorem problem_probabilistic_full_state_endpoint_good
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (omega : Omega) (homega : omega ∉ data.bad) :
    (‖data.initialAmplitude (data.actualInitial omega) -
        data.initialAmplitude (data.referenceInitial omega)‖ ≤
      data.initialDelta) ∧
    (‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      data.finalDelta) :=
  ⟨data.initial_near_on_good omega homega,
    data.final_near_on_good omega homega⟩

theorem problem_probabilistic_full_state_endpoint_moment_errors
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    [IsProbabilityMeasure mu] :
    let certificate := data.toAmplitudeCouplingRestartCertificate
    ((|∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
        2 * M * data.initialDelta +
          2 * M ^ 2 * data.failureProbability) ∧
      (|∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw 0| ≤
        4 * M ^ 3 * data.initialDelta +
          2 * M ^ 4 * data.failureProbability)) ∧
    ((|∫ z, Complex.normSq z ∂certificate.actualLaw 1 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 1| ≤
        2 * M * data.finalDelta +
          2 * M ^ 2 * data.failureProbability) ∧
      (|∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw 1 -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw 1| ≤
        4 * M ^ 3 * data.finalDelta +
          2 * M ^ 4 * data.failureProbability)) :=
  data.endpoint_second_fourth_moment_errors

theorem problem_probabilistic_full_state_endpoint_abs_cube
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    [IsProbabilityMeasure mu]
    {g Cstate Cpicard Cfailure : Real}
    (hstateCubic : data.stateDelta ≤ Cstate * |g| ^ 3)
    (hpicardCubic : data.picardDelta ≤ Cpicard * |g| ^ 3)
    (hfailureCubic : data.failureProbability ≤ Cfailure * |g| ^ 3) :
    let certificate := data.toAmplitudeCouplingRestartCertificate
    ((|∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
        (2 * M * ((data.initialObservableAmplification : Real) * Cstate) +
          2 * M ^ 2 * Cfailure) * |g| ^ 3) ∧
      (|∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw 0| ≤
        (4 * M ^ 3 *
            ((data.initialObservableAmplification : Real) * Cstate) +
          2 * M ^ 4 * Cfailure) * |g| ^ 3)) ∧
    ((|∫ z, Complex.normSq z ∂certificate.actualLaw 1 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 1| ≤
        (2 * M *
            ((data.flowAmplification : Real) * Cstate + Cpicard) +
          2 * M ^ 2 * Cfailure) * |g| ^ 3) ∧
      (|∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw 1 -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw 1| ≤
        (4 * M ^ 3 *
            ((data.flowAmplification : Real) * Cstate + Cpicard) +
          2 * M ^ 4 * Cfailure) * |g| ^ 3)) :=
  data.endpoint_second_fourth_moment_errors_le_abs_cube
    hstateCubic hpicardCubic hfailureCubic

#print axioms problem_probabilistic_full_state_endpoint_certificate
#print axioms problem_probabilistic_full_state_endpoint_good
#print axioms problem_probabilistic_full_state_endpoint_moment_errors
#print axioms problem_probabilistic_full_state_endpoint_abs_cube

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTProbabilisticFullStateEndpointCertificate
