import ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate

/-!
# Consumer: full-state FPUT endpoint certificate

This consumer records that a coupling of complete states, together with
ordinary Mathlib Lipschitz estimates for the modal observables, produces the
two scalar restart endpoints required by kinetic moment shadowing.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFullStateEndpointCertificate

open MeasureTheory
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} {M : Real}

/-- The certificate retains the full state `X` internally and exposes only
the two complex modal endpoints to the restart argument. -/
def problem_full_state_endpoint_certificate
    (data : FullStateEndpointPropagationData Omega X mu M) :
    AmplitudeCouplingRestartCertificate mu M :=
  data.toAmplitudeCouplingRestartCertificate

/-- Endpoint zero follows from Lipschitzness of the initial amplitude;
endpoint one follows from Lipschitz flow propagation and Picard
consistency. -/
theorem problem_full_state_endpoint_near
    (data : FullStateEndpointPropagationData Omega X mu M) (omega : Omega) :
    (‖data.initialAmplitude (data.actualInitial omega) -
        data.initialAmplitude (data.referenceInitial omega)‖ ≤
      data.initialDelta) ∧
    (‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      data.finalDelta) :=
  ⟨data.initial_near omega, data.final_near omega⟩

/-- The empty-bad-set certificate gives explicit second and fourth moment
costs at both endpoints. -/
theorem problem_full_state_endpoint_moment_errors
    (data : FullStateEndpointPropagationData Omega X mu M)
    [IsProbabilityMeasure mu] :
    let certificate := data.toAmplitudeCouplingRestartCertificate
    ((|∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
        2 * M * data.initialDelta) ∧
      (|∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw 0 -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw 0| ≤
        4 * M ^ 3 * data.initialDelta)) ∧
    ((|∫ z, Complex.normSq z ∂certificate.actualLaw 1 -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw 1| ≤
        2 * M * data.finalDelta) ∧
      (|∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw 1 -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw 1| ≤
        4 * M ^ 3 * data.finalDelta)) :=
  data.endpoint_second_fourth_moment_errors

/-- Cubic state coupling and cubic Picard consistency remain cubic at the
propagated scalar endpoint. -/
theorem problem_full_state_endpoint_abs_cube
    (data : FullStateEndpointPropagationData Omega X mu M)
    {g Cstate Cpicard : Real}
    (hstateCubic : data.stateDelta ≤ Cstate * |g| ^ 3)
    (hpicardCubic : data.picardDelta ≤ Cpicard * |g| ^ 3) :
    data.finalDelta ≤
      ((data.flowAmplification : Real) * Cstate + Cpicard) * |g| ^ 3 :=
  data.finalDelta_le_abs_cube hstateCubic hpicardCubic

#print axioms problem_full_state_endpoint_certificate
#print axioms problem_full_state_endpoint_near
#print axioms problem_full_state_endpoint_moment_errors
#print axioms problem_full_state_endpoint_abs_cube

end


end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFullStateEndpointCertificate
