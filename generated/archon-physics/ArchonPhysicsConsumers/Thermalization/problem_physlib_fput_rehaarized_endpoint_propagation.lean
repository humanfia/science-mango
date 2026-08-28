import ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation

/-!
# Consumer: propagation of a re-Haarized coupling across one FPUT block

The consumer records the two conclusions used by the kinetic restart DAG:
the final common-source coupling is derived from initial closeness, flow
stability, and second-Picard consistency; and the associated endpoint laws
have explicit zero-failure moment costs.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTReHaarizedEndpointPropagation

open MeasureTheory
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation

noncomputable section

/-- Consumer-facing deterministic endpoint triangle. -/
theorem problem_rehaarized_endpoint_propagation
    (actualBlock referenceBlock : Complex → Complex) (x y : Complex)
    {initialDelta flowAmplification picardDelta : Real}
    (hA : 0 ≤ flowAmplification)
    (hxy : ‖x - y‖ ≤ initialDelta)
    (hflow : ‖actualBlock x - actualBlock y‖ ≤
      flowAmplification * ‖x - y‖)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta) :
    ‖actualBlock x - referenceBlock y‖ ≤
      flowAmplification * initialDelta + picardDelta :=
  norm_actualBlock_sub_referenceBlock_le actualBlock referenceBlock x y
    hA hxy hflow hpicard

/-- Consumer-facing cubic closure. -/
theorem problem_rehaarized_endpoint_abs_cube
    (actualBlock referenceBlock : Complex → Complex) (x y : Complex)
    {g initialDelta flowAmplification picardDelta Cinitial Cpicard : Real}
    (hA : 0 ≤ flowAmplification)
    (hxy : ‖x - y‖ ≤ initialDelta)
    (hflow : ‖actualBlock x - actualBlock y‖ ≤
      flowAmplification * ‖x - y‖)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta)
    (hdelta0 : initialDelta ≤ Cinitial * |g| ^ 3)
    (hdeltaPicard : picardDelta ≤ Cpicard * |g| ^ 3) :
    ‖actualBlock x - referenceBlock y‖ ≤
      (flowAmplification * Cinitial + Cpicard) * |g| ^ 3 :=
  norm_actualBlock_sub_referenceBlock_le_abs_cube
    actualBlock referenceBlock x y hA hxy hflow hpicard
      hdelta0 hdeltaPicard

/-- The constructed two-endpoint certificate has no bad samples and carries
the explicit endpoint moment costs. -/
theorem problem_rehaarized_endpoint_certificate_moments
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
    (data : ReHaarizedEndpointPropagationData mu M) :
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

#print axioms problem_rehaarized_endpoint_propagation
#print axioms problem_rehaarized_endpoint_abs_cube
#print axioms problem_rehaarized_endpoint_certificate_moments
#print axioms ReHaarizedEndpointPropagationData.toAmplitudeCouplingRestartCertificate

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTReHaarizedEndpointPropagation
