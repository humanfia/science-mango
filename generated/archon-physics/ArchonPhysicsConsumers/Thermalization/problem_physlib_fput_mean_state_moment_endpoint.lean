import ArchonPhysics.PhyslibFPUTMeanStateMomentEndpoint

/-!
# Consumer: direct mean-state FPUT endpoint moment control

This consumer checks that an `O(|g|^3)` mean coupling can be used directly
for moment propagation.  It does not turn that mean coupling into a
high-probability full-state RPA event and does not assert that an independent
fresh Haar state satisfies the premise.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTMeanStateMomentEndpoint

open MeasureTheory
open ArchonPhysics.PhyslibFPUTMeanStateMomentEndpoint

noncomputable section

theorem direct_mean_amplitude_contract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → Complex) (hX : Measurable X) (hY : Measurable Y)
    {M eta : Real} (hM : 0 ≤ M)
    (hDistanceIntegrable : Integrable (fun omega ↦ ‖X omega - Y omega‖) mu)
    (hMeanDistance :
      (∫ omega, ‖X omega - Y omega‖ ∂mu) ≤ eta)
    (hXBound : ∀ omega, ‖X omega‖ ≤ M)
    (hYBound : ∀ omega, ‖Y omega‖ ≤ M) :
    |∫ omega, Complex.normSq (X omega) ∂mu -
        ∫ omega, Complex.normSq (Y omega) ∂mu| ≤ 2 * M * eta ∧
    |∫ omega, Complex.normSq (X omega) ^ 2 ∂mu -
        ∫ omega, Complex.normSq (Y omega) ^ 2 ∂mu| ≤ 4 * M ^ 3 * eta :=
  meanCoupled_second_fourth_moment_errors
    mu X Y hX hY hM hDistanceIntegrable hMeanDistance hXBound hYBound

theorem mean_full_state_endpoint_contract
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    ((|∫ omega, Complex.normSq (data.actualInitialAmplitude omega) ∂mu -
          ∫ omega, Complex.normSq (data.referenceInitialAmplitude omega) ∂mu| ≤
        2 * M * ((data.initialObservableAmplification : Real) *
          data.stateMeanDelta)) ∧
      (|∫ omega, Complex.normSq (data.actualInitialAmplitude omega) ^ 2 ∂mu -
          ∫ omega, Complex.normSq (data.referenceInitialAmplitude omega) ^ 2 ∂mu| ≤
        4 * M ^ 3 * ((data.initialObservableAmplification : Real) *
          data.stateMeanDelta))) ∧
    ((|∫ omega, Complex.normSq (data.actualFinalAmplitude omega) ∂mu -
          ∫ omega, Complex.normSq (data.referenceFinalAmplitude omega) ∂mu| ≤
        2 * M * ((data.flowAmplification : Real) * data.stateMeanDelta +
          data.picardDelta)) ∧
      (|∫ omega, Complex.normSq (data.actualFinalAmplitude omega) ^ 2 ∂mu -
          ∫ omega, Complex.normSq (data.referenceFinalAmplitude omega) ^ 2 ∂mu| ≤
        4 * M ^ 3 * ((data.flowAmplification : Real) * data.stateMeanDelta +
          data.picardDelta))) :=
  data.endpoint_second_fourth_moment_errors

theorem cubic_mean_distance_is_sufficient
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {M g Cstate : Real}
    (data : MeanFullStateEndpointPropagationData Omega X mu M)
    (hstate : data.stateMeanDelta ≤ Cstate * |g| ^ 3) :
    |∫ omega, Complex.normSq (data.actualInitialAmplitude omega) ∂mu -
        ∫ omega, Complex.normSq (data.referenceInitialAmplitude omega) ∂mu| ≤
      2 * M * ((data.initialObservableAmplification : Real) * Cstate) *
        |g| ^ 3 := by
  calc
    _ ≤ 2 * M * ((data.initialObservableAmplification : Real) *
        data.stateMeanDelta) :=
      data.endpoint_second_fourth_moment_errors.1.1
    _ ≤ 2 * M * ((data.initialObservableAmplification : Real) *
        (Cstate * |g| ^ 3)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hstate
          data.initialObservableAmplification.coe_nonneg
      · exact mul_nonneg (by norm_num) data.M_nonneg
    _ = 2 * M * ((data.initialObservableAmplification : Real) * Cstate) *
        |g| ^ 3 := by ring

#print axioms meanCoupled_second_fourth_moment_errors
#print axioms MeanFullStateEndpointPropagationData.endpoint_second_fourth_moment_errors
#print axioms direct_mean_amplitude_contract
#print axioms mean_full_state_endpoint_contract
#print axioms cubic_mean_distance_is_sufficient

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTMeanStateMomentEndpoint
