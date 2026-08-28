import ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate

/-!
# Mean-state coupling controls FPUT endpoint moments directly

A high-probability full-state coupling is stronger than the moment control
needed by the kinetic restart.  This module records the direct Wasserstein-1
route: on a bounded complex-amplitude ball, the second- and fourth-moment
errors are controlled by the mean coupling distance itself.

Consequently an `O(|g|^3)` mean distance already gives `O(|g|^3)` moment
errors.  The `O(|g|^6)` input obtained by first creating a cubic-radius,
cubic-probability Markov event is sufficient but is not necessary for moment
propagation.

This theorem does not assert that an independently re-Haarized full state is
close to the Hamiltonian state.  That physical question remains separate.
-/

namespace ArchonPhysics.PhyslibFPUTMeanStateMomentEndpoint

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCouplingLawMomentControl
open ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

noncomputable section

/-- A bounded mean coupling controls the second and fourth amplitude moments
without introducing a bad event. -/
theorem meanCoupled_second_fourth_moment_errors
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
        ∫ omega, Complex.normSq (Y omega) ∂mu| ≤
        2 * M * eta ∧
    |∫ omega, Complex.normSq (X omega) ^ 2 ∂mu -
        ∫ omega, Complex.normSq (Y omega) ^ 2 ∂mu| ≤
        4 * M ^ 3 * eta := by
  have hXSecond : Integrable (fun omega ↦ Complex.normSq (X omega)) mu := by
    apply Integrable.of_bound
      (measurable_amplitudeSecondMomentObservable hX).aestronglyMeasurable
      (M ^ 2)
    filter_upwards with omega
    simpa [amplitudeSecondMomentObservable, Real.norm_eq_abs] using
      abs_amplitudeSecondMomentObservable_le hM hXBound omega
  have hYSecond : Integrable (fun omega ↦ Complex.normSq (Y omega)) mu := by
    apply Integrable.of_bound
      (measurable_amplitudeSecondMomentObservable hY).aestronglyMeasurable
      (M ^ 2)
    filter_upwards with omega
    simpa [amplitudeSecondMomentObservable, Real.norm_eq_abs] using
      abs_amplitudeSecondMomentObservable_le hM hYBound omega
  have hXFourth :
      Integrable (fun omega ↦ Complex.normSq (X omega) ^ 2) mu := by
    apply Integrable.of_bound
      (measurable_amplitudeFourthMomentObservable hX).aestronglyMeasurable
      (M ^ 4)
    filter_upwards with omega
    simpa [amplitudeFourthMomentObservable, Real.norm_eq_abs] using
      abs_amplitudeFourthMomentObservable_le hM hXBound omega
  have hYFourth :
      Integrable (fun omega ↦ Complex.normSq (Y omega) ^ 2) mu := by
    apply Integrable.of_bound
      (measurable_amplitudeFourthMomentObservable hY).aestronglyMeasurable
      (M ^ 4)
    filter_upwards with omega
    simpa [amplitudeFourthMomentObservable, Real.norm_eq_abs] using
      abs_amplitudeFourthMomentObservable_le hM hYBound omega
  have hSecondPoint : ∀ omega,
      |Complex.normSq (X omega) - Complex.normSq (Y omega)| ≤
        2 * M * ‖X omega - Y omega‖ := by
    intro omega
    exact abs_normSq_sub_normSq_le hM (norm_nonneg _)
      (hXBound omega) (hYBound omega) le_rfl
  have hFourthPoint : ∀ omega,
      |Complex.normSq (X omega) ^ 2 - Complex.normSq (Y omega) ^ 2| ≤
        4 * M ^ 3 * ‖X omega - Y omega‖ := by
    intro omega
    exact abs_normSq_sq_sub_normSq_sq_le hM (norm_nonneg _)
      (hXBound omega) (hYBound omega) le_rfl
  constructor
  · calc
      |∫ omega, Complex.normSq (X omega) ∂mu -
          ∫ omega, Complex.normSq (Y omega) ∂mu| =
          |∫ omega, Complex.normSq (X omega) -
            Complex.normSq (Y omega) ∂mu| := by
            rw [integral_sub hXSecond hYSecond]
      _ ≤ ∫ omega,
          |Complex.normSq (X omega) - Complex.normSq (Y omega)| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ omega, 2 * M * ‖X omega - Y omega‖ ∂mu := by
        apply integral_mono
        · simpa [Real.norm_eq_abs] using (hXSecond.sub hYSecond).norm
        · exact hDistanceIntegrable.const_mul (2 * M)
        · exact hSecondPoint
      _ = 2 * M * ∫ omega, ‖X omega - Y omega‖ ∂mu := by
        rw [integral_const_mul]
      _ ≤ 2 * M * eta :=
        mul_le_mul_of_nonneg_left hMeanDistance
          (mul_nonneg (by norm_num) hM)
  · calc
      |∫ omega, Complex.normSq (X omega) ^ 2 ∂mu -
          ∫ omega, Complex.normSq (Y omega) ^ 2 ∂mu| =
          |∫ omega, Complex.normSq (X omega) ^ 2 -
            Complex.normSq (Y omega) ^ 2 ∂mu| := by
            rw [integral_sub hXFourth hYFourth]
      _ ≤ ∫ omega,
          |Complex.normSq (X omega) ^ 2 -
            Complex.normSq (Y omega) ^ 2| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ omega, 4 * M ^ 3 * ‖X omega - Y omega‖ ∂mu := by
        apply integral_mono
        · simpa [Real.norm_eq_abs] using (hXFourth.sub hYFourth).norm
        · exact hDistanceIntegrable.const_mul (4 * M ^ 3)
        · exact hFourthPoint
      _ = 4 * M ^ 3 * ∫ omega, ‖X omega - Y omega‖ ∂mu := by
        rw [integral_const_mul]
      _ ≤ 4 * M ^ 3 * eta :=
        mul_le_mul_of_nonneg_left hMeanDistance
          (mul_nonneg (by norm_num) (pow_nonneg hM 3))


/-! ## Mean full-state endpoint data -/

/-- A bounded pair of measurable complex amplitudes has integrable coupling
distance on a probability space. -/
theorem amplitudeDistance_integrable_of_bounded
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → Complex) (hX : Measurable X) (hY : Measurable Y)
    {M : Real}
    (hXBound : ∀ omega, ‖X omega‖ ≤ M)
    (hYBound : ∀ omega, ‖Y omega‖ ≤ M) :
    Integrable (fun omega ↦ ‖X omega - Y omega‖) mu := by
  apply Integrable.of_bound (hX.sub hY).norm.aestronglyMeasurable (2 * M)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (norm_sub_le (X omega) (Y omega)).trans <| by
    calc
      ‖X omega‖ + ‖Y omega‖ ≤ M + M :=
        add_le_add (hXBound omega) (hYBound omega)
      _ = 2 * M := by ring

/-- Full-state endpoint input in which restart quality is measured only in
mean distance.  The Hamiltonian/Picard edge remains pointwise, while the
actual-to-reference state coupling is Wasserstein-1 type. -/
structure MeanFullStateEndpointPropagationData
    (Omega X : Type*) [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) (M : Real) where
  actualInitial : Omega → X
  referenceInitial : Omega → X
  initialAmplitude : X → Complex
  actualBlock : X → Complex
  referenceBlock : X → Complex
  stateMeanDelta : Real
  initialObservableAmplification : NNReal
  flowAmplification : NNReal
  picardDelta : Real
  M_nonneg : 0 ≤ M
  stateMeanDelta_nonneg : 0 ≤ stateMeanDelta
  picardDelta_nonneg : 0 ≤ picardDelta
  actualInitial_measurable : Measurable actualInitial
  referenceInitial_measurable : Measurable referenceInitial
  stateDistance_integrable :
    Integrable (fun omega ↦
      dist (actualInitial omega) (referenceInitial omega)) mu
  mean_state_near :
    (∫ omega, dist (actualInitial omega) (referenceInitial omega) ∂mu) ≤
      stateMeanDelta
  initialAmplitude_lipschitz :
    LipschitzWith initialObservableAmplification initialAmplitude
  actualBlock_lipschitz : LipschitzWith flowAmplification actualBlock
  referenceBlock_measurable : Measurable referenceBlock
  reference_consistent : ∀ omega,
    ‖actualBlock (referenceInitial omega) -
        referenceBlock (referenceInitial omega)‖ ≤ picardDelta
  actualInitial_bound : ∀ omega,
    ‖initialAmplitude (actualInitial omega)‖ ≤ M
  referenceInitial_bound : ∀ omega,
    ‖initialAmplitude (referenceInitial omega)‖ ≤ M
  actualFinal_bound : ∀ omega,
    ‖actualBlock (actualInitial omega)‖ ≤ M
  referenceFinal_bound : ∀ omega,
    ‖referenceBlock (referenceInitial omega)‖ ≤ M

namespace MeanFullStateEndpointPropagationData

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} {M : Real}

def actualInitialAmplitude
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Omega → Complex :=
  fun omega ↦ data.initialAmplitude (data.actualInitial omega)

def referenceInitialAmplitude
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Omega → Complex :=
  fun omega ↦ data.initialAmplitude (data.referenceInitial omega)

def actualFinalAmplitude
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Omega → Complex :=
  fun omega ↦ data.actualBlock (data.actualInitial omega)

def referenceFinalAmplitude
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Omega → Complex :=
  fun omega ↦ data.referenceBlock (data.referenceInitial omega)

theorem actualInitialAmplitude_measurable
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Measurable data.actualInitialAmplitude :=
  data.initialAmplitude_lipschitz.continuous.measurable.comp
    data.actualInitial_measurable

theorem referenceInitialAmplitude_measurable
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Measurable data.referenceInitialAmplitude :=
  data.initialAmplitude_lipschitz.continuous.measurable.comp
    data.referenceInitial_measurable

theorem actualFinalAmplitude_measurable
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Measurable data.actualFinalAmplitude :=
  data.actualBlock_lipschitz.continuous.measurable.comp
    data.actualInitial_measurable

theorem referenceFinalAmplitude_measurable
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Measurable data.referenceFinalAmplitude :=
  data.referenceBlock_measurable.comp data.referenceInitial_measurable

theorem initialAmplitudeDistance_integrable
    [IsProbabilityMeasure mu]
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Integrable (fun omega ↦
      ‖data.actualInitialAmplitude omega -
        data.referenceInitialAmplitude omega‖) mu :=
  amplitudeDistance_integrable_of_bounded mu
    data.actualInitialAmplitude data.referenceInitialAmplitude
    data.actualInitialAmplitude_measurable
    data.referenceInitialAmplitude_measurable
    data.actualInitial_bound data.referenceInitial_bound

theorem finalAmplitudeDistance_integrable
    [IsProbabilityMeasure mu]
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    Integrable (fun omega ↦
      ‖data.actualFinalAmplitude omega -
        data.referenceFinalAmplitude omega‖) mu :=
  amplitudeDistance_integrable_of_bounded mu
    data.actualFinalAmplitude data.referenceFinalAmplitude
    data.actualFinalAmplitude_measurable
    data.referenceFinalAmplitude_measurable
    data.actualFinal_bound data.referenceFinal_bound

/-- Mean initial amplitude distance obtained directly from the mean full-state
distance. -/
theorem mean_initialAmplitude_distance_le
    [IsProbabilityMeasure mu]
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    (∫ omega, ‖data.actualInitialAmplitude omega -
        data.referenceInitialAmplitude omega‖ ∂mu) ≤
      (data.initialObservableAmplification : Real) *
        data.stateMeanDelta := by
  calc
    (∫ omega, ‖data.actualInitialAmplitude omega -
        data.referenceInitialAmplitude omega‖ ∂mu) ≤
        ∫ omega, (data.initialObservableAmplification : Real) *
          dist (data.actualInitial omega) (data.referenceInitial omega) ∂mu := by
      apply integral_mono data.initialAmplitudeDistance_integrable
        (data.stateDistance_integrable.const_mul
          (data.initialObservableAmplification : Real))
      intro omega
      simpa only [actualInitialAmplitude, referenceInitialAmplitude,
        dist_eq_norm] using
        data.initialAmplitude_lipschitz.dist_le_mul
          (data.actualInitial omega) (data.referenceInitial omega)
    _ = (data.initialObservableAmplification : Real) *
        ∫ omega, dist (data.actualInitial omega)
          (data.referenceInitial omega) ∂mu := by
      rw [integral_const_mul]
    _ ≤ (data.initialObservableAmplification : Real) *
        data.stateMeanDelta :=
      mul_le_mul_of_nonneg_left data.mean_state_near
        data.initialObservableAmplification.coe_nonneg

/-- Mean endpoint amplitude distance after Lipschitz flow propagation and
the deterministic second-Picard comparison. -/
theorem mean_finalAmplitude_distance_le
    [IsProbabilityMeasure mu]
    (data : MeanFullStateEndpointPropagationData Omega X mu M) :
    (∫ omega, ‖data.actualFinalAmplitude omega -
        data.referenceFinalAmplitude omega‖ ∂mu) ≤
      (data.flowAmplification : Real) * data.stateMeanDelta +
        data.picardDelta := by
  have hscaledIntegrable :
      Integrable (fun omega ↦ (data.flowAmplification : Real) *
        dist (data.actualInitial omega) (data.referenceInitial omega)) mu :=
    data.stateDistance_integrable.const_mul (data.flowAmplification : Real)
  have hconstIntegrable : Integrable (fun _ : Omega ↦ data.picardDelta) mu :=
    integrable_const data.picardDelta
  have hmajorIntegrable :
      Integrable (fun omega ↦
        (data.flowAmplification : Real) *
            dist (data.actualInitial omega) (data.referenceInitial omega) +
          data.picardDelta) mu :=
    hscaledIntegrable.add hconstIntegrable
  have hflow (omega : Omega) :
      ‖data.actualBlock (data.actualInitial omega) -
          data.actualBlock (data.referenceInitial omega)‖ ≤
        (data.flowAmplification : Real) *
          dist (data.actualInitial omega) (data.referenceInitial omega) := by
    simpa only [dist_eq_norm] using
      data.actualBlock_lipschitz.dist_le_mul
        (data.actualInitial omega) (data.referenceInitial omega)
  have hscaledMean :
      (∫ omega, (data.flowAmplification : Real) *
        dist (data.actualInitial omega) (data.referenceInitial omega) ∂mu) ≤
      (data.flowAmplification : Real) * data.stateMeanDelta := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left data.mean_state_near
      data.flowAmplification.coe_nonneg
  have hmajorMean :
      (∫ omega, (data.flowAmplification : Real) *
          dist (data.actualInitial omega) (data.referenceInitial omega) +
        data.picardDelta ∂mu) ≤
      (data.flowAmplification : Real) * data.stateMeanDelta +
        data.picardDelta := by
    rw [integral_add hscaledIntegrable hconstIntegrable]
    have hconst :
        (∫ _ : Omega, data.picardDelta ∂mu) = data.picardDelta := by
      simp
    rw [hconst]
    exact add_le_add hscaledMean le_rfl
  calc
    (∫ omega, ‖data.actualFinalAmplitude omega -
        data.referenceFinalAmplitude omega‖ ∂mu) ≤
        ∫ omega, (data.flowAmplification : Real) *
            dist (data.actualInitial omega) (data.referenceInitial omega) +
          data.picardDelta ∂mu := by
      apply integral_mono data.finalAmplitudeDistance_integrable hmajorIntegrable
      intro omega
      calc
        ‖data.actualFinalAmplitude omega -
            data.referenceFinalAmplitude omega‖ ≤
            ‖data.actualBlock (data.actualInitial omega) -
                data.actualBlock (data.referenceInitial omega)‖ +
              ‖data.actualBlock (data.referenceInitial omega) -
                data.referenceBlock (data.referenceInitial omega)‖ := by
          unfold actualFinalAmplitude referenceFinalAmplitude
          exact norm_sub_le_norm_sub_add_norm_sub
            (data.actualBlock (data.actualInitial omega))
            (data.actualBlock (data.referenceInitial omega))
            (data.referenceBlock (data.referenceInitial omega))
        _ ≤ (data.flowAmplification : Real) *
              dist (data.actualInitial omega) (data.referenceInitial omega) +
            data.picardDelta :=
          add_le_add (hflow omega) (data.reference_consistent omega)
    _ ≤ _ := hmajorMean

/-- Direct endpoint moment bounds.  No Markov event and hence no product of
a good-event radius with a failure probability appears. -/
theorem endpoint_second_fourth_moment_errors
    [IsProbabilityMeasure mu]
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
          data.picardDelta))) := by
  exact ⟨meanCoupled_second_fourth_moment_errors mu
      data.actualInitialAmplitude data.referenceInitialAmplitude
      data.actualInitialAmplitude_measurable
      data.referenceInitialAmplitude_measurable data.M_nonneg
      data.initialAmplitudeDistance_integrable
      data.mean_initialAmplitude_distance_le
      data.actualInitial_bound data.referenceInitial_bound,
    meanCoupled_second_fourth_moment_errors mu
      data.actualFinalAmplitude data.referenceFinalAmplitude
      data.actualFinalAmplitude_measurable
      data.referenceFinalAmplitude_measurable data.M_nonneg
      data.finalAmplitudeDistance_integrable
      data.mean_finalAmplitude_distance_le
      data.actualFinal_bound data.referenceFinal_bound⟩

end MeanFullStateEndpointPropagationData
end

end ArchonPhysics.PhyslibFPUTMeanStateMomentEndpoint
