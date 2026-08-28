import ArchonPhysics.PhyslibFPUTLipschitzReHaarizedEndpointPropagation

/-!
# Full-state two-endpoint FPUT coupling certificate

This module turns a coupling of full FPUT states into the scalar amplitude
coupling consumed by the blockwise kinetic-shadowing argument.  A single
modal observable is evaluated on the actual and re-Haarized initial states.
Its standard Mathlib `LipschitzWith` estimate derives endpoint-zero
closeness from the state coupling.  A second Lipschitz estimate and the
second-Picard consistency edge derive endpoint-one closeness.

The resulting `AmplitudeCouplingRestartCertificate` has two genuine
endpoints, empty bad sets, and zero failure probability.  Thus the initial
and propagated second/fourth moment costs follow without replacing the full
state by a scalar `Complex → Complex` dynamics.
-/

namespace ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor
open ArchonPhysics.PhyslibFPUTLipschitzReHaarizedEndpointPropagation

noncomputable section

/-- Full-state input for a two-endpoint scalar amplitude coupling.

`initialAmplitude` is the same physical modal observable on the actual and
re-Haarized states.  `actualBlock` is the corresponding observable after one
actual Hamiltonian block, while `referenceBlock` is its second-Picard
reference. -/
structure FullStateEndpointPropagationData
    (Omega X : Type*) [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) (M : Real) where
  actualInitial : Omega → X
  referenceInitial : Omega → X
  initialAmplitude : X → Complex
  actualBlock : X → Complex
  referenceBlock : X → Complex
  stateDelta : Real
  initialObservableAmplification : NNReal
  flowAmplification : NNReal
  picardDelta : Real
  M_nonneg : 0 ≤ M
  stateDelta_nonneg : 0 ≤ stateDelta
  picardDelta_nonneg : 0 ≤ picardDelta
  actualInitial_measurable : Measurable actualInitial
  referenceInitial_measurable : Measurable referenceInitial
  initialAmplitude_lipschitz :
    LipschitzWith initialObservableAmplification initialAmplitude
  actualBlock_lipschitz : LipschitzWith flowAmplification actualBlock
  referenceBlock_measurable : Measurable referenceBlock
  initial_state_near : ∀ omega,
    dist (actualInitial omega) (referenceInitial omega) ≤ stateDelta
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

namespace FullStateEndpointPropagationData

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} {M : Real}

/-- Radius of the scalar initial-amplitude coupling derived from the
full-state coupling. -/
def initialDelta (data : FullStateEndpointPropagationData Omega X mu M) : Real :=
  (data.initialObservableAmplification : Real) * data.stateDelta

/-- Radius at the propagated endpoint, derived from flow Lipschitzness and
second-Picard consistency. -/
def finalDelta (data : FullStateEndpointPropagationData Omega X mu M) : Real :=
  (data.flowAmplification : Real) * data.stateDelta + data.picardDelta

theorem initialDelta_nonneg
    (data : FullStateEndpointPropagationData Omega X mu M) :
    0 ≤ data.initialDelta := by
  exact mul_nonneg data.initialObservableAmplification.coe_nonneg
    data.stateDelta_nonneg

theorem finalDelta_nonneg
    (data : FullStateEndpointPropagationData Omega X mu M) :
    0 ≤ data.finalDelta := by
  exact add_nonneg
    (mul_nonneg data.flowAmplification.coe_nonneg data.stateDelta_nonneg)
    data.picardDelta_nonneg

/-- The initial amplitude is close because it is a Lipschitz observable of
the coupled full states. -/
theorem initial_near
    (data : FullStateEndpointPropagationData Omega X mu M) (omega : Omega) :
    ‖data.initialAmplitude (data.actualInitial omega) -
        data.initialAmplitude (data.referenceInitial omega)‖ ≤
      data.initialDelta := by
  simpa only [initialDelta, dist_eq_norm] using
    data.initialAmplitude_lipschitz.dist_le_mul_of_le
      (data.initial_state_near omega)

/-- The existing Mathlib-grounded Lipschitz triangle applies directly to
the full state `X`. -/
theorem final_near
    (data : FullStateEndpointPropagationData Omega X mu M) (omega : Omega) :
    ‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      data.finalDelta := by
  exact norm_actualBlock_sub_referenceBlock_le_of_lipschitzWith
    data.actualBlock data.referenceBlock
    (data.actualInitial omega) (data.referenceInitial omega)
    data.flowAmplification data.actualBlock_lipschitz
    (data.initial_state_near omega) (data.reference_consistent omega)

/-- Actual scalar amplitudes at the initial and final endpoint, followed by
zero padding. -/
def actualEndpoints (data : FullStateEndpointPropagationData Omega X mu M) :
    Nat → Omega → Complex :=
  fun j omega ↦
    if j = 0 then data.initialAmplitude (data.actualInitial omega)
    else if j = 1 then data.actualBlock (data.actualInitial omega)
    else 0

/-- Reference scalar amplitudes at the initial and final endpoint, followed
by zero padding. -/
def referenceEndpoints (data : FullStateEndpointPropagationData Omega X mu M) :
    Nat → Omega → Complex :=
  fun j omega ↦
    if j = 0 then data.initialAmplitude (data.referenceInitial omega)
    else if j = 1 then data.referenceBlock (data.referenceInitial omega)
    else 0

/-- The two derived endpoint radii, followed by zero padding. -/
def endpointDelta
    (data : FullStateEndpointPropagationData Omega X mu M) : Nat → Real :=
  fun j ↦ if j = 0 then data.initialDelta
    else if j = 1 then data.finalDelta
    else 0

@[simp] theorem actualEndpoints_zero
    (data : FullStateEndpointPropagationData Omega X mu M) (omega : Omega) :
    data.actualEndpoints 0 omega =
      data.initialAmplitude (data.actualInitial omega) := by
  simp [actualEndpoints]

@[simp] theorem actualEndpoints_one
    (data : FullStateEndpointPropagationData Omega X mu M) (omega : Omega) :
    data.actualEndpoints 1 omega =
      data.actualBlock (data.actualInitial omega) := by
  simp [actualEndpoints]

@[simp] theorem referenceEndpoints_zero
    (data : FullStateEndpointPropagationData Omega X mu M) (omega : Omega) :
    data.referenceEndpoints 0 omega =
      data.initialAmplitude (data.referenceInitial omega) := by
  simp [referenceEndpoints]

@[simp] theorem referenceEndpoints_one
    (data : FullStateEndpointPropagationData Omega X mu M) (omega : Omega) :
    data.referenceEndpoints 1 omega =
      data.referenceBlock (data.referenceInitial omega) := by
  simp [referenceEndpoints]

@[simp] theorem endpointDelta_zero
    (data : FullStateEndpointPropagationData Omega X mu M) :
    data.endpointDelta 0 = data.initialDelta := by
  simp [endpointDelta]

@[simp] theorem endpointDelta_one
    (data : FullStateEndpointPropagationData Omega X mu M) :
    data.endpointDelta 1 = data.finalDelta := by
  simp [endpointDelta]

/-- The reusable two-endpoint amplitude certificate on the original common
probability space.  Both closeness fields are conclusions from full-state
data, and every exceptional set is empty. -/
def toAmplitudeCouplingRestartCertificate
    (data : FullStateEndpointPropagationData Omega X mu M) :
    AmplitudeCouplingRestartCertificate mu M := by
  apply AmplitudeCouplingRestartCertificate.ofUniformApproximation mu
    data.actualEndpoints data.referenceEndpoints data.endpointDelta
  · intro j
    by_cases hj0 : j = 0
    · subst j
      have heq : data.actualEndpoints 0 =
          fun omega ↦ data.initialAmplitude (data.actualInitial omega) := by
        funext omega
        simp [actualEndpoints]
      rw [heq]
      exact data.initialAmplitude_lipschitz.continuous.measurable.comp
        data.actualInitial_measurable
    · by_cases hj1 : j = 1
      · subst j
        have heq : data.actualEndpoints 1 =
            fun omega ↦ data.actualBlock (data.actualInitial omega) := by
          funext omega
          simp [actualEndpoints]
        rw [heq]
        exact data.actualBlock_lipschitz.continuous.measurable.comp
          data.actualInitial_measurable
      · have heq : data.actualEndpoints j = fun _ ↦ (0 : Complex) := by
          funext omega
          simp [actualEndpoints, hj0, hj1]
        rw [heq]
        exact measurable_const
  · intro j
    by_cases hj0 : j = 0
    · subst j
      have heq : data.referenceEndpoints 0 =
          fun omega ↦ data.initialAmplitude (data.referenceInitial omega) := by
        funext omega
        simp [referenceEndpoints]
      rw [heq]
      exact data.initialAmplitude_lipschitz.continuous.measurable.comp
        data.referenceInitial_measurable
    · by_cases hj1 : j = 1
      · subst j
        have heq : data.referenceEndpoints 1 =
            fun omega ↦ data.referenceBlock (data.referenceInitial omega) := by
          funext omega
          simp [referenceEndpoints]
        rw [heq]
        exact data.referenceBlock_measurable.comp data.referenceInitial_measurable
      · have heq : data.referenceEndpoints j = fun _ ↦ (0 : Complex) := by
          funext omega
          simp [referenceEndpoints, hj0, hj1]
        rw [heq]
        exact measurable_const
  · intro j
    by_cases hj0 : j = 0
    · simpa [endpointDelta, hj0] using data.initialDelta_nonneg
    · by_cases hj1 : j = 1
      · simpa [endpointDelta, hj0, hj1] using data.finalDelta_nonneg
      · simp [endpointDelta, hj0, hj1]
  · intro j omega
    by_cases hj0 : j = 0
    · simpa [actualEndpoints, referenceEndpoints, endpointDelta, hj0] using
        data.initial_near omega
    · by_cases hj1 : j = 1
      · simpa [actualEndpoints, referenceEndpoints, endpointDelta, hj0, hj1]
          using data.final_near omega
      · simp [actualEndpoints, referenceEndpoints, endpointDelta, hj0, hj1]
  · intro j omega
    by_cases hj0 : j = 0
    · simpa [actualEndpoints, hj0] using data.actualInitial_bound omega
    · by_cases hj1 : j = 1
      · simpa [actualEndpoints, hj0, hj1] using data.actualFinal_bound omega
      · simpa [actualEndpoints, hj0, hj1] using data.M_nonneg
  · intro j omega
    by_cases hj0 : j = 0
    · simpa [referenceEndpoints, hj0] using data.referenceInitial_bound omega
    · by_cases hj1 : j = 1
      · simpa [referenceEndpoints, hj0, hj1] using
          data.referenceFinal_bound omega
      · simpa [referenceEndpoints, hj0, hj1] using data.M_nonneg

@[simp] theorem certificate_failureProbability
    (data : FullStateEndpointPropagationData Omega X mu M) (j : Nat) :
    data.toAmplitudeCouplingRestartCertificate.failureProbability j = 0 := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

@[simp] theorem certificate_bad
    (data : FullStateEndpointPropagationData Omega X mu M) (j : Nat) :
    data.toAmplitudeCouplingRestartCertificate.bad j = ∅ := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

@[simp] theorem certificate_delta_zero
    (data : FullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.delta 0 = data.initialDelta := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

@[simp] theorem certificate_delta_one
    (data : FullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.delta 1 = data.finalDelta := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

/-- Both full-state endpoint laws inherit the explicit deterministic
second- and fourth-moment costs. -/
theorem endpoint_second_fourth_moment_errors
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
        4 * M ^ 3 * data.finalDelta)) := by
  dsimp only
  have hzero := certificate_pushforward_second_fourth_moment_errors
    mu data.M_nonneg data.toAmplitudeCouplingRestartCertificate 0
  have hone := certificate_pushforward_second_fourth_moment_errors
    mu data.M_nonneg data.toAmplitudeCouplingRestartCertificate 1
  simpa [couplingSecondMomentDefect, couplingFourthMomentDefect] using
    And.intro hzero hone

/-- Cubic full-state coupling gives a cubic initial amplitude radius. -/
theorem initialDelta_le_abs_cube
    (data : FullStateEndpointPropagationData Omega X mu M)
    {g Cstate : Real}
    (hstateCubic : data.stateDelta ≤ Cstate * |g| ^ 3) :
    data.initialDelta ≤
      (data.initialObservableAmplification : Real) * Cstate * |g| ^ 3 := by
  unfold initialDelta
  calc
    (data.initialObservableAmplification : Real) * data.stateDelta ≤
        (data.initialObservableAmplification : Real) *
          (Cstate * |g| ^ 3) :=
      mul_le_mul_of_nonneg_left hstateCubic
        data.initialObservableAmplification.coe_nonneg
    _ = (data.initialObservableAmplification : Real) * Cstate * |g| ^ 3 := by
      ring

/-- Cubic full-state coupling and cubic Picard consistency give a cubic
propagated endpoint radius. -/
theorem finalDelta_le_abs_cube
    (data : FullStateEndpointPropagationData Omega X mu M)
    {g Cstate Cpicard : Real}
    (hstateCubic : data.stateDelta ≤ Cstate * |g| ^ 3)
    (hpicardCubic : data.picardDelta ≤ Cpicard * |g| ^ 3) :
    data.finalDelta ≤
      ((data.flowAmplification : Real) * Cstate + Cpicard) * |g| ^ 3 := by
  unfold finalDelta
  calc
    (data.flowAmplification : Real) * data.stateDelta + data.picardDelta ≤
        (data.flowAmplification : Real) * (Cstate * |g| ^ 3) +
          Cpicard * |g| ^ 3 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hstateCubic
          data.flowAmplification.coe_nonneg)
        hpicardCubic
    _ = ((data.flowAmplification : Real) * Cstate + Cpicard) * |g| ^ 3 := by
      ring

end FullStateEndpointPropagationData

end

end ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
