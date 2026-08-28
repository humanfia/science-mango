import ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate

/-!
# Probabilistic full-state FPUT endpoint certificate

The earlier full-state endpoint constructor assumes

`dist (actualInitial omega) (referenceInitial omega) ≤ stateDelta`

for every sample.  It therefore uses `ofUniformApproximation`, whose bad sets
are definitionally empty and whose failure probabilities are definitionally
zero.  This module records the strictly weaker quantitative probabilistic RPA
interface: the full states need only be close outside one measurable bad event
of probability at most `failureProbability`.

The same bad event is propagated to both scalar endpoints.  Lipschitzness of
the modal observable and of the Hamiltonian block map derives the good-event
endpoint estimates; second-Picard consistency remains a deterministic input.
The existing general coupling theorem then gives, without changing constants,

* `2 M delta + 2 M^2 p` for the second moment, and
* `4 M^3 delta + 2 M^4 p` for the fourth moment.

This is still a quantitative probabilistic RPA condition.  It does not derive
the good-event full-state coupling from nonlinear Hamiltonian dynamics, but it
is weaker than uniform full-state coupling.
-/

namespace ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
open ArchonPhysics.PhyslibFPUTLipschitzReHaarizedEndpointPropagation

noncomputable section

/-- Full-state endpoint data under a quantitative probabilistic RPA coupling.

Only `initial_state_near_on_good` is probabilistic.  Flow stability is supplied
by a standard Mathlib `LipschitzWith` estimate and `reference_consistent` is the
deterministic second-Picard comparison. -/
structure ProbabilisticFullStateEndpointPropagationData
    (Omega X : Type*) [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) (M : Real) where
  actualInitial : Omega → X
  referenceInitial : Omega → X
  initialAmplitude : X → Complex
  actualBlock : X → Complex
  referenceBlock : X → Complex
  bad : Set Omega
  failureProbability : Real
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
  bad_measurable : MeasurableSet bad
  bad_probability : mu.real bad ≤ failureProbability
  initial_state_near_on_good : ∀ omega, omega ∉ bad →
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

namespace ProbabilisticFullStateEndpointPropagationData

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} {M : Real}

/-- Scalar radius at the initial endpoint. -/
def initialDelta
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) : Real :=
  (data.initialObservableAmplification : Real) * data.stateDelta

/-- Scalar radius at the propagated endpoint. -/
def finalDelta
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) : Real :=
  (data.flowAmplification : Real) * data.stateDelta + data.picardDelta

theorem initialDelta_nonneg
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    0 ≤ data.initialDelta := by
  exact mul_nonneg data.initialObservableAmplification.coe_nonneg
    data.stateDelta_nonneg

theorem finalDelta_nonneg
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    0 ≤ data.finalDelta := by
  exact add_nonneg
    (mul_nonneg data.flowAmplification.coe_nonneg data.stateDelta_nonneg)
    data.picardDelta_nonneg

theorem failureProbability_nonneg
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    0 ≤ data.failureProbability :=
  measureReal_nonneg.trans data.bad_probability

/-- Lipschitzness turns good-event full-state closeness into good-event
initial modal-amplitude closeness. -/
theorem initial_near_on_good
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (omega : Omega) (homega : omega ∉ data.bad) :
    ‖data.initialAmplitude (data.actualInitial omega) -
        data.initialAmplitude (data.referenceInitial omega)‖ ≤
      data.initialDelta := by
  simpa only [initialDelta, dist_eq_norm] using
    data.initialAmplitude_lipschitz.dist_le_mul_of_le
      (data.initial_state_near_on_good omega homega)

/-- The same good event propagates through one stable Hamiltonian block and
the deterministic second-Picard comparison. -/
theorem final_near_on_good
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (omega : Omega) (homega : omega ∉ data.bad) :
    ‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      data.finalDelta := by
  exact norm_actualBlock_sub_referenceBlock_le_of_lipschitzWith
    data.actualBlock data.referenceBlock
    (data.actualInitial omega) (data.referenceInitial omega)
    data.flowAmplification data.actualBlock_lipschitz
    (data.initial_state_near_on_good omega homega)
    (data.reference_consistent omega)

def actualEndpoints
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    Nat → Omega → Complex :=
  fun j omega ↦
    if j = 0 then data.initialAmplitude (data.actualInitial omega)
    else if j = 1 then data.actualBlock (data.actualInitial omega)
    else 0

def referenceEndpoints
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    Nat → Omega → Complex :=
  fun j omega ↦
    if j = 0 then data.initialAmplitude (data.referenceInitial omega)
    else if j = 1 then data.referenceBlock (data.referenceInitial omega)
    else 0

def endpointBad
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    Nat → Set Omega :=
  fun j ↦ if j = 0 then data.bad else if j = 1 then data.bad else ∅

def endpointDelta
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    Nat → Real :=
  fun j ↦ if j = 0 then data.initialDelta
    else if j = 1 then data.finalDelta else 0

def endpointFailureProbability
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    Nat → Real :=
  fun j ↦ if j = 0 then data.failureProbability
    else if j = 1 then data.failureProbability else 0

@[simp] theorem actualEndpoints_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (omega : Omega) :
    data.actualEndpoints 0 omega =
      data.initialAmplitude (data.actualInitial omega) := by
  simp [actualEndpoints]

@[simp] theorem actualEndpoints_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (omega : Omega) :
    data.actualEndpoints 1 omega = data.actualBlock (data.actualInitial omega) := by
  simp [actualEndpoints]

@[simp] theorem referenceEndpoints_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (omega : Omega) :
    data.referenceEndpoints 0 omega =
      data.initialAmplitude (data.referenceInitial omega) := by
  simp [referenceEndpoints]

@[simp] theorem referenceEndpoints_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
    (omega : Omega) :
    data.referenceEndpoints 1 omega =
      data.referenceBlock (data.referenceInitial omega) := by
  simp [referenceEndpoints]

@[simp] theorem endpointBad_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.endpointBad 0 = data.bad := by
  simp [endpointBad]

@[simp] theorem endpointBad_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.endpointBad 1 = data.bad := by
  simp [endpointBad]

@[simp] theorem endpointDelta_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.endpointDelta 0 = data.initialDelta := by
  simp [endpointDelta]

@[simp] theorem endpointDelta_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.endpointDelta 1 = data.finalDelta := by
  simp [endpointDelta]

@[simp] theorem endpointFailureProbability_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.endpointFailureProbability 0 = data.failureProbability := by
  simp [endpointFailureProbability]

@[simp] theorem endpointFailureProbability_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.endpointFailureProbability 1 = data.failureProbability := by
  simp [endpointFailureProbability]

/-- A probabilistic two-endpoint restart certificate.  The bad event and its
probability budget are retained exactly at both genuine endpoints. -/
def toAmplitudeCouplingRestartCertificate
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    AmplitudeCouplingRestartCertificate mu M where
  actual := data.actualEndpoints
  reference := data.referenceEndpoints
  bad := data.endpointBad
  delta := data.endpointDelta
  failureProbability := data.endpointFailureProbability
  actual_measurable := by
    intro j
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
  reference_measurable := by
    intro j
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
  bad_measurable := by
    intro j
    by_cases hj0 : j = 0
    · simpa [endpointBad, hj0] using data.bad_measurable
    · by_cases hj1 : j = 1
      · simpa [endpointBad, hj0, hj1] using data.bad_measurable
      · simp [endpointBad, hj0, hj1]
  delta_nonneg := by
    intro j
    by_cases hj0 : j = 0
    · simpa [endpointDelta, hj0] using data.initialDelta_nonneg
    · by_cases hj1 : j = 1
      · simpa [endpointDelta, hj0, hj1] using data.finalDelta_nonneg
      · simp [endpointDelta, hj0, hj1]
  bad_probability := by
    intro j
    by_cases hj0 : j = 0
    · simpa [endpointBad, endpointFailureProbability, hj0] using
        data.bad_probability
    · by_cases hj1 : j = 1
      · simpa [endpointBad, endpointFailureProbability, hj0, hj1] using
          data.bad_probability
      · simp [endpointBad, endpointFailureProbability, hj0, hj1]
  near_on_good := by
    intro j omega homega
    by_cases hj0 : j = 0
    · subst j
      simpa only [actualEndpoints_zero, referenceEndpoints_zero,
        endpointDelta_zero] using data.initial_near_on_good omega homega
    · by_cases hj1 : j = 1
      · subst j
        simpa only [actualEndpoints_one, referenceEndpoints_one,
          endpointDelta_one] using data.final_near_on_good omega homega
      · simp [actualEndpoints, referenceEndpoints, endpointDelta, hj0, hj1]
  actual_bound := by
    intro j omega
    by_cases hj0 : j = 0
    · simpa [actualEndpoints, hj0] using data.actualInitial_bound omega
    · by_cases hj1 : j = 1
      · simpa [actualEndpoints, hj0, hj1] using data.actualFinal_bound omega
      · simpa [actualEndpoints, hj0, hj1] using data.M_nonneg
  reference_bound := by
    intro j omega
    by_cases hj0 : j = 0
    · simpa [referenceEndpoints, hj0] using data.referenceInitial_bound omega
    · by_cases hj1 : j = 1
      · simpa [referenceEndpoints, hj0, hj1] using
          data.referenceFinal_bound omega
      · simpa [referenceEndpoints, hj0, hj1] using data.M_nonneg

@[simp] theorem certificate_bad_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.bad 0 = data.bad := rfl

@[simp] theorem certificate_bad_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.bad 1 = data.bad := by
  simp [toAmplitudeCouplingRestartCertificate]

@[simp] theorem certificate_failureProbability_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.failureProbability 0 =
      data.failureProbability := rfl

@[simp] theorem certificate_failureProbability_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.failureProbability 1 =
      data.failureProbability := by
  simp [toAmplitudeCouplingRestartCertificate]

@[simp] theorem certificate_delta_zero
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.delta 0 = data.initialDelta := rfl

@[simp] theorem certificate_delta_one
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M) :
    data.toAmplitudeCouplingRestartCertificate.delta 1 = data.finalDelta := by
  simp [toAmplitudeCouplingRestartCertificate]

/-- Both endpoint law errors retain the sharp bad-event terms supplied by the
general common-source coupling theorem. -/
theorem endpoint_second_fourth_moment_errors
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
          2 * M ^ 4 * data.failureProbability)) := by
  dsimp only
  have hzero := certificate_pushforward_second_fourth_moment_errors
    mu data.M_nonneg data.toAmplitudeCouplingRestartCertificate 0
  have hone := certificate_pushforward_second_fourth_moment_errors
    mu data.M_nonneg data.toAmplitudeCouplingRestartCertificate 1
  simpa [couplingSecondMomentDefect, couplingFourthMomentDefect] using
    And.intro hzero hone

theorem initialDelta_le_abs_cube
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
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

theorem finalDelta_le_abs_cube
    (data : ProbabilisticFullStateEndpointPropagationData Omega X mu M)
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

/-- If both the good-event state radius and its failure probability are
`O(|g|^3)`, then all initial and propagated second/fourth endpoint moment
errors are explicitly `O(|g|^3)`. -/
theorem endpoint_second_fourth_moment_errors_le_abs_cube
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
          2 * M ^ 4 * Cfailure) * |g| ^ 3)) := by
  dsimp only
  have hmoments := data.endpoint_second_fourth_moment_errors
  have hinitial := data.initialDelta_le_abs_cube hstateCubic
  have hfinal := data.finalDelta_le_abs_cube hstateCubic hpicardCubic
  have htwoM : 0 ≤ 2 * M := mul_nonneg (by norm_num) data.M_nonneg
  have hfourM3 : 0 ≤ 4 * M ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg data.M_nonneg 3)
  have htwoM2 : 0 ≤ 2 * M ^ 2 :=
    mul_nonneg (by norm_num) (pow_nonneg data.M_nonneg 2)
  have htwoM4 : 0 ≤ 2 * M ^ 4 :=
    mul_nonneg (by norm_num) (pow_nonneg data.M_nonneg 4)
  constructor
  · constructor
    · exact hmoments.1.1.trans <| by
        calc
          2 * M * data.initialDelta + 2 * M ^ 2 * data.failureProbability ≤
              2 * M *
                  ((data.initialObservableAmplification : Real) * Cstate *
                    |g| ^ 3) +
                2 * M ^ 2 * (Cfailure * |g| ^ 3) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hinitial htwoM)
              (mul_le_mul_of_nonneg_left hfailureCubic htwoM2)
          _ = (2 * M *
                  ((data.initialObservableAmplification : Real) * Cstate) +
                2 * M ^ 2 * Cfailure) * |g| ^ 3 := by ring
    · exact hmoments.1.2.trans <| by
        calc
          4 * M ^ 3 * data.initialDelta +
              2 * M ^ 4 * data.failureProbability ≤
              4 * M ^ 3 *
                  ((data.initialObservableAmplification : Real) * Cstate *
                    |g| ^ 3) +
                2 * M ^ 4 * (Cfailure * |g| ^ 3) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hinitial hfourM3)
              (mul_le_mul_of_nonneg_left hfailureCubic htwoM4)
          _ = (4 * M ^ 3 *
                  ((data.initialObservableAmplification : Real) * Cstate) +
                2 * M ^ 4 * Cfailure) * |g| ^ 3 := by ring
  · constructor
    · exact hmoments.2.1.trans <| by
        calc
          2 * M * data.finalDelta + 2 * M ^ 2 * data.failureProbability ≤
              2 * M *
                  (((data.flowAmplification : Real) * Cstate + Cpicard) *
                    |g| ^ 3) +
                2 * M ^ 2 * (Cfailure * |g| ^ 3) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hfinal htwoM)
              (mul_le_mul_of_nonneg_left hfailureCubic htwoM2)
          _ = (2 * M *
                  ((data.flowAmplification : Real) * Cstate + Cpicard) +
                2 * M ^ 2 * Cfailure) * |g| ^ 3 := by ring
    · exact hmoments.2.2.trans <| by
        calc
          4 * M ^ 3 * data.finalDelta +
              2 * M ^ 4 * data.failureProbability ≤
              4 * M ^ 3 *
                  (((data.flowAmplification : Real) * Cstate + Cpicard) *
                    |g| ^ 3) +
                2 * M ^ 4 * (Cfailure * |g| ^ 3) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hfinal hfourM3)
              (mul_le_mul_of_nonneg_left hfailureCubic htwoM4)
          _ = (4 * M ^ 3 *
                  ((data.flowAmplification : Real) * Cstate + Cpicard) +
                2 * M ^ 4 * Cfailure) * |g| ^ 3 := by ring

end ProbabilisticFullStateEndpointPropagationData

end

end ArchonPhysics.PhyslibFPUTProbabilisticFullStateEndpointCertificate
