import ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor

/-!
# Re-Haarized initial couplings propagated across one FPUT block

This module supplies the deterministic triangle which was missing between a
restart coupling at the beginning of a block and the coupling needed at its
end.  If the actual block map is stable on the coupled pair and its value at
the reference initial datum is close to a second-Picard reference, then the
endpoint displacement is

`flowAmplification * initialDelta + picardDelta`.

The corresponding common-source certificate has two genuine endpoints:
index `0` is the re-Haarized initial pair and index `1` is the propagated
actual/second-Picard pair.  All later indices are padded by zero.  Its bad
sets are empty, so no endpoint coupling is assumed and no probability of
failure is introduced.
-/

namespace ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor

noncomputable section

/-! ## The deterministic one-block triangle -/

/-- Stability of the actual block map and consistency of the reference
second-Picard map propagate an initial common-source displacement to the
block endpoint.  In particular, the final coupling is a conclusion rather
than a hypothesis. -/
theorem norm_actualBlock_sub_referenceBlock_le
    {E : Type*} [SeminormedAddCommGroup E]
    (actualBlock referenceBlock : E → E) (x y : E)
    {initialDelta flowAmplification picardDelta : Real}
    (hflowAmplification : 0 ≤ flowAmplification)
    (hinitial : ‖x - y‖ ≤ initialDelta)
    (hflow : ‖actualBlock x - actualBlock y‖ ≤
      flowAmplification * ‖x - y‖)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta) :
    ‖actualBlock x - referenceBlock y‖ ≤
      flowAmplification * initialDelta + picardDelta := by
  calc
    ‖actualBlock x - referenceBlock y‖ =
        ‖(actualBlock x - actualBlock y) +
          (actualBlock y - referenceBlock y)‖ := by
      congr 1
      abel
    _ ≤ ‖actualBlock x - actualBlock y‖ +
        ‖actualBlock y - referenceBlock y‖ := norm_add_le _ _
    _ ≤ flowAmplification * ‖x - y‖ + picardDelta :=
      add_le_add hflow hpicard
    _ ≤ flowAmplification * initialDelta + picardDelta :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinitial hflowAmplification) le_rfl

/-- Cubic initial re-Haarization and cubic second-Picard consistency remain
cubic after one stable block. -/
theorem norm_actualBlock_sub_referenceBlock_le_abs_cube
    {E : Type*} [SeminormedAddCommGroup E]
    (actualBlock referenceBlock : E → E) (x y : E)
    {g initialDelta flowAmplification picardDelta Cinitial Cpicard : Real}
    (hflowAmplification : 0 ≤ flowAmplification)
    (hinitial : ‖x - y‖ ≤ initialDelta)
    (hflow : ‖actualBlock x - actualBlock y‖ ≤
      flowAmplification * ‖x - y‖)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta)
    (hinitialCubic : initialDelta ≤ Cinitial * |g| ^ 3)
    (hpicardCubic : picardDelta ≤ Cpicard * |g| ^ 3) :
    ‖actualBlock x - referenceBlock y‖ ≤
      (flowAmplification * Cinitial + Cpicard) * |g| ^ 3 := by
  calc
    ‖actualBlock x - referenceBlock y‖ ≤
        flowAmplification * initialDelta + picardDelta :=
      norm_actualBlock_sub_referenceBlock_le actualBlock referenceBlock x y
        hflowAmplification hinitial hflow hpicard
    _ ≤ flowAmplification * (Cinitial * |g| ^ 3) +
          Cpicard * |g| ^ 3 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinitialCubic hflowAmplification)
        hpicardCubic
    _ = (flowAmplification * Cinitial + Cpicard) * |g| ^ 3 := by ring

/-! ## A two-endpoint common-source certificate -/

/-- Data which derives, rather than assumes, a two-endpoint amplitude
coupling.  `actualBlock` propagates the actual and re-Haarized initial data;
`referenceBlock` is the second-Picard reference map. -/
structure ReHaarizedEndpointPropagationData
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (M : Real) where
  actualInitial : Omega → Complex
  referenceInitial : Omega → Complex
  actualBlock : Complex → Complex
  referenceBlock : Complex → Complex
  initialDelta : Real
  flowAmplification : Real
  picardDelta : Real
  M_nonneg : 0 ≤ M
  initialDelta_nonneg : 0 ≤ initialDelta
  flowAmplification_nonneg : 0 ≤ flowAmplification
  picardDelta_nonneg : 0 ≤ picardDelta
  actualInitial_measurable : Measurable actualInitial
  referenceInitial_measurable : Measurable referenceInitial
  actualBlock_measurable : Measurable actualBlock
  referenceBlock_measurable : Measurable referenceBlock
  initial_near : ∀ omega,
    ‖actualInitial omega - referenceInitial omega‖ ≤ initialDelta
  actualBlock_stable : ∀ omega,
    ‖actualBlock (actualInitial omega) -
        actualBlock (referenceInitial omega)‖ ≤
      flowAmplification *
        ‖actualInitial omega - referenceInitial omega‖
  reference_consistent : ∀ omega,
    ‖actualBlock (referenceInitial omega) -
        referenceBlock (referenceInitial omega)‖ ≤ picardDelta
  actualInitial_bound : ∀ omega, ‖actualInitial omega‖ ≤ M
  referenceInitial_bound : ∀ omega, ‖referenceInitial omega‖ ≤ M
  actualFinal_bound : ∀ omega, ‖actualBlock (actualInitial omega)‖ ≤ M
  referenceFinal_bound : ∀ omega,
    ‖referenceBlock (referenceInitial omega)‖ ≤ M

namespace ReHaarizedEndpointPropagationData

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} {M : Real}

/-- The derived endpoint displacement. -/
def finalDelta (data : ReHaarizedEndpointPropagationData mu M) : Real :=
  data.flowAmplification * data.initialDelta + data.picardDelta

theorem finalDelta_nonneg
    (data : ReHaarizedEndpointPropagationData mu M) :
    0 ≤ data.finalDelta := by
  exact add_nonneg
    (mul_nonneg data.flowAmplification_nonneg data.initialDelta_nonneg)
    data.picardDelta_nonneg

/-- Endpoint one is close because of the initial coupling, flow stability,
and reference consistency. -/
theorem final_near
    (data : ReHaarizedEndpointPropagationData mu M) (omega : Omega) :
    ‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      data.finalDelta := by
  exact norm_actualBlock_sub_referenceBlock_le
    data.actualBlock data.referenceBlock
    (data.actualInitial omega) (data.referenceInitial omega)
    data.flowAmplification_nonneg (data.initial_near omega)
    (data.actualBlock_stable omega) (data.reference_consistent omega)

/-- Actual amplitudes at the initial and final endpoints; later indices are
zero padding. -/
def actualEndpoints (data : ReHaarizedEndpointPropagationData mu M) :
    Nat → Omega → Complex :=
  fun j omega ↦
    if j = 0 then data.actualInitial omega
    else if j = 1 then data.actualBlock (data.actualInitial omega)
    else 0

/-- Reference amplitudes at the initial and final endpoints; later indices
are zero padding. -/
def referenceEndpoints (data : ReHaarizedEndpointPropagationData mu M) :
    Nat → Omega → Complex :=
  fun j omega ↦
    if j = 0 then data.referenceInitial omega
    else if j = 1 then data.referenceBlock (data.referenceInitial omega)
    else 0

/-- The initial radius at endpoint zero and the derived propagated radius at
endpoint one. -/
def endpointDelta (data : ReHaarizedEndpointPropagationData mu M) : Nat → Real :=
  fun j ↦
    if j = 0 then data.initialDelta
    else if j = 1 then data.finalDelta
    else 0

@[simp] theorem actualEndpoints_zero
    (data : ReHaarizedEndpointPropagationData mu M) (omega : Omega) :
    data.actualEndpoints 0 omega = data.actualInitial omega := by
  simp [actualEndpoints]

@[simp] theorem actualEndpoints_one
    (data : ReHaarizedEndpointPropagationData mu M) (omega : Omega) :
    data.actualEndpoints 1 omega =
      data.actualBlock (data.actualInitial omega) := by
  simp [actualEndpoints]

@[simp] theorem referenceEndpoints_zero
    (data : ReHaarizedEndpointPropagationData mu M) (omega : Omega) :
    data.referenceEndpoints 0 omega = data.referenceInitial omega := by
  simp [referenceEndpoints]

@[simp] theorem referenceEndpoints_one
    (data : ReHaarizedEndpointPropagationData mu M) (omega : Omega) :
    data.referenceEndpoints 1 omega =
      data.referenceBlock (data.referenceInitial omega) := by
  simp [referenceEndpoints]

@[simp] theorem endpointDelta_zero
    (data : ReHaarizedEndpointPropagationData mu M) :
    data.endpointDelta 0 = data.initialDelta := by
  simp [endpointDelta]

@[simp] theorem endpointDelta_one
    (data : ReHaarizedEndpointPropagationData mu M) :
    data.endpointDelta 1 = data.finalDelta := by
  simp [endpointDelta]

/-- The endpoint-indexed restart certificate.  Its final closeness field is
proved by `final_near`; it is not supplied as certificate input. -/
def toAmplitudeCouplingRestartCertificate
    (data : ReHaarizedEndpointPropagationData mu M) :
    AmplitudeCouplingRestartCertificate mu M := by
  apply AmplitudeCouplingRestartCertificate.ofUniformApproximation mu
    data.actualEndpoints data.referenceEndpoints data.endpointDelta
  · intro j
    by_cases hj0 : j = 0
    · have heq : data.actualEndpoints j = data.actualInitial := by
        funext omega
        simp [actualEndpoints, hj0]
      rw [heq]
      exact data.actualInitial_measurable
    · by_cases hj1 : j = 1
      · have heq : data.actualEndpoints j =
            fun omega ↦ data.actualBlock (data.actualInitial omega) := by
          funext omega
          simp [actualEndpoints, hj1]
        rw [heq]
        exact data.actualBlock_measurable.comp data.actualInitial_measurable
      · have heq : data.actualEndpoints j = fun _ ↦ (0 : Complex) := by
          funext omega
          simp [actualEndpoints, hj0, hj1]
        rw [heq]
        exact measurable_const
  · intro j
    by_cases hj0 : j = 0
    · have heq : data.referenceEndpoints j = data.referenceInitial := by
        funext omega
        simp [referenceEndpoints, hj0]
      rw [heq]
      exact data.referenceInitial_measurable
    · by_cases hj1 : j = 1
      · have heq : data.referenceEndpoints j =
            fun omega ↦ data.referenceBlock (data.referenceInitial omega) := by
          funext omega
          simp [referenceEndpoints, hj1]
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
    (data : ReHaarizedEndpointPropagationData mu M) (j : Nat) :
    data.toAmplitudeCouplingRestartCertificate.failureProbability j = 0 := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

@[simp] theorem certificate_bad
    (data : ReHaarizedEndpointPropagationData mu M) (j : Nat) :
    data.toAmplitudeCouplingRestartCertificate.bad j = ∅ := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

@[simp] theorem certificate_delta_zero
    (data : ReHaarizedEndpointPropagationData mu M) :
    data.toAmplitudeCouplingRestartCertificate.delta 0 = data.initialDelta := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

@[simp] theorem certificate_delta_one
    (data : ReHaarizedEndpointPropagationData mu M) :
    data.toAmplitudeCouplingRestartCertificate.delta 1 = data.finalDelta := by
  simp [toAmplitudeCouplingRestartCertificate,
    AmplitudeCouplingRestartCertificate.ofUniformApproximation]

/-- Both endpoint laws inherit explicit second- and fourth-moment costs.  The
endpoint-one cost contains the derived stability/Picard radius. -/
theorem endpoint_second_fourth_moment_errors
    (data : ReHaarizedEndpointPropagationData mu M)
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

/-- The endpoint radius itself is cubic when the initial re-Haarization and
second-Picard radii are cubic. -/
theorem finalDelta_le_abs_cube
    (data : ReHaarizedEndpointPropagationData mu M)
    {g Cinitial Cpicard : Real}
    (hinitialCubic : data.initialDelta ≤ Cinitial * |g| ^ 3)
    (hpicardCubic : data.picardDelta ≤ Cpicard * |g| ^ 3) :
    data.finalDelta ≤
      (data.flowAmplification * Cinitial + Cpicard) * |g| ^ 3 := by
  unfold finalDelta
  calc
    data.flowAmplification * data.initialDelta + data.picardDelta ≤
        data.flowAmplification * (Cinitial * |g| ^ 3) +
          Cpicard * |g| ^ 3 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinitialCubic
          data.flowAmplification_nonneg)
        hpicardCubic
    _ = (data.flowAmplification * Cinitial + Cpicard) * |g| ^ 3 := by ring

/-- Pointwise cubic endpoint coupling, obtained from the data rather than
postulated at endpoint one. -/
theorem final_near_abs_cube
    (data : ReHaarizedEndpointPropagationData mu M)
    {g Cinitial Cpicard : Real}
    (hinitialCubic : data.initialDelta ≤ Cinitial * |g| ^ 3)
    (hpicardCubic : data.picardDelta ≤ Cpicard * |g| ^ 3)
    (omega : Omega) :
    ‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      (data.flowAmplification * Cinitial + Cpicard) * |g| ^ 3 :=
  (data.final_near omega).trans
    (data.finalDelta_le_abs_cube hinitialCubic hpicardCubic)

end ReHaarizedEndpointPropagationData

end

end ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation
