import ArchonPhysics.CanonicalLInfinityLogEntropyDifferentialPairing
import ArchonPhysics.CanonicalLInfinityLogEntropyFunctional
import ArchonPhysics.PositiveLogTaylorRemainder

/-!
# Differentiating the canonical logarithmic entropy above the repair floor

The pointwise logarithmic Taylor estimate is integrated against the finite
canonical reference measure.  On states with an essential lower bound
strictly above the floor used by `canonicalLogEntropy`, the lower bound is
stable in an `L-infinity` neighbourhood.  The integrated quadratic remainder
therefore proves a genuine Frechet derivative and, by composition, the usual
chain rule along differentiable canonical trajectories.

The strict buffer is essential: no differentiability assertion is made at a
state meeting the kink of the pointwise `max floor` repair.
-/

namespace ArchonPhysics.CanonicalLInfinityLogEntropyChainRule

open Filter MeasureTheory Metric Set
open Asymptotics
open ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity
open ArchonPhysics.CanonicalLInfinityLogEntropyDifferentialPairing
open ArchonPhysics.CanonicalLInfinityLogEntropyFunctional
open ArchonPhysics.PositiveLogTaylorRemainder
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory Topology

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- On two canonical states with a common genuine essential floor, the
integrated logarithmic Taylor remainder is quadratic in their
`L-infinity` distance. -/
theorem norm_canonicalLogEntropy_sub_sub_differential_le
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action₁ action₂ : CanonicalLInfinity collision)
    (haction₁ : AELowerBound collision floor action₁)
    (haction₂ : AELowerBound collision floor action₂) :
    ‖canonicalLogEntropy collision floor action₂ -
        canonicalLogEntropy collision floor action₁ -
        canonicalLogEntropyDifferential collision floor hfloor action₁
          (action₂ - action₁)‖ ≤
      (floor⁻¹ ^ 2 * ‖action₂ - action₁‖ ^ 2) *
        (collisionReferenceMeasure collision).real univ := by
  let measure := collisionReferenceMeasure collision
  let representative₁ :=
    positiveFloorRepresentative collision floor action₁
  let representative₂ :=
    positiveFloorRepresentative collision floor action₂
  have hlog₁ : Integrable (fun mode => Real.log (representative₁ mode)) measure :=
    integrable_log_positiveFloorRepresentative collision hfloor action₁
  have hlog₂ : Integrable (fun mode => Real.log (representative₂ mode)) measure :=
    integrable_log_positiveFloorRepresentative collision hfloor action₂
  have hinverse : IsBoundedMeasurable (fun mode => (representative₁ mode)⁻¹) := by
    change IsBoundedMeasurable
      (inversePositiveFloorRepresentative collision floor action₁)
    exact inversePositiveFloorRepresentative_isBoundedMeasurable
      collision hfloor action₁
  have hlinear : Integrable
      (fun mode => (representative₁ mode)⁻¹ * (action₂ - action₁) mode)
      measure := by
    exact (boundedMeasurableTest_memLp_one collision hinverse).integrable_mul
      (Lp.memLp (action₂ - action₁))
  have hremainderIntegral :
      canonicalLogEntropy collision floor action₂ -
          canonicalLogEntropy collision floor action₁ -
          canonicalLogEntropyDifferential collision floor hfloor action₁
            (action₂ - action₁) =
        ∫ mode,
          (Real.log (representative₂ mode) -
              Real.log (representative₁ mode)) -
            (representative₁ mode)⁻¹ *
              (representative₂ mode - representative₁ mode)
          ∂measure := by
    rw [canonicalLogEntropy, canonicalLogEntropy,
      canonicalLogEntropyDifferential_apply]
    change
      (∫ mode, Real.log (representative₂ mode) ∂measure) -
          (∫ mode, Real.log (representative₁ mode) ∂measure) -
          (∫ mode, (representative₁ mode)⁻¹ *
            (action₂ - action₁) mode ∂measure) = _
    have hlogSub : Integrable
        (fun mode => Real.log (representative₂ mode) -
          Real.log (representative₁ mode)) measure := hlog₂.sub hlog₁
    calc
      (∫ mode, Real.log (representative₂ mode) ∂measure) -
            (∫ mode, Real.log (representative₁ mode) ∂measure) -
            (∫ mode, (representative₁ mode)⁻¹ *
              (action₂ - action₁) mode ∂measure) =
          (∫ mode, Real.log (representative₂ mode) -
            Real.log (representative₁ mode) ∂measure) -
            (∫ mode, (representative₁ mode)⁻¹ *
              (action₂ - action₁) mode ∂measure) := by
        rw [integral_sub hlog₂ hlog₁]
      _ = ∫ mode,
          (Real.log (representative₂ mode) -
              Real.log (representative₁ mode)) -
            (representative₁ mode)⁻¹ * (action₂ - action₁) mode
          ∂measure := by
        rw [integral_sub hlogSub hlinear]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub action₂ action₁,
          positiveFloorRepresentative_ae_eq collision action₁ haction₁,
          positiveFloorRepresentative_ae_eq collision action₂ haction₂]
          with mode hsub hrepresentative₁ hrepresentative₂
        simp only [Pi.sub_apply] at hsub
        rw [hsub, ← hrepresentative₁, ← hrepresentative₂]
  rw [hremainderIntegral]
  apply norm_integral_le_of_norm_le_const
  filter_upwards
    [positiveFloorRepresentative_sub_norm_le_ae
      collision floor action₂ action₁] with mode hmode
  calc
    ‖(Real.log (representative₂ mode) - Real.log (representative₁ mode)) -
        (representative₁ mode)⁻¹ *
          (representative₂ mode - representative₁ mode)‖ ≤
        floor⁻¹ ^ 2 *
          ‖representative₂ mode - representative₁ mode‖ ^ 2 :=
      norm_log_sub_log_sub_inv_mul_sub_le hfloor
        (floor_le_positiveFloorRepresentative collision floor action₁ mode)
        (floor_le_positiveFloorRepresentative collision floor action₂ mode)
    _ ≤ floor⁻¹ ^ 2 * ‖action₂ - action₁‖ ^ 2 := by
      gcongr

/-- A strict essential buffer above the repair floor makes the repaired
canonical log entropy genuinely Frechet differentiable. -/
theorem hasFDerivAt_canonicalLogEntropy_of_strictAELowerBound
    (collision : ResonantThreeWaveMeasure Mode)
    {floor buffer : Real} (hfloor : 0 < floor) (hfloorBuffer : floor < buffer)
    (action : CanonicalLInfinity collision)
    (hactionBuffer : AELowerBound collision buffer action) :
    HasFDerivAt (canonicalLogEntropy collision floor)
      (canonicalLogEntropyDifferential collision floor hfloor action) action := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  let coefficient := floor⁻¹ ^ 2 *
    (collisionReferenceMeasure collision).real univ
  have hactionFloor : AELowerBound collision floor action :=
    hactionBuffer.mono fun _mode hmode => (le_of_lt hfloorBuffer).trans hmode
  have hremainderBigO :
      (fun direction : CanonicalLInfinity collision =>
          canonicalLogEntropy collision floor (action + direction) -
            canonicalLogEntropy collision floor action -
            canonicalLogEntropyDifferential collision floor hfloor action
              direction) =O[𝓝 0]
        (fun direction : CanonicalLInfinity collision => ‖direction‖ ^ 2) := by
    apply IsBigO.of_bound coefficient
    filter_upwards
      [Metric.ball_mem_nhds
        (0 : CanonicalLInfinity collision) (sub_pos.mpr hfloorBuffer)]
      with direction hdirection
    have hdirectionNorm : ‖direction‖ < buffer - floor := by
      simpa only [mem_ball, dist_zero_right] using hdirection
    have hnearbyRaw : AELowerBound collision
        (buffer - ‖(action + direction) - action‖) (action + direction) :=
      aeLowerBound_sub_norm collision hactionBuffer
    have hnearby : AELowerBound collision floor (action + direction) :=
      hnearbyRaw.mono fun _mode hmode => by
        have hnorm : ‖(action + direction) - action‖ = ‖direction‖ := by
          rw [add_sub_cancel_left]
        rw [hnorm] at hmode
        linarith
    have hremainder :=
      norm_canonicalLogEntropy_sub_sub_differential_le
        collision hfloor action (action + direction) hactionFloor hnearby
    calc
      ‖canonicalLogEntropy collision floor (action + direction) -
          canonicalLogEntropy collision floor action -
          canonicalLogEntropyDifferential collision floor hfloor action
            direction‖ ≤
          (floor⁻¹ ^ 2 * ‖direction‖ ^ 2) *
            (collisionReferenceMeasure collision).real univ := by
        simpa only [add_sub_cancel_left] using hremainder
      _ = coefficient * ‖‖direction‖ ^ 2‖ := by
        dsimp only [coefficient]
        rw [norm_pow, norm_norm]
        ring
  exact hremainderBigO.trans_isLittleO
    (isLittleO_norm_pow_id (E' := CanonicalLInfinity collision) one_lt_two)

/-- Chain rule for an arbitrary differentiable canonical trajectory, at a
time where the state lies strictly above the repair floor. -/
theorem hasDerivAt_canonicalLogEntropy_comp_of_strictAELowerBound
    (collision : ResonantThreeWaveMeasure Mode)
    {floor buffer time : Real} (hfloor : 0 < floor)
    (hfloorBuffer : floor < buffer)
    (trajectory : Real → CanonicalLInfinity collision)
    (velocity : CanonicalLInfinity collision)
    (htrajectory : HasDerivAt trajectory velocity time)
    (hactionBuffer : AELowerBound collision buffer (trajectory time)) :
    HasDerivAt
      (fun s => canonicalLogEntropy collision floor (trajectory s))
      (canonicalLogEntropyDifferential collision floor hfloor
        (trajectory time) velocity) time := by
  simpa only [Function.comp_def] using!
    (hasFDerivAt_canonicalLogEntropy_of_strictAELowerBound
      collision hfloor hfloorBuffer (trajectory time) hactionBuffer).comp_hasDerivAt
        time htrajectory

/-- Along the genuine coupling-scaled RN collision ODE, the derivative of
the canonical logarithmic entropy is exactly coupling squared times entropy
production, provided the current state has a strict buffer above the repair
floor. -/
theorem hasDerivAt_canonicalLogEntropy_along_rnCollisionODE
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {floor buffer time : Real} (hfloor : 0 < floor)
    (hfloorBuffer : floor < buffer)
    (trajectory : Real → CanonicalLInfinity collision)
    (htrajectory : HasDerivAt trajectory
      (rnCollisionVectorField collision g (trajectory time)) time)
    (hactionBuffer : AELowerBound collision buffer (trajectory time)) :
    HasDerivAt
      (fun s => canonicalLogEntropy collision floor (trajectory s))
      (g ^ 2 * canonicalLogEntropyProduction collision floor
        (trajectory time)) time := by
  have hactionFloor : AELowerBound collision floor (trajectory time) :=
    hactionBuffer.mono fun _mode hmode => (le_of_lt hfloorBuffer).trans hmode
  have hchain := hasDerivAt_canonicalLogEntropy_comp_of_strictAELowerBound
    collision hfloor hfloorBuffer trajectory
      (rnCollisionVectorField collision g (trajectory time))
      htrajectory hactionBuffer
  rw [canonicalLogEntropyDifferential_rnCollisionVectorField_eq
    collision g hfloor (trajectory time) hactionFloor] at hchain
  exact hchain

end

end ArchonPhysics.CanonicalLInfinityLogEntropyChainRule
