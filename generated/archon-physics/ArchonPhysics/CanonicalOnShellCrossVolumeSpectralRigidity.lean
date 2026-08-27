import ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
import ArchonPhysics.CanonicalOnShellLInfinityEntropyRigidity

/-!
# Canonical rigidity from a cross-volume actual spectral atlas

This is the target-facing F2 adapter for genuine finite-volume harmonic
charts whose lattice sizes may increase.  The earlier manual patch family is
gone: actual simple positive modes with nonzero true Jacobian generate the
local patches, and Lindelöf extraction enumerates them.

The remaining analytic obligations are deliberately explicit predicates:
actual regular chart images cover the additive triangle, every actual local
pushforward is dominated by the limiting child trace, and the limiting child
trace is absolutely continuous with respect to planar volume.
-/

namespace ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity

open Filter MeasureTheory Set
open ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ResonantThreeWaveKineticLInfinityEntropyStationarity
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open scoped ENNReal MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The genuine weighted local lower-averaging property for a cross-volume
family of actual two-mass charts. -/
def CrossVolumeActualLocalLowerAveraging
    (spec : Nat → ActualTwoMassChartSpec)
    (W : Real) (target : Measure (Real × Real)) : Prop :=
  ∀ chartIndex point,
    point ∈ (spec chartIndex).regularSource →
    ∀ patch : Set (Real × Real),
      point ∈ patch →
      IsOpen patch →
      patch ⊆ iidMassPairSupport →
      DifferentiableOn Real (spec chartIndex).chart patch →
      InjOn (spec chartIndex).chart patch →
      Measure.map (spec chartIndex).chart
          (iidMassPairLaw.restrict patch) ≪
        target.restrict (additiveFrequencyTriangle W)

/-- Almost-everywhere coverage of the physical child-frequency triangle by
actual regular charts, allowing the finite volume to vary with the chart. -/
def CrossVolumeActualTriangleCover
    (spec : Nat → ActualTwoMassChartSpec) (W : Real) : Prop :=
  volume
    (additiveFrequencyTriangle W \
      ⋃ chartIndex,
        (spec chartIndex).chart '' (spec chartIndex).regularSource) = 0

/-- Cross-volume actual spectral data and the upper child-trace estimate give
the exact bounded-measurable balance-rigidity contract for the canonical
on-shell weak limit. -/
theorem boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_crossVolume_actualAtlas
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (spec : Nat → ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec collisionFrequencyCeiling)
    (hupper :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling)) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    BoundedMeasurableAEFrequencyBalanceRigid collision := by
  have hlower :
      volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) := by
    exact
      volume_additiveTriangle_ac_of_crossVolume_actualTwoMass_regularSources
        spec collisionFrequencyCeiling
          (Measure.map markedChildFrequencyPair target)
          (by simpa [CrossVolumeActualLocalLowerAveraging] using hlocal)
          (by simpa [CrossVolumeActualTriangleCover] using hcover)
  exact
    boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_equivalentChildTrace
      ensemble time htime_pos htime target hweak hlower hupper

/-- Final equality-case endpoint with the manual atlas removed: zero entropy
implies true unclipped stationarity and frequency-proportional inverse action
once the three explicit cross-volume trace estimates hold. -/
theorem stationary_and_inverseAction_ae_proportional_of_canonicalOnShell_crossVolume_actualAtlas
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (spec : Nat → ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec collisionFrequencyCeiling)
    (hupper :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling))
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak))
    (hactionFloor : AELowerBound
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak) floor action)
    (hzero : canonicalLogEntropyProduction
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak) floor action = 0) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    collisionMap collision action = 0 ∧
      ∃ scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure collision,
          (action mode)⁻¹ = scale * collision.frequency mode := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  have hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision := by
    exact
      boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_crossVolume_actualAtlas
        ensemble time htime_pos htime target hweak spec hlocal hcover hupper
  exact
    stationary_and_inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
      collision hrigid hfloor action hactionFloor hzero

end

end ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity
