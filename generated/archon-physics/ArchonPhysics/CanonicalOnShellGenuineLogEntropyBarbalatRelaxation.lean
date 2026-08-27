import ArchonPhysics.CanonicalLInfinityGenuineLogEntropyBarbalatRelaxation
import ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity

/-!
# Actual canonical on-shell relaxation by the Barbalat route

This target-facing adapter joins the actual cross-volume random-mass atlas to
the genuine-log Barbalat endpoint.  The selected physical deficit need not be
monotone; uniform continuity of the scaled entropy production along the RN
orbit is the remaining trajectory regularity input.
-/

namespace ArchonPhysics.CanonicalOnShellGenuineLogEntropyBarbalatRelaxation

open Filter MeasureTheory Set
open ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalLInfinityGenuineLogEntropyBarbalatRelaxation
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The actual canonical on-shell collision relaxes along a compact strictly
positive RN orbit without assuming monotonicity of the physical deficit. -/
theorem tendsto_deficit_zero_of_canonicalOnShell_crossVolume_genuineLogEntropy_barbalat
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (spec : Nat -> ActualTwoMassChartSpec)
    (hlocal : CrossVolumeActualLocalLowerAveraging spec
      collisionFrequencyCeiling (Measure.map markedChildFrequencyPair target))
    (hcover : CrossVolumeActualTriangleCover spec collisionFrequencyCeiling)
    (hupper :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling))
    (g : Real) (hg : g ≠ 0)
    {repairFloor actualBuffer : Real} (hrepairFloor : 0 < repairFloor)
    (hstrictBuffer : repairFloor < actualBuffer)
    (states : Set (CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)))
    (hstates : IsCompact states)
    (trajectory : Real -> CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak))
    (deficit : CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak) -> Real)
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (htrajectoryODE : forall t, 0 <= t ->
      HasDerivAt trajectory
        (rnCollisionVectorField
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          g (trajectory t)) t)
    (hdeficitContinuous : ContinuousOn deficit states)
    (hactionBuffer : forall action, action ∈ states ->
      AELowerBound
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak) actualBuffer action)
    (hdeficitEquilibrium : forall action, action ∈ states ->
      (exists scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure
            (ofCanonicalBroadenedWeakLimit ensemble time
              htime_pos htime target hweak),
          (action mode)⁻¹ = scale *
            (ofCanonicalBroadenedWeakLimit ensemble time
              htime_pos htime target hweak).frequency mode) ->
      deficit action = 0)
    (hdeficitNonnegative : forall t, 0 <= t ->
      0 <= deficit (trajectory t))
    (hdissipationTrajectoryUniformContinuous :
      UniformContinuousOn
        (fun t => g ^ 2 *
          canonicalLogEntropyProduction
            (ofCanonicalBroadenedWeakLimit ensemble time
              htime_pos htime target hweak)
            repairFloor (trajectory t))
        (Ici 0)) :
    Tendsto (fun t => deficit (trajectory t)) atTop (nhds 0) := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  have hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision := by
    exact
      boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_crossVolume_actualAtlas
        ensemble time htime_pos htime target hweak spec hlocal hcover hupper
  exact
    tendsto_deficit_zero_of_compact_canonicalLogEntropy_barbalat_rnCollisionODE
      collision hrigid g hg hrepairFloor hstrictBuffer states hstates
        trajectory deficit htrajectory htrajectoryODE hdeficitContinuous
        hactionBuffer hdeficitEquilibrium hdeficitNonnegative
        hdissipationTrajectoryUniformContinuous

end

end ArchonPhysics.CanonicalOnShellGenuineLogEntropyBarbalatRelaxation
