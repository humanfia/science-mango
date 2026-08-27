import ArchonPhysics.CanonicalLInfinityCompactOrbitDissipationUniformContinuity
import ArchonPhysics.CanonicalOnShellGenuineLogEntropyBarbalatRelaxation

/-!
# Automatic actual canonical on-shell Barbalat relaxation

Compactness of the RN orbit and the genuine collision ODE automatically make
the scaled entropy production uniformly continuous in time.  This removes the
last trajectory-regularity premise from the target-facing Barbalat adapter.
-/

namespace ArchonPhysics.CanonicalOnShellAutomaticGenuineLogEntropyBarbalatRelaxation

open Filter MeasureTheory Set
open ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
open ArchonPhysics.CanonicalLInfinityCompactOrbitDissipationUniformContinuity
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity
open ArchonPhysics.CanonicalOnShellGenuineLogEntropyBarbalatRelaxation
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

/-- Actual canonical on-shell compact-orbit relaxation with the genuine
entropy derivative, entropy ceiling, threshold coercivity, deficit
monotonicity, and dissipation time modulus all generated internally. -/
theorem tendsto_deficit_zero_of_canonicalOnShell_crossVolume_automatic_barbalat
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
      0 <= deficit (trajectory t)) :
    Tendsto (fun t => deficit (trajectory t)) atTop (nhds 0) := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  have hdissipationUniform : UniformContinuousOn
      (fun t => g ^ 2 *
        canonicalLogEntropyProduction collision repairFloor (trajectory t))
      (Ici 0) :=
    uniformContinuousOn_scaled_canonicalLogEntropyProduction_along_compact_rnCollisionODE
      collision g hrepairFloor states hstates trajectory htrajectory
        htrajectoryODE
  exact
    tendsto_deficit_zero_of_canonicalOnShell_crossVolume_genuineLogEntropy_barbalat
      ensemble time htime_pos htime target hweak spec hlocal hcover hupper
        g hg hrepairFloor hstrictBuffer states hstates trajectory deficit
        htrajectory htrajectoryODE hdeficitContinuous hactionBuffer
        hdeficitEquilibrium hdeficitNonnegative hdissipationUniform

end

end ArchonPhysics.CanonicalOnShellAutomaticGenuineLogEntropyBarbalatRelaxation
