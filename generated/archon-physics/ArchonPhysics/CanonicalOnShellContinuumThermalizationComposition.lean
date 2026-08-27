import ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction
import ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2

/-!
# Direct continuum on-shell F2--F3 thermalization composition

The canonical microscopic hitting-time transfer is already parametrized by
an arbitrary real-valued kinetic distance.  Consequently the genuine
continuum Rayleigh--Jeans distance does not need to be encoded as a finite
collision model before it can feed the release law.

This module makes that direct path explicit.  The continuum entropy theorem
supplies the robust two-time window; a matching local-uniform microscopic
approximation then supplies the high-probability inverse-square law.  The
model-specific on-shell atlas, global positive trajectory, initial
separation, and microscopic approximation hypotheses remain visible.
-/

namespace ArchonPhysics.CanonicalOnShellContinuumThermalizationComposition

open ArchonPhysics
open ArchonPhysics.ActualTwoMassCrossVolumeSpectralAtlas
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction
open ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellCrossVolumeSpectralRigidity
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/--
The exact continuum on-shell relaxation window composes directly with a
matching microscopic kinetic-window approximation.  In particular no
finite `FiniteCollisionModel` adapter occurs in this statement.
-/
theorem KineticWindowApproximation.exists_highProbabilityG2Bounds_of_canonicalOnShell
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
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
    (kineticCoupling : Real) (hkineticCoupling : kineticCoupling ≠ 0)
    {repairFloor actualBuffer : Real} (hrepairFloor : 0 < repairFloor)
    (hstrictBuffer : repairFloor < actualBuffer)
    (states : Set (CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)))
    (hstates : IsCompact states)
    (trajectory : Real -> CanonicalLInfinity
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak))
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (htrajectoryODE : forall t, 0 <= t ->
      HasDerivAt trajectory
        (rnCollisionVectorField
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          kineticCoupling (trajectory t)) t)
    (hactionBuffer : forall action, action ∈ states ->
      AELowerBound
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak) actualBuffer action)
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real -> Nat}
    (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : 0 < delta) (hthreshold : delta < 1 / 8)
    (hseparated : delta < rayleighJeansDistance
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)
      (trajectory 0))
    (microscopic : KineticWindowApproximation kappa beta hbeta mu delta
      sizeCutoff
      (fun t => rayleighJeansDistance
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak)
        (trajectory t))) :
    exists lower upper : Real,
      HighProbabilityG2Bounds
        canonicalIIDMassPhaseEnsemble.probability
        (measurableClosedEquilibrationTime kappa beta hbeta mu delta)
        sizeCutoff lower upper := by
  obtain ⟨lower, upper, window⟩ :=
    exists_robustRayleighJeansHittingWindow_of_canonicalOnShell
      ensemble time htime_pos htime target hweak spec hlocal hcover hupper
      kineticCoupling hkineticCoupling hrepairFloor hstrictBuffer
      states hstates trajectory htrajectory htrajectoryODE hactionBuffer
      delta hdelta hseparated
  exact ⟨lower, upper,
    ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction.KineticWindowApproximation.toHighProbabilityG2Bounds_of_twoTimeWindow
      hmu0 hmu1 hthreshold microscopic window⟩

end

end ArchonPhysics.CanonicalOnShellContinuumThermalizationComposition
