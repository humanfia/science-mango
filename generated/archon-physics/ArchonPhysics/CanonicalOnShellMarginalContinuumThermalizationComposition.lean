import ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction
import ArchonPhysics.CanonicalOnShellMarginalRayleighJeansDistanceF2

/-!
# Direct marginal-dominated continuum F2--F3 release composition

This is the sector-compatible release path.  It composes the weaker
marginal-dominated canonical Rayleigh--Jeans window directly with the
canonical microscopic local-uniform approximation, without introducing a
finite collision model or requiring upper absolute continuity of the full
two-child frequency law.
-/

namespace ArchonPhysics.CanonicalOnShellMarginalContinuumThermalizationComposition

open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.CanonicalFrozenProbabilisticThermalizationReduction
open ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarginalRayleighJeansDistanceF2
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

/-- Sector-compatible continuum kinetic relaxation and a matching
microscopic approximation imply the release-level inverse-square law. -/
theorem KineticWindowApproximation.exists_highProbabilityG2Bounds_of_marginalDominatedCanonicalOnShell
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target))
    (hlower :
      volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling))
    (hfrequencyReferenceAC :
      let collision := ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak
      Measure.map collision.frequency (collisionReferenceMeasure collision) ≪
        (volume : Measure Real))
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
    exists_robustRayleighJeansHittingWindow_of_marginalDominatedCanonicalOnShell
      ensemble time htime_pos htime target hweak hlower hfrequencyReferenceAC
      kineticCoupling hkineticCoupling hrepairFloor hstrictBuffer
      states hstates trajectory htrajectory htrajectoryODE hactionBuffer
      delta hdelta hseparated
  exact ⟨lower, upper,
    ArchonPhysics.CanonicalFrozenTwoTimeThermalizationReduction.KineticWindowApproximation.toHighProbabilityG2Bounds_of_twoTimeWindow
      hmu0 hmu1 hthreshold microscopic window⟩

end

end ArchonPhysics.CanonicalOnShellMarginalContinuumThermalizationComposition
