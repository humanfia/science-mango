import ArchonPhysics.CanonicalLInfinityCompactOrbitDissipationUniformContinuity
import ArchonPhysics.CanonicalLInfinityGenuineLogEntropyBarbalatRelaxation
import ArchonPhysics.CanonicalOnShellMarginalDominatedRigidity
import ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2

/-!
# Rayleigh--Jeans F2 from marginal-dominated canonical rigidity

The full child-frequency pair law may contain genuine diagonal singularities.
For entropy rigidity one only needs planar volume to be dominated by the
child trace on the additive triangle, together with absolute continuity of
the one-dimensional collision-reference frequency marginal.  This module
feeds exactly those weaker hypotheses into the concrete Rayleigh--Jeans
distance and the genuine-log Barbalat relaxation theorem.
-/

namespace ArchonPhysics.CanonicalOnShellMarginalRayleighJeansDistanceF2

open Filter MeasureTheory Metric Set
open ArchonPhysics
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalLInfinityCompactOrbitDissipationUniformContinuity
open ArchonPhysics.CanonicalLInfinityGenuineLogEntropyBarbalatRelaxation
open ArchonPhysics.CanonicalLInfinityLogEntropyFunctional
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarginalDominatedRigidity
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.PositiveTimeTwoTimeKineticHittingBounds
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.TwoTimeKineticHittingBounds
open scoped ENNReal MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The concrete Rayleigh--Jeans distance relaxes under the exact weaker
marginal-dominated rigidity inputs. -/
theorem tendsto_rayleighJeansDistance_zero_of_marginalDominatedCanonicalOnShell
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
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (htrajectoryODE : forall t, 0 <= t ->
      HasDerivAt trajectory
        (rnCollisionVectorField
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          g (trajectory t)) t)
    (hactionBuffer : forall action, action ∈ states ->
      AELowerBound
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak) actualBuffer action) :
    Tendsto
      (fun t => rayleighJeansDistance
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak)
        (trajectory t))
      atTop (nhds 0) := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  have hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision := by
    exact canonicalOnShell_rigid_of_dominatedTrace_frequencyReferenceAC
      ensemble time htime_pos htime target hweak hlower hfrequencyReferenceAC
  have hdissipationUniform : UniformContinuousOn
      (fun t => g ^ 2 *
        canonicalLogEntropyProduction collision repairFloor (trajectory t))
      (Ici 0) :=
    uniformContinuousOn_scaled_canonicalLogEntropyProduction_along_compact_rnCollisionODE
      collision g hrepairFloor states hstates trajectory htrajectory
        htrajectoryODE
  exact
    tendsto_deficit_zero_of_compact_canonicalLogEntropy_barbalat_rnCollisionODE
      collision hrigid g hg hrepairFloor hstrictBuffer states hstates
      trajectory (rayleighJeansDistance collision) htrajectory htrajectoryODE
      (continuous_rayleighJeansDistance collision).continuousOn hactionBuffer
      (fun action _haction hequilibrium =>
        rayleighJeansDistance_eq_zero_of_equilibrium
          collision action hequilibrium)
      (fun t _ht => rayleighJeansDistance_nonnegative
        collision (trajectory t))
      hdissipationUniform

/-- The weaker marginal conditions also give a robust release-level kinetic
window whenever the initial state is separated from the equilibrium class. -/
theorem exists_robustRayleighJeansHittingWindow_of_marginalDominatedCanonicalOnShell
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
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (htrajectoryODE : forall t, 0 <= t ->
      HasDerivAt trajectory
        (rnCollisionVectorField
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          g (trajectory t)) t)
    (hactionBuffer : forall action, action ∈ states ->
      AELowerBound
        (ofCanonicalBroadenedWeakLimit ensemble time
          htime_pos htime target hweak) actualBuffer action)
    (delta : Real) (hdelta : 0 < delta)
    (hseparated : delta < rayleighJeansDistance
      (ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak)
      (trajectory 0)) :
    exists lower upper : Real,
      RobustKineticHittingWindow
        (fun t => rayleighJeansDistance
          (ofCanonicalBroadenedWeakLimit ensemble time
            htime_pos htime target hweak)
          (trajectory t))
        delta lower upper := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  let distance : Real -> Real :=
    fun t => rayleighJeansDistance collision (trajectory t)
  have hrelax : Tendsto distance atTop (nhds 0) := by
    exact tendsto_rayleighJeansDistance_zero_of_marginalDominatedCanonicalOnShell
      ensemble time htime_pos htime target hweak hlower hfrequencyReferenceAC
      g hg hrepairFloor hstrictBuffer states hstates trajectory htrajectory
      htrajectoryODE hactionBuffer
  have htrajectoryContinuousAt : ContinuousAt trajectory 0 :=
    (htrajectoryODE 0 le_rfl).continuousAt
  have hdistanceContinuousAt : ContinuousAt distance 0 :=
    (continuous_rayleighJeansDistance collision).continuousAt.comp
      htrajectoryContinuousAt
  have hright : Tendsto distance (nhdsWithin 0 (Ioi 0))
      (nhds (rayleighJeansDistance collision (trajectory 0))) :=
    hdistanceContinuousAt.mono_left inf_le_left
  exact exists_robustKineticHittingWindow_of_tendsto_right
    distance (rayleighJeansDistance collision (trajectory 0)) delta
      hdelta hseparated hright hrelax

end

end ArchonPhysics.CanonicalOnShellMarginalRayleighJeansDistanceF2
