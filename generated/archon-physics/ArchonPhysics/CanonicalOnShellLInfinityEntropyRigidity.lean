import ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity
import ArchonPhysics.ResonantThreeWaveKineticLInfinityEntropyStationarity

/-!
# Canonical on-shell L-infinity entropy rigidity

This target-facing composition joins the actual canonical broadened weak-limit
collision, iid two-mass spectral atlas, bounded-measurable balance rigidity,
and the canonical `L-infinity` equality case of the H-theorem.
-/

namespace ArchonPhysics.CanonicalOnShellLInfinityEntropyRigidity

open Filter MeasureTheory Set
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

/-- For the actual canonical on-shell weak-limit collision, the iid mass-pair
atlas and the remaining upper trace bound classify every positive
zero-entropy canonical `L-infinity` state and prove it is stationary. -/
theorem stationary_and_inverseAction_ae_proportional_of_canonicalOnShell_atlas
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
    (patch : Nat → Set (Real × Real))
    (hpatchMeasurable : ∀ n, MeasurableSet (patch n))
    (hpatchSupport : ∀ n, patch n ⊆ iidMassPairSupport)
    (chart : Nat → Real × Real → Real × Real)
    (hchart : ∀ n, DifferentiableOn Real (chart n) (patch n))
    (hchartInj : ∀ n, InjOn (chart n) (patch n))
    (hcover : volume
      (additiveFrequencyTriangle collisionFrequencyCeiling \
        ⋃ n, chart n '' patch n) = 0)
    (hlower : ∀ n,
      Measure.map (chart n) (iidMassPairLaw.restrict (patch n)) ≪
        (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling))
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
    exact boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_iidMassPair_atlas
      ensemble time htime_pos htime target hweak patch hpatchMeasurable
      hpatchSupport chart hchart hchartInj hcover hlower hupper
  exact
    stationary_and_inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
      collision hrigid hfloor action hactionFloor hzero

end

end ArchonPhysics.CanonicalOnShellLInfinityEntropyRigidity
