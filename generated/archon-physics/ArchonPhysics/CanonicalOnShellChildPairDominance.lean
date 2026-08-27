import ArchonPhysics.CanonicalOnShellChildPairTrace
import ArchonPhysics.ContinuousThreeWaveBalanceDominatedTrace

/-!
# Canonical on-shell rigidity from child-trace domination

This target-facing adapter weakens the positive-density contract of
`CanonicalOnShellChildPairTrace`.  It asks only for the null-set domination
which a lower multiparameter spectral-averaging theorem must establish.
-/

namespace ArchonPhysics.CanonicalOnShellChildPairDominance

open Set MeasureTheory
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceDominatedTrace
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open Filter

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A canonical broadened weak limit has continuous frequency-profile
rigidity as soon as its direct child projection dominates planar Lebesgue
null sets on the physical additive triangle. -/
theorem continuousFrequencyProfile_ae_proportional_of_canonicalOnShell_dominatedChildTrace
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
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile
      (Icc (0 : Real) collisionFrequencyCeiling))
    (hbalance :
      let collision := ofCanonicalBroadenedWeakLimit ensemble time
        htime_pos htime target hweak
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (htrace :
      volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling)) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    exists beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  have htargetSupport :
      (target : Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 :=
    canonicalBroadenedWeakLimit_compl_uniformSupport_eq_zero
      ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
      time htime_pos target hweak
  have hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈
            Icc (0 : Real) collisionFrequencyCeiling := by
    change ∀ᵐ triad ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
      forall leg : Fin 3,
        (triad leg).2 ∈ Icc (0 : Real) collisionFrequencyCeiling
    exact target_frequency_mem_uniformBand_ae htargetSupport
  have hfrequencyReference :
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        collision.frequency mode ∈
          Icc (0 : Real) collisionFrequencyCeiling :=
    frequency_mem_ae_collisionReference_of_triad_ae collision
      hfrequencyCollision
  apply continuousFrequencyProfile_ae_proportional_of_dominated_volumeTrace
    collision (by unfold collisionFrequencyCeiling; positivity)
      hfrequencyCollision hfrequencyReference hprofile hbalance
  simpa [collision,
    childFrequencyPairMeasure_ofCanonicalBroadenedWeakLimit] using htrace

end

end ArchonPhysics.CanonicalOnShellChildPairDominance
