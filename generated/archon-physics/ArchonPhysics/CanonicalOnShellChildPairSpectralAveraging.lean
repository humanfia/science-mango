import ArchonPhysics.CanonicalOnShellChildPairDominance
import ArchonPhysics.TwoParameterSpectralAveragingAtlas

/-!
# Canonical child-trace domination from a two-mass spectral atlas

This target-facing adapter replaces the raw reverse-absolute-continuity
premise of `CanonicalOnShellChildPairDominance` by two explicit pieces of
model data:

* differentiable injective two-mass charts cover the additive frequency
  triangle up to planar Lebesgue measure zero;
* the iid-mass averaged pushforward of each chart is absolutely continuous
  with respect to the canonical on-shell child-pair trace.

No conclusion from the spectral-averaging literature is postulated.  A model
proof must construct the charts and establish every local lower-averaging
statement supplied below.
-/

namespace ArchonPhysics.CanonicalOnShellChildPairSpectralAveraging

open Set MeasureTheory
open ArchonPhysics.CanonicalOnShellChildPairDominance
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The countable iid-two-mass atlas assumptions imply the exact canonical
child-pair reverse absolute continuity used by continuous balance rigidity. -/
theorem dominatedChildTrace_of_countable_iidMassPair_atlas
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
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
          (additiveFrequencyTriangle collisionFrequencyCeiling)) :
    volume.restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) := by
  exact
    volume_restrict_additiveTriangle_absolutelyContinuous_of_countable_iidMassPair_atlas
      collisionFrequencyCeiling patch hpatchMeasurable hpatchSupport chart
      hchart hchartInj hcover (Measure.map markedChildFrequencyPair target)
      hlower

/-- Canonical on-shell frequency-profile rigidity with the raw child-trace
domination condition replaced by a countable iid-two-mass spectral atlas. -/
theorem continuousFrequencyProfile_ae_proportional_of_canonicalOnShell_iidMassPair_atlas
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
          (additiveFrequencyTriangle collisionFrequencyCeiling)) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    exists beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  apply
    continuousFrequencyProfile_ae_proportional_of_canonicalOnShell_dominatedChildTrace
      ensemble time htime_pos htime target hweak hprofile hbalance
  exact dominatedChildTrace_of_countable_iidMassPair_atlas target patch
    hpatchMeasurable hpatchSupport chart hchart hchartInj hcover hlower

end

end ArchonPhysics.CanonicalOnShellChildPairSpectralAveraging
