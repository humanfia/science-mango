import ArchonPhysics.BroadenedResonanceWeakLimitSupport
import ArchonPhysics.RandomMassThreeWaveCollisionNetwork
import ArchonPhysics.ResonantThreeWaveMeasure

/-!
# Canonical on-shell marked collision clusters

Any finite weak limit of the canonical deterministic marked collision
measure, broadened along observation times tending to infinity, is carried
by the additive decay-resonance surface.  Consequently every such supplied
cluster point canonically defines a `ResonantThreeWaveMeasure` on
rank-frequency marks.

This module proves the support and interface conversion.  It does not assert
that a finite cluster point exists, is unique, or has positive mass.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalOnShellMarkedCluster

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.BroadenedResonanceWeakLimitSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- On marked triples, the decay-channel mismatch is exactly
`omega_0 - omega_1 - omega_2`. -/
theorem markedFrequencyMismatch_decay_eq
    (marks : Fin 3 -> RankFrequencyMark) :
    markedFrequencyMismatch decayInteractionSign marks =
      (marks 0).2 - (marks 1).2 - (marks 2).2 := by
  unfold markedFrequencyMismatch
  unfold ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit.forgetRankFrequencyTripleEuclidean
  unfold ArchonPhysics.CanonicalRankFrequencyMarkedMeasure.forgetRankFrequencyTriple
  unfold ArchonPhysics.CanonicalJointFrequencyEuclideanBridge.euclideanFrequencyTripleMismatch
  unfold ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral.frequencyTripleMismatch
  rw [Fin.sum_univ_three]
  simp [decayInteractionSign]
  ring

/-- Every supplied finite weak cluster of the canonical broadened marked
measures is supported on additive decay resonance. -/
theorem canonicalBroadenedWeakLimit_decay_resonance_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target)) :
    ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
      (marks 0).2 = (marks 1).2 + (marks 2).2 := by
  have hzero :
      ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
        markedFrequencyMismatch decayInteractionSign marks = 0 := by
    apply weakLimit_mismatch_eq_zero_ae
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
      (markedFrequencyMismatch decayInteractionSign)
      (continuous_markedFrequencyMismatch decayInteractionSign)
      time htime_pos htime target
    simpa [canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit] using hweak
  filter_upwards [hzero] with marks hmarks
  rw [markedFrequencyMismatch_decay_eq] at hmarks
  linarith

/-- Package a finite marked collision measure with additive resonance support
as the common resonant-three-wave interface. -/
def ofMarkedFiniteMeasure
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hresonance :
      ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
        (marks 0).2 = (marks 1).2 + (marks 2).2) :
    ResonantThreeWaveMeasure RankFrequencyMark where
  frequency := fun mark => mark.2
  measurable_frequency := measurable_snd
  collisionMeasure := target
  resonance_ae := hresonance

/-- A supplied finite large-time cluster of the canonical broadened marked
measures canonically induces a resonant three-wave measure. -/
def ofCanonicalBroadenedWeakLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target)) :
    ResonantThreeWaveMeasure RankFrequencyMark :=
  ofMarkedFiniteMeasure target
    (canonicalBroadenedWeakLimit_decay_resonance_ae
      ensemble time htime_pos htime target hweak)

@[simp]
theorem ofCanonicalBroadenedWeakLimit_collisionMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target)) :
    (ofCanonicalBroadenedWeakLimit ensemble time htime_pos htime target hweak).collisionMeasure =
      target := by
  rfl

end

end ArchonPhysics.CanonicalOnShellMarkedCluster
