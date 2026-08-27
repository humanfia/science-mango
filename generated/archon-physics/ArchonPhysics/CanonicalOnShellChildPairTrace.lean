import ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
import ArchonPhysics.ContinuousThreeWaveBalanceAEBounded

/-!
# Canonical on-shell child-frequency trace adapter

This module identifies the child-frequency-pair measure of a canonical marked
on-shell cluster with the direct child projection of its supplied finite
marked target.  It also converts the canonical compact marked support into
collision- and reference-a.e. physical frequency bounds.

Consequently a positive planar density for this explicit projected target is
exactly the remaining trace input for continuous frequency-profile rigidity;
there is no separate abstract full-support premise in the final theorem.
-/

namespace ArchonPhysics.CanonicalOnShellChildPairTrace

open Set MeasureTheory
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.ContinuousThreeWaveBalanceAEBounded
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open Filter

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Directly forget the ranks and parent coordinate, retaining the two child
frequencies of a marked triad. -/
def markedChildFrequencyPair
    (marks : Fin 3 -> RankFrequencyMark) : Real × Real :=
  ((marks 1).2, (marks 2).2)

theorem measurable_markedChildFrequencyPair :
    Measurable markedChildFrequencyPair := by
  unfold markedChildFrequencyPair
  fun_prop

@[simp] theorem childFrequencyPair_ofMarkedFiniteMeasure
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hresonance :
      ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
        (marks 0).2 = (marks 1).2 + (marks 2).2) :
    childFrequencyPair (ofMarkedFiniteMeasure target hresonance) =
      markedChildFrequencyPair := by
  rfl

/-- The abstract child-pair measure of a packaged marked finite measure is
definitionally the direct child-frequency pushforward of that target. -/
theorem childFrequencyPairMeasure_ofMarkedFiniteMeasure
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hresonance :
      ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
        (marks 0).2 = (marks 1).2 + (marks 2).2) :
    childFrequencyPairMeasure (ofMarkedFiniteMeasure target hresonance) =
      Measure.map markedChildFrequencyPair target := by
  rfl

/-- The same exact pushforward identity specialized to a canonical broadened
weak limit. -/
theorem childFrequencyPairMeasure_ofCanonicalBroadenedWeakLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign (time n) (htime_pos n))
      atTop (nhds target)) :
    childFrequencyPairMeasure
        (ofCanonicalBroadenedWeakLimit ensemble time htime_pos htime
          target hweak) =
      Measure.map markedChildFrequencyPair target := by
  rfl

/-- A canonical compact-box support certificate gives physical frequency
bounds on all three collision legs almost everywhere. -/
theorem target_frequency_mem_uniformBand_ae
    {target : FiniteMeasure (Fin 3 -> RankFrequencyMark)}
    (htargetSupport :
      (target : Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0) :
    ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
      forall leg : Fin 3,
        (marks leg).2 ∈ Icc (0 : Real) collisionFrequencyCeiling := by
  have hmem :
      ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
        marks ∈ collisionRankFrequencyTripleSupport :=
    ae_iff.mpr htargetSupport
  filter_upwards [hmem] with marks hmarks
  intro leg
  exact ⟨(hmarks.1 leg).2, (hmarks.2 leg).2⟩

/-- Any collision-a.e. all-leg frequency bound passes to the sum of its three
leg marginals, hence to the canonical mode reference measure. -/
theorem frequency_mem_ae_collisionReference_of_triad_ae
    {Mode : Type*} [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) {W : Real}
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      collision.frequency mode ∈ Icc (0 : Real) W := by
  have hset : MeasurableSet
      {mode : Mode | collision.frequency mode ∈ Icc (0 : Real) W} :=
    measurableSet_Icc.preimage collision.measurable_frequency
  have hleg (leg : Fin 3) :
      ∀ᵐ mode ∂legMarginal collision leg,
        collision.frequency mode ∈ Icc (0 : Real) W := by
    unfold legMarginal
    exact (ae_map_iff (p := fun mode =>
      collision.frequency mode ∈ Icc (0 : Real) W)
      (measurable_triadLeg leg).aemeasurable hset).2
        (hfrequency.mono fun triad htriad => htriad leg)
  rw [collisionReferenceMeasure, ae_add_measure_iff, ae_add_measure_iff]
  exact ⟨⟨hleg 0, hleg 1⟩, hleg 2⟩

/-- Target-facing continuous rigidity theorem for a canonical on-shell marked
cluster.  The abstract support hypothesis has been replaced by one explicit
positive-density identity for the direct child projection of `target`. -/
theorem continuousFrequencyProfile_ae_proportional_of_canonicalOnShell_positiveChildTrace
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign (time n) (htime_pos n))
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
    {density : Real × Real -> ENNReal}
    (hdensity : AEMeasurable density
      (volume.restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling)))
    (hdensity_ne_zero :
      ∀ᵐ pair ∂volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling),
        density pair ≠ 0)
    (hpair :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) =
        (volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling)).withDensity
            density) :
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
  apply
    continuousFrequencyProfile_ae_proportional_of_positive_volumeTrace_ae_bounds
      collision (by unfold collisionFrequencyCeiling; positivity)
      hfrequencyCollision hfrequencyReference hprofile hbalance
      hdensity hdensity_ne_zero
  simpa [collision,
    childFrequencyPairMeasure_ofCanonicalBroadenedWeakLimit] using hpair

end

end ArchonPhysics.CanonicalOnShellChildPairTrace
