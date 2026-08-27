import ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
import ArchonPhysics.CanonicalOnShellChildPairSpectralAveraging
import ArchonPhysics.CanonicalOnShellMarkedGraphSupport
import ArchonPhysics.CanonicalRankFrequencyMarkedMeasurableRigidity

/-!
# Canonical on-shell bounded measurable rigidity

This module proves the exact balance-rigidity contract used by the continuum
entropy equality case for an actual canonical broadened weak-limit collision.
Measurable bounded marked weights are reduced to their scalar IDS-graph
profiles, whose L-infinity membership follows from the global marked bound.

The first endpoint assumes equivalence of child-trace and planar null sets.
The second obtains the lower direction from a countable iid-two-mass spectral
atlas, leaving only the upper absolute-continuity direction as a trace input.
-/

namespace ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity

open Set MeasureTheory
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalOnShellChildPairSpectralAveraging
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalOnShellMarkedGraphSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedBalanceRigidity
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasurableRigidity
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A globally bounded measurable marked weight has an essentially bounded
scalar representative on every frequency measure. -/
theorem rankFrequencyGraphProfile_memLp_top_of_isBoundedMeasurable
    {F : Real -> Real} (hF : Measurable F)
    {weight : RankFrequencyMark -> Real}
    (hweight : IsBoundedMeasurable weight) (μ : Measure Real) :
    MemLp (rankFrequencyGraphProfile F weight) ∞ μ := by
  obtain ⟨bound, hbound⟩ := hweight.exists_norm_bound
  exact memLp_top_of_bound
    (measurable_rankFrequencyGraphProfile hF hweight.measurable).aestronglyMeasurable
    bound (Filter.Eventually.of_forall fun omega => hbound _)

/-- An actual canonical broadened weak-limit collision satisfies bounded
measurable a.e. frequency-balance rigidity when its child trace and planar
Lebesgue measure have the same null sets on the physical additive triangle. -/
theorem boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_equivalentChildTrace
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
    (hlower :
      volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling))
    (hupper :
      (Measure.map markedChildFrequencyPair target).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling)) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    BoundedMeasurableAEFrequencyBalanceRigid collision := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  change BoundedMeasurableAEFrequencyBalanceRigid collision
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
  have hgraphZero :
      (target : Measure (Fin 3 -> RankFrequencyMark))
        (rankFrequencyTripleGraph
          ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue)ᶜ = 0 :=
    canonicalBroadenedWeakLimit_compl_graph_eq_zero
      ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
      time htime_pos target hweak
  have hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph
          ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue := by
    change ∀ᵐ triad ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
      triad ∈ rankFrequencyTripleGraph
        ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue
    exact ae_iff.mpr hgraphZero
  have hlowerLocal :
      volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) := by
    simpa [collision,
      childFrequencyPairMeasure_ofCanonicalBroadenedWeakLimit] using hlower
  have hupperLocal :
      (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
        volume.restrict
          (additiveFrequencyTriangle collisionFrequencyCeiling) := by
    simpa [collision,
      childFrequencyPairMeasure_ofCanonicalBroadenedWeakLimit] using hupper
  intro weight hweight hbalance
  have hprofileMemLp :
      MemLp
        (rankFrequencyGraphProfile
          ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue
          weight) ∞
        (volume.restrict
          (Icc (0 : Real) collisionFrequencyCeiling)) :=
    rankFrequencyGraphProfile_memLp_top_of_isBoundedMeasurable
      ArchonPhysics.CanonicalScalarIDSContinuity.continuous_canonicalScalarIDSValue.measurable
      hweight _
  exact measurableMarkedWeight_linear_ae_of_graph_equivalentVolumeTrace
    collision
    ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue
    ArchonPhysics.CanonicalScalarIDSContinuity.continuous_canonicalScalarIDSValue.measurable
    (fun _ => rfl) hgraph hweight.measurable hbalance
    (by unfold collisionFrequencyCeiling; positivity)
    hfrequencyCollision hprofileMemLp hlowerLocal hupperLocal

/-- The countable iid-two-mass atlas discharges lower child-trace domination.
Only the upper absolute-continuity direction for the actual limiting child
trace remains as a direct trace hypothesis. -/
theorem boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_iidMassPair_atlas
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
          (additiveFrequencyTriangle collisionFrequencyCeiling)) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    BoundedMeasurableAEFrequencyBalanceRigid collision := by
  apply boundedMeasurableAEFrequencyBalanceRigid_of_canonicalOnShell_equivalentChildTrace
    ensemble time htime_pos htime target hweak
  · exact dominatedChildTrace_of_countable_iidMassPair_atlas target patch
      hpatchMeasurable hpatchSupport chart hchart hchartInj hcover hlower
  · exact hupper

end

end ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity
