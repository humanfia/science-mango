import ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity

/-!
# Canonical rigidity from a lower child trace and regular one-leg marginals

The child-frequency pair law of the frozen random lattice can contain a
diagonal singular sector (for example when the two child modes coincide).
Consequently, upper absolute continuity of the *whole pair law* with respect
to planar volume is stronger than the entropy equality case actually needs.

This file records the weaker, truth-compatible interface.  Lower domination
of the additive-triangle trace transfers the balance identity to planar
volume.  Absolute continuity of the one-leg frequency reference measure then
transfers the resulting one-dimensional Cauchy classification back to every
collision leg.  Arbitrary singular correlations between two legs are allowed.
-/

namespace ArchonPhysics.MeasurableThreeWaveBalanceMarginalRigidity

open Set MeasureTheory
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.MeasurableThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Three one-leg frequency absolute-continuity estimates combine to the
absolute continuity of the full collision reference frequency measure. -/
theorem map_frequency_collisionReference_absolutelyContinuous_of_legs
    (collision : ResonantThreeWaveMeasure Mode) (reference : Measure Real)
    (hleg : ∀ leg : Fin 3,
      Measure.map collision.frequency (legMarginal collision leg) ≪ reference) :
    Measure.map collision.frequency (collisionReferenceMeasure collision) ≪
      reference := by
  rw [collisionReferenceMeasure,
    Measure.map_add _ _ collision.measurable_frequency,
    Measure.map_add _ _ collision.measurable_frequency]
  exact Measure.AbsolutelyContinuous.add_left
    (Measure.AbsolutelyContinuous.add_left (hleg 0) (hleg 1)) (hleg 2)

/-- A lower planar trace and an absolutely continuous one-leg frequency
reference suffice for measurable frequency-balance rigidity.  No upper
absolute-continuity assertion about the joint child-pair trace is used. -/
theorem measurableFrequencyProfile_ae_proportional_of_dominatedTrace_frequencyReferenceAC
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
        ∀ leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    {profile : Real → Real} (hprofile : Measurable profile)
    (hintegrable : IntegrableOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hlower : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W))
    (hfrequencyReferenceAC :
      Measure.map collision.frequency (collisionReferenceMeasure collision) ≪
        (volume : Measure Real)) :
    ∃ beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  obtain ⟨beta, hlinear⟩ :=
    measurableFrequencyProfile_linear_volume_ae_of_equivalentTrace
      collision hW hfrequency hprofile hintegrable hbalance hlower
  refine ⟨beta, ?_⟩
  have hfrequencyReference :
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        collision.frequency mode ∈ Icc (0 : Real) W :=
    frequency_mem_ae_collisionReference_of_triad_ae collision hfrequency
  have hmappedMem :
      ∀ᵐ omega ∂Measure.map collision.frequency
          (collisionReferenceMeasure collision),
        omega ∈ Icc (0 : Real) W :=
    (ae_map_iff collision.measurable_frequency.aemeasurable
      measurableSet_Icc).2 hfrequencyReference
  have hrestrictedAC :=
    hfrequencyReferenceAC.restrict (Icc (0 : Real) W)
  rw [Measure.restrict_eq_self_of_ae_mem hmappedMem] at hrestrictedAC
  have hmapped :
      ∀ᵐ omega ∂Measure.map collision.frequency
          (collisionReferenceMeasure collision),
        profile omega = beta * omega :=
    hrestrictedAC.ae_le hlinear
  have hset : MeasurableSet {omega : Real | profile omega = beta * omega} :=
    measurableSet_eq_fun hprofile (measurable_const.mul measurable_id)
  exact (ae_map_iff collision.measurable_frequency.aemeasurable hset).1 hmapped

/-- The bounded-profile version used by canonical `L∞` inverse actions. -/
theorem measurableFrequencyProfile_ae_proportional_of_memLp_top_dominatedTrace_frequencyReferenceAC
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
        ∀ leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    {profile : Real → Real} (hprofile : Measurable profile)
    (hmemLp : MemLp profile ∞ (volume.restrict (Icc (0 : Real) W)))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hlower : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W))
    (hfrequencyReferenceAC :
      Measure.map collision.frequency (collisionReferenceMeasure collision) ≪
        (volume : Measure Real)) :
    ∃ beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  exact
    measurableFrequencyProfile_ae_proportional_of_dominatedTrace_frequencyReferenceAC
      collision hW hfrequency hprofile (hmemLp.integrable (by simp))
        hbalance hlower hfrequencyReferenceAC

end

end ArchonPhysics.MeasurableThreeWaveBalanceMarginalRigidity

namespace ArchonPhysics.CanonicalRankFrequencyMarkedMarginalRigidity

open Set MeasureTheory
open ArchonPhysics.CanonicalRankFrequencyMarkedBalanceRigidity
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasurableRigidity
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.MeasurableThreeWaveBalanceMarginalRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal

noncomputable section

/-- Marked graph rigidity with a potentially singular joint child trace.  The
only upper absolute-continuity input is the scalar frequency marginal of the
collision reference measure. -/
theorem measurableMarkedWeight_linear_ae_of_graph_dominatedVolumeTrace_frequencyReferenceAC
    (collision : ResonantThreeWaveMeasure RankFrequencyMark)
    (F : Real → Real) (hF : Measurable F)
    (hfrequencyProjection : ∀ mark, collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 → RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    {weight : RankFrequencyMark → Real} (hweight : Measurable weight)
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 → RankFrequencyMark)),
        weight (triad 0) = weight (triad 1) + weight (triad 2))
    {W : Real} (hW : 0 < W)
    (hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 → RankFrequencyMark)),
        ∀ leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    (hprofileMemLp : MemLp (rankFrequencyGraphProfile F weight) ∞
      (volume.restrict (Icc (0 : Real) W)))
    (hlower : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W))
    (hfrequencyReferenceAC :
      Measure.map collision.frequency (collisionReferenceMeasure collision) ≪
        (volume : Measure Real)) :
    ∃ beta : Real,
      ∀ᵐ mark ∂collisionReferenceMeasure collision,
        weight mark = beta * collision.frequency mark := by
  have hprofile : Measurable (rankFrequencyGraphProfile F weight) :=
    measurable_rankFrequencyGraphProfile hF hweight
  have hprofileBalance := graphProfile_balance_ae_of_weight_balance
    collision F hfrequencyProjection hgraph weight hbalance
  obtain ⟨beta, hlinear⟩ :=
    measurableFrequencyProfile_ae_proportional_of_memLp_top_dominatedTrace_frequencyReferenceAC
      collision hW hfrequencyCollision hprofile hprofileMemLp
        hprofileBalance hlower hfrequencyReferenceAC
  refine ⟨beta, ?_⟩
  have hfactor := measurableWeight_eq_graphProfile_ae_collisionReferenceMeasure
    collision F hF hfrequencyProjection hgraph hweight
  filter_upwards [hfactor, hlinear] with mark hmark hmarkLinear
  rw [hmark]
  exact hmarkLinear

end

end ArchonPhysics.CanonicalRankFrequencyMarkedMarginalRigidity

namespace ArchonPhysics.CanonicalOnShellMarginalDominatedRigidity

open Filter Set MeasureTheory
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarkedClusterCompactSupport
open ArchonPhysics.CanonicalOnShellMarkedGraphSupport
open ArchonPhysics.CanonicalOnShellBoundedMeasurableRigidity
open ArchonPhysics.CanonicalRankFrequencyMarkedBalanceRigidity
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalRigidity
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Canonical bounded-measurable balance rigidity from lower child-trace
domination and one-leg frequency regularity.  This permits diagonal or other
singular correlations in the full child-frequency pair law. -/
theorem canonicalOnShell_rigid_of_dominatedTrace_frequencyReferenceAC
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hweak : Tendsto
      (fun n ↦
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
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
        (volume : Measure Real)) :
    let collision := ofCanonicalBroadenedWeakLimit ensemble time
      htime_pos htime target hweak
    BoundedMeasurableAEFrequencyBalanceRigid collision := by
  let collision := ofCanonicalBroadenedWeakLimit ensemble time
    htime_pos htime target hweak
  change BoundedMeasurableAEFrequencyBalanceRigid collision
  have htargetSupport :
      (target : Measure (Fin 3 → RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 :=
    canonicalBroadenedWeakLimit_compl_uniformSupport_eq_zero
      ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
      time htime_pos target hweak
  have hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 → RankFrequencyMark)),
        ∀ leg : Fin 3,
          collision.frequency (triad leg) ∈
            Icc (0 : Real) collisionFrequencyCeiling := by
    change ∀ᵐ triad ∂(target : Measure (Fin 3 → RankFrequencyMark)),
      ∀ leg : Fin 3,
        (triad leg).2 ∈ Icc (0 : Real) collisionFrequencyCeiling
    exact target_frequency_mem_uniformBand_ae htargetSupport
  have hgraphZero :
      (target : Measure (Fin 3 → RankFrequencyMark))
        (rankFrequencyTripleGraph
          ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue)ᶜ = 0 :=
    canonicalBroadenedWeakLimit_compl_graph_eq_zero
      ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
      time htime_pos target hweak
  have hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 → RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph
          ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue := by
    change ∀ᵐ triad ∂(target : Measure (Fin 3 → RankFrequencyMark)),
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
  exact
    measurableMarkedWeight_linear_ae_of_graph_dominatedVolumeTrace_frequencyReferenceAC
      collision
      ArchonPhysics.CanonicalScalarIDSBlockApproximation.canonicalScalarIDSValue
      ArchonPhysics.CanonicalScalarIDSContinuity.continuous_canonicalScalarIDSValue.measurable
      (fun _ ↦ rfl) hgraph hweight.measurable hbalance
      (by unfold collisionFrequencyCeiling; positivity)
      hfrequencyCollision hprofileMemLp hlowerLocal hfrequencyReferenceAC

end

end ArchonPhysics.CanonicalOnShellMarginalDominatedRigidity
