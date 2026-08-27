import ArchonPhysics.ContinuousThreeWaveBalanceVolumeTrace

/-!
# Continuous three-wave rigidity under almost-everywhere frequency bounds

The ambient mode type of the canonical marked limit is `Real × Real`, so its
frequency projection is not bounded on every point of the type.  Only the
collision and reference measures are carried by the physical compact box.
This module gives the measure-correct version of continuous balance rigidity:
frequency bounds are required collision-a.e. and reference-a.e., not globally
on unused ambient modes.
-/

namespace ArchonPhysics.ContinuousThreeWaveBalanceAEBounded

open Set MeasureTheory
open ArchonPhysics.AdditiveTriangleMeasureSupport
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ContinuousIntervalAdditiveRigidity
open ArchonPhysics.ContinuousThreeWaveBalanceVolumeTrace
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Collision-a.e. physical frequency bounds suffice to transfer a balanced
continuous profile to the full additive triangle and classify it there. -/
theorem continuousFrequencyProfile_linear_of_collision_ae_bounds
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hfullSupport : additiveFrequencyTriangle W ⊆
      ((childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W)).support) :
    exists beta : Real,
      forall omega, omega ∈ Icc (0 : Real) W ->
        profile omega = beta * omega := by
  let balanceSet : Set (Real × Real) :=
    {pair ∈ additiveFrequencyTriangle W |
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2}
  have htriad :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        childFrequencyPair collision triad ∈ balanceSet := by
    filter_upwards [collision.resonance_ae, hbalance, hfrequency] with
      triad hresonance hbalanced hfrequencyTriad
    have hchildOne := hfrequencyTriad 1
    have hchildTwo := hfrequencyTriad 2
    have hparent := hfrequencyTriad 0
    constructor
    · exact ⟨hchildOne.1, hchildTwo.1,
        hresonance ▸ hparent.2⟩
    · simpa only [childFrequencyPair, hresonance] using hbalanced
  have hbalancePair :
      ∀ᵐ pair ∂childFrequencyPairMeasure collision, pair ∈ balanceSet := by
    have hm : AEMeasurable (childFrequencyPair collision)
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)) :=
      (measurable_childFrequencyPair collision).aemeasurable
    have hs : MeasurableSet balanceSet := by
      dsimp only [balanceSet]
      exact (isClosed_frequencyBalanceSet hprofile).measurableSet
    unfold childFrequencyPairMeasure
    exact (ae_map_iff (p := fun pair => pair ∈ balanceSet) hm
      (by simpa using hs)).2 htriad
  have hbalanceRestricted :
      ∀ᵐ pair ∂(childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W),
        profile (pair.1 + pair.2) = profile pair.1 + profile pair.2 := by
    apply ae_restrict_of_ae
    filter_upwards [hbalancePair] with pair hpair
    exact hpair.2
  have hpointwisePair :=
    continuousOn_frequencyBalance_of_ae_restrict_of_fullSupport
      hprofile hfullSupport hbalanceRestricted
  have hadd : forall x, x ∈ Icc (0 : Real) W ->
      forall y, y ∈ Icc (0 : Real) W -> x + y <= W ->
        profile (x + y) = profile x + profile y := by
    intro x hx y hy hxy
    exact hpointwisePair (x, y) ⟨hx.1, hy.1, hxy⟩
  exact continuousOn_interval_additive_linear profile hW hprofile hadd

/-- Adding the physically correct reference-a.e. frequency bound turns the
interval classification into the a.e. proportionality conclusion needed by
the entropy equality case. -/
theorem continuousFrequencyProfile_ae_proportional_of_collision_ae_bounds
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    (hfrequencyReference :
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        collision.frequency mode ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hfullSupport : additiveFrequencyTriangle W ⊆
      ((childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W)).support) :
    exists beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  obtain ⟨beta, hbeta⟩ :=
    continuousFrequencyProfile_linear_of_collision_ae_bounds collision hW
      hfrequencyCollision hprofile hbalance hfullSupport
  refine ⟨beta, ?_⟩
  filter_upwards [hfrequencyReference] with mode hmode
  exact hbeta _ hmode

/-- Positive planar child-pair density plus collision/reference-a.e. compact
frequency support gives continuous-profile rigidity without a false global
bound on the ambient marked type. -/
theorem continuousFrequencyProfile_ae_proportional_of_positive_volumeTrace_ae_bounds
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    (hfrequencyReference :
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        collision.frequency mode ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    {density : Real × Real -> ENNReal}
    (hdensity : AEMeasurable density
      (volume.restrict (additiveFrequencyTriangle W)))
    (hdensity_ne_zero :
      ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
        density pair ≠ 0)
    (hpair :
      (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W) =
        (volume.restrict (additiveFrequencyTriangle W)).withDensity density) :
    exists beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  apply continuousFrequencyProfile_ae_proportional_of_collision_ae_bounds
    collision hW hfrequencyCollision hfrequencyReference hprofile hbalance
  exact fullSupport_of_restrict_eq_withDensity hW hdensity
    hdensity_ne_zero hpair

end

end ArchonPhysics.ContinuousThreeWaveBalanceAEBounded
