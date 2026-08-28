import ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

/-!
# Hard-frequency restriction of a resonant three-wave measure

The acoustic Rayleigh--Jeans action is not globally bounded near zero
frequency.  For a positive cutoff, the physically correct hard subsystem is
obtained by retaining only triads whose three legs lie above the cutoff.  A
global `max cutoff` extension of the frequency agrees with the original
frequency on that restricted measure, preserves resonance almost everywhere,
and supplies the positive frequency floor required by canonical L-infinity
kinetic theory.
-/

namespace ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction

open Filter MeasureTheory Set
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Triads for which every physical frequency is at least `cutoff`. -/
def hardFrequencyTriads
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real) :
    Set (Fin 3 -> Mode) :=
  ⋂ leg : Fin 3,
    (fun triad => collision.frequency (triad leg)) ⁻¹' Ici cutoff

theorem measurableSet_hardFrequencyTriads
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real) :
    MeasurableSet (hardFrequencyTriads collision cutoff) := by
  unfold hardFrequencyTriads
  apply MeasurableSet.iInter
  intro leg
  exact measurableSet_Ici.preimage
    (collision.measurable_frequency.comp (measurable_pi_apply leg))

theorem mem_hardFrequencyTriads_iff
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real)
    (triad : Fin 3 -> Mode) :
    triad ∈ hardFrequencyTriads collision cutoff <->
      forall leg : Fin 3, cutoff <= collision.frequency (triad leg) := by
  simp [hardFrequencyTriads]

/-- Restrict the collision law to hard triads and extend its frequency by a
global cutoff.  The extension is invisible on the restricted collision law. -/
def hardFrequencyRestriction
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real) :
    ResonantThreeWaveMeasure Mode where
  frequency := fun mode => max cutoff (collision.frequency mode)
  measurable_frequency := measurable_const.max collision.measurable_frequency
  collisionMeasure := collision.collisionMeasure.restrict
    (hardFrequencyTriads collision cutoff)
  resonance_ae := by
    have hresonance :
        ∀ᵐ triad ∂((collision.collisionMeasure :
          Measure (Fin 3 -> Mode)).restrict
            (hardFrequencyTriads collision cutoff)),
          collision.frequency (triad 0) =
            collision.frequency (triad 1) +
              collision.frequency (triad 2) :=
      ae_restrict_of_ae collision.resonance_ae
    have hhard :
        ∀ᵐ triad ∂((collision.collisionMeasure :
          Measure (Fin 3 -> Mode)).restrict
            (hardFrequencyTriads collision cutoff)),
          triad ∈ hardFrequencyTriads collision cutoff :=
      self_mem_ae_restrict (measurableSet_hardFrequencyTriads collision cutoff)
    filter_upwards [hresonance, hhard] with triad hresonance hhard
    have hleg : forall leg : Fin 3,
        max cutoff (collision.frequency (triad leg)) =
          collision.frequency (triad leg) := by
      intro leg
      exact max_eq_right
        ((mem_hardFrequencyTriads_iff collision cutoff triad).1 hhard leg)
    rw [hleg 0, hleg 1, hleg 2]
    exact hresonance

@[simp]
theorem hardFrequencyRestriction_frequency
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real)
    (mode : Mode) :
    (hardFrequencyRestriction collision cutoff).frequency mode =
      max cutoff (collision.frequency mode) := by
  rfl

@[simp]
theorem hardFrequencyRestriction_collisionMeasure
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real) :
    ((hardFrequencyRestriction collision cutoff).collisionMeasure :
      Measure (Fin 3 -> Mode)) =
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)).restrict
          (hardFrequencyTriads collision cutoff) := by
  rfl

/-- The restricted frequency has a genuine global lower bound, not merely an
almost-everywhere one. -/
theorem cutoff_le_hardFrequencyRestriction_frequency
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real)
    (mode : Mode) :
    cutoff <= (hardFrequencyRestriction collision cutoff).frequency mode := by
  rw [hardFrequencyRestriction_frequency]
  exact le_max_left _ _

/-- Any measurable all-leg property of a collision law descends to its
canonical three-leg reference measure. -/
theorem property_ae_collisionReference_of_triad_ae
    (collision : ResonantThreeWaveMeasure Mode) (property : Mode -> Prop)
    (hproperty : MeasurableSet {mode | property mode})
    (htriad :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3, property (triad leg)) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision, property mode := by
  have hleg (leg : Fin 3) :
      ∀ᵐ mode ∂legMarginal collision leg, property mode := by
    unfold legMarginal
    exact (ae_map_iff (p := property)
      (measurable_triadLeg leg).aemeasurable hproperty).2
        (htriad.mono fun triad hmode => hmode leg)
  rw [collisionReferenceMeasure, ae_add_measure_iff, ae_add_measure_iff]
  exact ⟨⟨hleg 0, hleg 1⟩, hleg 2⟩

/-- Every mode seen by the hard collision reference has original physical
frequency at least the cutoff. -/
theorem original_frequency_ge_cutoff_ae_reference
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real) :
    ∀ᵐ mode ∂collisionReferenceMeasure
        (hardFrequencyRestriction collision cutoff),
      cutoff <= collision.frequency mode := by
  apply property_ae_collisionReference_of_triad_ae
    (hardFrequencyRestriction collision cutoff)
    (fun mode => cutoff <= collision.frequency mode)
    (measurableSet_Ici.preimage collision.measurable_frequency)
  rw [hardFrequencyRestriction_collisionMeasure]
  have hhard :
      ∀ᵐ triad ∂((collision.collisionMeasure :
        Measure (Fin 3 -> Mode)).restrict
          (hardFrequencyTriads collision cutoff)),
        triad ∈ hardFrequencyTriads collision cutoff :=
    self_mem_ae_restrict (measurableSet_hardFrequencyTriads collision cutoff)
  exact hhard.mono fun triad htriad =>
    (mem_hardFrequencyTriads_iff collision cutoff triad).1 htriad

/-- The totalized hard frequency agrees almost everywhere with the original
physical frequency on the hard collision reference. -/
theorem hardFrequencyRestriction_frequency_eq_original_ae_reference
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real) :
    (hardFrequencyRestriction collision cutoff).frequency =ᵐ[
        collisionReferenceMeasure (hardFrequencyRestriction collision cutoff)]
      collision.frequency := by
  filter_upwards [original_frequency_ge_cutoff_ae_reference
    collision cutoff] with mode hmode
  rw [hardFrequencyRestriction_frequency, max_eq_right hmode]

end

end ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
