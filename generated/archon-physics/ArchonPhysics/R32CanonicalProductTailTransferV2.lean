import ArchonPhysics.R32RandomMassSpec

/-!
# Canonical product-law tail transfer, corrected version

The frozen v0.3 sample law is a product of the complete iid mass sequence
and the complete iid Haar phase sequence. A uniform bound on every
frozen-mass phase section therefore bounds the joint canonical event by the
same constant.

The finite-coordinate result allows an event to depend jointly and
arbitrarily on both first-N blocks. A mass-dependent finite-grid or bond
observable at positive time may be inserted into the event. The proof uses
only the time-zero product coordinates and assumes no fresh positive-time
independence.
-/

namespace ArchonPhysics.R32CanonicalProductTailTransferV2

open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.R32RandomMassSpec
open ArchonPhysics.RandomPhaseMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-! ## Full sequence product-law transfer -/

/-- A uniform phase-section bound transfers to the complete canonical
mass/phase product event. The event may depend on both complete sequences. -/
theorem canonical_measureReal_le_of_phase_sections
    (event : Set RandomEnsemble.SampleSpace)
    (hevent : MeasurableSet event) {p : Real}
    (hsection : ∀ mass : RandomEnsemble.RawMassSequence,
      RandomEnsemble.phaseSequenceLaw.real
          (Prod.mk mass ⁻¹' event) ≤ p) :
    canonicalIIDMassPhaseEnsemble.probability.real event ≤ p := by
  have hp : 0 ≤ p := by
    calc
      0 ≤ RandomEnsemble.phaseSequenceLaw.real
          (Prod.mk (fun _ => 0) ⁻¹' event) := measureReal_nonneg
      _ ≤ p := hsection (fun _ => 0)
  rw [canonical_probability_eq_mass_phase_product, measureReal_def,
    Measure.prod_apply hevent]
  apply ENNReal.toReal_le_of_le_ofReal hp
  calc
    (∫⁻ mass, RandomEnsemble.phaseSequenceLaw
        (Prod.mk mass ⁻¹' event) ∂(RandomEnsemble.massSequenceLaw)) ≤
        ∫⁻ _mass, ENNReal.ofReal p
          ∂(RandomEnsemble.massSequenceLaw) := by
      apply lintegral_mono
      intro mass
      apply (ENNReal.le_ofReal_iff_toReal_le
        (measure_ne_top RandomEnsemble.phaseSequenceLaw _) hp).2
      simpa only [measureReal_def] using hsection mass
    _ = ENNReal.ofReal p := by simp

/-! ## Exact finite-coordinate Haar law -/

/- Use exactly the normalized Haar instances used by finitePhaseHaarLaw. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The first N canonical mass representatives of a raw mass sequence.
Clipping makes these exactly the positive representatives carried by the
canonical ensemble. -/
def firstNCanonicalMass {N : Nat} [NeZero N]
    (mass : RandomEnsemble.RawMassSequence) : Lattice.Configuration N :=
  fun site => RandomEnsemble.clippedMass (mass site.val)

theorem measurable_firstNCanonicalMass {N : Nat} [NeZero N] :
    Measurable (firstNCanonicalMass (N := N)) := by
  exact measurable_pi_lambda _ fun site =>
    RandomEnsemble.measurable_clippedMass.comp
      (measurable_pi_apply site.val)

/-- Restrict the complete phase sequence to the first N periodic-lattice
coordinates. -/
def firstNPhase {N : Nat} [NeZero N]
    (phase : RandomEnsemble.PhaseSequence) :
    IIDMassPhaseEnsemble.PhaseConfiguration N :=
  fun site => phase site.val

theorem measurable_firstNPhase {N : Nat} [NeZero N] :
    Measurable (firstNPhase (N := N)) := by
  exact measurable_pi_lambda _ fun site => measurable_pi_apply site.val

/-- Under the complete iid phase law, restriction to the first N coordinates
has exactly the normalized finite product Haar law. -/
theorem firstNPhase_hasLaw_finitePhaseHaarLaw
    {N : Nat} [NeZero N] :
    HasLaw (firstNPhase (N := N))
      (finitePhaseHaarLaw (Lattice.Site N))
      RandomEnsemble.phaseSequenceLaw := by
  have hindep : iIndepFun
      (fun site : Lattice.Site N =>
        fun phase : RandomEnsemble.PhaseSequence => phase site.val)
      RandomEnsemble.phaseSequenceLaw := by
    unfold RandomEnsemble.phaseSequenceLaw
    exact (iIndepFun_infinitePi
      (fun _ : Nat => measurable_id)).precomp (ZMod.val_injective N)
  have hcoord : ∀ site : Lattice.Site N,
      HasLaw
        (fun phase : RandomEnsemble.PhaseSequence => phase site.val)
        RandomEnsemble.phaseCoordinateLaw
        RandomEnsemble.phaseSequenceLaw := by
    intro site
    exact (measurePreserving_eval_infinitePi
      (fun _ : Nat => RandomEnsemble.phaseCoordinateLaw)
      site.val).hasLaw
  have hjoint :
      HasLaw (firstNPhase (N := N))
        (Measure.infinitePi
          (fun _ : Lattice.Site N =>
            RandomEnsemble.phaseCoordinateLaw))
        RandomEnsemble.phaseSequenceLaw := by
    exact hindep.hasLaw_infinitePi hcoord
      measurable_firstNPhase.aemeasurable
  rw [finitePhaseProductLaw_eq_finitePhaseHaarLaw] at hjoint
  exact hjoint

/-! ## Joint first-N mass/phase events -/

/-- The complete first-N block read from the canonical product coordinates. -/
def canonicalFirstNBlock {N : Nat} [NeZero N]
    (sample : RandomEnsemble.SampleSpace) :
    Lattice.Configuration N ×
      IIDMassPhaseEnsemble.PhaseConfiguration N :=
  (firstNCanonicalMass sample.1, firstNPhase sample.2)

theorem measurable_canonicalFirstNBlock {N : Nat} [NeZero N] :
    Measurable (canonicalFirstNBlock (N := N)) := by
  exact
    (measurable_firstNCanonicalMass.comp measurable_fst).prodMk
      (measurable_firstNPhase.comp measurable_snd)

/-- The coordinate block is the canonical ensemble's finite restriction. -/
theorem canonicalFirstNBlock_eq_restrictions {N : Nat} [NeZero N]
    (sample : RandomEnsemble.SampleSpace) :
    canonicalFirstNBlock (N := N) sample =
      (canonicalIIDMassPhaseEnsemble.restrictMass sample,
        canonicalIIDMassPhaseEnsemble.restrictPhase sample) := by
  rfl

/-- With a raw mass sequence frozen, a measurable finite-block phase section
has exactly its finite Haar-section measure. -/
theorem canonicalFirstNBlock_phaseSection_measureReal_eq_finiteHaar
    {N : Nat} [NeZero N]
    (event : Set (Lattice.Configuration N ×
      IIDMassPhaseEnsemble.PhaseConfiguration N))
    (hevent : MeasurableSet event)
    (mass : RandomEnsemble.RawMassSequence) :
    RandomEnsemble.phaseSequenceLaw.real
        (Prod.mk mass ⁻¹' (canonicalFirstNBlock (N := N) ⁻¹' event)) =
      (finitePhaseHaarLaw (Lattice.Site N)).real
        (Prod.mk (firstNCanonicalMass (N := N) mass) ⁻¹' event) := by
  have hsection : MeasurableSet
      {phase : IIDMassPhaseEnsemble.PhaseConfiguration N |
        (firstNCanonicalMass (N := N) mass, phase) ∈ event} :=
    measurable_prodMk_left hevent
  change RandomEnsemble.phaseSequenceLaw.real
      {phase : RandomEnsemble.PhaseSequence |
        (firstNCanonicalMass (N := N) mass,
          firstNPhase (N := N) phase) ∈ event} =
    (finitePhaseHaarLaw (Lattice.Site N)).real
      {phase : IIDMassPhaseEnsemble.PhaseConfiguration N |
        (firstNCanonicalMass (N := N) mass, phase) ∈ event}
  exact
    (firstNPhase_hasLaw_finitePhaseHaarLaw (N := N)).measureReal_eq hsection

/-- Finite-coordinate transfer requiring a bound only on mass configurations
that actually arise from canonical raw sequences. -/
theorem canonical_finite_event_measureReal_le_of_raw_sections
    {N : Nat} [NeZero N]
    (event : Set (Lattice.Configuration N ×
      IIDMassPhaseEnsemble.PhaseConfiguration N))
    (hevent : MeasurableSet event) {p : Real}
    (hsection : ∀ rawMass : RandomEnsemble.RawMassSequence,
      (finitePhaseHaarLaw (Lattice.Site N)).real
          (Prod.mk (firstNCanonicalMass (N := N) rawMass) ⁻¹' event) ≤ p) :
    canonicalIIDMassPhaseEnsemble.probability.real
        {sample |
          (canonicalIIDMassPhaseEnsemble.restrictMass sample,
            canonicalIIDMassPhaseEnsemble.restrictPhase sample) ∈ event} ≤ p := by
  change canonicalIIDMassPhaseEnsemble.probability.real
    (canonicalFirstNBlock (N := N) ⁻¹' event) ≤ p
  apply canonical_measureReal_le_of_phase_sections
    (canonicalFirstNBlock (N := N) ⁻¹' event)
    (hevent.preimage measurable_canonicalFirstNBlock)
  intro rawMass
  rw [canonicalFirstNBlock_phaseSection_measureReal_eq_finiteHaar
    event hevent rawMass]
  exact hsection rawMass

/-- Finite-coordinate transfer with the stronger convenient hypothesis that
the Haar-section bound holds for every finite mass configuration.

The event may depend jointly on all first-N masses and phases. A deterministic
mass-dependent positive-time flow, finite time grid, or bond observable can
define the event; no independence of that derived observable is assumed. -/
theorem canonical_finite_event_measureReal_le
    {N : Nat} [NeZero N]
    (event : Set (Lattice.Configuration N ×
      IIDMassPhaseEnsemble.PhaseConfiguration N))
    (hevent : MeasurableSet event) {p : Real}
    (hsection : ∀ mass : Lattice.Configuration N,
      (finitePhaseHaarLaw (Lattice.Site N)).real
          (Prod.mk mass ⁻¹' event) ≤ p) :
    canonicalIIDMassPhaseEnsemble.probability.real
        {sample |
          (canonicalIIDMassPhaseEnsemble.restrictMass sample,
            canonicalIIDMassPhaseEnsemble.restrictPhase sample) ∈ event} ≤ p := by
  apply canonical_finite_event_measureReal_le_of_raw_sections event hevent
  intro rawMass
  exact hsection (firstNCanonicalMass rawMass)

#print axioms canonical_measureReal_le_of_phase_sections
#print axioms firstNPhase_hasLaw_finitePhaseHaarLaw
#print axioms canonicalFirstNBlock_phaseSection_measureReal_eq_finiteHaar
#print axioms canonical_finite_event_measureReal_le_of_raw_sections
#print axioms canonical_finite_event_measureReal_le

end

end ArchonPhysics.R32CanonicalProductTailTransferV2
