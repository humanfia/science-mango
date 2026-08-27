import ArchonPhysics.FiniteHarmonicHaarPhasePropagation
import ArchonPhysics.OrderedSpectrumContinuity
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Mass-dependent harmonic propagation of Haar phases

Let `m` be a random mass state and let `theta` be an independent finite Haar
phase block.  For every measurable mass-dependent phase advance `a(m)`, the
skew translation

`(m, theta) |-> (m, a(m) + theta)`

preserves the product of the mass law and finite product Haar measure.  Thus
the evolved phase block is still product Haar and is still independent of the
mass block, even though its realized translation depends on that block.

The final section constructs `a(m)` from the measurable ordered harmonic
frequencies of the clipped positive random-mass chain.  This closes the
fiberwise free-harmonic conditional-law step.  It does **not** propagate an
RPA hypothesis through nonlinear FPUT or Lennard--Jones evolution.
-/

namespace ArchonPhysics.MassDependentHarmonicHaarPhasePropagation

open MeasureTheory ProbabilityTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity

noncomputable section

section FiberwiseSkew

variable {MassState d : Type*} [MeasurableSpace MassState]

/-- The mass-preserving skew translation by a mass-dependent phase advance. -/
def massDependentPhaseSkew (advance : MassState -> UnitAddTorus d) :
    MassState × UnitAddTorus d -> MassState × UnitAddTorus d :=
  fun state => (state.1, advance state.1 + state.2)

/-- Joint measurability of the skew translation follows from measurability of
the advance. -/
theorem measurable_massDependentPhaseSkew
    (advance : MassState -> UnitAddTorus d)
    (hadvance : Measurable advance) :
    Measurable (massDependentPhaseSkew advance) := by
  exact measurable_fst.prodMk
    ((hadvance.comp measurable_fst).add measurable_snd)

variable [Fintype d]

/- Match the normalized Haar instances used by `finitePhaseHaarLaw`. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : SFinite (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

/-- First-principles fiberwise theorem: every measurable mass-dependent Haar
translation preserves the joint product law. -/
theorem measurePreserving_massDependentPhaseSkew
    (massLaw : Measure MassState) [SFinite massLaw]
    (advance : MassState -> UnitAddTorus d)
    (hadvance : Measurable advance) :
    MeasurePreserving (massDependentPhaseSkew advance)
      (massLaw.prod (finitePhaseHaarLaw d))
      (massLaw.prod (finitePhaseHaarLaw d)) := by
  change MeasurePreserving
    (fun state : MassState × UnitAddTorus d =>
      (state.1, advance state.1 + state.2))
    (massLaw.prod (finitePhaseHaarLaw d))
    (massLaw.prod (finitePhaseHaarLaw d))
  have hfiber : forall mass : MassState,
      Measure.map (fun phase => advance mass + phase)
          (finitePhaseHaarLaw d) =
        finitePhaseHaarLaw d := by
    intro mass
    unfold finitePhaseHaarLaw
    exact (measurePreserving_add_left volume (advance mass)).map_eq
  exact (MeasurePreserving.id massLaw).skew_product
    (g := fun mass phase => advance mass + phase)
    ((hadvance.comp measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall hfiber)

/-- Transfer the invariant product law to any sample carrying an independent
mass block and finite product-Haar phase block. -/
theorem massDependentJoint_hasLaw_of_indep
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P]
    (massLaw : Measure MassState) [IsProbabilityMeasure massLaw]
    (advance : MassState -> UnitAddTorus d)
    (hadvance : Measurable advance)
    (mass : Omega -> MassState) (phase : Omega -> UnitAddTorus d)
    (hmass : HasLaw mass massLaw P)
    (hphase : HasLaw phase (finitePhaseHaarLaw d) P)
    (hindep : IndepFun mass phase P) :
    HasLaw (fun sample =>
      (mass sample, advance (mass sample) + phase sample))
      (massLaw.prod (finitePhaseHaarLaw d)) P := by
  change HasLaw
    (massDependentPhaseSkew advance ∘ fun sample =>
      (mass sample, phase sample))
    (massLaw.prod (finitePhaseHaarLaw d)) P
  exact (measurePreserving_massDependentPhaseSkew massLaw advance
    hadvance).hasLaw.comp (hindep.hasLaw_prod hmass hphase)

/-- The evolved finite phase block keeps the complete product Haar law. -/
theorem massDependentPhase_hasLaw_of_indep
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P]
    (massLaw : Measure MassState) [IsProbabilityMeasure massLaw]
    (advance : MassState -> UnitAddTorus d)
    (hadvance : Measurable advance)
    (mass : Omega -> MassState) (phase : Omega -> UnitAddTorus d)
    (hmass : HasLaw mass massLaw P)
    (hphase : HasLaw phase (finitePhaseHaarLaw d) P)
    (hindep : IndepFun mass phase P) :
    HasLaw (fun sample => advance (mass sample) + phase sample)
      (finitePhaseHaarLaw d) P := by
  have hjoint := massDependentJoint_hasLaw_of_indep massLaw advance
    hadvance mass phase hmass hphase hindep
  change HasLaw
    (Prod.snd ∘ fun sample =>
      (mass sample, advance (mass sample) + phase sample))
    (finitePhaseHaarLaw d) P
  exact measurePreserving_snd.hasLaw.comp hjoint

/-- Although the translation is mass-dependent, the mass block and evolved
phase block remain independent. -/
theorem mass_indep_massDependentPhase_of_indep
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P]
    (massLaw : Measure MassState) [IsProbabilityMeasure massLaw]
    (advance : MassState -> UnitAddTorus d)
    (hadvance : Measurable advance)
    (mass : Omega -> MassState) (phase : Omega -> UnitAddTorus d)
    (hmass : HasLaw mass massLaw P)
    (hphase : HasLaw phase (finitePhaseHaarLaw d) P)
    (hindep : IndepFun mass phase P) :
    IndepFun mass (fun sample => advance (mass sample) + phase sample) P := by
  have hevolved := massDependentPhase_hasLaw_of_indep massLaw advance
    hadvance mass phase hmass hphase hindep
  refine (indepFun_iff_hasLaw_prodMk_prod hmass hevolved).2 ?_
  exact massDependentJoint_hasLaw_of_indep massLaw advance hadvance
    mass phase hmass hphase hindep

end FiberwiseSkew

/-! ## Measurable ordered-frequency advance from a random mass sequence -/

/-- Infinite mass sequences are used as the conditioning block. -/
abbrev MassSequence := Nat -> Real

/-- Turn any real mass sequence into a pointwise-positive finite mass
configuration by the same clipping map used by the verified ensembles. -/
def clippedPositiveMassFromSequence {N : Nat} [NeZero N]
    (mass : MassSequence) : Lattice.PositiveMassConfig N where
  mass := fun site => RandomEnsemble.clippedMass (mass site.val)
  mass_pos := fun site => RandomEnsemble.clippedMass_pos (mass site.val)

theorem measurable_clippedPositiveMassFromSequence_coordinate
    {N : Nat} [NeZero N] (site : Lattice.Site N) :
    Measurable fun mass : MassSequence =>
      (clippedPositiveMassFromSequence mass).mass site := by
  exact RandomEnsemble.measurable_clippedMass.comp
    (measurable_pi_apply site.val)

/-- Reindex periodic phase coordinates by the finite ordered-mode index. -/
def orderedModeIndexOfSite {N : Nat} [NeZero N] :
    Lattice.Site N -> Fin (Fintype.card (Lattice.Site N)) :=
  (Fintype.equivOfCardEq (Fintype.card_fin _)).symm

/-- Ordered harmonic angular frequency determined by the random mass
sequence, reindexed onto the finite phase block. -/
def massSequenceOrderedModeFrequency {N : Nat} [NeZero N]
    (mass : MassSequence) (mode : Lattice.Site N) : Real :=
  harmonicOrderedModeFrequency
    (fun m : MassSequence => clippedPositiveMassFromSequence m)
    mass (orderedModeIndexOfSite mode)

theorem measurable_massSequenceOrderedModeFrequency
    {N : Nat} [NeZero N] :
    Measurable (massSequenceOrderedModeFrequency (N := N)) := by
  have hordered : Measurable (fun mass : MassSequence =>
      fun k : Fin (Fintype.card (Lattice.Site N)) =>
        harmonicOrderedModeFrequency
          (fun m : MassSequence =>
            clippedPositiveMassFromSequence (N := N) m) mass k) :=
    measurable_harmonicOrderedModeFrequencies_unconditional
      (fun m : MassSequence =>
        clippedPositiveMassFromSequence (N := N) m)
      measurable_clippedPositiveMassFromSequence_coordinate
  exact measurable_pi_lambda _ fun mode =>
    (measurable_pi_apply (orderedModeIndexOfSite mode)).comp hordered

/-- Mass-dependent free-harmonic advance built from the ordered angular
frequencies, with radians converted to turns. -/
def orderedHarmonicPhaseAdvance {N : Nat} [NeZero N]
    (time : Real) (mass : MassSequence) :
    Lattice.Site N -> UnitAddCircle :=
  harmonicPhaseAdvance (massSequenceOrderedModeFrequency mass) time

theorem measurable_orderedHarmonicPhaseAdvance
    {N : Nat} [NeZero N] (time : Real) :
    Measurable (orderedHarmonicPhaseAdvance (N := N) time) := by
  apply measurable_pi_lambda
  intro mode
  change Measurable fun mass : MassSequence =>
    ((massSequenceOrderedModeFrequency mass mode * time /
      (2 * Real.pi) : Real) : UnitAddCircle)
  have hfrequency : Measurable fun mass : MassSequence =>
      massSequenceOrderedModeFrequency mass mode :=
    (measurable_pi_apply mode).comp
      measurable_massSequenceOrderedModeFrequency
  exact AddCircle.measurable_mk'.comp
    ((hfrequency.mul_const time).div_const (2 * Real.pi))

/-! ## Truncated-Gaussian mass/Haar-phase ensemble adapter -/

namespace GaussianIIDMassPhaseEnsemble

open ArchonPhysics.TruncatedGaussianMassLaw

variable {parameters : Parameters}
variable {Omega : Type*} [MeasurableSpace Omega]

/-- The complete mass sequence carried by a verified Gaussian ensemble. -/
def ensembleMassSequence
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    (sample : Omega) : MassSequence :=
  fun index => ensemble.mass index sample

theorem measurable_ensembleMassSequence
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega) :
    Measurable (ensembleMassSequence ensemble) := by
  exact measurable_pi_lambda _ ensemble.mass_measurable

/-- The full mass sequence has the canonical iid truncated-Gaussian law. -/
theorem ensembleMassSequence_hasLaw
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega) :
    HasLaw (ensembleMassSequence ensemble)
      (TruncatedGaussianIIDMassSequence.probability parameters)
      ensemble.probability := by
  unfold ensembleMassSequence TruncatedGaussianIIDMassSequence.probability
  exact ensemble.mass_iIndep.hasLaw_infinitePi ensemble.mass_hasLaw
    (measurable_pi_lambda _ ensemble.mass_measurable).aemeasurable

/-- The full Gaussian mass sequence is independent of every finite phase
restriction. -/
theorem ensembleMassSequence_indep_restrictPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] :
    IndepFun (ensembleMassSequence ensemble)
      (ensemble.restrictPhase (N := N)) ensemble.probability := by
  have hPhase : Measurable
      (fun phase : Nat -> UnitAddCircle =>
        fun site : Lattice.Site N => phase site.val) :=
    measurable_pi_lambda _ fun site => measurable_pi_apply site.val
  have hindep := ensemble.mass_phase_indep.comp measurable_id hPhase
  change IndepFun
    (fun sample index => ensemble.mass index sample)
    (fun (sample : Omega) (site : Lattice.Site N) =>
      ensemble.phase site.val sample)
    ensemble.probability
  simpa [ensembleMassSequence,
    ArchonPhysics.GaussianIIDMassPhaseEnsemble.restrictPhase,
    Function.comp_def] using hindep

/-- Evolve the finite phase block by a measurable advance depending on the
complete mass sequence. -/
def massDependentFreeRestrictedPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (advance : MassSequence -> Lattice.Site N -> UnitAddCircle)
    (sample : Omega) : Lattice.Site N -> UnitAddCircle :=
  advance (ensembleMassSequence ensemble sample) +
    ensemble.restrictPhase sample

/-- The evolved Gaussian-ensemble phase block retains full finite product
Haar law for every measurable mass-dependent advance. -/
theorem massDependentFreeRestrictedPhase_hasLaw
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (advance : MassSequence -> Lattice.Site N -> UnitAddCircle)
    (hadvance : Measurable advance) :
    HasLaw (massDependentFreeRestrictedPhase ensemble advance)
      (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  change HasLaw (fun sample =>
    advance (ensembleMassSequence ensemble sample) +
      ensemble.restrictPhase sample)
    (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability
  exact massDependentPhase_hasLaw_of_indep
    (TruncatedGaussianIIDMassSequence.probability parameters)
    advance hadvance (ensembleMassSequence ensemble)
    (ensemble.restrictPhase (N := N))
    (ensembleMassSequence_hasLaw ensemble)
    (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble)
    (ensembleMassSequence_indep_restrictPhase ensemble)

/-- The complete mass sequence remains independent of the evolved phase
block, despite the mass-dependent translation. -/
theorem ensembleMassSequence_indep_massDependentFreeRestrictedPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (advance : MassSequence -> Lattice.Site N -> UnitAddCircle)
    (hadvance : Measurable advance) :
    IndepFun (ensembleMassSequence ensemble)
      (massDependentFreeRestrictedPhase ensemble advance)
      ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  change IndepFun (ensembleMassSequence ensemble)
    (fun sample =>
      advance (ensembleMassSequence ensemble sample) +
        ensemble.restrictPhase sample) ensemble.probability
  exact mass_indep_massDependentPhase_of_indep
    (TruncatedGaussianIIDMassSequence.probability parameters)
    advance hadvance (ensembleMassSequence ensemble)
    (ensemble.restrictPhase (N := N))
    (ensembleMassSequence_hasLaw ensemble)
    (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble)
    (ensembleMassSequence_indep_restrictPhase ensemble)

/-- Hence the finite mass restriction is also independent of the evolved
phase block. -/
theorem restrictMass_indep_massDependentFreeRestrictedPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (advance : MassSequence -> Lattice.Site N -> UnitAddCircle)
    (hadvance : Measurable advance) :
    IndepFun (ensemble.restrictMass (N := N))
      (massDependentFreeRestrictedPhase ensemble advance)
      ensemble.probability := by
  have hRestrict : Measurable
      (fun mass : MassSequence =>
        fun site : Lattice.Site N => mass site.val) :=
    measurable_pi_lambda _ fun site => measurable_pi_apply site.val
  have hindep :=
    (ensembleMassSequence_indep_massDependentFreeRestrictedPhase
      ensemble advance hadvance).comp hRestrict measurable_id
  change IndepFun
    (fun (sample : Omega) (site : Lattice.Site N) =>
      ensemble.mass site.val sample)
    (massDependentFreeRestrictedPhase ensemble advance)
    ensemble.probability
  simpa [ensembleMassSequence,
    ArchonPhysics.GaussianIIDMassPhaseEnsemble.restrictMass,
    Function.comp_def] using hindep

/-- For verified ensemble samples, clipping the already-supported mass
representative does not change any finite mass coordinate. -/
theorem clippedPositiveMassFrom_ensembleMassSequence_mass
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) (site : Lattice.Site N) :
    (clippedPositiveMassFromSequence
      (ensembleMassSequence ensemble sample)).mass site =
      (ensemble.restrictPositiveMass sample).mass site := by
  change RandomEnsemble.clippedMass (ensemble.mass site.val sample) =
    ensemble.mass site.val sample
  exact RandomEnsemble.clippedMass_eq_self
    (ensemble.mass_mem_support site.val sample)

/-- Actual mass-dependent free harmonic phase evolution using the measurable
ordered frequency vector. -/
def orderedMassDependentFreeRestrictedPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (time : Real) :
    Omega -> Lattice.Site N -> UnitAddCircle :=
  massDependentFreeRestrictedPhase ensemble
    (orderedHarmonicPhaseAdvance (N := N) time)

/-- The ordered-frequency evolved phase block is still finite product Haar. -/
theorem orderedMassDependentFreeRestrictedPhase_hasLaw
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (time : Real) :
    HasLaw (orderedMassDependentFreeRestrictedPhase (N := N) ensemble time)
      (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability := by
  exact massDependentFreeRestrictedPhase_hasLaw ensemble
    (orderedHarmonicPhaseAdvance (N := N) time)
    (measurable_orderedHarmonicPhaseAdvance time)

/-- The finite Gaussian mass block remains independent of the phases evolved
with its own ordered harmonic frequencies. -/
theorem restrictMass_indep_orderedMassDependentFreeRestrictedPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (time : Real) :
    IndepFun (ensemble.restrictMass (N := N))
      (orderedMassDependentFreeRestrictedPhase (N := N) ensemble time)
      ensemble.probability := by
  exact restrictMass_indep_massDependentFreeRestrictedPhase ensemble
    (orderedHarmonicPhaseAdvance (N := N) time)
    (measurable_orderedHarmonicPhaseAdvance time)

end GaussianIIDMassPhaseEnsemble

end

end ArchonPhysics.MassDependentHarmonicHaarPhasePropagation
