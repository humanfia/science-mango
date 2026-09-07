import ArchonPhysics.MassDependentHarmonicHaarPhasePropagation
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Frozen v0.3 random-mass specification

The campaign's frozen v0.3 model uses the canonical iid law which is uniform
on `[4/5, 6/5]`, together with an independent iid normalized-Haar phase
sequence.  This file records that exact specification and closes one missing
adapter in the canonical (uniform-mass) chain.

`MassDependentHarmonicHaarPhasePropagation` already proves the corresponding
adapter for the parallel truncated-Gaussian interface.  Here we prove it for
`IIDMassPhaseEnsemble`: after advancing every finite phase coordinate by the
ordered harmonic frequency of the same random mass sample, the complete phase
block still has product Haar law and is still independent of the finite mass
block.  Combining this with the resultant proof of almost-sure simple spectrum
gives a single finite-volume certificate containing:

* the exact infinite product probability space;
* the exact finite iid mass and product-Haar phase laws;
* mass/phase independence before and after mass-dependent free propagation;
* exact Haar Fourier cancellation for every nonzero charge; and
* almost-sure simple spectrum with the last ordered mode as the unique zero
  frequency and every other ordered frequency strictly positive.

This is a probability/spectral specification.  It does not assert nonlinear
random-phase propagation, kinetic convergence, or thermalization.
-/

namespace ArchonPhysics.R32RandomMassSpec

open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.MassDependentHarmonicHaarPhasePropagation
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomPhaseMoments
open MeasureTheory ProbabilityTheory
open UnitAddTorus

noncomputable section

/-! ## The exact frozen one-coordinate and product laws -/

/-- The one-site mass law used by the frozen v0.3 campaign is exactly
normalized Lebesgue measure conditioned to `[4/5,6/5]`. -/
theorem massCoordinateLaw_eq_uniform_four_fifths_six_fifths :
    RandomEnsemble.massCoordinateLaw =
      ProbabilityTheory.cond (volume : Measure Real)
        (Set.Icc (4 / 5 : Real) (6 / 5 : Real)) := by
  rfl

/-- The canonical sample law is exactly the product of the countable iid mass
law and the countable iid Haar phase law. -/
theorem canonical_probability_eq_mass_phase_product :
    canonicalIIDMassPhaseEnsemble.probability =
      RandomEnsemble.massSequenceLaw.prod RandomEnsemble.phaseSequenceLaw := by
  rfl

/-- Every canonical representative lies pointwise in the frozen mass box. -/
theorem canonical_mass_mem_frozen_box (index : Nat)
    (sample : RandomEnsemble.SampleSpace) :
    (4 / 5 : Real) <= canonicalIIDMassPhaseEnsemble.mass index sample ∧
      canonicalIIDMassPhaseEnsemble.mass index sample <= (6 / 5 : Real) := by
  simpa [RandomEnsemble.massSupport, RandomEnsemble.massLower,
    RandomEnsemble.massUpper] using
    canonicalIIDMassPhaseEnsemble.mass_mem_support index sample

/-! ## Canonical uniform-mass dependent phase propagation -/

/-- The complete mass sequence carried by any verified uniform-mass
ensemble. -/
def ensembleMassSequence
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (sample : Omega) : Nat -> Real :=
  fun index => ensemble.mass index sample

theorem measurable_ensembleMassSequence
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) :
    Measurable (ensembleMassSequence ensemble) := by
  exact measurable_pi_lambda _ ensemble.mass_measurable

/-- The complete mass sequence has the canonical countable iid uniform law. -/
theorem ensembleMassSequence_hasLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) :
    HasLaw (ensembleMassSequence ensemble)
      RandomEnsemble.massSequenceLaw ensemble.probability := by
  unfold ensembleMassSequence RandomEnsemble.massSequenceLaw
  exact ensemble.mass_iIndep.hasLaw_infinitePi ensemble.mass_hasLaw
    (measurable_pi_lambda _ ensemble.mass_measurable).aemeasurable

/-- The full uniform mass sequence is independent of every finite phase
restriction. -/
theorem ensembleMassSequence_indep_restrictPhase
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
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
  simpa [ensembleMassSequence, IIDMassPhaseEnsemble.restrictPhase,
    Function.comp_def] using hindep

/-- Translate the finite phase block by an arbitrary measurable function of
the complete uniform mass sequence. -/
def massDependentRestrictedPhase
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (advance : (Nat -> Real) -> Lattice.Site N -> UnitAddCircle)
    (sample : Omega) : Lattice.Site N -> UnitAddCircle :=
  advance (ensembleMassSequence ensemble sample) +
    ensemble.restrictPhase sample

/-- A measurable mass-dependent translation preserves the entire finite
product Haar phase law for every verified uniform-mass ensemble. -/
theorem massDependentRestrictedPhase_hasLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (advance : (Nat -> Real) -> Lattice.Site N -> UnitAddCircle)
    (hadvance : Measurable advance) :
    HasLaw (massDependentRestrictedPhase ensemble advance)
      (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  change HasLaw (fun sample =>
    advance (ensembleMassSequence ensemble sample) +
      ensemble.restrictPhase sample)
    (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability
  exact massDependentPhase_hasLaw_of_indep
    RandomEnsemble.massSequenceLaw advance hadvance
    (ensembleMassSequence ensemble) (ensemble.restrictPhase (N := N))
    (ensembleMassSequence_hasLaw ensemble)
    (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble)
    (ensembleMassSequence_indep_restrictPhase ensemble)

/-- The complete mass sequence remains independent of the translated phase
block even though the translation depends on that mass sequence. -/
theorem ensembleMassSequence_indep_massDependentRestrictedPhase
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (advance : (Nat -> Real) -> Lattice.Site N -> UnitAddCircle)
    (hadvance : Measurable advance) :
    IndepFun (ensembleMassSequence ensemble)
      (massDependentRestrictedPhase ensemble advance)
      ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  change IndepFun (ensembleMassSequence ensemble)
    (fun sample =>
      advance (ensembleMassSequence ensemble sample) +
        ensemble.restrictPhase sample) ensemble.probability
  exact mass_indep_massDependentPhase_of_indep
    RandomEnsemble.massSequenceLaw advance hadvance
    (ensembleMassSequence ensemble) (ensemble.restrictPhase (N := N))
    (ensembleMassSequence_hasLaw ensemble)
    (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble)
    (ensembleMassSequence_indep_restrictPhase ensemble)

/-- Hence the finite mass restriction also remains independent of the
mass-dependent translated phase block. -/
theorem restrictMass_indep_massDependentRestrictedPhase
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (advance : (Nat -> Real) -> Lattice.Site N -> UnitAddCircle)
    (hadvance : Measurable advance) :
    IndepFun (ensemble.restrictMass (N := N))
      (massDependentRestrictedPhase ensemble advance)
      ensemble.probability := by
  have hRestrict : Measurable
      (fun mass : Nat -> Real =>
        fun site : Lattice.Site N => mass site.val) :=
    measurable_pi_lambda _ fun site => measurable_pi_apply site.val
  have hindep :=
    (ensembleMassSequence_indep_massDependentRestrictedPhase
      ensemble advance hadvance).comp hRestrict measurable_id
  change IndepFun
    (fun (sample : Omega) (site : Lattice.Site N) =>
      ensemble.mass site.val sample)
    (massDependentRestrictedPhase ensemble advance)
    ensemble.probability
  simpa [ensembleMassSequence, IIDMassPhaseEnsemble.restrictMass,
    Function.comp_def] using hindep

/-- Advance the uniform ensemble's phase block using the actual measurable
ordered harmonic frequencies of its own random mass realization. -/
def orderedMassDependentFreePhase
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (time : Real) :
    Omega -> Lattice.Site N -> UnitAddCircle :=
  massDependentRestrictedPhase ensemble
    (orderedHarmonicPhaseAdvance (N := N) time)

/-- The actual ordered-frequency evolved phase block remains product Haar. -/
theorem orderedMassDependentFreePhase_hasLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (time : Real) :
    HasLaw (orderedMassDependentFreePhase (N := N) ensemble time)
      (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability := by
  exact massDependentRestrictedPhase_hasLaw ensemble
    (orderedHarmonicPhaseAdvance (N := N) time)
    (measurable_orderedHarmonicPhaseAdvance time)

/-- The finite random mass block remains independent of phases evolved with
its own ordered harmonic frequency vector. -/
theorem restrictMass_indep_orderedMassDependentFreePhase
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (time : Real) :
    IndepFun (ensemble.restrictMass (N := N))
      (orderedMassDependentFreePhase (N := N) ensemble time)
      ensemble.probability := by
  exact restrictMass_indep_massDependentRestrictedPhase ensemble
    (orderedHarmonicPhaseAdvance (N := N) time)
    (measurable_orderedHarmonicPhaseAdvance time)

/- Use the same normalized Haar instances as `finitePhaseHaarLaw`. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Exact phase nondegeneracy after mass-dependent free propagation: every
nontrivial finite Fourier character has expectation zero. -/
theorem orderedMassDependentFreePhase_mFourier_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (time : Real)
    (charge : Lattice.Site N -> Int) :
    (∫ sample,
      mFourier charge
        (orderedMassDependentFreePhase (N := N) ensemble time sample)
      ∂ensemble.probability) =
      if charge = 0 then 1 else 0 := by
  calc
    _ = ∫ phase, mFourier charge phase
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      simpa [Function.comp_def] using
        (orderedMassDependentFreePhase_hasLaw ensemble time).integral_comp
          (mFourier charge).continuous.aestronglyMeasurable
    _ = if charge = 0 then 1 else 0 :=
      integral_mFourier_eq_ite charge

/-- In particular every nonzero phase charge cancels exactly. -/
theorem orderedMassDependentFreePhase_mFourier_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (time : Real)
    (charge : Lattice.Site N -> Int) (hcharge : charge ≠ 0) :
    (∫ sample,
      mFourier charge
        (orderedMassDependentFreePhase (N := N) ensemble time sample)
      ∂ensemble.probability) = 0 := by
  rw [orderedMassDependentFreePhase_mFourier_expectation,
    if_neg hcharge]

/-! ## One kernel-closed finite-volume v0.3 certificate -/

/-- Exact finite-volume random-mass/phase and spectral nondegeneracy package
for the frozen canonical v0.3 ensemble. -/
def CanonicalFiniteSpec {N : Nat} [NeZero N] (time : Real) : Prop :=
  HasLaw (canonicalIIDMassPhaseEnsemble.restrictMassFin (N := N))
      (RandomEnsemble.finiteMassLaw N)
      canonicalIIDMassPhaseEnsemble.probability ∧
  HasLaw (orderedMassDependentFreePhase (N := N)
      canonicalIIDMassPhaseEnsemble time)
      (finitePhaseHaarLaw (Lattice.Site N))
      canonicalIIDMassPhaseEnsemble.probability ∧
  IndepFun (canonicalIIDMassPhaseEnsemble.restrictMass (N := N))
      (orderedMassDependentFreePhase (N := N)
        canonicalIIDMassPhaseEnsemble time)
      canonicalIIDMassPhaseEnsemble.probability ∧
  (∀ charge : Lattice.Site N -> Int, charge ≠ 0 ->
    (∫ sample,
      mFourier charge
        (orderedMassDependentFreePhase (N := N)
          canonicalIIDMassPhaseEnsemble time sample)
      ∂canonicalIIDMassPhaseEnsemble.probability) = 0) ∧
  ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
    SimpleOrderedSpectrum
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) sample)) ∧
      ∀ mode : Fin (Fintype.card (Lattice.Site N)),
        0 < orderedModeFrequency
            (harmonicHermitian
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) sample)) mode ↔
          mode ≠ lastOrderedIndex (ι := Lattice.Site N)

/-- The canonical uniform-mass/Haar-phase construction inhabits the complete
finite-volume specification for every `N >= 2` and every real free time. -/
theorem canonicalFiniteSpec (time : Real)
    {N : Nat} [NeZero N] (hN : 2 <= N) :
    CanonicalFiniteSpec (N := N) time := by
  refine ⟨canonicalIIDMassPhaseEnsemble.restrictMassFin_hasLaw,
    orderedMassDependentFreePhase_hasLaw
      canonicalIIDMassPhaseEnsemble time,
    restrictMass_indep_orderedMassDependentFreePhase
      canonicalIIDMassPhaseEnsemble time,
    ?_, ?_⟩
  · intro charge hcharge
    exact orderedMassDependentFreePhase_mFourier_eq_zero
      canonicalIIDMassPhaseEnsemble time charge hcharge
  · filter_upwards
      [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
        canonicalIIDMassPhaseEnsemble hN] with sample hsimple
    have hsimple' : SimpleOrderedSpectrum
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) sample)) := by
      simpa [harmonicHermitianSample, harmonicHermitian] using hsimple
    refine ⟨hsimple', ?_⟩
    intro mode
    exact orderedModeFrequency_pos_iff_ne_last
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := N) sample) hsimple' mode

#print axioms massCoordinateLaw_eq_uniform_four_fifths_six_fifths
#print axioms canonical_probability_eq_mass_phase_product
#print axioms orderedMassDependentFreePhase_hasLaw
#print axioms orderedMassDependentFreePhase_mFourier_expectation
#print axioms canonicalFiniteSpec

end

end ArchonPhysics.R32RandomMassSpec
