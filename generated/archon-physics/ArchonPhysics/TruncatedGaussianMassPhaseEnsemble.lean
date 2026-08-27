import ArchonPhysics.TruncatedGaussianIIDMassSequence

/-!
# Truncated-Gaussian mass and Haar-phase ensemble

The pre-existing `ArchonPhysics.IIDMassPhaseEnsemble` intentionally fixes its
mass marginal to the canonical uniform law.  Changing that field would force a
wide refactor of uniform-law consumers.  This module instead provides a
parallel, explicitly parameterized interface for truncated-Gaussian masses.

The canonical sample space is the product of the countable iid mass space from
`TruncatedGaussianIIDMassSequence` and the existing countable Haar phase space.
The clipped mass representatives are pointwise positive.  We prove exact
marginal laws, mutual independence inside each block, independence of the two
blocks, and finite-periodic restrictions yielding `Lattice.PositiveMassConfig`.

This is ensemble infrastructure only; it contains no kinetic-limit or
thermalization assertion.
-/

namespace ArchonPhysics

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace TruncatedGaussianMassPhaseEnsemble

open TruncatedGaussianMassLaw

/-- The canonical sample contains an iid truncated-Gaussian mass sequence and
an independent iid Haar phase sequence. -/
abbrev SampleSpace := TruncatedGaussianIIDMassSequence.SampleSpace × RandomEnsemble.PhaseSequence

/-- Product probability law of the mass and phase blocks. -/
def canonicalLaw (parameters : Parameters) : Measure SampleSpace :=
  (TruncatedGaussianIIDMassSequence.probability parameters).prod RandomEnsemble.phaseSequenceLaw

noncomputable instance canonicalLaw.instIsProbabilityMeasure
    (parameters : Parameters) : IsProbabilityMeasure (canonicalLaw parameters) := by
  unfold canonicalLaw
  infer_instance

/-- Raw mass coordinate before the null-set clipping modification. -/
def rawMassAt (n : Nat) : SampleSpace → Real := fun sample ↦ sample.1 n

/-- Pointwise-positive mass coordinate. -/
def massAt (n : Nat) : SampleSpace → Real :=
  fun sample ↦ TruncatedGaussianIIDMassSequence.massAt n sample.1

/-- Haar phase coordinate. -/
def phaseAt (n : Nat) : SampleSpace → UnitAddCircle := fun sample ↦ sample.2 n

theorem measurable_rawMassAt (n : Nat) : Measurable (rawMassAt n) := by
  unfold rawMassAt
  fun_prop

theorem measurable_massAt (n : Nat) : Measurable (massAt n) := by
  unfold massAt
  exact TruncatedGaussianIIDMassSequence.measurable_massAt n |>.comp measurable_fst

theorem measurable_phaseAt (n : Nat) : Measurable (phaseAt n) := by
  unfold phaseAt
  fun_prop

/-- The entire raw mass block has its countable product law. -/
theorem rawMassSequence_hasLaw (parameters : Parameters) :
    HasLaw (fun sample : SampleSpace ↦ sample.1)
      (TruncatedGaussianIIDMassSequence.probability parameters) (canonicalLaw parameters) := by
  exact (MeasureTheory.measurePreserving_fst
    (μ := TruncatedGaussianIIDMassSequence.probability parameters)
    (ν := RandomEnsemble.phaseSequenceLaw)).hasLaw

/-- The entire phase block has its countable Haar product law. -/
theorem phaseSequence_hasLaw (parameters : Parameters) :
    HasLaw (fun sample : SampleSpace ↦ sample.2)
      RandomEnsemble.phaseSequenceLaw (canonicalLaw parameters) := by
  exact (MeasureTheory.measurePreserving_snd
    (μ := TruncatedGaussianIIDMassSequence.probability parameters)
    (ν := RandomEnsemble.phaseSequenceLaw)).hasLaw

/-- Every raw mass coordinate has the truncated-Gaussian marginal. -/
theorem rawMassAt_hasLaw (parameters : Parameters) (n : Nat) :
    HasLaw (rawMassAt n) (coordinateLaw parameters) (canonicalLaw parameters) := by
  have hEval : HasLaw (Function.eval n) (coordinateLaw parameters)
      (TruncatedGaussianIIDMassSequence.probability parameters) :=
    TruncatedGaussianIIDMassSequence.rawMassAt_hasLaw parameters n
  change HasLaw
    (Function.eval n ∘ fun sample : SampleSpace ↦ sample.1)
    (coordinateLaw parameters) (canonicalLaw parameters)
  exact hEval.comp (rawMassSequence_hasLaw parameters)

/-- Every clipped positive mass coordinate keeps the same marginal. -/
theorem massAt_hasLaw (parameters : Parameters) (n : Nat) :
    HasLaw (massAt n) (coordinateLaw parameters) (canonicalLaw parameters) := by
  have hMass : HasLaw (TruncatedGaussianIIDMassSequence.massAt n) (coordinateLaw parameters)
      (TruncatedGaussianIIDMassSequence.probability parameters) :=
    TruncatedGaussianIIDMassSequence.massAt_hasLaw parameters n
  change HasLaw
    (TruncatedGaussianIIDMassSequence.massAt n ∘ fun sample : SampleSpace ↦ sample.1)
    (coordinateLaw parameters) (canonicalLaw parameters)
  exact hMass.comp (rawMassSequence_hasLaw parameters)

/-- Every phase coordinate has normalized Haar law. -/
theorem phaseAt_hasLaw (parameters : Parameters) (n : Nat) :
    HasLaw (phaseAt n) RandomEnsemble.phaseCoordinateLaw
      (canonicalLaw parameters) := by
  have hEval : HasLaw (Function.eval n) RandomEnsemble.phaseCoordinateLaw
      RandomEnsemble.phaseSequenceLaw :=
    (measurePreserving_eval_infinitePi
      (fun _ : Nat ↦ RandomEnsemble.phaseCoordinateLaw) n).hasLaw
  change HasLaw
    (Function.eval n ∘ fun sample : SampleSpace ↦ sample.2)
    RandomEnsemble.phaseCoordinateLaw (canonicalLaw parameters)
  exact hEval.comp (phaseSequence_hasLaw parameters)

/-- The raw mass coordinates are mutually independent on the product sample
space. -/
theorem rawMassCoordinates_iIndep (parameters : Parameters) :
    iIndepFun rawMassAt (canonicalLaw parameters) := by
  have hm : AEMeasurable
      (fun sample : SampleSpace ↦ fun n ↦ rawMassAt n sample)
      (canonicalLaw parameters) :=
    (measurable_pi_lambda _ measurable_rawMassAt).aemeasurable
  apply (ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi
    (fun n ↦ rawMassAt_hasLaw parameters n) hm).2
  simpa [rawMassAt, TruncatedGaussianIIDMassSequence.probability] using
    rawMassSequence_hasLaw parameters

/-- Coordinatewise clipping preserves mutual independence of the mass block. -/
theorem massCoordinates_iIndep (parameters : Parameters) :
    iIndepFun massAt (canonicalLaw parameters) := by
  have hindep := (rawMassCoordinates_iIndep parameters).comp
    (fun _ : Nat ↦ RandomEnsemble.clippedMass)
    (fun _ ↦ RandomEnsemble.measurable_clippedMass)
  change iIndepFun
    (fun n ↦ RandomEnsemble.clippedMass ∘ rawMassAt n)
    (canonicalLaw parameters)
  exact hindep

/-- Haar phase coordinates are mutually independent on the product sample
space. -/
theorem phaseCoordinates_iIndep (parameters : Parameters) :
    iIndepFun phaseAt (canonicalLaw parameters) := by
  have hm : AEMeasurable
      (fun sample : SampleSpace ↦ fun n ↦ phaseAt n sample)
      (canonicalLaw parameters) :=
    (measurable_pi_lambda _ measurable_phaseAt).aemeasurable
  apply (ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi
    (fun n ↦ phaseAt_hasLaw parameters n) hm).2
  simpa [phaseAt, RandomEnsemble.phaseSequenceLaw] using
    phaseSequence_hasLaw parameters

/-- The full clipped mass sequence is independent of the full phase sequence. -/
theorem massSequence_indep_phaseSequence (parameters : Parameters) :
    IndepFun (fun sample ↦ fun n ↦ massAt n sample)
      (fun sample ↦ fun n ↦ phaseAt n sample) (canonicalLaw parameters) := by
  have hClip : Measurable
      (fun raw : TruncatedGaussianIIDMassSequence.SampleSpace ↦
        fun n ↦ RandomEnsemble.clippedMass (raw n)) := by
    exact measurable_pi_lambda _ fun n ↦
      RandomEnsemble.measurable_clippedMass.comp (measurable_pi_apply n)
  have hindep := ProbabilityTheory.indepFun_prod
    (μ := TruncatedGaussianIIDMassSequence.probability parameters)
    (ν := RandomEnsemble.phaseSequenceLaw)
    (X := fun raw : TruncatedGaussianIIDMassSequence.SampleSpace ↦
      fun n ↦ RandomEnsemble.clippedMass (raw n))
    (Y := id) hClip measurable_id
  change IndepFun
    (fun sample : SampleSpace ↦
      fun n ↦ RandomEnsemble.clippedMass (sample.1 n))
    (fun sample : SampleSpace ↦ sample.2)
    ((TruncatedGaussianIIDMassSequence.probability parameters).prod
      RandomEnsemble.phaseSequenceLaw)
  exact hindep

theorem massAt_mem_support (n : Nat) (sample : SampleSpace) :
    massAt n sample ∈ RandomEnsemble.massSupport :=
  TruncatedGaussianIIDMassSequence.massAt_mem_support n sample.1

theorem massAt_pos (n : Nat) (sample : SampleSpace) : 0 < massAt n sample :=
  TruncatedGaussianIIDMassSequence.massAt_pos n sample.1

end TruncatedGaussianMassPhaseEnsemble

/-! ## Verified ensemble interface -/

/-- Verified interface for iid truncated-Gaussian positive masses and an
independent iid Haar phase block. -/
structure GaussianIIDMassPhaseEnsemble
    (parameters : TruncatedGaussianMassLaw.Parameters)
    (Omega : Type*) [MeasurableSpace Omega] where
  /-- Probability measure on the supplied sample space. -/
  probability : Measure Omega
  /-- Pointwise-positive mass coordinates. -/
  mass : Nat → Omega → Real
  /-- Haar phase coordinates. -/
  phase : Nat → Omega → UnitAddCircle
  /-- The supplied measure has total mass one. -/
  probability_univ : probability Set.univ = 1
  /-- Every mass coordinate is measurable. -/
  mass_measurable : ∀ n, Measurable (mass n)
  /-- Every phase coordinate is measurable. -/
  phase_measurable : ∀ n, Measurable (phase n)
  /-- Every mass coordinate has the selected truncated-Gaussian law. -/
  mass_hasLaw : ∀ n, HasLaw (mass n)
    (TruncatedGaussianMassLaw.coordinateLaw parameters) probability
  /-- Every phase coordinate has normalized Haar law. -/
  phase_hasLaw : ∀ n, HasLaw (phase n)
    RandomEnsemble.phaseCoordinateLaw probability
  /-- Mass coordinates are mutually independent. -/
  mass_iIndep : iIndepFun mass probability
  /-- Phase coordinates are mutually independent. -/
  phase_iIndep : iIndepFun phase probability
  /-- The full mass and phase blocks are independent. -/
  mass_phase_indep : IndepFun (fun sample n ↦ mass n sample)
    (fun sample n ↦ phase n sample) probability
  /-- Representatives lie pointwise in the frozen positive support. -/
  mass_mem_support : ∀ n sample,
    mass n sample ∈ RandomEnsemble.massSupport

/-- Canonical product construction of the verified Gaussian ensemble. -/
def canonicalGaussianIIDMassPhaseEnsemble
    (parameters : TruncatedGaussianMassLaw.Parameters) :
    GaussianIIDMassPhaseEnsemble parameters
      TruncatedGaussianMassPhaseEnsemble.SampleSpace where
  probability := TruncatedGaussianMassPhaseEnsemble.canonicalLaw parameters
  mass := TruncatedGaussianMassPhaseEnsemble.massAt
  phase := TruncatedGaussianMassPhaseEnsemble.phaseAt
  probability_univ := by simp
  mass_measurable := TruncatedGaussianMassPhaseEnsemble.measurable_massAt
  phase_measurable := TruncatedGaussianMassPhaseEnsemble.measurable_phaseAt
  mass_hasLaw := TruncatedGaussianMassPhaseEnsemble.massAt_hasLaw parameters
  phase_hasLaw := TruncatedGaussianMassPhaseEnsemble.phaseAt_hasLaw parameters
  mass_iIndep := TruncatedGaussianMassPhaseEnsemble.massCoordinates_iIndep parameters
  phase_iIndep := TruncatedGaussianMassPhaseEnsemble.phaseCoordinates_iIndep parameters
  mass_phase_indep :=
    TruncatedGaussianMassPhaseEnsemble.massSequence_indep_phaseSequence parameters
  mass_mem_support := TruncatedGaussianMassPhaseEnsemble.massAt_mem_support

namespace GaussianIIDMassPhaseEnsemble

open TruncatedGaussianMassLaw

variable {parameters : Parameters}
variable {Omega : Type*} [MeasurableSpace Omega]

/-- Restrict the infinite mass sequence to a finite periodic chain. -/
def restrictMass (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) : Lattice.Configuration N :=
  fun site ↦ ensemble.mass site.val sample

/-- Finite phase configurations on the periodic sites. -/
abbrev PhaseConfiguration (N : Nat) := Lattice.Site N → UnitAddCircle

/-- Restrict the infinite phase sequence to a finite periodic chain. -/
def restrictPhase (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) : PhaseConfiguration N :=
  fun site ↦ ensemble.phase site.val sample

theorem measurable_restrictMass
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] : Measurable (ensemble.restrictMass (N := N)) := by
  exact measurable_pi_lambda _ fun site ↦ ensemble.mass_measurable site.val

theorem measurable_restrictPhase
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] : Measurable (ensemble.restrictPhase (N := N)) := by
  exact measurable_pi_lambda _ fun site ↦ ensemble.phase_measurable site.val

/-- Every finite restricted mass coordinate keeps the selected Gaussian law. -/
theorem restrictMass_hasLaw
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (site : Lattice.Site N) :
    HasLaw (fun sample ↦ ensemble.restrictMass sample site)
      (coordinateLaw parameters) ensemble.probability := by
  simpa [restrictMass] using ensemble.mass_hasLaw site.val

/-- Every finite restricted phase coordinate keeps Haar law. -/
theorem restrictPhase_hasLaw
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (site : Lattice.Site N) :
    HasLaw (fun sample ↦ ensemble.restrictPhase sample site)
      RandomEnsemble.phaseCoordinateLaw ensemble.probability := by
  simpa [restrictPhase] using ensemble.phase_hasLaw site.val

/-- Finite restricted mass coordinates remain mutually independent. -/
theorem restrictMass_iIndep
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] :
    iIndepFun (fun (site : Lattice.Site N) sample ↦
      ensemble.restrictMass sample site) ensemble.probability := by
  simpa [restrictMass] using
    ensemble.mass_iIndep.precomp (ZMod.val_injective N)

/-- Finite restricted phase coordinates remain mutually independent. -/
theorem restrictPhase_iIndep
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] :
    iIndepFun (fun (site : Lattice.Site N) sample ↦
      ensemble.restrictPhase sample site) ensemble.probability := by
  simpa [restrictPhase] using
    ensemble.phase_iIndep.precomp (ZMod.val_injective N)

/-- Finite mass and phase restrictions remain independent as blocks. -/
theorem restrictMass_indep_restrictPhase
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] :
    IndepFun (ensemble.restrictMass (N := N))
      (ensemble.restrictPhase (N := N)) ensemble.probability := by
  have hMass : Measurable
      (fun mass : Nat → Real ↦ fun site : Lattice.Site N ↦ mass site.val) :=
    measurable_pi_lambda _ fun site ↦ measurable_pi_apply site.val
  have hPhase : Measurable
      (fun phase : Nat → UnitAddCircle ↦
        fun site : Lattice.Site N ↦ phase site.val) :=
    measurable_pi_lambda _ fun site ↦ measurable_pi_apply site.val
  have hindep := ensemble.mass_phase_indep.comp hMass hPhase
  change IndepFun
    (fun sample : Omega ↦
      fun site : Lattice.Site N ↦ ensemble.mass site.val sample)
    (fun sample : Omega ↦
      fun site : Lattice.Site N ↦ ensemble.phase site.val sample)
    ensemble.probability
  simpa [Function.comp_def] using hindep

/-- The finite restriction is a total positive-mass configuration. -/
def restrictPositiveMass
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) : Lattice.PositiveMassConfig N where
  mass := ensemble.restrictMass sample
  mass_pos := fun site ↦ RandomEnsemble.massLower_pos.trans_le
    (ensemble.mass_mem_support site.val sample).1

@[simp] theorem restrictPositiveMass_mass
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) (site : Lattice.Site N) :
    (ensemble.restrictPositiveMass sample).mass site =
      ensemble.mass site.val sample := by
  rfl

end GaussianIIDMassPhaseEnsemble

end

end ArchonPhysics
