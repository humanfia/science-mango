import Mathlib
import ArchonPhysics.Lattice

/-!
# An iid random-mass and independent-phase ensemble

This module constructs one infinite product probability space carrying iid
mass coordinates and iid Haar-uniform phase coordinates.  The two coordinate
blocks are independent.  Masses have the fixed compact support `[4 / 5, 6 / 5]`
and are therefore strictly positive.

The raw product coordinate already lies in this interval almost surely.  A
measurable clipping map changes it only on a null set and gives a pointwise
positive representative, which can be restricted to a
`Lattice.PositiveMassConfig N` for every nonempty finite periodic chain.

This is probability-space infrastructure only.  It contains no Hamiltonian
evolution, localization, kinetic-limit, or thermalization assertion.
-/

namespace ArchonPhysics

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace RandomEnsemble

/-- The fixed lower endpoint of the random-mass support. -/
def massLower : Real := 4 / 5

/-- The fixed upper endpoint of the random-mass support. -/
def massUpper : Real := 6 / 5

/-- The compact support of one mass coordinate. -/
def massSupport : Set Real := Set.Icc massLower massUpper

theorem massLower_pos : 0 < massLower := by
  norm_num [massLower]

theorem massLower_le_massUpper : massLower ≤ massUpper := by
  norm_num [massLower, massUpper]

/-- The common mass law: normalized Lebesgue measure on `[4 / 5, 6 / 5]`. -/
def massCoordinateLaw : Measure Real :=
  ProbabilityTheory.cond volume massSupport

noncomputable instance massCoordinateLaw.instIsProbabilityMeasure :
    IsProbabilityMeasure massCoordinateLaw := by
  unfold massCoordinateLaw
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · simp [massSupport, massLower, massUpper, Real.volume_Icc]
    norm_num
  · simp [massSupport, massLower, massUpper, Real.volume_Icc]

/-- The common phase law: normalized Haar measure on the unit additive circle. -/
def phaseCoordinateLaw : Measure UnitAddCircle := volume

noncomputable instance phaseCoordinateLaw.instIsProbabilityMeasure :
    IsProbabilityMeasure phaseCoordinateLaw :=
  ⟨by
    unfold phaseCoordinateLaw
    exact UnitAddCircle.measure_univ⟩

/-- A raw mass coordinate has the prescribed support almost surely. -/
theorem massCoordinate_mem_support_ae :
    ∀ᵐ m ∂massCoordinateLaw, m ∈ massSupport := by
  simpa [massCoordinateLaw, massSupport] using
    (ProbabilityTheory.ae_cond_mem (measurableSet_Icc :
      MeasurableSet (Set.Icc massLower massUpper)))

/-- Clip arbitrary real input to the prescribed mass interval. -/
def clippedMass (x : Real) : Real :=
  max massLower (min massUpper x)

theorem clippedMass_mem_support (x : Real) : clippedMass x ∈ massSupport := by
  constructor
  · exact le_max_left _ _
  · exact max_le massLower_le_massUpper (min_le_left _ _)

theorem clippedMass_pos (x : Real) : 0 < clippedMass x :=
  massLower_pos.trans_le (clippedMass_mem_support x).1

theorem clippedMass_eq_self {x : Real} (hx : x ∈ massSupport) : clippedMass x = x := by
  simp [clippedMass, hx.1, hx.2]

theorem measurable_clippedMass : Measurable clippedMass := by
  unfold clippedMass
  fun_prop

/-- Infinite raw mass sequences. -/
abbrev RawMassSequence := Nat → Real

/-- Infinite phase sequences. -/
abbrev PhaseSequence := Nat → UnitAddCircle

/-- The canonical sample space carries a mass block and a phase block. -/
abbrev SampleSpace := RawMassSequence × PhaseSequence

/-- Infinite product law of the iid raw mass coordinates. -/
def massSequenceLaw : Measure RawMassSequence :=
  Measure.infinitePi (fun _ : Nat ↦ massCoordinateLaw)

/-- Infinite product law of the iid Haar phase coordinates. -/
def phaseSequenceLaw : Measure PhaseSequence :=
  Measure.infinitePi (fun _ : Nat ↦ phaseCoordinateLaw)

noncomputable instance massSequenceLaw.instIsProbabilityMeasure :
    IsProbabilityMeasure massSequenceLaw := by
  unfold massSequenceLaw
  infer_instance

noncomputable instance phaseSequenceLaw.instIsProbabilityMeasure :
    IsProbabilityMeasure phaseSequenceLaw := by
  unfold phaseSequenceLaw
  infer_instance

/-- The product law making the full mass block independent of the phase block. -/
def canonicalLaw : Measure SampleSpace :=
  massSequenceLaw.prod phaseSequenceLaw

noncomputable instance canonicalLaw.instIsProbabilityMeasure :
    IsProbabilityMeasure canonicalLaw := by
  unfold canonicalLaw
  infer_instance

/-- The unmodified mass coordinate on the canonical product space. -/
def rawMassAt (n : Nat) : SampleSpace → Real :=
  fun ω ↦ ω.1 n

/-- The pointwise positive representative of the mass coordinate. -/
def massAt (n : Nat) : SampleSpace → Real :=
  fun ω ↦ clippedMass (rawMassAt n ω)

/-- The phase coordinate on the canonical product space. -/
def phaseAt (n : Nat) : SampleSpace → UnitAddCircle :=
  fun ω ↦ ω.2 n

theorem measurable_rawMassAt (n : Nat) : Measurable (rawMassAt n) := by
  unfold rawMassAt
  fun_prop

theorem measurable_massAt (n : Nat) : Measurable (massAt n) := by
  unfold massAt
  exact measurable_clippedMass.comp (measurable_rawMassAt n)

theorem measurable_phaseAt (n : Nat) : Measurable (phaseAt n) := by
  unfold phaseAt
  fun_prop

/-- The whole raw mass block has its infinite product law. -/
theorem rawMassSequence_hasLaw :
    HasLaw (fun ω : SampleSpace ↦ ω.1) massSequenceLaw canonicalLaw := by
  exact (MeasureTheory.measurePreserving_fst
    (μ := massSequenceLaw) (ν := phaseSequenceLaw)).hasLaw

/-- The whole phase block has its infinite product law. -/
theorem phaseSequence_hasLaw :
    HasLaw (fun ω : SampleSpace ↦ ω.2) phaseSequenceLaw canonicalLaw := by
  exact (MeasureTheory.measurePreserving_snd
    (μ := massSequenceLaw) (ν := phaseSequenceLaw)).hasLaw

/-- Every raw mass coordinate has the common compactly supported law. -/
theorem rawMassAt_hasLaw (n : Nat) :
    HasLaw (rawMassAt n) massCoordinateLaw canonicalLaw := by
  have hEval : HasLaw (Function.eval n) massCoordinateLaw massSequenceLaw :=
    (measurePreserving_eval_infinitePi
      (fun _ : Nat ↦ massCoordinateLaw) n).hasLaw
  change HasLaw (Function.eval n ∘ fun ω : SampleSpace ↦ ω.1) massCoordinateLaw canonicalLaw
  exact hEval.comp rawMassSequence_hasLaw

/-- Every phase coordinate has normalized Haar law. -/
theorem phaseAt_hasLaw (n : Nat) :
    HasLaw (phaseAt n) phaseCoordinateLaw canonicalLaw := by
  have hEval : HasLaw (Function.eval n) phaseCoordinateLaw phaseSequenceLaw :=
    (measurePreserving_eval_infinitePi
      (fun _ : Nat ↦ phaseCoordinateLaw) n).hasLaw
  change HasLaw (Function.eval n ∘ fun ω : SampleSpace ↦ ω.2) phaseCoordinateLaw canonicalLaw
  exact hEval.comp phaseSequence_hasLaw

/-- The raw mass coordinate is in the support almost surely. -/
theorem rawMassAt_mem_support_ae (n : Nat) :
    ∀ᵐ ω ∂canonicalLaw, rawMassAt n ω ∈ massSupport := by
  apply ((rawMassAt_hasLaw n).ae_iff ?_).2
  · exact massCoordinate_mem_support_ae
  · apply MeasurableSet.mem
    unfold massSupport
    exact measurableSet_Icc

/-- Clipping changes a raw mass coordinate only on a null set. -/
theorem massAt_eq_rawMassAt_ae (n : Nat) :
    massAt n =ᵐ[canonicalLaw] rawMassAt n := by
  filter_upwards [rawMassAt_mem_support_ae n] with ω hω
  exact clippedMass_eq_self hω

/-- Every pointwise positive mass representative still has the common mass law. -/
theorem massAt_hasLaw (n : Nat) :
    HasLaw (massAt n) massCoordinateLaw canonicalLaw :=
  (rawMassAt_hasLaw n).congr (massAt_eq_rawMassAt_ae n)

/-- The raw mass coordinates are mutually independent. -/
theorem rawMassCoordinates_iIndep :
    iIndepFun rawMassAt canonicalLaw := by
  have hm : AEMeasurable (fun ω : SampleSpace ↦ fun n ↦ rawMassAt n ω) canonicalLaw :=
    (measurable_pi_lambda _ measurable_rawMassAt).aemeasurable
  apply (ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi
    (fun n ↦ rawMassAt_hasLaw n) hm).2
  simpa [rawMassAt, massSequenceLaw] using rawMassSequence_hasLaw

/-- The pointwise positive mass representatives remain mutually independent. -/
theorem massCoordinates_iIndep :
    iIndepFun massAt canonicalLaw := by
  have h := rawMassCoordinates_iIndep.comp
    (fun _ : Nat ↦ clippedMass) (fun _ ↦ measurable_clippedMass)
  change iIndepFun (fun n ↦ clippedMass ∘ rawMassAt n) canonicalLaw
  exact h

/-- The Haar phase coordinates are mutually independent. -/
theorem phaseCoordinates_iIndep :
    iIndepFun phaseAt canonicalLaw := by
  have hm : AEMeasurable (fun ω : SampleSpace ↦ fun n ↦ phaseAt n ω) canonicalLaw :=
    (measurable_pi_lambda _ measurable_phaseAt).aemeasurable
  apply (ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi
    (fun n ↦ phaseAt_hasLaw n) hm).2
  simpa [phaseAt, phaseSequenceLaw] using phaseSequence_hasLaw

/-- The full pointwise positive mass sequence. -/
def massSequence (omega : SampleSpace) : Nat → Real :=
  fun n ↦ massAt n omega

/-- The full phase sequence. -/
def phaseSequence (omega : SampleSpace) : Nat → UnitAddCircle :=
  fun n ↦ phaseAt n omega

/-- The entire mass sequence is independent of the entire phase sequence. -/
theorem massSequence_indep_phaseSequence :
    IndepFun massSequence phaseSequence canonicalLaw := by
  have hClip : Measurable (fun x : RawMassSequence ↦ fun n ↦ clippedMass (x n)) := by
    exact measurable_pi_lambda _ fun n ↦
      measurable_clippedMass.comp (measurable_pi_apply n)
  have h := ProbabilityTheory.indepFun_prod
    (μ := massSequenceLaw) (ν := phaseSequenceLaw)
    (X := fun x : RawMassSequence ↦ fun n ↦ clippedMass (x n))
    (Y := id) hClip measurable_id
  change IndepFun (fun ω : SampleSpace ↦ fun n ↦ clippedMass (ω.1 n))
    (fun ω : SampleSpace ↦ ω.2) (massSequenceLaw.prod phaseSequenceLaw)
  exact h

theorem massAt_mem_support (n : Nat) (omega : SampleSpace) :
    massAt n omega ∈ massSupport :=
  clippedMass_mem_support _

theorem massAt_pos (n : Nat) (omega : SampleSpace) : 0 < massAt n omega :=
  clippedMass_pos _

end RandomEnsemble

/--
Verified interface for an infinite iid positive-mass ensemble with an
independent iid phase block on a supplied probability space.
-/
structure IIDMassPhaseEnsemble (Omega : Type*) [MeasurableSpace Omega] where
  /-- The probability measure on the supplied sample space. -/
  probability : Measure Omega
  /-- The positive mass coordinates. -/
  mass : Nat → Omega → Real
  /-- The phase coordinates. -/
  phase : Nat → Omega → UnitAddCircle
  /-- The supplied measure has total mass one. -/
  probability_univ : probability Set.univ = 1
  /-- Every mass coordinate is measurable. -/
  mass_measurable : ∀ n, Measurable (mass n)
  /-- Every phase coordinate is measurable. -/
  phase_measurable : ∀ n, Measurable (phase n)
  /-- All mass coordinates have the fixed common law. -/
  mass_hasLaw : ∀ n,
    HasLaw (mass n) RandomEnsemble.massCoordinateLaw probability
  /-- All phase coordinates have normalized Haar law. -/
  phase_hasLaw : ∀ n,
    HasLaw (phase n) RandomEnsemble.phaseCoordinateLaw probability
  /-- The mass coordinates are mutually independent. -/
  mass_iIndep : iIndepFun mass probability
  /-- The phase coordinates are mutually independent. -/
  phase_iIndep : iIndepFun phase probability
  /-- The full mass block and full phase block are independent. -/
  mass_phase_indep :
    IndepFun (fun omega n ↦ mass n omega) (fun omega n ↦ phase n omega) probability
  /-- The chosen representatives lie pointwise in the fixed positive support. -/
  mass_mem_support : ∀ n omega, mass n omega ∈ RandomEnsemble.massSupport

/-- The canonical infinite-product construction of the verified interface. -/
def canonicalIIDMassPhaseEnsemble :
    IIDMassPhaseEnsemble RandomEnsemble.SampleSpace where
  probability := RandomEnsemble.canonicalLaw
  mass := RandomEnsemble.massAt
  phase := RandomEnsemble.phaseAt
  probability_univ := by simp
  mass_measurable := RandomEnsemble.measurable_massAt
  phase_measurable := RandomEnsemble.measurable_phaseAt
  mass_hasLaw := RandomEnsemble.massAt_hasLaw
  phase_hasLaw := RandomEnsemble.phaseAt_hasLaw
  mass_iIndep := RandomEnsemble.massCoordinates_iIndep
  phase_iIndep := RandomEnsemble.phaseCoordinates_iIndep
  mass_phase_indep := RandomEnsemble.massSequence_indep_phaseSequence
  mass_mem_support := RandomEnsemble.massAt_mem_support

namespace IIDMassPhaseEnsemble

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Restrict an infinite mass sequence to the sites of a finite periodic chain. -/
def restrictMass (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (omega : Omega) : Lattice.Configuration N :=
  fun i ↦ ensemble.mass i.val omega

/-- Finite phase configurations on the periodic sites. -/
abbrev PhaseConfiguration (N : Nat) := Lattice.Site N → UnitAddCircle

/-- Restrict an infinite phase sequence to the sites of a finite periodic chain. -/
def restrictPhase (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (omega : Omega) : PhaseConfiguration N :=
  fun i ↦ ensemble.phase i.val omega

theorem measurable_restrictMass (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] : Measurable (ensemble.restrictMass (N := N)) := by
  exact measurable_pi_lambda _ fun i ↦ ensemble.mass_measurable i.val

theorem measurable_restrictPhase (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] : Measurable (ensemble.restrictPhase (N := N)) := by
  exact measurable_pi_lambda _ fun i ↦ ensemble.phase_measurable i.val

/-- Every coordinate of the finite mass restriction keeps the common law. -/
theorem restrictMass_hasLaw (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (i : Lattice.Site N) :
    HasLaw (fun omega ↦ ensemble.restrictMass omega i)
      RandomEnsemble.massCoordinateLaw ensemble.probability := by
  simpa [restrictMass] using ensemble.mass_hasLaw i.val

/-- Every coordinate of the finite phase restriction keeps Haar law. -/
theorem restrictPhase_hasLaw (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (i : Lattice.Site N) :
    HasLaw (fun omega ↦ ensemble.restrictPhase omega i)
      RandomEnsemble.phaseCoordinateLaw ensemble.probability := by
  simpa [restrictPhase] using ensemble.phase_hasLaw i.val

/-- The finite mass coordinates remain mutually independent. -/
theorem restrictMass_iIndep (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] :
    iIndepFun (fun (i : Lattice.Site N) (omega : Omega) ↦
      ensemble.restrictMass omega i) ensemble.probability := by
  simpa [restrictMass] using
    ensemble.mass_iIndep.precomp (ZMod.val_injective N)

/-- The finite phase coordinates remain mutually independent. -/
theorem restrictPhase_iIndep (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] :
    iIndepFun (fun (i : Lattice.Site N) (omega : Omega) ↦
      ensemble.restrictPhase omega i) ensemble.probability := by
  simpa [restrictPhase] using
    ensemble.phase_iIndep.precomp (ZMod.val_injective N)

/-- The finite mass and phase restrictions remain independent as blocks. -/
theorem restrictMass_indep_restrictPhase (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] :
    IndepFun (ensemble.restrictMass (N := N)) (ensemble.restrictPhase (N := N))
      ensemble.probability := by
  have hMass : Measurable
      (fun x : Nat → Real ↦ fun i : Lattice.Site N ↦ x i.val) :=
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.val
  have hPhase : Measurable
      (fun x : Nat → UnitAddCircle ↦ fun i : Lattice.Site N ↦ x i.val) :=
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.val
  have h := ensemble.mass_phase_indep.comp hMass hPhase
  change IndepFun
    (fun omega : Omega ↦ fun i : Lattice.Site N ↦ ensemble.mass i.val omega)
    (fun omega : Omega ↦ fun i : Lattice.Site N ↦ ensemble.phase i.val omega)
    ensemble.probability
  simpa [Function.comp_def] using h

/-- The finite restriction gives a total positive-mass configuration. -/
def restrictPositiveMass (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) : Lattice.PositiveMassConfig N where
  mass := ensemble.restrictMass omega
  mass_pos := fun i ↦
    RandomEnsemble.massLower_pos.trans_le (ensemble.mass_mem_support i.val omega).1

@[simp] theorem restrictPositiveMass_mass (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (i : Lattice.Site N) :
    (ensemble.restrictPositiveMass omega).mass i = ensemble.mass i.val omega := by
  rfl

end IIDMassPhaseEnsemble

end

end ArchonPhysics
