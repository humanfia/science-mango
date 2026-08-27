import ArchonPhysics.FiniteEnsemblePhaseMoments
import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble
import Mathlib.MeasureTheory.Group.Measure

/-!
# Finite harmonic propagation of Haar phases

For a fixed finite vector of angular frequencies, free harmonic evolution only
adds the deterministic phase advance `omega * t / (2 * pi)` on each unit
circle.  Translation invariance of Haar measure therefore gives an exact
first-principles propagation statement: the finite product Haar law is
unchanged, and coordinate independence is retained.

The Gaussian-mass adapter below deliberately keeps the frequency vector
deterministic.  It may be obtained after fixing a mass realization, but it may
not depend on the random sample in the theorem.  Consequently the adapter also
preserves independence between the finite mass block and the evolved phase
block.

This module covers harmonic/free evolution only.  It does **not** prove that
random phases propagate through nonlinear FPUT or Lennard--Jones dynamics, and
it is not a nonlinear RPA certificate.
-/

namespace ArchonPhysics.FiniteHarmonicHaarPhasePropagation

open MeasureTheory ProbabilityTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.RandomPhaseMoments

noncomputable section

variable {d : Type*}

/-- Phase advance on the unit additive circle for angular frequency `omega`.
The division by `2 * pi` converts radians to turns. -/
def harmonicPhaseAdvance (frequency : d -> Real) (time : Real) :
    UnitAddTorus d :=
  fun mode =>
    ((frequency mode * time / (2 * Real.pi) : Real) : UnitAddCircle)

/-- Free harmonic evolution in phase coordinates at fixed frequencies. -/
def freeHarmonicPhaseEvolution (frequency : d -> Real) (time : Real) :
    UnitAddTorus d -> UnitAddTorus d :=
  fun phase => harmonicPhaseAdvance frequency time + phase

@[simp] theorem freeHarmonicPhaseEvolution_apply
    (frequency : d -> Real) (time : Real) (phase : UnitAddTorus d)
    (mode : d) :
    freeHarmonicPhaseEvolution frequency time phase mode =
      harmonicPhaseAdvance frequency time mode + phase mode := rfl

/- These are exactly the local normalized-Haar instances used in
`RandomPhaseMoments.finitePhaseHaarLaw`. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Deterministic free harmonic phase translation preserves the normalized
finite product Haar law exactly. -/
theorem measurePreserving_freeHarmonicPhaseEvolution
    [Fintype d]
    (frequency : d -> Real) (time : Real) :
    MeasurePreserving (freeHarmonicPhaseEvolution frequency time)
      (finitePhaseHaarLaw d) (finitePhaseHaarLaw d) := by
  unfold freeHarmonicPhaseEvolution finitePhaseHaarLaw
  exact measurePreserving_add_left volume
    (harmonicPhaseAdvance frequency time)

/-- Equivalent push-forward formulation of finite product Haar invariance. -/
theorem map_freeHarmonicPhaseEvolution_finitePhaseHaarLaw
    [Fintype d]
    (frequency : d -> Real) (time : Real) :
    Measure.map (freeHarmonicPhaseEvolution frequency time)
        (finitePhaseHaarLaw d) =
      finitePhaseHaarLaw d :=
  (measurePreserving_freeHarmonicPhaseEvolution frequency time).map_eq

/-- A random finite phase block with product Haar law keeps that full joint law
after fixed-frequency free evolution. -/
theorem freeHarmonicPhaseEvolution_hasLaw
    [Fintype d]
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {phase : Omega -> UnitAddTorus d}
    (frequency : d -> Real) (time : Real)
    (hphase : HasLaw phase (finitePhaseHaarLaw d) P) :
    HasLaw (fun sample =>
      freeHarmonicPhaseEvolution frequency time (phase sample))
      (finitePhaseHaarLaw d) P := by
  simpa [Function.comp_def] using
    (measurePreserving_freeHarmonicPhaseEvolution frequency time).hasLaw.comp
      hphase

/-- Coordinate presentation of fixed-frequency free phase evolution. -/
def freeHarmonicCoordinatePhase
    {Omega : Type*} (frequency : d -> Real) (time : Real)
    (phase : d -> Omega -> UnitAddCircle) :
    d -> Omega -> UnitAddCircle :=
  fun mode sample =>
    harmonicPhaseAdvance frequency time mode + phase mode sample

/-- Independent phase coordinates remain independent under their separate
deterministic harmonic translations. -/
theorem freeHarmonicCoordinatePhase_iIndep
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (frequency : d -> Real) (time : Real)
    (phase : d -> Omega -> UnitAddCircle)
    (hphase : iIndepFun phase P) :
    iIndepFun (freeHarmonicCoordinatePhase frequency time phase) P := by
  change iIndepFun (fun mode sample =>
    harmonicPhaseAdvance frequency time mode + phase mode sample) P
  have htranslated := hphase.comp
    (fun mode theta => harmonicPhaseAdvance frequency time mode + theta)
    (fun mode => measurable_const_add
      (harmonicPhaseAdvance frequency time mode))
  simpa [Function.comp_def] using htranslated

/-- Every translated coordinate keeps the same normalized Haar marginal.
Together with `freeHarmonicCoordinatePhase_iIndep`, this is the iid
preservation statement. -/
theorem freeHarmonicCoordinatePhase_hasLaw
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (frequency : d -> Real) (time : Real)
    (phase : d -> Omega -> UnitAddCircle)
    (hphase : forall mode, HasLaw (phase mode)
      RandomEnsemble.phaseCoordinateLaw P)
    (mode : d) :
    HasLaw (freeHarmonicCoordinatePhase frequency time phase mode)
      RandomEnsemble.phaseCoordinateLaw P := by
  change HasLaw (fun sample =>
    harmonicPhaseAdvance frequency time mode + phase mode sample)
    RandomEnsemble.phaseCoordinateLaw P
  rw [ArchonPhysics.CanonicalRandomPhaseMoments.phaseCoordinateLaw_eq_haar]
    at hphase ⊢
  have htranslate : HasLaw
      (fun theta : UnitAddCircle =>
        harmonicPhaseAdvance frequency time mode + theta)
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
    (measurePreserving_add_left AddCircle.haarAddCircle
      (harmonicPhaseAdvance frequency time mode)).hasLaw
  simpa [Function.comp_def] using
    htranslate.comp (hphase mode)

namespace GaussianIIDMassPhaseEnsemble

open ArchonPhysics.TruncatedGaussianMassLaw

variable {parameters : Parameters}
variable {Omega : Type*} [MeasurableSpace Omega]

/-- Fixed-frequency free evolution of the finite Gaussian-ensemble phase
restriction.  The frequency vector is deterministic, not sample-dependent. -/
def freeHarmonicRestrictedPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N -> Real) (time : Real) (sample : Omega) :
    ArchonPhysics.GaussianIIDMassPhaseEnsemble.PhaseConfiguration N :=
  freeHarmonicPhaseEvolution frequency time
    (ensemble.restrictPhase sample)

/-- The finite restriction of the truncated-Gaussian/Haar ensemble has the
same normalized product Haar law used by the phase-moment API. -/
theorem restrictPhase_hasLaw_finitePhaseHaarLaw
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] :
    HasLaw (ensemble.restrictPhase (N := N))
      (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability := by
  have hJoint :
      HasLaw (ensemble.restrictPhase (N := N))
        (Measure.infinitePi
          (fun _ : Lattice.Site N => RandomEnsemble.phaseCoordinateLaw))
        ensemble.probability :=
    ensemble.restrictPhase_iIndep.hasLaw_infinitePi
      ensemble.restrictPhase_hasLaw
      ensemble.measurable_restrictPhase.aemeasurable
  rw [FiniteEnsemblePhaseMoments.finitePhaseProductLaw_eq_finitePhaseHaarLaw] at hJoint
  exact hJoint

/-- The complete finite evolved phase block still has product Haar law. -/
theorem freeHarmonicRestrictedPhase_hasLaw
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N -> Real) (time : Real) :
    HasLaw (freeHarmonicRestrictedPhase ensemble frequency time)
      (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability := by
  exact freeHarmonicPhaseEvolution_hasLaw frequency time
    (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble)

/-- Coordinate independence survives fixed-frequency free evolution. -/
theorem freeHarmonicRestrictedPhase_iIndep
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N -> Real) (time : Real) :
    iIndepFun (fun (mode : Lattice.Site N) sample =>
      freeHarmonicRestrictedPhase ensemble frequency time sample mode)
      ensemble.probability := by
  change iIndepFun
    (freeHarmonicCoordinatePhase frequency time
      (fun mode sample => ensemble.restrictPhase sample mode))
    ensemble.probability
  exact freeHarmonicCoordinatePhase_iIndep frequency time
    (fun mode sample => ensemble.restrictPhase sample mode)
    ensemble.restrictPhase_iIndep

/-- Each evolved coordinate retains the common normalized Haar marginal. -/
theorem freeHarmonicRestrictedPhase_coordinate_hasLaw
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N -> Real) (time : Real)
    (mode : Lattice.Site N) :
    HasLaw (fun sample =>
      freeHarmonicRestrictedPhase ensemble frequency time sample mode)
      RandomEnsemble.phaseCoordinateLaw ensemble.probability := by
  change HasLaw
    (freeHarmonicCoordinatePhase frequency time
      (fun site sample => ensemble.restrictPhase sample site) mode)
    RandomEnsemble.phaseCoordinateLaw ensemble.probability
  exact freeHarmonicCoordinatePhase_hasLaw frequency time
    (fun site sample => ensemble.restrictPhase sample site)
    ensemble.restrictPhase_hasLaw mode

/-- A deterministic phase translation is measurable on the finite torus. -/
theorem measurable_freeHarmonicPhaseEvolution
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N -> Real) (time : Real) :
    Measurable (freeHarmonicPhaseEvolution frequency time) :=
  measurable_const_add (harmonicPhaseAdvance frequency time)

/-- For a deterministic frequency vector, the random finite mass block stays
independent of the freely evolved phase block.  This does not cover a
sample-dependent frequency vector without an additional conditional-law
argument. -/
theorem restrictMass_indep_freeHarmonicRestrictedPhase
    (ensemble : ArchonPhysics.GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N -> Real) (time : Real) :
    IndepFun (ensemble.restrictMass (N := N))
      (freeHarmonicRestrictedPhase ensemble frequency time)
      ensemble.probability := by
  change IndepFun (ensemble.restrictMass (N := N))
    (fun sample => freeHarmonicPhaseEvolution frequency time
      (ensemble.restrictPhase sample)) ensemble.probability
  have hindep := ensemble.restrictMass_indep_restrictPhase.comp
    measurable_id (measurable_freeHarmonicPhaseEvolution frequency time)
  simpa [Function.comp_def] using hindep

end GaussianIIDMassPhaseEnsemble

end

end ArchonPhysics.FiniteHarmonicHaarPhasePropagation
