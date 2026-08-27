import ArchonPhysics.FiniteHarmonicHaarPhasePropagation

/-!
# Consumer: five-site free harmonic propagation of iid Haar phases

This acceptance target specializes the first-principles translation theorem to
the canonical truncated-Gaussian mass/Haar-phase ensemble.  The five harmonic
frequencies are fixed constants, so the evolved phase block remains product
Haar and remains independent of the random mass block.

This is only a free/harmonic propagation check.  It is not a nonlinear random
phase approximation statement.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory
open ArchonPhysics
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation.GaussianIIDMassPhaseEnsemble

noncomputable section

namespace FiveSiteHarmonicHaar

/-- Nondegenerate positive truncated-Gaussian mass parameters. -/
def parameters : TruncatedGaussianMassLaw.Parameters where
  mean := 1
  variance := 1 / 100
  variance_ne_zero := by norm_num

abbrev SampleSpace := TruncatedGaussianMassPhaseEnsemble.SampleSpace

def ensemble : GaussianIIDMassPhaseEnsemble parameters SampleSpace :=
  canonicalGaussianIIDMassPhaseEnsemble parameters

/-- A deterministic five-mode angular-frequency vector. -/
def frequency : Lattice.Site 5 -> Real := fun _ => 5 / 4

/-- A fixed observation time. -/
def observationTime : Real := 7 / 3

abbrev evolvedPhase (sample : SampleSpace) :
    GaussianIIDMassPhaseEnsemble.PhaseConfiguration 5 :=
  freeHarmonicRestrictedPhase ensemble frequency observationTime sample

/-- Kernel-checked finite free propagation contract: full product law,
coordinate Haar marginals, coordinate independence, and mass/phase block
independence are all retained. -/
theorem problem_finite_harmonic_haar_phase_propagation :
    MeasurePreserving
        (freeHarmonicPhaseEvolution frequency observationTime)
        (finitePhaseHaarLaw (Lattice.Site 5))
        (finitePhaseHaarLaw (Lattice.Site 5)) ∧
      HasLaw evolvedPhase (finitePhaseHaarLaw (Lattice.Site 5))
        ensemble.probability ∧
      (forall mode : Lattice.Site 5,
        HasLaw (fun sample => evolvedPhase sample mode)
          RandomEnsemble.phaseCoordinateLaw ensemble.probability) ∧
      iIndepFun (fun (mode : Lattice.Site 5) sample =>
        evolvedPhase sample mode) ensemble.probability ∧
      IndepFun (ensemble.restrictMass (N := 5)) evolvedPhase
        ensemble.probability := by
  refine ⟨measurePreserving_freeHarmonicPhaseEvolution frequency
      observationTime, ?_, ?_, ?_, ?_⟩
  · simpa [evolvedPhase] using
      (freeHarmonicRestrictedPhase_hasLaw ensemble frequency observationTime)
  · intro mode
    simpa [evolvedPhase] using
      (freeHarmonicRestrictedPhase_coordinate_hasLaw ensemble frequency
        observationTime mode)
  · simpa [evolvedPhase] using
      (freeHarmonicRestrictedPhase_iIndep ensemble frequency observationTime)
  · simpa [evolvedPhase] using
      (restrictMass_indep_freeHarmonicRestrictedPhase ensemble frequency
        observationTime)

#print axioms problem_finite_harmonic_haar_phase_propagation
#print axioms measurePreserving_freeHarmonicPhaseEvolution
#print axioms restrictMass_indep_freeHarmonicRestrictedPhase

end FiveSiteHarmonicHaar

end

end ArchonPhysicsConsumers.Thermalization
