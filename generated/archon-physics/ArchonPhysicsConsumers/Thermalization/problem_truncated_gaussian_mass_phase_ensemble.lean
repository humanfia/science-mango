import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble

/-!
# Acceptance target: a five-site Gaussian-mass/Haar-phase chain

This consumer instantiates the canonical product ensemble at mean one and
variance `1/100`, restricts it to five periodic sites, and checks marginal
laws, independence, measurability, and the pointwise-positive mass adapter.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory
open ArchonPhysics

noncomputable section

namespace GaussianMassPhase

/-- Concrete nondegenerate Gaussian parameters. -/
def parameters : TruncatedGaussianMassLaw.Parameters where
  mean := 1
  variance := 1 / 100
  variance_ne_zero := by norm_num

abbrev SampleSpace := TruncatedGaussianMassPhaseEnsemble.SampleSpace

def ensemble : GaussianIIDMassPhaseEnsemble parameters SampleSpace :=
  canonicalGaussianIIDMassPhaseEnsemble parameters

def fiveSiteMass (sample : SampleSpace) : Lattice.Configuration 5 :=
  ensemble.restrictMass (N := 5) sample

def fiveSitePhase (sample : SampleSpace) :
    GaussianIIDMassPhaseEnsemble.PhaseConfiguration 5 :=
  ensemble.restrictPhase (N := 5) sample

def fiveSitePositiveMass (sample : SampleSpace) : Lattice.PositiveMassConfig 5 :=
  ensemble.restrictPositiveMass (N := 5) sample

/-- Executable acceptance statement for the Gaussian chain adapter. -/
theorem problem_truncated_gaussian_mass_phase_ensemble :
    Measurable fiveSiteMass ∧
      (∀ site : Lattice.Site 5,
        HasLaw (fun sample ↦ fiveSiteMass sample site)
          (TruncatedGaussianMassLaw.coordinateLaw parameters)
          ensemble.probability) ∧
      iIndepFun (fun (site : Lattice.Site 5) sample ↦
        fiveSiteMass sample site) ensemble.probability ∧
      (∀ site : Lattice.Site 5,
        HasLaw (fun sample ↦ fiveSitePhase sample site)
          RandomEnsemble.phaseCoordinateLaw ensemble.probability) ∧
      iIndepFun (fun (site : Lattice.Site 5) sample ↦
        fiveSitePhase sample site) ensemble.probability ∧
      IndepFun fiveSiteMass fiveSitePhase ensemble.probability ∧
      (∀ sample site, 0 < (fiveSitePositiveMass sample).mass site) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ensemble.measurable_restrictMass (N := 5)
  · intro site
    simpa [fiveSiteMass] using ensemble.restrictMass_hasLaw (N := 5) site
  · simpa [fiveSiteMass] using ensemble.restrictMass_iIndep (N := 5)
  · intro site
    simpa [fiveSitePhase] using ensemble.restrictPhase_hasLaw (N := 5) site
  · simpa [fiveSitePhase] using ensemble.restrictPhase_iIndep (N := 5)
  · change IndepFun (ensemble.restrictMass (N := 5))
      (ensemble.restrictPhase (N := 5)) ensemble.probability
    exact ensemble.restrictMass_indep_restrictPhase (N := 5)
  · intro sample site
    exact (fiveSitePositiveMass sample).mass_pos site

end GaussianMassPhase

end

end ArchonPhysicsConsumers.Thermalization
