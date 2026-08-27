import ArchonPhysics.MassDependentHarmonicHaarPhasePropagation

/-!
# Consumer: five-site mass-dependent free harmonic Haar propagation

This target uses the canonical truncated-Gaussian mass/Haar-phase ensemble.
The phase advance is computed from each sample's own measurable ordered
harmonic frequencies.  It checks the fiberwise skew-product invariance, the
evolved product Haar law, and independence from the finite mass block.

No nonlinear FPUT or Lennard--Jones random-phase propagation is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory
open ArchonPhysics
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.MassDependentHarmonicHaarPhasePropagation
open ArchonPhysics.MassDependentHarmonicHaarPhasePropagation.GaussianIIDMassPhaseEnsemble

noncomputable section

namespace FiveSiteMassDependentHaar

def parameters : TruncatedGaussianMassLaw.Parameters where
  mean := 1
  variance := 1 / 100
  variance_ne_zero := by norm_num

abbrev SampleSpace := TruncatedGaussianMassPhaseEnsemble.SampleSpace

def ensemble : GaussianIIDMassPhaseEnsemble parameters SampleSpace :=
  canonicalGaussianIIDMassPhaseEnsemble parameters

def observationTime : Real := 7 / 3

abbrev massAdvance : MassSequence -> Lattice.Site 5 -> UnitAddCircle :=
  orderedHarmonicPhaseAdvance observationTime

abbrev evolvedPhase : SampleSpace -> Lattice.Site 5 -> UnitAddCircle :=
  orderedMassDependentFreeRestrictedPhase ensemble observationTime

/-- Acceptance contract for genuinely mass-dependent free harmonic phase
translation on five sites. -/
theorem problem_mass_dependent_harmonic_haar_phase_propagation :
    MeasurePreserving (massDependentPhaseSkew massAdvance)
        ((TruncatedGaussianIIDMassSequence.probability parameters).prod
          (finitePhaseHaarLaw (Lattice.Site 5)))
        ((TruncatedGaussianIIDMassSequence.probability parameters).prod
          (finitePhaseHaarLaw (Lattice.Site 5))) ∧
      Measurable massAdvance ∧
      HasLaw evolvedPhase (finitePhaseHaarLaw (Lattice.Site 5))
        ensemble.probability ∧
      IndepFun (ensemble.restrictMass (N := 5)) evolvedPhase
        ensemble.probability ∧
      (forall sample mode,
        evolvedPhase sample mode =
          massAdvance (ensembleMassSequence ensemble sample) mode +
            ensemble.restrictPhase sample mode) := by
  refine ⟨measurePreserving_massDependentPhaseSkew
      (TruncatedGaussianIIDMassSequence.probability parameters)
      massAdvance (measurable_orderedHarmonicPhaseAdvance observationTime),
    measurable_orderedHarmonicPhaseAdvance observationTime, ?_, ?_, ?_⟩
  · exact orderedMassDependentFreeRestrictedPhase_hasLaw ensemble
      observationTime
  · exact restrictMass_indep_orderedMassDependentFreeRestrictedPhase
      ensemble observationTime
  · intro sample mode
    rfl

#print axioms problem_mass_dependent_harmonic_haar_phase_propagation
#print axioms measurePreserving_massDependentPhaseSkew
#print axioms restrictMass_indep_orderedMassDependentFreeRestrictedPhase

end FiveSiteMassDependentHaar

end

end ArchonPhysicsConsumers.Thermalization
