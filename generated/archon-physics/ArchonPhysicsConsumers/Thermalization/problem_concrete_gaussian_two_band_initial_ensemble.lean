import ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble

/-!
# Consumer: concrete five-site Gaussian two-band initial ensemble

This target fixes energy density `2/5` on five sites.  It checks the exact
conditioned-Gaussian mass marginal, compact positive support, extensive total
modal energy, nonnegativity, quantitative initial nonequilibrium, the
positive-frequency `E / omega` action identity, and product-Haar phase
preservation under the sample-dependent free harmonic frequencies.

No nonlinear random-phase or thermalization assertion is part of this
acceptance target.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory
open ArchonPhysics
open ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
open ArchonPhysics.MassDependentHarmonicHaarPhasePropagation
open ArchonPhysics.MassDependentHarmonicHaarPhasePropagation.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.RandomPhaseMoments
open scoped BigOperators

noncomputable section

namespace ConcreteGaussianTwoBand

def energyDensity : Real := 2 / 5

def observationTime : Real := 7 / 3

/-- Kernel-checked acceptance contract for the concrete default initial
ensemble and its free-harmonic random-phase propagation. -/
theorem problem_concrete_gaussian_two_band_initial_ensemble :
    (forall index : Nat,
      HasLaw (concreteEnsemble.mass index)
        (TruncatedGaussianMassLaw.coordinateLaw concreteMassParameters)
        concreteEnsemble.probability) ∧
    (forall index sample,
      concreteEnsemble.mass index sample ∈ RandomEnsemble.massSupport) ∧
    (∑ mode : OrderedMode 5,
      orderedModalEnergy 5 energyDensity mode) = 5 * energyDensity ∧
    (forall mode : OrderedMode 5,
      0 <= orderedModalEnergy 5 energyDensity mode) ∧
    (1 / 8 : Real) <=
      ∑ mode : OrderedMode 5,
        |orderedEnergyShape 5 mode -
          orderedPositiveUniformWeight
            (Fintype.card (Lattice.Site 5)) mode| ∧
    (forall (mass : MassSequence) (mode : Lattice.Site 5),
      0 < massSequenceOrderedModeFrequency mass mode ->
        massSequenceOrderedModeFrequency mass mode *
            initialAction energyDensity mass mode =
          modalEnergyAtPhaseSite energyDensity mode) ∧
    HasLaw (initialPhase (N := 5))
      (finitePhaseHaarLaw (Lattice.Site 5))
      concreteEnsemble.probability ∧
    IndepFun (concreteEnsemble.restrictMass (N := 5))
      (initialPhase (N := 5)) concreteEnsemble.probability ∧
    HasLaw
      (orderedMassDependentFreeRestrictedPhase
        (N := 5) concreteEnsemble observationTime)
      (finitePhaseHaarLaw (Lattice.Site 5))
      concreteEnsemble.probability ∧
    IndepFun (concreteEnsemble.restrictMass (N := 5))
      (orderedMassDependentFreeRestrictedPhase
        (N := 5) concreteEnsemble observationTime)
      concreteEnsemble.probability := by
  refine ⟨massCoordinate_hasLaw, massCoordinate_mem_support, ?_, ?_, ?_,
    ?_, initialPhase_hasLaw, initialMass_indep_initialPhase,
    freeEvolvedPhase_hasLaw observationTime,
    initialMass_indep_freeEvolvedPhase observationTime⟩
  · simpa using
      (sum_orderedModalEnergy_eq_total (N := 5) (by norm_num)
        energyDensity)
  · intro mode
    exact orderedModalEnergy_nonneg (N := 5) (by norm_num)
      (by norm_num [energyDensity]) mode
  · exact orderedEnergyShape_l1_separated (N := 5) (by norm_num)
  · intro mass mode hfrequency
    exact frequency_mul_initialAction energyDensity mass mode hfrequency

#print axioms problem_concrete_gaussian_two_band_initial_ensemble
#print axioms sum_orderedModalEnergy_eq_total
#print axioms freeEvolvedPhase_hasLaw

end ConcreteGaussianTwoBand

end

end ArchonPhysicsConsumers.Thermalization
