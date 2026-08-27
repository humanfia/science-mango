import ArchonPhysics.PaperNumericalLowTenthInitialEnsemble

/-!
# Consumer: paper-numerical periodic low-ten-percent initial ensemble

This acceptance target uses `N = 101`, so there are exactly one hundred
positive ordered modes and the explicit floor convention excites exactly ten
of them.  At energy density `2/5` it checks the uniform `[4/5,6/5]` mass law,
positive support, zero translation-mode energy, exact extensive energy,
nonnegativity, the exact `9/5` initial `l1` distance from equipartition,
product-Haar phase law, and mass--phase independence.

This is a periodic-boundary initialization target.  It makes no Wick-RPA,
nonlinear phase-propagation, kinetic-limit, or thermalization assertion.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory
open ArchonPhysics
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.PaperNumericalLowTenthInitialEnsemble
open ArchonPhysics.RandomPhaseMoments
open scoped BigOperators

noncomputable section

namespace PaperNumericalLowTenth

def energyDensity : Real := 2 / 5

/-- Kernel-checked acceptance contract for the truth-audited periodic
low-ten-percent initial ensemble. -/
theorem problem_paper_numerical_low_tenth_initial_ensemble :
    excitedPositiveModeCount (101 - 1) = 10 ∧
    (⟨99, by norm_num⟩ : Fin 100) ∈ excitedPositiveModes 100 ∧
    (forall index : Nat,
      HasLaw (paperUniformEnsemble.mass index)
        RandomEnsemble.massCoordinateLaw
        paperUniformEnsemble.probability) ∧
    (forall index sample,
      paperUniformEnsemble.mass index sample ∈
        RandomEnsemble.massSupport) ∧
    orderedModalEnergy 101 energyDensity
      (lastSiteOrderedIndex
        (Fintype.card (Lattice.Site 101))) = 0 ∧
    (∑ mode : OrderedMode 101,
      orderedModalEnergy 101 energyDensity mode) =
        101 * energyDensity ∧
    (forall mode : OrderedMode 101,
      0 <= orderedModalEnergy 101 energyDensity mode) ∧
    (∑ mode : OrderedMode 101,
      |orderedEnergyShape 101 mode -
        orderedPositiveUniformWeight
          (Fintype.card (Lattice.Site 101)) mode|) = 9 / 5 ∧
    HasLaw (initialPhase (N := 101))
      (finitePhaseHaarLaw (Lattice.Site 101))
      paperUniformEnsemble.probability ∧
    IndepFun (paperUniformEnsemble.restrictMass (N := 101))
      (initialPhase (N := 101)) paperUniformEnsemble.probability := by
  refine ⟨by norm_num [excitedPositiveModeCount], ?_,
    massCoordinate_hasLaw, massCoordinate_mem_support, ?_, ?_, ?_, ?_,
    initialPhase_hasLaw, initialMass_indep_initialPhase⟩
  · exact last_positive_rank_mem_excited (M := 100) (by norm_num) _ (by norm_num)
  · simp [orderedModalEnergy, orderedEnergyShape]
  · simpa using
      (sum_orderedModalEnergy_eq_total (N := 101) (by norm_num)
        energyDensity)
  · intro mode
    exact orderedModalEnergy_nonneg (N := 101)
      (by norm_num [energyDensity]) mode
  · rw [orderedEnergyShape_l1_eq (N := 101) (by norm_num)]
    norm_num [excitedPositiveModeCount]

#print axioms problem_paper_numerical_low_tenth_initial_ensemble
#print axioms lowTenthPositiveEnergyProfile_l1_eq
#print axioms initialPhase_hasLaw

end PaperNumericalLowTenth

end

end ArchonPhysicsConsumers.Thermalization
