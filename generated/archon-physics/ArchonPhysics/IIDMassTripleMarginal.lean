import ArchonPhysics.ThreeParameterSpectralAveragingDensity
import Mathlib.Probability.HasLaw

/-!
# The actual iid law of three selected mass coordinates

This module connects the abstract iid ensemble interface to the concrete
three-mass averaging law.  Three distinct coordinates have exactly the
nested product law used by the lifted spectral chart.  Consequently every
nonnegative measurable observable depending only on those coordinates can
be integrated against the explicit mass-triple law.
-/

namespace ArchonPhysics.IIDMassTripleMarginal

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Three selected physical mass coordinates in the nested product
convention of MassTriple. -/
def ensembleMassTriple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (i j k : Nat) (omega : Omega) : MassTriple :=
  ((ensemble.mass i omega, ensemble.mass j omega), ensemble.mass k omega)

theorem measurable_ensembleMassTriple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (i j k : Nat) :
    Measurable (ensembleMassTriple ensemble i j k) := by
  unfold ensembleMassTriple
  exact ((ensemble.mass_measurable i).prodMk
    (ensemble.mass_measurable j)).prodMk (ensemble.mass_measurable k)

/-- Three pairwise distinct iid mass coordinates have exactly the concrete
three-fold product law used by spectral averaging. -/
theorem ensembleMassTriple_hasLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {i j k : Nat} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    HasLaw (ensembleMassTriple ensemble i j k)
      iidMassTripleLaw ensemble.probability := by
  let _ : IsFiniteMeasure ensemble.probability :=
    ⟨by rw [ensemble.probability_univ]; norm_num⟩
  have hpairIndep : IndepFun (ensemble.mass i) (ensemble.mass j)
      ensemble.probability :=
    ensemble.mass_iIndep.indepFun hij
  have hpairLaw :
      HasLaw (fun omega => (ensemble.mass i omega, ensemble.mass j omega))
        iidMassPairLaw ensemble.probability := by
    simpa [iidMassPairLaw] using
      hpairIndep.hasLaw_prod (ensemble.mass_hasLaw i)
        (ensemble.mass_hasLaw j)
  have hpairThirdIndep :
      IndepFun
        (fun omega => (ensemble.mass i omega, ensemble.mass j omega))
        (ensemble.mass k) ensemble.probability :=
    ensemble.mass_iIndep.indepFun_prodMk ensemble.mass_measurable
      i j k hik hjk
  change HasLaw
    (fun omega => ((ensemble.mass i omega, ensemble.mass j omega),
      ensemble.mass k omega))
    (iidMassPairLaw.prod massCoordinateLaw) ensemble.probability
  exact hpairThirdIndep.hasLaw_prod hpairLaw (ensemble.mass_hasLaw k)

/-- Integral transport for every nonnegative measurable observable of the
three selected masses. -/
theorem lintegral_ensembleMassTriple_eq_iidMassTripleLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {i j k : Nat} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {observable : MassTriple → ENNReal}
    (hmeasurable : AEMeasurable observable iidMassTripleLaw) :
    ∫⁻ omega, observable (ensembleMassTriple ensemble i j k omega)
        ∂ensemble.probability =
      ∫⁻ triple, observable triple ∂iidMassTripleLaw := by
  exact (ensembleMassTriple_hasLaw ensemble hij hik hjk).lintegral_comp
    hmeasurable

end

end ArchonPhysics.IIDMassTripleMarginal
