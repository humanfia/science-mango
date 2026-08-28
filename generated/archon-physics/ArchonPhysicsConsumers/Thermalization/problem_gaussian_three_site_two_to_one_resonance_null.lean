import ArchonPhysics.GaussianThreeSiteTwoToOneResonanceNull

/-!
# Consumer: Gaussian three-site dangerous-resonance nullity

These endpoints expose the strongest unconditional annealed conclusion
currently available for the three degenerate FPUT denominators: at volume
three, every exact positive two-to-one modal resonance is null under the
genuine truncated-Gaussian mass law.  No quantitative small-ball rate or
volume-uniform estimate is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.GaussianThreeSiteTwoToOneResonanceNull
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.TruncatedGaussianMassLaw
open MeasureTheory

noncomputable section

/-- Any of the three dangerous scalar relations, after naming its undoubled
mode `parent` and doubled positive mode `child`, belongs to one null event. -/
theorem problem_probability_exists_gaussian_threeSite_dangerousMismatch_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) :
    ensemble.probability
        {omega | ∃ parent child : Lattice.Site 3,
          0 < modeFrequency
              (ensemble.restrictPositiveMass (N := 3) omega) child ∧
            modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) parent -
              2 * modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) child = 0} = 0 :=
  probability_exists_positive_twoToOne_mismatch_eq_zero ensemble

/-- Fixed-mode nullity for direct use on one repeated-away, observed-carrier,
or observed-free dangerous summand. -/
theorem problem_probability_fixed_gaussian_threeSite_dangerousMismatch_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (parent child : Lattice.Site 3) :
    ensemble.probability
        {omega |
          0 < modeFrequency
              (ensemble.restrictPositiveMass (N := 3) omega) child ∧
            modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) parent -
              2 * modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) child = 0} = 0 :=
  probability_fixed_positive_twoToOne_mismatch_eq_zero ensemble parent child

/-- Almost-everywhere nonzero denominator, conditional only on the doubled
leg being a positive mode. -/
theorem problem_gaussian_threeSite_dangerousMismatch_ne_zero_ae
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (parent child : Lattice.Site 3) :
    ∀ᵐ omega ∂ensemble.probability,
      0 < modeFrequency
          (ensemble.restrictPositiveMass (N := 3) omega) child →
        modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) parent -
          2 * modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) child ≠ 0 :=
  fixed_positive_twoToOne_mismatch_ne_zero_ae ensemble parent child

#print axioms
  problem_probability_exists_gaussian_threeSite_dangerousMismatch_eq_zero
#print axioms
  problem_probability_fixed_gaussian_threeSite_dangerousMismatch_eq_zero
#print axioms problem_gaussian_threeSite_dangerousMismatch_ne_zero_ae

end

end ArchonPhysicsConsumers.Thermalization
