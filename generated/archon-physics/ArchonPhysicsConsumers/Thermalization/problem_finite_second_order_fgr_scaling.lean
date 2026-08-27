import ArchonPhysics.FiniteSecondOrderFGRScaling

/-!
# Consumer: finite five-site second-order FGR scaling

This consumer specializes the finite-Haar second-order scaling theorem to the
canonical five-site phase block.  It is only a contract for a supplied
two-step Picard polynomial; it makes no microscopic, kinetic-limit, or
random-phase-propagation claim.
-/

namespace ArchonPhysicsConsumers.Thermalization.FiniteSecondOrderFGRScaling

open MeasureTheory Filter
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteSecondOrderPhaseExpansion
open ArchonPhysics.FiniteSecondOrderFGRScaling
open scoped ComplexConjugate Topology

noncomputable section

/-- On five sites, vanishing first-order charge selection and balanced
initial/second-step charges produce the complete second-order coefficient. -/
theorem fiveSite_twoStep_FGR_scaled_limit_contract
    (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode (Lattice.Site 5)))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hsecondCharge : monomialCharge zFactors = monomialCharge uFactors) :
    Tendsto
      (fun epsilon : Real =>
        ((∫ phase : UnitAddTorus (Lattice.Site 5),
              Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
                zCoefficient wCoefficient uCoefficient
                zFactors wFactors uFactors phase) ∂finitePhaseHaarLaw (Lattice.Site 5)) -
          Complex.normSq zCoefficient) / epsilon ^ 2)
      (nhdsWithin 0 ({0} : Set Real)ᶜ)
      (nhds (Complex.normSq wCoefficient +
        2 * (zCoefficient * conj uCoefficient).re)) := by
  exact integral_normSq_phaseTwoStep_scaled_tendsto_balanced
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hsecondCharge

/-- The five-site scaled remainder is exactly linear plus quadratic in the
coupling; in particular the full coefficient has already been subtracted. -/
theorem fiveSite_twoStep_FGR_scaled_remainder_contract
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode (Lattice.Site 5)))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hepsilon : epsilon ≠ 0) :
    (finitePhaseTwoStepMomentPolynomial epsilon
          zCoefficient wCoefficient uCoefficient
          zFactors wFactors uFactors - Complex.normSq zCoefficient) /
          epsilon ^ 2 -
        finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors =
      epsilon * chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors +
        epsilon ^ 2 * Complex.normSq uCoefficient := by
  exact finitePhaseTwoStepMomentPolynomial_scaled_remainder_eq epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon


/-- The actual five-site Haar average obeys the explicit linear-plus-quadratic
scaled remainder bound. -/
theorem fiveSite_twoStep_FGR_scaled_remainder_bound_contract
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode (Lattice.Site 5)))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hepsilon : epsilon ≠ 0) :
    abs (((∫ phase : UnitAddTorus (Lattice.Site 5),
            Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
              zCoefficient wCoefficient uCoefficient
              zFactors wFactors uFactors phase)
            ∂finitePhaseHaarLaw (Lattice.Site 5)) -
          Complex.normSq zCoefficient) / epsilon ^ 2 -
        finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors) ≤
      abs epsilon * abs (chargeSelectedInterference
        wCoefficient uCoefficient wFactors uFactors) +
        abs epsilon ^ 2 * Complex.normSq uCoefficient := by
  exact abs_integral_normSq_phaseTwoStep_scaled_remainder_le epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon
#print axioms fiveSite_twoStep_FGR_scaled_limit_contract
#print axioms fiveSite_twoStep_FGR_scaled_remainder_contract
#print axioms fiveSite_twoStep_FGR_scaled_remainder_bound_contract
#print axioms integral_normSq_phaseTwoStep_scaled_tendsto_balanced
#print axioms abs_finitePhaseTwoStepMomentPolynomial_scaled_remainder_le

end

end ArchonPhysicsConsumers.Thermalization.FiniteSecondOrderFGRScaling
