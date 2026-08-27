import ArchonPhysics.FiniteSecondOrderPhaseExpansion

/-!
# Consumer: fixed five-site second-order phase expansion

This consumer instantiates the exact phase-average theorem on the canonical
five-site phase block.  Its coefficients are deterministic.  It also checks
directly that the balanced second-order coefficient contains both the square
of the first correction and the initial/second-correction interference.
-/

namespace ArchonPhysicsConsumers.Thermalization.FiniteSecondOrderPhaseExpansion

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteSecondOrderPhaseExpansion
open scoped ComplexConjugate

noncomputable section

/-- The canonical five-site phase restriction consumes the exact fixed finite
Haar expansion. -/
theorem canonicalFiveSitePhaseAverage_contract
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode (Lattice.Site 5))) :
    (∫ omega, Complex.normSq
      (phaseTwoStepPerturbedAmplitude epsilon
        zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
        (canonicalIIDMassPhaseEnsemble.restrictPhase (N := 5) omega))
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      finitePhaseTwoStepMomentPolynomial epsilon
        zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors := by
  exact ensemble_integral_normSq_phaseTwoStepPerturbedAmplitude
    canonicalIIDMassPhaseEnsemble epsilon
      zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors

/-- When the initial and second-correction monomials have the same charge, the
complete `epsilon^2` coefficient retains both contributions. -/
theorem fiveSiteBalancedSecondOrder_contract
    (zCoefficient wCoefficient uCoefficient : Complex)
    (balancedFactors : List (SignedMode (Lattice.Site 5))) :
    finitePhaseSecondOrderCoefficient
        zCoefficient wCoefficient uCoefficient balancedFactors balancedFactors =
      Complex.normSq wCoefficient +
        2 * (zCoefficient * conj uCoefficient).re := by
  simp [finitePhaseSecondOrderCoefficient, chargeSelectedInterference]

/-- Unequal total charges kill only the corresponding interference term. -/
theorem fiveSiteUnbalancedInterference_contract
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode (Lattice.Site 5)))
    (hcharge : monomialCharge leftFactors ≠ monomialCharge rightFactors) :
    chargeSelectedInterference
      leftCoefficient rightCoefficient leftFactors rightFactors = 0 := by
  simp [chargeSelectedInterference, hcharge]

end

end ArchonPhysicsConsumers.Thermalization.FiniteSecondOrderPhaseExpansion
