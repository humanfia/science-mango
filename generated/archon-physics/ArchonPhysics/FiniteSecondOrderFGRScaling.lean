import ArchonPhysics.FiniteSecondOrderPhaseExpansion

/-!
# Second-order scaling of a finite two-step phase expansion

This module extracts the exact second-order scaling statement from the
finite-Haar two-step moment polynomial.  When the charge-selected first-order
interference vanishes, division of the averaged moment increment by
`epsilon^2` leaves the complete second-order coefficient, followed by an
explicit `epsilon` term and an explicit `epsilon^2` term.

The complete coefficient is not just the square of the first correction.  It
also contains the charge-selected interference between the initial amplitude
and the supplied second correction.  When those two monomials have equal
charge, the coefficient is exactly

`|w|^2 + 2 Re (z * conj u)`.

These are fixed finite-dimensional polynomial identities and their elementary
punctured-neighbourhood limit.  They do not derive the supplied corrections
from a microscopic flow, propagate random phases, identify a collision
kernel, or prove a kinetic or thermodynamic limit.
-/

namespace ArchonPhysics.FiniteSecondOrderFGRScaling

open MeasureTheory Filter
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteSecondOrderPhaseExpansion
open scoped ComplexConjugate Topology

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- If the averaged first-order interference vanishes, the finite-Haar moment
increment starts exactly at order two. -/
theorem finitePhaseTwoStepMomentPolynomial_increment_eq
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0) :
    finitePhaseTwoStepMomentPolynomial epsilon
          zCoefficient wCoefficient uCoefficient
          zFactors wFactors uFactors - Complex.normSq zCoefficient =
      epsilon ^ 2 * finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors +
        epsilon ^ 3 * chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors +
        epsilon ^ 4 * Complex.normSq uCoefficient := by
  unfold finitePhaseTwoStepMomentPolynomial
  rw [hfirst]
  ring

/-- Exact scaled identity on the punctured coupling line.  The two remainder
terms have respective orders `epsilon` and `epsilon^2`. -/
theorem finitePhaseTwoStepMomentPolynomial_scaled_eq
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hepsilon : epsilon ≠ 0) :
    (finitePhaseTwoStepMomentPolynomial epsilon
          zCoefficient wCoefficient uCoefficient
          zFactors wFactors uFactors - Complex.normSq zCoefficient) /
        epsilon ^ 2 =
      finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors +
        epsilon * chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors +
        epsilon ^ 2 * Complex.normSq uCoefficient := by
  rw [finitePhaseTwoStepMomentPolynomial_increment_eq epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors hfirst]
  field_simp

/-- Exact remainder after subtracting the complete second-order coefficient. -/
theorem finitePhaseTwoStepMomentPolynomial_scaled_remainder_eq
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
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
  rw [finitePhaseTwoStepMomentPolynomial_scaled_eq epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon]
  ring

/-- Explicit absolute error bound for the scaled second-order increment. -/
theorem abs_finitePhaseTwoStepMomentPolynomial_scaled_remainder_le
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hepsilon : epsilon ≠ 0) :
    abs ((finitePhaseTwoStepMomentPolynomial epsilon
            zCoefficient wCoefficient uCoefficient
            zFactors wFactors uFactors - Complex.normSq zCoefficient) /
          epsilon ^ 2 -
        finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors) <=
      abs epsilon * abs (chargeSelectedInterference
        wCoefficient uCoefficient wFactors uFactors) +
        abs epsilon ^ 2 * Complex.normSq uCoefficient := by
  rw [finitePhaseTwoStepMomentPolynomial_scaled_remainder_eq epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon]
  calc
    abs (epsilon * chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors +
        epsilon ^ 2 * Complex.normSq uCoefficient) <=
        abs (epsilon * chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors) +
          abs (epsilon ^ 2 * Complex.normSq uCoefficient) := abs_add_le _ _
    _ = abs epsilon * abs (chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors) +
        abs epsilon ^ 2 * Complex.normSq uCoefficient := by
      rw [abs_mul, abs_mul, abs_pow,
        abs_of_nonneg (Complex.normSq_nonneg uCoefficient)]

/-- The scaled finite polynomial converges to its complete second-order
coefficient as the nonzero coupling tends to zero. -/
theorem finitePhaseTwoStepMomentPolynomial_scaled_tendsto
    (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0) :
    Tendsto
      (fun epsilon : Real =>
        (finitePhaseTwoStepMomentPolynomial epsilon
              zCoefficient wCoefficient uCoefficient
              zFactors wFactors uFactors - Complex.normSq zCoefficient) /
          epsilon ^ 2)
      (nhdsWithin 0 ({0} : Set Real)ᶜ)
      (nhds (finitePhaseSecondOrderCoefficient
        zCoefficient wCoefficient uCoefficient zFactors uFactors)) := by
  let second := finitePhaseSecondOrderCoefficient
    zCoefficient wCoefficient uCoefficient zFactors uFactors
  let third := chargeSelectedInterference
    wCoefficient uCoefficient wFactors uFactors
  let fourth := Complex.normSq uCoefficient
  have hcontinuous : ContinuousAt
      (fun epsilon : Real => second + epsilon * third + epsilon ^ 2 * fourth) 0 := by
    fun_prop
  have hpolynomial : Tendsto
      (fun epsilon : Real => second + epsilon * third + epsilon ^ 2 * fourth)
      (nhdsWithin 0 ({0} : Set Real)ᶜ) (nhds second) := by
    simpa [second, third, fourth] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply (tendsto_congr' ?_).mpr hpolynomial
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hepsilon_ne : epsilon ≠ 0 := by
    simpa using hepsilon
  exact finitePhaseTwoStepMomentPolynomial_scaled_eq epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon_ne

/-- The same exact scaled identity written for the actual finite-Haar phase
average rather than for its polynomial normal form. -/
theorem integral_normSq_phaseTwoStep_scaled_eq
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hepsilon : epsilon ≠ 0) :
    ((∫ phase : UnitAddTorus d,
          Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
            zCoefficient wCoefficient uCoefficient
            zFactors wFactors uFactors phase) ∂finitePhaseHaarLaw d) -
        Complex.normSq zCoefficient) / epsilon ^ 2 =
      finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors +
        epsilon * chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors +
        epsilon ^ 2 * Complex.normSq uCoefficient := by
  rw [integral_normSq_phaseTwoStepPerturbedAmplitude]
  exact finitePhaseTwoStepMomentPolynomial_scaled_eq epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon


/-- Exact remainder identity for the finite-Haar averaged scaled increment. -/
theorem integral_normSq_phaseTwoStep_scaled_remainder_eq
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hepsilon : epsilon ≠ 0) :
    ((∫ phase : UnitAddTorus d,
          Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
            zCoefficient wCoefficient uCoefficient
            zFactors wFactors uFactors phase) ∂finitePhaseHaarLaw d) -
        Complex.normSq zCoefficient) / epsilon ^ 2 -
        finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors =
      epsilon * chargeSelectedInterference
          wCoefficient uCoefficient wFactors uFactors +
        epsilon ^ 2 * Complex.normSq uCoefficient := by
  rw [integral_normSq_phaseTwoStepPerturbedAmplitude]
  exact finitePhaseTwoStepMomentPolynomial_scaled_remainder_eq epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon

/-- Explicit remainder bound for the actual finite-Haar averaged quotient. -/
theorem abs_integral_normSq_phaseTwoStep_scaled_remainder_le
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hepsilon : epsilon ≠ 0) :
    abs (((∫ phase : UnitAddTorus d,
            Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
              zCoefficient wCoefficient uCoefficient
              zFactors wFactors uFactors phase) ∂finitePhaseHaarLaw d) -
          Complex.normSq zCoefficient) / epsilon ^ 2 -
        finitePhaseSecondOrderCoefficient
          zCoefficient wCoefficient uCoefficient zFactors uFactors) ≤
      abs epsilon * abs (chargeSelectedInterference
        wCoefficient uCoefficient wFactors uFactors) +
        abs epsilon ^ 2 * Complex.normSq uCoefficient := by
  rw [integral_normSq_phaseTwoStepPerturbedAmplitude]
  exact abs_finitePhaseTwoStepMomentPolynomial_scaled_remainder_le epsilon
    zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
    hfirst hepsilon
/-- The actual finite-Haar averaged quotient has the same second-order limit. -/
theorem integral_normSq_phaseTwoStep_scaled_tendsto
    (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0) :
    Tendsto
      (fun epsilon : Real =>
        ((∫ phase : UnitAddTorus d,
              Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
                zCoefficient wCoefficient uCoefficient
                zFactors wFactors uFactors phase) ∂finitePhaseHaarLaw d) -
          Complex.normSq zCoefficient) / epsilon ^ 2)
      (nhdsWithin 0 ({0} : Set Real)ᶜ)
      (nhds (finitePhaseSecondOrderCoefficient
        zCoefficient wCoefficient uCoefficient zFactors uFactors)) := by
  simpa only [integral_normSq_phaseTwoStepPerturbedAmplitude] using
    finitePhaseTwoStepMomentPolynomial_scaled_tendsto
      zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors hfirst

/-- If the initial and second-correction monomials have equal charge, the
finite-Haar FGR-scale limit displays both pieces of the complete coefficient. -/
theorem integral_normSq_phaseTwoStep_scaled_tendsto_balanced
    (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (hfirst : chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors = 0)
    (hsecondCharge : monomialCharge zFactors = monomialCharge uFactors) :
    Tendsto
      (fun epsilon : Real =>
        ((∫ phase : UnitAddTorus d,
              Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
                zCoefficient wCoefficient uCoefficient
                zFactors wFactors uFactors phase) ∂finitePhaseHaarLaw d) -
          Complex.normSq zCoefficient) / epsilon ^ 2)
      (nhdsWithin 0 ({0} : Set Real)ᶜ)
      (nhds (Complex.normSq wCoefficient +
        2 * (zCoefficient * conj uCoefficient).re)) := by
  simpa [finitePhaseSecondOrderCoefficient, chargeSelectedInterference,
    hsecondCharge] using
      integral_normSq_phaseTwoStep_scaled_tendsto
        zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors hfirst

end

end ArchonPhysics.FiniteSecondOrderFGRScaling
