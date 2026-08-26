import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Probability.ProductMeasure

/-!
# Exact Haar random-phase moments

Wave-kinetic diagram expansions average products of random phases.  For Haar
phases the correct rule is charge balance, not the Gaussian Isserlis pairing
formula: a monomial has nonzero expectation exactly when every phase index has
the same positive and negative multiplicity.

This module states that rule first on a finite product of unit additive
circles.  It is grounded in Mathlib's multivariate Fourier characters and
their orthonormality.  In particular, repeated indices are handled with their
exact Haar coefficient rather than a Gaussian pairing multiplicity.
-/

namespace ArchonPhysics.RandomPhaseMoments

open MeasureTheory
open UnitAddTorus

noncomputable section

/- Use the same normalized Haar product measure as Mathlib's multivariate
Fourier orthogonality theorem. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- The explicit normalized Haar product law used by the phase-moment API. -/
def finitePhaseHaarLaw (d : Type*) [Fintype d] : Measure (UnitAddTorus d) :=
  volume

/-- The expectation of a finite Haar character is its zero-charge indicator. -/
theorem integral_mFourier_eq_ite (charge : d → Int) :
    (∫ phase : UnitAddTorus d, mFourier charge phase ∂finitePhaseHaarLaw d) =
      if charge = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (orthonormal_mFourier (d := d))) (0 : d → Int) charge
  simpa [ContinuousMap.inner_toLp, mFourier_zero, eq_comm, finitePhaseHaarLaw] using h

/-- A charge-balanced finite Haar monomial has expectation one. -/
theorem integral_mFourier_eq_one {charge : d → Int} (hcharge : charge = 0) :
    (∫ phase : UnitAddTorus d, mFourier charge phase ∂finitePhaseHaarLaw d) = 1 := by
  rw [integral_mFourier_eq_ite, if_pos hcharge]

/-- A charge-unbalanced finite Haar monomial has expectation zero. -/
theorem integral_mFourier_eq_zero {charge : d → Int} (hcharge : charge ≠ 0) :
    (∫ phase : UnitAddTorus d, mFourier charge phase ∂finitePhaseHaarLaw d) = 0 := by
  rw [integral_mFourier_eq_ite, if_neg hcharge]

/-- Haar fourth moment at one index: unlike a complex Gaussian, it is exactly one. -/
theorem singlePhase_fourthMoment :
    (∫ phase : UnitAddCircle,
      fourier 1 phase * fourier 1 phase *
        fourier (-1) phase * fourier (-1) phase
      ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [← fourier_add]
  simp

end

end ArchonPhysics.RandomPhaseMoments
