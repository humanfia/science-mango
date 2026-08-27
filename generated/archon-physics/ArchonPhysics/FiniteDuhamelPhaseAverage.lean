import ArchonPhysics.FinitePhaseMonomials
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finite Duhamel phase averages

This module records only the finite random-phase algebra needed by a Duhamel
expansion.  A correction is a finite deterministic linear combination of
multivariate Haar characters.  Its mean retains precisely the zero-charge
terms, while its second absolute moment retains every pair of terms carrying
the same charge.

In particular, distinct terms with a repeated charge contribute cross terms;
the second moment is not reduced to a diagonal sum.  No dynamical, collision
kernel, kinetic-limit, or convergence claim is made here.
-/

namespace ArchonPhysics.FiniteDuhamelPhaseAverage

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/- Use the normalized Haar coordinate measure underlying
`finitePhaseHaarLaw`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d J : Type*} [Fintype d] [Fintype J]

/-- A finite deterministic linear combination of phase characters. -/
def finitePhaseCorrection
    (coefficient : J → ℂ) (charge : J → d → Int)
    (phase : UnitAddTorus d) : ℂ :=
  ∑ j, coefficient j * mFourier (charge j) phase

/-- A finite phase correction is continuous. -/
theorem finitePhaseCorrection_continuous
    (coefficient : J → ℂ) (charge : J → d → Int) :
    Continuous (finitePhaseCorrection coefficient charge) := by
  unfold finitePhaseCorrection
  fun_prop

/-- Every finite Haar character is integrable under the normalized finite
product Haar law. -/
theorem integrable_mFourier_finitePhaseHaarLaw (charge : d → Int) :
    Integrable (fun phase : UnitAddTorus d ↦ mFourier charge phase)
      (finitePhaseHaarLaw d) := by
  rw [finitePhaseHaarLaw]
  exact (mFourier charge).continuous.integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

/-- First-order finite phase averaging: exactly the zero-charge terms
survive. -/
theorem integral_finitePhaseCorrection_eq_zeroChargeSum
    (coefficient : J → ℂ) (charge : J → d → Int) :
    (∫ phase : UnitAddTorus d,
      finitePhaseCorrection coefficient charge phase
      ∂finitePhaseHaarLaw d) =
      ∑ j, if charge j = 0 then coefficient j else 0 := by
  change (∫ phase : UnitAddTorus d,
    ∑ j, coefficient j * mFourier (charge j) phase
    ∂finitePhaseHaarLaw d) = _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, integral_mFourier_eq_ite]
    by_cases hcharge : charge j = 0 <;> simp [hcharge]
  · intro j hj
    exact (integrable_mFourier_finitePhaseHaarLaw
      (charge j)).const_mul (coefficient j)

/-- Product of a character and the conjugate of another character is the
difference-charge character. -/
theorem mFourier_mul_star_mFourier
    (leftCharge rightCharge : d → Int) (phase : UnitAddTorus d) :
    mFourier leftCharge phase *
        starRingEnd ℂ (mFourier rightCharge phase) =
      mFourier (leftCharge - rightCharge) phase := by
  simp only [← mFourier_neg, ← mFourier_add, sub_eq_add_neg]

/-- Pointwise expansion of `correction * conj correction` as a correction
indexed by all ordered term pairs. -/
theorem finitePhaseCorrection_mul_star_eq_pairCorrection
    (coefficient : J → ℂ) (charge : J → d → Int)
    (phase : UnitAddTorus d) :
    finitePhaseCorrection coefficient charge phase *
        starRingEnd ℂ (finitePhaseCorrection coefficient charge phase) =
      finitePhaseCorrection
        (fun pair : J × J ↦
          coefficient pair.1 * starRingEnd ℂ (coefficient pair.2))
        (fun pair : J × J ↦ charge pair.1 - charge pair.2) phase := by
  simp only [finitePhaseCorrection, map_sum, map_mul]
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (coefficient j * mFourier (charge j) phase) *
        (starRingEnd ℂ (coefficient k) *
          starRingEnd ℂ (mFourier (charge k) phase)) =
      (coefficient j * starRingEnd ℂ (coefficient k)) *
        (mFourier (charge j) phase *
          starRingEnd ℂ (mFourier (charge k) phase)) := by ring
    _ = (coefficient j * starRingEnd ℂ (coefficient k)) *
        mFourier (charge j - charge k) phase := by
      rw [mFourier_mul_star_mFourier]

/-- Exact second absolute moment.  Every ordered pair of terms with equal
charge survives, including off-diagonal pairs with repeated charge. -/
theorem integral_finitePhaseCorrection_mul_star_eq_equalChargePairSum
    (coefficient : J → ℂ) (charge : J → d → Int) :
    (∫ phase : UnitAddTorus d,
      finitePhaseCorrection coefficient charge phase *
        starRingEnd ℂ (finitePhaseCorrection coefficient charge phase)
      ∂finitePhaseHaarLaw d) =
      ∑ j, ∑ k,
        if charge j = charge k then
          coefficient j * starRingEnd ℂ (coefficient k) else 0 := by
  calc
    (∫ phase : UnitAddTorus d,
      finitePhaseCorrection coefficient charge phase *
        starRingEnd ℂ (finitePhaseCorrection coefficient charge phase)
      ∂finitePhaseHaarLaw d) =
        ∫ phase : UnitAddTorus d,
          finitePhaseCorrection
            (fun pair : J × J ↦
              coefficient pair.1 * starRingEnd ℂ (coefficient pair.2))
            (fun pair : J × J ↦ charge pair.1 - charge pair.2) phase
          ∂finitePhaseHaarLaw d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦
        finitePhaseCorrection_mul_star_eq_pairCorrection
          coefficient charge phase
    _ = ∑ pair : J × J,
        if charge pair.1 - charge pair.2 = 0 then
          coefficient pair.1 * starRingEnd ℂ (coefficient pair.2) else 0 :=
      integral_finitePhaseCorrection_eq_zeroChargeSum
        (fun pair : J × J ↦
          coefficient pair.1 * starRingEnd ℂ (coefficient pair.2))
        (fun pair : J × J ↦ charge pair.1 - charge pair.2)
    _ = ∑ j, ∑ k,
        if charge j = charge k then
          coefficient j * starRingEnd ℂ (coefficient k) else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [sub_eq_zero]

/-- Actual-ensemble first-order corollary obtained from the full finite joint
Haar law of `restrictPhase`. -/
theorem ensemble_finitePhaseCorrection_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (coefficient : J → ℂ)
    (charge : J → Lattice.Site N → Int) :
    (∫ omega,
      finitePhaseCorrection coefficient charge
        (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      ∑ j, if charge j = 0 then coefficient j else 0 := by
  calc
    (∫ omega,
      finitePhaseCorrection coefficient charge
        (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
        ∫ phase,
          finitePhaseCorrection coefficient charge phase
          ∂finitePhaseHaarLaw (Lattice.Site N) := by
      simpa [Function.comp_def] using
        (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble
          (N := N)).integral_comp
            (finitePhaseCorrection_continuous
              coefficient charge).aestronglyMeasurable
    _ = ∑ j, if charge j = 0 then coefficient j else 0 :=
      integral_finitePhaseCorrection_eq_zeroChargeSum coefficient charge

/-- Actual-ensemble second absolute moment, retaining all equal-charge term
pairs rather than only the diagonal. -/
theorem ensemble_finitePhaseCorrection_mul_star_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (coefficient : J → ℂ)
    (charge : J → Lattice.Site N → Int) :
    (∫ omega,
      finitePhaseCorrection coefficient charge
          (ensemble.restrictPhase omega) *
        starRingEnd ℂ
          (finitePhaseCorrection coefficient charge
            (ensemble.restrictPhase omega))
      ∂ensemble.probability) =
      ∑ j, ∑ k,
        if charge j = charge k then
          coefficient j * starRingEnd ℂ (coefficient k) else 0 := by
  calc
    (∫ omega,
      finitePhaseCorrection coefficient charge
          (ensemble.restrictPhase omega) *
        starRingEnd ℂ
          (finitePhaseCorrection coefficient charge
            (ensemble.restrictPhase omega))
      ∂ensemble.probability) =
        ∫ phase,
          finitePhaseCorrection coefficient charge phase *
            starRingEnd ℂ
              (finitePhaseCorrection coefficient charge phase)
          ∂finitePhaseHaarLaw (Lattice.Site N) := by
      simpa [Function.comp_def] using
        (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble
          (N := N)).integral_comp
            (((finitePhaseCorrection_continuous coefficient charge).mul
              ((finitePhaseCorrection_continuous coefficient charge).star)).aestronglyMeasurable)
    _ = ∑ j, ∑ k,
        if charge j = charge k then
          coefficient j * starRingEnd ℂ (coefficient k) else 0 :=
      integral_finitePhaseCorrection_mul_star_eq_equalChargePairSum
        coefficient charge

end

end ArchonPhysics.FiniteDuhamelPhaseAverage
