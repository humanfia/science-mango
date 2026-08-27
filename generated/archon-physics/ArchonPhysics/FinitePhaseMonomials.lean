import ArchonPhysics.FiniteEnsemblePhaseMoments

/-!
# Finite signed phase monomials

This module turns a finite list of phase or conjugate-phase factors into its
integer charge vector.  Repeated modes are retained in the list and therefore
contribute repeatedly to the charge; no Gaussian pairing rule is used.

The resulting monomial is exactly Mathlib's multivariate Fourier character.
Consequently its normalized Haar integral, and its expectation in any
verified `IIDMassPhaseEnsemble`, obey the exact charge-balance selector.
-/

namespace ArchonPhysics.FinitePhaseMonomials

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Whether a monomial factor is a phase or its complex conjugate. -/
inductive PhaseSign
  | phase
  | conjugate
  deriving DecidableEq, Repr

namespace PhaseSign

/-- The integer Fourier exponent carried by a signed phase factor. -/
def exponent : PhaseSign → Int
  | phase => 1
  | conjugate => -1

@[simp] theorem exponent_phase : exponent .phase = 1 := rfl

@[simp] theorem exponent_conjugate : exponent .conjugate = -1 := rfl

end PhaseSign

/-- One occurrence of a mode in a finite signed phase monomial.  A list of
these factors may contain the same mode any number of times. -/
structure SignedMode (d : Type*) where
  mode : d
  sign : PhaseSign
  deriving DecidableEq, Repr

namespace SignedMode

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The single-mode integer charge vector of one signed factor. -/
def charge (factor : SignedMode d) : d → Int :=
  Pi.single factor.mode factor.sign.exponent

/-- The complex phase factor represented by a signed mode. -/
def phaseFactor (factor : SignedMode d) (phase : UnitAddTorus d) : ℂ :=
  match factor.sign with
  | .phase => fourier 1 (phase factor.mode)
  | .conjugate => starRingEnd ℂ (fourier 1 (phase factor.mode))

/-- A single signed phase factor is its one-mode multivariate Fourier
character. -/
theorem phaseFactor_eq_mFourier
    (factor : SignedMode d) (phase : UnitAddTorus d) :
    phaseFactor factor phase = mFourier factor.charge phase := by
  rcases factor with ⟨mode, sign⟩
  cases sign <;>
    simp [phaseFactor, charge, PhaseSign.exponent, Pi.single_neg,
      mFourier_neg, mFourier_single]

end SignedMode

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The total integer charge/count vector of a finite signed monomial. -/
def monomialCharge : List (SignedMode d) → d → Int
  | [] => 0
  | factor :: rest => factor.charge + monomialCharge rest

omit [Fintype d] in
/-- Pointwise, the charge vector is the signed occurrence count.  This
statement makes the treatment of repeated modes explicit. -/
theorem monomialCharge_apply
    (factors : List (SignedMode d)) (mode : d) :
    monomialCharge factors mode =
      (factors.map fun factor =>
        if mode = factor.mode then factor.sign.exponent else 0).sum := by
  induction factors with
  | nil => simp [monomialCharge]
  | cons factor rest ih =>
      simp [monomialCharge, SignedMode.charge, Pi.single_apply, ih]

/-- The unit-amplitude product of a finite list of signed phase factors. -/
def unitSignedMonomial :
    List (SignedMode d) → UnitAddTorus d → ℂ
  | [], _ => 1
  | factor :: rest, phase =>
      factor.phaseFactor phase * unitSignedMonomial rest phase

/-- A finite signed monomial is exactly the Fourier character of its total
charge vector. -/
theorem unitSignedMonomial_eq_mFourier
    (factors : List (SignedMode d)) (phase : UnitAddTorus d) :
    unitSignedMonomial factors phase =
      mFourier (monomialCharge factors) phase := by
  induction factors with
  | nil => simp [unitSignedMonomial, monomialCharge, mFourier_zero]
  | cons factor rest ih =>
      simp only [unitSignedMonomial, monomialCharge]
      rw [ih, SignedMode.phaseFactor_eq_mFourier]
      exact mFourier_add.symm

/-- A signed monomial multiplied by an arbitrary deterministic complex
coefficient. -/
def weightedSignedMonomial
    (coefficient : ℂ) (factors : List (SignedMode d))
    (phase : UnitAddTorus d) : ℂ :=
  coefficient * unitSignedMonomial factors phase

/-- A deterministic nonnegative real amplitude profile on the finite mode
space. -/
abbrev NonnegativeAmplitudeProfile (d : Type*) := d → NNReal

/-- The deterministic coefficient obtained by multiplying the amplitudes of
all occurrences, including repeated modes. -/
def amplitudeCoefficient
    (amplitude : NonnegativeAmplitudeProfile d)
    (factors : List (SignedMode d)) : ℂ :=
  (factors.map fun factor => ((amplitude factor.mode : ℝ) : ℂ)).prod

/-- The finite signed phase monomial carrying a nonnegative real amplitude
profile. -/
def amplitudeSignedMonomial
    (amplitude : NonnegativeAmplitudeProfile d)
    (factors : List (SignedMode d)) (phase : UnitAddTorus d) : ℂ :=
  weightedSignedMonomial (amplitudeCoefficient amplitude factors) factors phase

/-- Exact Haar expectation of a unit-amplitude finite signed monomial. -/
theorem integral_unitSignedMonomial_eq_ite
    (factors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d, unitSignedMonomial factors phase
      ∂finitePhaseHaarLaw d) =
      if monomialCharge factors = 0 then 1 else 0 := by
  simpa only [unitSignedMonomial_eq_mFourier] using
    integral_mFourier_eq_ite (monomialCharge factors)

/-- Exact Haar expectation with an arbitrary deterministic coefficient. -/
theorem integral_weightedSignedMonomial_eq_ite
    (coefficient : ℂ) (factors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      weightedSignedMonomial coefficient factors phase
      ∂finitePhaseHaarLaw d) =
      if monomialCharge factors = 0 then coefficient else 0 := by
  simp only [weightedSignedMonomial, integral_const_mul,
    integral_unitSignedMonomial_eq_ite]
  split_ifs <;> simp

/-- Exact Haar expectation for a nonnegative real amplitude profile. -/
theorem integral_amplitudeSignedMonomial_eq_ite
    (amplitude : NonnegativeAmplitudeProfile d)
    (factors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      amplitudeSignedMonomial amplitude factors phase
      ∂finitePhaseHaarLaw d) =
      if monomialCharge factors = 0 then
        amplitudeCoefficient amplitude factors else 0 := by
  simpa only [amplitudeSignedMonomial] using
    integral_weightedSignedMonomial_eq_ite
      (amplitudeCoefficient amplitude factors) factors

/-- Exact expectation of a unit-amplitude signed monomial in the actual
finite phase block of any verified ensemble. -/
theorem ensemble_unitSignedMonomial_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (factors : List (SignedMode (Lattice.Site N))) :
    (∫ omega,
      unitSignedMonomial factors (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      if monomialCharge factors = 0 then 1 else 0 := by
  simpa only [unitSignedMonomial_eq_mFourier] using
    restrictPhase_mFourier_expectation ensemble (monomialCharge factors)

/-- Exact ensemble expectation with an arbitrary deterministic coefficient. -/
theorem ensemble_weightedSignedMonomial_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (coefficient : ℂ)
    (factors : List (SignedMode (Lattice.Site N))) :
    (∫ omega,
      weightedSignedMonomial coefficient factors
        (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      if monomialCharge factors = 0 then coefficient else 0 := by
  simp only [weightedSignedMonomial, integral_const_mul,
    ensemble_unitSignedMonomial_expectation]
  split_ifs <;> simp

/-- Exact ensemble expectation for a nonnegative real amplitude profile. -/
theorem ensemble_amplitudeSignedMonomial_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (amplitude : NonnegativeAmplitudeProfile (Lattice.Site N))
    (factors : List (SignedMode (Lattice.Site N))) :
    (∫ omega,
      amplitudeSignedMonomial amplitude factors
        (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      if monomialCharge factors = 0 then
        amplitudeCoefficient amplitude factors else 0 := by
  simpa only [amplitudeSignedMonomial] using
    ensemble_weightedSignedMonomial_expectation ensemble
      (amplitudeCoefficient amplitude factors) factors

end

end ArchonPhysics.FinitePhaseMonomials
