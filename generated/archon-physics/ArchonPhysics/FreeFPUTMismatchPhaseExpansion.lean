import ArchonPhysics.FreeFPUTTensorPhaseExpansion
import ArchonPhysics.InteractionPictureDuhamel
import ArchonPhysics.ModalPhaseMismatch

/-!
# Exact free FPUT interaction-picture mismatch expansion

The free quadratic FPUT source is already an exact finite polynomial in the
initial Haar characters.  This module makes its time oscillation explicit.
Because harmonic phases are measured in turns while `mFourier` includes the
factor `2 * pi`, a charge `q` evolves with the angular phase

`exp (-I * t * sum_j q_j * omega_j)`.

Multiplication by the output interaction-picture phase therefore produces
the exact mismatch `omega_k - sum_j q_j * omega_j`.  The final theorem
integrates the resulting finite sum and identifies every time factor with the
existing `oscillatoryIntegral`.  All statements are finite-volume identities;
no random-phase propagation or kinetic-limit hypothesis is introduced.
-/

namespace ArchonPhysics.FreeFPUTMismatchPhaseExpansion

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhaseRenormalization

open scoped Interval

noncomputable section

/-- Pairing of an integer Fourier charge with an angular-frequency vector. -/
def chargeFrequency {d : Type*} [Fintype d]
    (charge : d → Int) (frequency : d → Real) : Real :=
  ∑ mode, (charge mode : Real) * frequency mode

/-- The output interaction-picture frequency minus the frequency carried by
one input phase character. -/
def outputChargeMismatch {d : Type*} [Fintype d]
    (outputFrequency : Real) (charge : d → Int)
    (frequency : d → Real) : Real :=
  outputFrequency - chargeFrequency charge frequency

/-- A multivariate Fourier character is multiplicative under phase
translation. -/
theorem mFourier_add_phase {d : Type*} [Fintype d]
    (charge : d → Int) (left right : UnitAddTorus d) :
    mFourier charge (left + right) =
      mFourier charge left * mFourier charge right := by
  classical
  unfold mFourier
  simp only [ContinuousMap.coe_mk, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro mode hmode
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Exact time phase of a multivariate Fourier character along the physical
free orbit.  The `2 * pi` in `mFourier` cancels the conversion from angular
frequency to turns in `harmonicPhaseAdvance`. -/
theorem mFourier_physicalFreePhaseEvolution
    {d : Type*} [Fintype d]
    (charge : d → Int) (frequency : d → Real) (time : Real)
    (phase : UnitAddTorus d) :
    mFourier charge (physicalFreePhaseEvolution frequency time phase) =
      Complex.exp
          ((Complex.I * (-(chargeFrequency charge frequency) : Real)) * time) *
        mFourier charge phase := by
  classical
  rw [show physicalFreePhaseEvolution frequency time phase =
      harmonicPhaseAdvance (fun mode ↦ -frequency mode) time + phase by rfl]
  rw [mFourier_add_phase]
  congr 1
  unfold mFourier harmonicPhaseAdvance
  simp only [ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  unfold chargeFrequency
  push_cast
  field_simp [Real.pi_ne_zero]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mode hmode
  ring

/-- Multiplying a freely evolved character by the output interaction-picture
phase produces exactly the output-minus-input charge mismatch. -/
theorem phaseFactor_mul_mFourier_physicalFreePhaseEvolution
    {d : Type*} [Fintype d]
    (outputFrequency : Real) (charge : d → Int)
    (frequency : d → Real) (time : Real) (phase : UnitAddTorus d) :
    phaseFactor (outputFrequency * time) *
        mFourier charge (physicalFreePhaseEvolution frequency time phase) =
      Complex.exp
          ((Complex.I *
            (outputChargeMismatch outputFrequency charge frequency : Real)) * time) *
        mFourier charge phase := by
  rw [mFourier_physicalFreePhaseEvolution]
  unfold phaseFactor outputChargeMismatch
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Mismatch of one signed quadratic source monomial after rotating the
observed output mode. -/
def quadraticPhaseMismatch {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) : Real :=
  outputChargeMismatch (frequency observed)
    (quadraticPhaseCharge term) frequency

/-- The quadratic mismatch is literally the output frequency minus the
charge-weighted sum of the two input frequencies. -/
theorem quadraticPhaseMismatch_eq_output_sub_chargeFrequency
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    quadraticPhaseMismatch frequency observed term =
      frequency observed -
        chargeFrequency (quadraticPhaseCharge term) frequency := rfl

/-- Exact finite mismatch expansion of the freely evaluated quadratic FPUT
source after multiplication by the output interaction-picture phase and an
arbitrary time-independent coupling. -/
theorem freeQuadraticPicardIntegrand_eq_mismatchSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticPicardIntegrand
        (coupling * phaseFactor (frequency observed * time))
        m observed radius frequency time phase =
      ∑ term : QuadraticPhaseTerm N,
        (coupling * quadraticPhaseCoefficient m observed radius term *
          mFourier (quadraticPhaseCharge term) phase) *
          Complex.exp
            ((Complex.I *
              (quadraticPhaseMismatch frequency observed term : Real)) * time) := by
  classical
  rw [freeQuadraticPicardIntegrand_eq_finitePhaseCorrection]
  unfold finitePhaseCorrection
  apply Finset.sum_congr rfl
  intro term hterm
  simp only [quadraticPicardCoefficient]
  have hphase :=
    phaseFactor_mul_mFourier_physicalFreePhaseEvolution
      (frequency observed) (quadraticPhaseCharge term) frequency time phase
  have hphaseMismatch :
      phaseFactor (frequency observed * time) *
          mFourier (quadraticPhaseCharge term)
            (physicalFreePhaseEvolution frequency time phase) =
        Complex.exp
            ((Complex.I *
              (quadraticPhaseMismatch frequency observed term : Real)) * time) *
          mFourier (quadraticPhaseCharge term) phase := by
    simpa only [quadraticPhaseMismatch] using hphase
  rw [show
    ((coupling * phaseFactor (frequency observed * time)) *
        quadraticPhaseCoefficient m observed radius term) *
      mFourier (quadraticPhaseCharge term)
        (physicalFreePhaseEvolution frequency time phase) =
      (coupling * quadraticPhaseCoefficient m observed radius term) *
        (phaseFactor (frequency observed * time) *
          mFourier (quadraticPhaseCharge term)
            (physicalFreePhaseEvolution frequency time phase)) by ring]
  rw [hphaseMismatch]
  ring

/-- A constant coefficient times one mismatch exponential integrates to the
existing oscillatory factor. -/
theorem intervalIntegral_const_mul_mismatchExp
    (coefficient : Complex) (mismatch time : Real) :
    (∫ s in (0 : Real)..time, coefficient *
      Complex.exp ((Complex.I * mismatch) * s)) =
      coefficient * oscillatoryIntegral mismatch time := by
  unfold oscillatoryIntegral
  rw [intervalIntegral.integral_const_mul]

/-- Exact Duhamel-ready formula: the time integral of the freely evaluated
quadratic interaction-picture source is a finite sum of initial phase
characters multiplied by the canonical oscillatory integrals at their exact
frequency mismatches. -/
theorem intervalIntegral_freeQuadraticPicardIntegrand_eq_mismatchSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    (∫ s in (0 : Real)..time,
      freeQuadraticPicardIntegrand
        (coupling * phaseFactor (frequency observed * s))
        m observed radius frequency s phase) =
      ∑ term : QuadraticPhaseTerm N,
        (coupling * quadraticPhaseCoefficient m observed radius term *
          mFourier (quadraticPhaseCharge term) phase) *
          oscillatoryIntegral
            (quadraticPhaseMismatch frequency observed term) time := by
  classical
  calc
    (∫ s in (0 : Real)..time,
      freeQuadraticPicardIntegrand
        (coupling * phaseFactor (frequency observed * s))
        m observed radius frequency s phase) =
        ∫ s in (0 : Real)..time,
          ∑ term : QuadraticPhaseTerm N,
            (coupling * quadraticPhaseCoefficient m observed radius term *
              mFourier (quadraticPhaseCharge term) phase) *
              Complex.exp
                ((Complex.I *
                  (quadraticPhaseMismatch frequency observed term : Real)) * s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact freeQuadraticPicardIntegrand_eq_mismatchSum
        coupling m observed radius frequency s phase
    _ = ∑ term : QuadraticPhaseTerm N,
        ∫ s in (0 : Real)..time,
          (coupling * quadraticPhaseCoefficient m observed radius term *
            mFourier (quadraticPhaseCharge term) phase) *
            Complex.exp
              ((Complex.I *
                (quadraticPhaseMismatch frequency observed term : Real)) * s) := by
      apply intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume)
      intro term hterm
      exact Continuous.intervalIntegrable (μ := MeasureTheory.volume)
        (by fun_prop : Continuous (fun s : Real =>
          (coupling * quadraticPhaseCoefficient m observed radius term *
            mFourier (quadraticPhaseCharge term) phase) *
            Complex.exp
              ((Complex.I *
                (quadraticPhaseMismatch frequency observed term : Real)) * s)))
        0 time
    _ = ∑ term : QuadraticPhaseTerm N,
        (coupling * quadraticPhaseCoefficient m observed radius term *
          mFourier (quadraticPhaseCharge term) phase) *
          oscillatoryIntegral
            (quadraticPhaseMismatch frequency observed term) time := by
      apply Finset.sum_congr rfl
      intro term hterm
      exact intervalIntegral_const_mul_mismatchExp
        (coupling * quadraticPhaseCoefficient m observed radius term *
          mFourier (quadraticPhaseCharge term) phase)
        (quadraticPhaseMismatch frequency observed term) time

end

end ArchonPhysics.FreeFPUTMismatchPhaseExpansion
