import ArchonPhysics.PhyslibHamiltonDuhamel
import ArchonPhysics.FreeFPUTDuhamelResonanceBridge
import ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
import ArchonPhysics.NormalizedResonancePeakKernel
import ArchonPhysics.ResonanceWeightSinc

/-!
# Hamiltonian first-layer Duhamel broadening

This module isolates the exact finite-mode mechanism that precedes a wave
kinetic limit.  For the quadratic part of the finite FPUT Hamiltonian it
connects, without a kinetic equation:

* the projected Hamiltonian force along the free harmonic orbit;
* its first interaction-picture Duhamel/Picard integral;
* the signed frequency mismatch of each finite modal term;
* the exact oscillatory integral and its squared-sinc finite-time
  broadening.

The first theorem below recalls that the *true* nonlinear Physlib trajectory
has an exact Duhamel formula.  The subsequent first-layer source is obtained
by inserting the free harmonic orbit into the quadratic part of that
Hamiltonian force.  Thus the broadened kernel is an algebraic consequence of
squaring a Hamiltonian Duhamel time integral; it is not postulated from a
kinetic equation.

Only the termwise/diagonal first-layer weight is identified with the positive
squared-sinc kernel.  Squaring the complete modal sum also produces coherent
same-charge cross terms, already retained by
`FiniteHaarOscillatorySecondMoment`; this file does not discard them.  No
random-phase propagation, thermodynamic limit, diagram remainder estimate,
or microscopic-to-WKE convergence is asserted.
-/

namespace ArchonPhysics.HamiltonianFirstLayerBroadening

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.ResonanceWeightSinc
open ArchonPhysics.ReducedModeTransform

open scoped Interval

noncomputable section

/-! ## Exact Hamiltonian origin -/

/-- An actual differentiable Physlib Hamilton trajectory obeys the exact
interaction-picture Duhamel formula.  This restatement is the microscopic
origin used below; its only dynamical hypothesis is
`SatisfiesHamiltonEquations`, not a kinetic equation. -/
theorem physlibHamiltonian_interactionPicture_eq_initial_add_duhamel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t : Real) :
    phaseRenormalize (modeFrequency m k * t)
        (physlibModeAmplitude m k p q t) =
      physlibModeAmplitude m k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m kappa beta g k q s := by
  exact interactionPicture_physlibMode_eq_initial_add_integral_of_differentiable
    m kappa beta g k p q hp hq hHamilton homega t

/-- The quadratic part of the physical Hamiltonian source, after the output
mode is put in the interaction picture and all input coordinates are
evaluated on the free harmonic orbit. -/
def freeQuadraticHamiltonianRotatedSource
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  phaseFactor (modeFrequency m observed * time) *
    forcedModeSource (modeFrequency m observed)
      (-(kappa * g * distinguishedTensorContraction m
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        observed 2))

/-- The freely evaluated Hamiltonian source is literally the already
verified quadratic FPUT Picard integrand with its physical coupling. -/
theorem freeQuadraticHamiltonianRotatedSource_eq_picardIntegrand
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticHamiltonianRotatedSource
        kappa g m observed radius time phase =
      freeQuadraticPicardIntegrand
        (physicalQuadraticCoupling kappa g m observed *
          phaseFactor (modeFrequency m observed * time))
        m observed radius (modeFrequency m) time phase := by
  rw [freeQuadraticPicardIntegrand,
    freeQuadraticTensorSource_eq_complex_tensorContraction]
  unfold freeQuadraticHamiltonianRotatedSource forcedModeSource
    physicalQuadraticCoupling modeAmplitudeNormalization
  push_cast
  ring

/-- The physical quadratic first Picard correction, defined directly as the
time integral of the freely evaluated Hamiltonian force. -/
def physicalFreeQuadraticHamiltonianFirstLayer
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  ∫ s in (0 : Real)..time,
    freeQuadraticHamiltonianRotatedSource
      kappa g m observed radius s phase

/-- The direct Hamiltonian definition agrees with the existing finite FPUT
interaction-picture first Picard correction. -/
theorem physicalFreeQuadraticHamiltonianFirstLayer_eq_correction
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) :
    physicalFreeQuadraticHamiltonianFirstLayer
        kappa g m observed radius time phase =
      freeQuadraticInteractionPictureCorrection
        (physicalQuadraticCoupling kappa g m observed)
        m observed radius (modeFrequency m) time phase := by
  unfold physicalFreeQuadraticHamiltonianFirstLayer
    freeQuadraticInteractionPictureCorrection
  apply intervalIntegral.integral_congr
  intro s hs
  exact freeQuadraticHamiltonianRotatedSource_eq_picardIntegrand
    kappa g m observed radius s phase

/-! ## Fast phase, mismatch, and exact broadening -/

/-- One constant-coefficient fast-phase term produced after decomposing a
finite Hamiltonian source into modal monomials. -/
def firstLayerOscillatoryDuhamelTerm
    (coefficient : Complex) (mismatch time : Real) : Complex :=
  ∫ s in (0 : Real)..time,
    coefficient * Complex.exp ((Complex.I * mismatch) * s)

/-- Exact evaluation of a first-layer fast-phase term by the canonical
oscillatory integral. -/
theorem firstLayerOscillatoryDuhamelTerm_eq
    (coefficient : Complex) (mismatch time : Real) :
    firstLayerOscillatoryDuhamelTerm coefficient mismatch time =
      coefficient * oscillatoryIntegral mismatch time := by
  exact intervalIntegral_const_mul_mismatchExp coefficient mismatch time

/-- Away from resonance the same Hamiltonian time integral has its exact
exponential-over-mismatch form. -/
theorem firstLayerOscillatoryDuhamelTerm_eq_div
    (coefficient : Complex) {mismatch time : Real}
    (hmismatch : mismatch ≠ 0) :
    firstLayerOscillatoryDuhamelTerm coefficient mismatch time =
      coefficient *
        ((Complex.exp (Complex.I * (mismatch * time)) - 1) /
          (Complex.I * mismatch)) := by
  rw [firstLayerOscillatoryDuhamelTerm_eq,
    oscillatoryIntegral_eq_div hmismatch]

/-- Squaring one positive-time Duhamel term and dividing by elapsed time
produces exactly its coefficient weight times the finite-time broadened
resonance kernel. -/
theorem normSq_firstLayerOscillatoryDuhamelTerm_div_time_eq
    (coefficient : Complex) (mismatch : Real) {time : Real}
    (htime : 0 < time) :
    Complex.normSq
          (firstLayerOscillatoryDuhamelTerm coefficient mismatch time) /
        time =
      Complex.normSq coefficient *
        finiteTimeResonanceWeight mismatch time := by
  rw [firstLayerOscillatoryDuhamelTerm_eq,
    Complex.normSq_mul, finiteTimeResonanceWeight, if_pos htime]
  simp only [Complex.normSq_eq_norm_sq]
  ring

/-- Equivalent exact squared-sinc formula for the same first-layer
Hamiltonian Duhamel weight. -/
theorem normSq_firstLayerOscillatoryDuhamelTerm_div_time_eq_sinc
    (coefficient : Complex) (mismatch : Real) {time : Real}
    (htime : 0 < time) :
    Complex.normSq
          (firstLayerOscillatoryDuhamelTerm coefficient mismatch time) /
        time =
      Complex.normSq coefficient *
        (time * Real.sinc (mismatch * time / 2) ^ 2) := by
  rw [normSq_firstLayerOscillatoryDuhamelTerm_div_time_eq
      coefficient mismatch htime,
    finiteTimeResonanceWeight_eq_mul_sinc_sq mismatch htime]

/-- Dividing by the exact total broadening mass converts the Hamiltonian
Duhamel weight into the unit-mass finite-time resonance kernel. -/
theorem normalized_normSq_firstLayerOscillatoryDuhamelTerm_eq_kernel
    (coefficient : Complex) (mismatch : Real) {time : Real}
    (htime : 0 < time) :
    (Complex.normSq
          (firstLayerOscillatoryDuhamelTerm coefficient mismatch time) /
        time) / (2 * sincSquareMass) =
      Complex.normSq coefficient *
        normalizedFiniteTimeResonanceKernel mismatch time := by
  rw [normSq_firstLayerOscillatoryDuhamelTerm_div_time_eq
      coefficient mismatch htime]
  unfold normalizedFiniteTimeResonanceKernel
  ring

/-! ## Finite FPUT modal specialization -/

/-- Time-independent coefficient of one signed finite FPUT quadratic term,
including its initial phase character. -/
def physicalQuadraticFirstLayerCoefficient
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (term : QuadraticPhaseTerm N) : Complex :=
  freeQuadraticDuhamelCoefficient
      (physicalQuadraticCoupling kappa g m observed)
      m observed radius term *
    mFourier (quadraticPhaseCharge term) phase

/-- One signed finite FPUT Hamiltonian Duhamel term with its exact
output-minus-input resonance mismatch. -/
def physicalQuadraticFirstLayerTerm
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N))
    (term : QuadraticPhaseTerm N) : Complex :=
  firstLayerOscillatoryDuhamelTerm
    (physicalQuadraticFirstLayerCoefficient
      kappa g m observed radius phase term)
    (quadraticPhaseMismatch (modeFrequency m) observed term) time

/-- The Hamiltonian first layer is the finite sum of its signed modal
Duhamel terms.  No collision operator appears on either side. -/
theorem physicalFreeQuadraticHamiltonianFirstLayer_eq_termSum
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) :
    physicalFreeQuadraticHamiltonianFirstLayer
        kappa g m observed radius time phase =
      ∑ term : QuadraticPhaseTerm N,
        physicalQuadraticFirstLayerTerm
          kappa g m observed radius time phase term := by
  rw [physicalFreeQuadraticHamiltonianFirstLayer_eq_correction,
    freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum]
  unfold physicalQuadraticFirstLayerTerm
    physicalQuadraticFirstLayerCoefficient
    firstLayerOscillatoryDuhamelTerm
    FiniteHaarOscillatorySecondMoment.finiteHaarOscillatorySum
    FiniteHaarOscillatorySecondMoment.oscillatoryCoefficient
    finitePhaseCorrection
  apply Finset.sum_congr rfl
  intro term hterm
  rw [intervalIntegral_const_mul_mismatchExp]
  ring

/-- Initial Haar characters have unit squared norm, so the coefficient weight
of one diagonal term is independent of the initial phase. -/
theorem normSq_physicalQuadraticFirstLayerCoefficient
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (term : QuadraticPhaseTerm N) :
    Complex.normSq
        (physicalQuadraticFirstLayerCoefficient
          kappa g m observed radius phase term) =
      Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physicalQuadraticCoupling kappa g m observed)
          m observed radius term) := by
  rw [physicalQuadraticFirstLayerCoefficient, Complex.normSq_mul]
  simp only [Complex.normSq_eq_norm_sq,
    FreeFPUTDuhamelResonanceBridge.norm_mFourier_apply_eq_one,
    one_pow, mul_one]

/-- Exact diagonal first-layer FPUT rate.  The mismatch is the true signed
sum of the finite random-mass normal-mode frequencies. -/
theorem normSq_physicalQuadraticFirstLayerTerm_div_time_eq
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    {time : Real} (htime : 0 < time)
    (phase : UnitAddTorus (Lattice.Site N))
    (term : QuadraticPhaseTerm N) :
    Complex.normSq
          (physicalQuadraticFirstLayerTerm
            kappa g m observed radius time phase term) /
        time =
      Complex.normSq
          (freeQuadraticDuhamelCoefficient
            (physicalQuadraticCoupling kappa g m observed)
            m observed radius term) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed term) time := by
  unfold physicalQuadraticFirstLayerTerm
  rw [normSq_firstLayerOscillatoryDuhamelTerm_div_time_eq _ _ htime,
    normSq_physicalQuadraticFirstLayerCoefficient]

/-- Unit-mass normalized version of the exact diagonal FPUT first-layer
weight. -/
theorem normalized_normSq_physicalQuadraticFirstLayerTerm_eq_kernel
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    {time : Real} (htime : 0 < time)
    (phase : UnitAddTorus (Lattice.Site N))
    (term : QuadraticPhaseTerm N) :
    (Complex.normSq
          (physicalQuadraticFirstLayerTerm
            kappa g m observed radius time phase term) /
        time) / (2 * sincSquareMass) =
      Complex.normSq
          (freeQuadraticDuhamelCoefficient
            (physicalQuadraticCoupling kappa g m observed)
            m observed radius term) *
        normalizedFiniteTimeResonanceKernel
          (quadraticPhaseMismatch (modeFrequency m) observed term) time := by
  rw [normSq_physicalQuadraticFirstLayerTerm_div_time_eq
      kappa g m observed radius htime phase term]
  unfold normalizedFiniteTimeResonanceKernel
  ring

/-- The finite diagonal trace is exactly the sum of the corresponding
Hamiltonian coefficient weights tested against the broadened mismatch
kernel.  This is deliberately not identified with the squared norm of the
full term sum, which also contains coherent cross terms. -/
theorem sum_normSq_physicalQuadraticFirstLayerTerm_div_time_eq
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    {time : Real} (htime : 0 < time)
    (phase : UnitAddTorus (Lattice.Site N)) :
    (∑ term : QuadraticPhaseTerm N,
        Complex.normSq
            (physicalQuadraticFirstLayerTerm
              kappa g m observed radius time phase term) /
          time) =
      ∑ term : QuadraticPhaseTerm N,
        Complex.normSq
            (freeQuadraticDuhamelCoefficient
              (physicalQuadraticCoupling kappa g m observed)
              m observed radius term) *
          finiteTimeResonanceWeight
            (quadraticPhaseMismatch (modeFrequency m) observed term) time := by
  apply Finset.sum_congr rfl
  intro term hterm
  exact normSq_physicalQuadraticFirstLayerTerm_div_time_eq
    kappa g m observed radius htime phase term

end

end ArchonPhysics.HamiltonianFirstLayerBroadening
