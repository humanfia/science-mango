import ArchonPhysics.FreeFPUTCubicPhaseExpansion
import ArchonPhysics.PhyslibInitialModalReference
import ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

/-!
# The free initial character and the direct cubic second-Picard bridge

The free complex initial amplitude of one observed positive-frequency mode
is a single initial-phase character.  This supplies the one-term `A0` family
needed beside the already finite quadratic and cubic Picard families.

The same module identifies the direct cubic source extracted in the Physlib
second-Picard decomposition with the independently developed free cubic
phase expansion, both pointwise and after finite-time integration.  All
equalities are finite-volume identities.  No nonlinear phase propagation or
limiting assertion is made.
-/

namespace ArchonPhysics.FreeFPUTA0DirectCubicBridge

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibInitialModalReference

open scoped Interval

noncomputable section

/-! ## The one-character free initial family -/

/-- The zeroth-order family has exactly one term. -/
abbrev FreeInitialPhaseTerm := Fin 1

/-- The sole `A0` term carries one positive phase charge at the observed
mode. -/
def freeInitialPhaseCharge {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (_term : FreeInitialPhaseTerm) :
    Lattice.Site N → Int :=
  (binarySignedMode observed 0).charge

/-- Radial coefficient of the canonical free initial complex amplitude.  At
positive frequency this is the usual `omega * radius / sqrt (2 * omega)`
normalization.  The formula is totalized by Lean at zero frequency. -/
def freeInitialPhaseCoefficient {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (observed : Lattice.Site N) (_term : FreeInitialPhaseTerm) : Complex :=
  ((frequency observed * radius observed /
    Real.sqrt (2 * frequency observed) : Real) : Complex)

/-- The complex amplitude obtained from the free radial/phase position and
momentum at time zero. -/
def canonicalFreeComplexInitialAmplitude {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N) : Complex :=
  complexModeAmplitude (frequency observed)
    (freeWeightedConfiguration radius frequency 0 phase observed)
    (freeReferenceInitialModalMomentum radius frequency phase observed)

/-- At time zero the free weighted coordinate has the stated radial/phase
form. -/
theorem freeWeightedConfiguration_zero_apply
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N) :
    freeWeightedConfiguration radius frequency 0 phase observed =
      radius observed * (unitPhase (phase observed)).re := by
  simp [freeWeightedConfiguration, freeRealModeCoordinate,
    realPhaseModeCoordinate, physicalFreePhaseEvolution,
    ArchonPhysics.FiniteHarmonicHaarPhasePropagation.freeHarmonicPhaseEvolution,
    ArchonPhysics.FiniteHarmonicHaarPhasePropagation.harmonicPhaseAdvance]

/-- The sole charge character is the first phase character of the observed
mode. -/
theorem mFourier_freeInitialPhaseCharge
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (term : FreeInitialPhaseTerm)
    (phase : UnitAddTorus (Lattice.Site N)) :
    mFourier (freeInitialPhaseCharge observed term) phase =
      unitPhase (phase observed) := by
  have hcharacter :=
    SignedMode.phaseFactor_eq_mFourier
      (binarySignedMode observed 0) phase
  simpa [freeInitialPhaseCharge, binarySignedMode, binaryPhaseSign,
    SignedMode.phaseFactor, unitPhase] using hcharacter.symm

/-- Algebraic form of the initial amplitude.  This identity is totalized for
all real frequencies; physical use of `complexModeAmplitude` is restricted
below to positive frequency. -/
theorem canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N) :
    canonicalFreeComplexInitialAmplitude radius frequency phase observed =
      ((frequency observed * radius observed /
        Real.sqrt (2 * frequency observed) : Real) : Complex) *
        unitPhase (phase observed) := by
  unfold canonicalFreeComplexInitialAmplitude
  rw [freeWeightedConfiguration_zero_apply]
  apply Complex.ext
  · simp only [complexModeAmplitude_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · simp only [complexModeAmplitude_im, freeReferenceInitialModalMomentum,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    ring

/-- For a positive-frequency observed mode, the canonical free initial
amplitude is exactly a `Fin 1` finite-character correction. -/
theorem canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N)
    (_hfrequency : 0 < frequency observed) :
    canonicalFreeComplexInitialAmplitude radius frequency phase observed =
      finitePhaseCorrection
        (freeInitialPhaseCoefficient radius frequency observed)
        (freeInitialPhaseCharge observed) phase := by
  rw [canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase]
  unfold finitePhaseCorrection freeInitialPhaseCoefficient
  rw [Fin.sum_univ_one]
  rw [mFourier_freeInitialPhaseCharge]

/-- At zero frequency the totalized complex-amplitude convention returns
zero.  It therefore does not encode a possibly nonzero translation coordinate
or momentum; such a mode lies outside the positive-frequency `A0` family. -/
theorem canonicalFreeComplexInitialAmplitude_eq_zero_of_frequency_eq_zero
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N)
    (hzero : frequency observed = 0) :
    canonicalFreeComplexInitialAmplitude radius frequency phase observed = 0 := by
  rw [canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase]
  simp [hzero]

/-- The one-character family is likewise zero under the totalized
zero-frequency normalization. -/
theorem freeInitialPhaseFamily_eq_zero_of_frequency_eq_zero
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (observed : Lattice.Site N)
    (hzero : frequency observed = 0) :
    finitePhaseCorrection
        (freeInitialPhaseCoefficient radius frequency observed)
        (freeInitialPhaseCharge observed) phase = 0 := by
  unfold finitePhaseCorrection freeInitialPhaseCoefficient
  simp [hzero]

/-- Specialization to the canonical radius and phase extracted from actual
Physlib initial position and momentum. -/
theorem physlibInitialComplexAmplitude_eq_phaseFamily_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q₀ p₀ : HilbertConfiguration N)
    (observed : Lattice.Site N)
    (hfrequency : 0 < modeFrequency m observed) :
    complexModeAmplitude (modeFrequency m observed)
        (physlibInitialModalPosition m q₀ observed)
        (physlibInitialModalMomentum m p₀ observed) =
      finitePhaseCorrection
        (freeInitialPhaseCoefficient
          (physlibInitialReferenceRadius m q₀ p₀)
          (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (physlibInitialReferencePhase m q₀ p₀) := by
  rw [← complexModeAmplitude_physlibInitialReference_zero_of_pos
    m q₀ p₀ observed hfrequency]
  exact canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
    (physlibInitialReferenceRadius m q₀ p₀) (modeFrequency m)
    (physlibInitialReferencePhase m q₀ p₀) observed hfrequency

/-! ## Thin bridge to the Physlib direct cubic second-Picard term -/

/-- The direct cubic source extracted in the Physlib second-Picard module is
definitionally the independently expanded physical free cubic integrand. -/
theorem physlibFreeCubicSecondPicardRotatedSource_eq_physicalIntegrand
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibFreeCubicSecondPicardRotatedSource
        m beta observed radius phase time =
      physicalFreeCubicPicardIntegrand
        beta m observed radius (modeFrequency m) time phase := rfl

/-- The integrated direct cubic component of the Physlib `A2` coefficient. -/
def physlibFreeCubicSecondPicardCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Complex :=
  ∫ s in (0 : Real)..time,
    physlibFreeCubicSecondPicardRotatedSource
      m beta observed radius phase s

/-- The integrated direct cubic Physlib component is exactly the finite
oscillatory family from `FreeFPUTCubicPhaseExpansion`. -/
theorem physlibFreeCubicSecondPicardCoefficient_eq_oscillatoryFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibFreeCubicSecondPicardCoefficient
        m beta observed radius phase time =
      finiteHaarOscillatorySum
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (modeFrequency m observed) beta)
          m observed radius)
        cubicPhaseCharge (cubicPhaseMismatch (modeFrequency m) observed)
        time phase := by
  unfold physlibFreeCubicSecondPicardCoefficient
  exact intervalIntegral_physicalFreeCubicPicardIntegrand_eq_oscillatoryFamily
    beta m observed radius (modeFrequency m) time phase

/-- At a zero-frequency observed mode the direct cubic component vanishes,
both before and after integration. -/
theorem physlibFreeCubicSecondPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hzero : modeFrequency m observed = 0) :
    physlibFreeCubicSecondPicardCoefficient
        m beta observed radius phase time = 0 := by
  unfold physlibFreeCubicSecondPicardCoefficient
  have hsource :
      physlibFreeCubicSecondPicardRotatedSource
          m beta observed radius phase = 0 := by
    funext s
    exact physlibFreeCubicSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
        m beta observed radius phase s hzero
  rw [hsource]
  simp

end

end ArchonPhysics.FreeFPUTA0DirectCubicBridge
