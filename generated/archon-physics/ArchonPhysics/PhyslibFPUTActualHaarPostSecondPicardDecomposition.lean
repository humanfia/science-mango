import ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
import ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
import ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion

/-!
# Haar decomposition of the actual post-second-Picard modal energy

For a genuine phase-indexed family of Physlib Hamilton trajectories, this
module separates the exact modal energy into two parts.

* The two-step Picard amplitude is an already proved finite character family.
  Haar integration therefore keeps all and only matched-charge ordered pairs.
* The difference between the true nonlinear orbit and that amplitude is kept
  as the literal post-second-Picard interference plus remainder square.

The second part is not declared to be a finite character polynomial: such a
claim would require an additional nonlinear phase-covariance theorem.  It is
instead bounded directly by the microscopic energy-window estimate.  No RPA,
kinetic equation, diagram-remainder certificate, or independent-frequency
hypothesis is used.
-/

namespace ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0A1ChargeSeparation
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments
open scoped ComplexConjugate

noncomputable section

/- Use the normalized Haar probability measure underlying the existing
finite-phase API. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

/-! ## Exact removal of every unmatched phase-charge pair -/

/-- The finite sum of all ordered cross terms whose two charges do not
match.  It is written as an honest character sum, with the charge difference
on each ordered pair. -/
def unmatchedChargePairCharacterSum
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int)
    (phase : UnitAddTorus d) : Complex :=
  finitePhaseCorrection
    (fun pair : J × K ↦
      if leftCharge pair.1 = rightCharge pair.2 then 0
      else leftCoefficient pair.1 * starRingEnd Complex (rightCoefficient pair.2))
    (fun pair : J × K ↦ leftCharge pair.1 - rightCharge pair.2)
    phase

/-- Every unmatched ordered pair has a nonzero difference charge, so the
entire finite unmatched family has exactly zero Haar expectation. -/
theorem integral_unmatchedChargePairCharacterSum_eq_zero
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    (∫ phase : UnitAddTorus d,
      unmatchedChargePairCharacterSum leftCoefficient leftCharge
        rightCoefficient rightCharge phase ∂finitePhaseHaarLaw d) = 0 := by
  rw [show unmatchedChargePairCharacterSum leftCoefficient leftCharge
      rightCoefficient rightCharge =
      finitePhaseCorrection
        (fun pair : J × K ↦
          if leftCharge pair.1 = rightCharge pair.2 then 0
          else leftCoefficient pair.1 *
            starRingEnd Complex (rightCoefficient pair.2))
        (fun pair : J × K ↦
          leftCharge pair.1 - rightCharge pair.2) by rfl]
  rw [integral_finitePhaseCorrection_eq_zeroChargeSum]
  classical
  apply Finset.sum_eq_zero
  intro pair hpair
  by_cases hcharge : leftCharge pair.1 = rightCharge pair.2
  · simp [hcharge]
  · simp [sub_ne_zero.mpr hcharge]

/-! ## Explicit finite matched-charge polynomial -/

/-- The exact finite matched-charge polynomial of the physical `A0`, `A1`,
and complete `A2` character families.  Each `equalChargeCrossPairSum` inside
this definition is a finite ordered-pair sum; hence repeated-charge
(recollision) pairs are retained rather than diagonalized. -/
def physlibMatchedChargeTwoStepMoment
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  finiteCharacterFamilyTwoStepMomentPolynomial g
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
    (freeInitialPhaseCharge observed)
    (physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed)
    quadraticPhaseCharge
    (completeSecondPicardCoefficient m kappa beta radius observed time)
    completeSecondPicardCharge

/-- The parity separation of the one-leg `A0` charge and every two-leg `A1`
charge removes the entire order-`g` term.  All same-charge terms at orders
`g^2`, `g^3`, and `g^4` remain explicit finite sums. -/
theorem physlibMatchedChargeTwoStepMoment_eq_without_firstOrder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    physlibMatchedChargeTwoStepMoment m kappa beta g radius time observed =
      sameChargeFamilySquare
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (freeInitialPhaseCharge observed) +
        g ^ 2 * finiteCharacterFamilySecondOrderCoefficient
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (freeInitialPhaseCharge observed)
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          quadraticPhaseCharge
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge +
        g ^ 3 * equalChargeFamilyInterference
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          quadraticPhaseCharge
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge +
        g ^ 4 * sameChargeFamilySquare
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge := by
  unfold physlibMatchedChargeTwoStepMoment
    finiteCharacterFamilyTwoStepMomentPolynomial
  rw [equalChargeFamilyInterference_freeInitial_quadratic_eq_zero]
  ring

/-- Pointwise equality between the physical two-step amplitude and its three
finite character families. -/
theorem physlibTwoStepAmplitude_eq_finiteCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    twoStepPerturbedAmplitude g
        (canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed)
        (physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase time) =
      finiteCharacterFamilyTwoStepAmplitude g
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)
        quadraticPhaseCharge
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge phase := by
  unfold finiteCharacterFamilyTwoStepAmplitude
  rw [canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
      radius (modeFrequency m) phase observed homega,
    physlibQuadraticFirstPicardCoefficient_eq_characterFamily,
    physlibFPUTSecondPicardCoefficient_eq_completeCharacterFamily]

/-! ## The actual nonlinear correction -/

/-- Literal energy correction caused by adding the exact nonlinear remainder
`R` to a supplied two-step amplitude `A`: `2 Re(A conj R) + |R|^2`. -/
def postSecondPicardEnergyCorrection (A R : Complex) : Real :=
  secondMomentFirst A R + secondMomentSecond R

/-- Actual interaction-picture squared amplitude of a phase-indexed family
of microscopic Physlib trajectories. -/
def actualPhaseModalNormSq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) : Real :=
  Complex.normSq
    (phaseRenormalize (modeFrequency m observed * time)
      (physlibModeAmplitude m observed (p phase) (q phase) time))

/-- The exact phase-dependent post-second-Picard correction of the actual
trajectory.  The true remainder stays unexpanded. -/
def actualPostSecondPicardEnergyCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Real :=
  postSecondPicardEnergyCorrection
    (twoStepPerturbedAmplitude g
      (canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase observed)
      (physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed)
      (physlibFPUTSecondPicardCoefficient
        m kappa beta observed radius phase time))
    (physlibFPUTAfterSecondPicardRemainderCoefficient
      m kappa beta g observed (q phase) radius phase time)

/-- Pointwise exact decomposition for a genuine microscopic solution.  The
only initial-data condition identifies its actual initial amplitude with the
canonical radial/Haar phase used by the Picard expansion. -/
theorem actualPhaseModalNormSq_eq_twoStep_add_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (time : Real) (phase : UnitAddTorus (Lattice.Site N)) :
    actualPhaseModalNormSq m observed p q time phase =
      Complex.normSq
        (twoStepPerturbedAmplitude g
          (canonicalFreeComplexInitialAmplitude
            radius (modeFrequency m) phase observed)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time)) +
        actualPostSecondPicardEnergyCorrection
          m kappa beta g observed q radius time phase := by
  have h := normSq_interactionPicture_physlibMode_eq_twoStepPolynomial_add_remainder
    m kappa beta g observed (p phase) (q phase) (hp phase) (hq phase)
      (hHamilton phase) homega radius phase time
  rw [hinitial phase] at h
  rw [actualPhaseModalNormSq, h]
  rw [normSq_twoStepPerturbedAmplitude]
  unfold actualPostSecondPicardEnergyCorrection
    postSecondPicardEnergyCorrection
  ring

/-- Exact expectation identity requiring no measurability assumption on the
true nonlinear remainder: subtracting the displayed correction pointwise
leaves the finite matched-charge Picard moment. -/
theorem integral_actualPhaseModalNormSq_sub_correction_eq_matchedCharge
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (time : Real) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      (actualPhaseModalNormSq m observed p q time phase -
        actualPostSecondPicardEnergyCorrection
          m kappa beta g observed q radius time phase)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      physlibMatchedChargeTwoStepMoment
        m kappa beta g radius time observed := by
  calc
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
        Complex.normSq
          (twoStepPerturbedAmplitude g
            (canonicalFreeComplexInitialAmplitude
              radius (modeFrequency m) phase observed)
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed)
            (physlibFPUTSecondPicardCoefficient
              m kappa beta observed radius phase time))
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        dsimp only
        rw [actualPhaseModalNormSq_eq_twoStep_add_correction
          m kappa beta g observed p q hp hq hHamilton radius homega
            hinitial time phase]
        ring
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
        Complex.normSq
          (finiteCharacterFamilyTwoStepAmplitude g
            (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
            (freeInitialPhaseCharge observed)
            (physlibQuadraticFirstPicardCharacterCoefficient
              m kappa radius time observed)
            quadraticPhaseCharge
            (completeSecondPicardCoefficient
              m kappa beta radius observed time)
            completeSecondPicardCharge phase)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        dsimp only
        rw [physlibTwoStepAmplitude_eq_finiteCharacterFamily
          m kappa beta g radius phase time observed homega]
    _ = _ := integral_normSq_finiteCharacterFamilyTwoStepAmplitude
      g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (freeInitialPhaseCharge observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m kappa radius time observed)
      quadraticPhaseCharge
      (completeSecondPicardCoefficient
        m kappa beta radius observed time)
      completeSecondPicardCharge

/-! ## Explicit estimable envelope for the nonlinear correction -/

/-- Finite `l1` mass of deterministic character coefficients. -/
def finiteCharacterCoefficientAbsMass
    {J : Type*} [Fintype J] (coefficient : J → Complex) : Real :=
  ∑ j, ‖coefficient j‖

theorem norm_finitePhaseCorrection_le_coefficientAbsMass
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → Complex) (charge : J → d → Int)
    (phase : UnitAddTorus d) :
    ‖finitePhaseCorrection coefficient charge phase‖ ≤
      finiteCharacterCoefficientAbsMass coefficient := by
  unfold finitePhaseCorrection finiteCharacterCoefficientAbsMass
  calc
    ‖∑ j, coefficient j * mFourier (charge j) phase‖ ≤
        ∑ j, ‖coefficient j * mFourier (charge j) phase‖ :=
      norm_sum_le _ _
    _ = ∑ j, ‖coefficient j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_mFourier_apply_eq_one, mul_one]

/-- Explicit finite coefficient-mass envelope for a two-step character
amplitude. -/
def finiteCharacterTwoStepAbsMass
    {J0 J1 J2 : Type*} [Fintype J0] [Fintype J1] [Fintype J2]
    (g : Real) (zCoefficient : J0 → Complex)
    (wCoefficient : J1 → Complex) (uCoefficient : J2 → Complex) : Real :=
  finiteCharacterCoefficientAbsMass zCoefficient +
    |g| * finiteCharacterCoefficientAbsMass wCoefficient +
    g ^ 2 * finiteCharacterCoefficientAbsMass uCoefficient

theorem norm_finiteCharacterFamilyTwoStepAmplitude_le
    {d J0 J1 J2 : Type*} [Fintype d]
    [Fintype J0] [Fintype J1] [Fintype J2]
    (g : Real)
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int)
    (phase : UnitAddTorus d) :
    ‖finiteCharacterFamilyTwoStepAmplitude g zCoefficient zCharge
        wCoefficient wCharge uCoefficient uCharge phase‖ ≤
      finiteCharacterTwoStepAbsMass g zCoefficient wCoefficient uCoefficient := by
  unfold finiteCharacterFamilyTwoStepAmplitude twoStepPerturbedAmplitude
    finiteCharacterTwoStepAbsMass
  calc
    ‖finitePhaseCorrection zCoefficient zCharge phase +
        (g : Complex) * finitePhaseCorrection wCoefficient wCharge phase +
        ((g ^ 2 : Real) : Complex) *
          finitePhaseCorrection uCoefficient uCharge phase‖ ≤
      ‖finitePhaseCorrection zCoefficient zCharge phase‖ +
        ‖(g : Complex) * finitePhaseCorrection wCoefficient wCharge phase‖ +
        ‖((g ^ 2 : Real) : Complex) *
          finitePhaseCorrection uCoefficient uCharge phase‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖finitePhaseCorrection zCoefficient zCharge phase‖ +
        |g| * ‖finitePhaseCorrection wCoefficient wCharge phase‖ +
        g ^ 2 * ‖finitePhaseCorrection uCoefficient uCharge phase‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg g)]
    _ ≤ finiteCharacterCoefficientAbsMass zCoefficient +
        |g| * finiteCharacterCoefficientAbsMass wCoefficient +
        g ^ 2 * finiteCharacterCoefficientAbsMass uCoefficient := by
      exact add_le_add
        (add_le_add
          (norm_finitePhaseCorrection_le_coefficientAbsMass
            zCoefficient zCharge phase)
          (mul_le_mul_of_nonneg_left
            (norm_finitePhaseCorrection_le_coefficientAbsMass
              wCoefficient wCharge phase) (abs_nonneg g)))
        (mul_le_mul_of_nonneg_left
          (norm_finitePhaseCorrection_le_coefficientAbsMass
            uCoefficient uCharge phase) (sq_nonneg g))

theorem abs_secondMomentFirst_le (A R : Complex) :
    |secondMomentFirst A R| ≤ 2 * ‖A‖ * ‖R‖ := by
  unfold secondMomentFirst
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  calc
    2 * |(A * conj R).re| ≤ 2 * ‖A * conj R‖ := by
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ = 2 * ‖A‖ * ‖R‖ := by
      rw [norm_mul, Complex.norm_conj]
      ring

/-- Deterministic correction estimate.  It contains both the interference
with the actual nonlinear remainder and the remainder square. -/
theorem abs_postSecondPicardEnergyCorrection_le
    (A R : Complex) {Amax B : Real}
    (hAmax : 0 ≤ Amax)
    (hA : ‖A‖ ≤ Amax) (hR : ‖R‖ ≤ B) :
    |postSecondPicardEnergyCorrection A R| ≤
      2 * Amax * B + B ^ 2 := by
  have hAR : ‖A‖ * ‖R‖ ≤ Amax * B :=
    mul_le_mul hA hR (norm_nonneg R) hAmax
  have hR2 : ‖R‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg R) hR 2
  unfold postSecondPicardEnergyCorrection
  calc
    |secondMomentFirst A R + secondMomentSecond R| ≤
        |secondMomentFirst A R| + |secondMomentSecond R| := abs_add_le _ _
    _ ≤ 2 * ‖A‖ * ‖R‖ + ‖R‖ ^ 2 := by
      exact add_le_add (abs_secondMomentFirst_le A R) (by
        simp [secondMomentSecond, Complex.normSq_eq_norm_sq])
    _ ≤ 2 * Amax * B + B ^ 2 := by nlinarith

/-- Physical specialization: the actual correction is controlled by an
explicit finite coefficient sum and any supplied genuine remainder norm
bound. -/
theorem abs_actualPostSecondPicardEnergyCorrection_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (homega : 0 < modeFrequency m observed)
    {B : Real}
    (hR : ‖physlibFPUTAfterSecondPicardRemainderCoefficient
      m kappa beta g observed (q phase) radius phase time‖ ≤ B) :
    |actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time phase| ≤
      2 * finiteCharacterTwoStepAbsMass g
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          (completeSecondPicardCoefficient
            m kappa beta radius observed time) * B + B ^ 2 := by
  let Amax := finiteCharacterTwoStepAbsMass g
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
    (physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed)
    (completeSecondPicardCoefficient
      m kappa beta radius observed time)
  have hAmax : 0 ≤ Amax := by
    unfold Amax finiteCharacterTwoStepAbsMass
      finiteCharacterCoefficientAbsMass
    positivity
  have hA : ‖twoStepPerturbedAmplitude g
      (canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase observed)
      (physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed)
      (physlibFPUTSecondPicardCoefficient
        m kappa beta observed radius phase time)‖ ≤ Amax := by
    rw [physlibTwoStepAmplitude_eq_finiteCharacterFamily
      m kappa beta g radius phase time observed homega]
    exact norm_finiteCharacterFamilyTwoStepAmplitude_le
      g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (freeInitialPhaseCharge observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m kappa radius time observed)
      quadraticPhaseCharge
      (completeSecondPicardCoefficient
        m kappa beta radius observed time)
      completeSecondPicardCharge phase
  exact abs_postSecondPicardEnergyCorrection_le _ _ hAmax hA hR

/-- If the actual correction is measurable and obeys a uniform deterministic
bound, it is Haar integrable.  Measurability is deliberately explicit: it is
an analytic property of the selected nonlinear flow, not an RPA assumption. -/
theorem integrable_actualCorrection_of_measurable_of_bound
    {N : Nat} [NeZero N] (correction :
      UnitAddTorus (Lattice.Site N) → Real)
    (hmeasurable : Measurable correction) {C : Real}
    (hbound : ∀ phase, |correction phase| ≤ C) :
    Integrable correction (finitePhaseHaarLaw (Lattice.Site N)) := by
  apply Integrable.of_bound hmeasurable.aestronglyMeasurable C
  filter_upwards with phase
  simpa only [Real.norm_eq_abs] using hbound phase

/-- Once the literal nonlinear correction is integrable, the actual Haar
expectation is exactly the finite matched-charge sum plus that correction.
No term of the nonlinear correction is silently cancelled. -/
theorem integral_actualPhaseModalNormSq_eq_matchedCharge_add_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (time : Real)
    (hcorrection : Integrable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time)
      (finitePhaseHaarLaw (Lattice.Site N))) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      actualPhaseModalNormSq m observed p q time phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      physlibMatchedChargeTwoStepMoment
          m kappa beta g radius time observed +
        ∫ phase : UnitAddTorus (Lattice.Site N),
          actualPostSecondPicardEnergyCorrection
            m kappa beta g observed q radius time phase
          ∂finitePhaseHaarLaw (Lattice.Site N) := by
  let zCoefficient :=
    freeInitialPhaseCoefficient radius (modeFrequency m) observed
  let wCoefficient :=
    physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed
  let uCoefficient :=
    completeSecondPicardCoefficient m kappa beta radius observed time
  have htwoStep : Integrable (fun phase : UnitAddTorus (Lattice.Site N) ↦
      Complex.normSq
        (finiteCharacterFamilyTwoStepAmplitude g
          zCoefficient (freeInitialPhaseCharge observed)
          wCoefficient quadraticPhaseCharge
          uCoefficient completeSecondPicardCharge phase))
      (finitePhaseHaarLaw (Lattice.Site N)) := by
    have hcontinuous : Continuous (fun phase : UnitAddTorus (Lattice.Site N) ↦
        Complex.normSq
          (finiteCharacterFamilyTwoStepAmplitude g
            zCoefficient (freeInitialPhaseCharge observed)
            wCoefficient quadraticPhaseCharge
            uCoefficient completeSecondPicardCharge phase)) := by
      unfold finiteCharacterFamilyTwoStepAmplitude twoStepPerturbedAmplitude
      have hz := finitePhaseCorrection_continuous
        zCoefficient (freeInitialPhaseCharge observed)
      have hw := finitePhaseCorrection_continuous
        wCoefficient quadraticPhaseCharge
      have hu := finitePhaseCorrection_continuous
        uCoefficient completeSecondPicardCharge
      fun_prop
    exact hcontinuous.integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  calc
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
        (Complex.normSq
          (finiteCharacterFamilyTwoStepAmplitude g
            zCoefficient (freeInitialPhaseCharge observed)
            wCoefficient quadraticPhaseCharge
            uCoefficient completeSecondPicardCharge phase) +
          actualPostSecondPicardEnergyCorrection
            m kappa beta g observed q radius time phase)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        dsimp only
        dsimp only [zCoefficient, wCoefficient, uCoefficient]
        rw [← physlibTwoStepAmplitude_eq_finiteCharacterFamily
          m kappa beta g radius phase time observed homega]
        exact actualPhaseModalNormSq_eq_twoStep_add_correction
          m kappa beta g observed p q hp hq hHamilton radius homega
            hinitial time phase
    _ = (∫ phase : UnitAddTorus (Lattice.Site N),
          Complex.normSq
            (finiteCharacterFamilyTwoStepAmplitude g
              zCoefficient (freeInitialPhaseCharge observed)
              wCoefficient quadraticPhaseCharge
              uCoefficient completeSecondPicardCharge phase)
          ∂finitePhaseHaarLaw (Lattice.Site N)) +
        ∫ phase : UnitAddTorus (Lattice.Site N),
          actualPostSecondPicardEnergyCorrection
            m kappa beta g observed q radius time phase
          ∂finitePhaseHaarLaw (Lattice.Site N) :=
      integral_add htwoStep hcorrection
    _ = _ := by
      rw [integral_normSq_finiteCharacterFamilyTwoStepAmplitude]
      rfl

/-- The expectation of an integrable uniformly bounded correction has the
same explicit bound. -/
theorem abs_integral_actualCorrection_le
    {N : Nat} [NeZero N]
    (correction : UnitAddTorus (Lattice.Site N) → Real)
    (_hintegrable : Integrable correction
      (finitePhaseHaarLaw (Lattice.Site N)))
    {C : Real} (hbound : ∀ phase, |correction phase| ≤ C) :
    |∫ phase : UnitAddTorus (Lattice.Site N), correction phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤ C := by
  have h := norm_integral_le_of_norm_le_const
      (μ := finitePhaseHaarLaw (Lattice.Site N))
      (f := correction) (C := C)
      (Filter.Eventually.of_forall fun phase ↦ by
        simpa only [Real.norm_eq_abs] using hbound phase)
  rw [Measure.real, measure_univ] at h
  norm_num at h
  simpa only [Real.norm_eq_abs] using h

/-- Bundled expectation-level endpoint.  Measurability plus the explicit
uniform bound makes the literal nonlinear correction integrable; the actual
modal expectation is then the finite matched-charge diagram sum plus that
correction, whose expectation obeys the same bound. -/
theorem integral_actualPhaseModalNormSq_eq_matchedCharge_add_boundedCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (time : Real)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time))
    {C : Real}
    (hbound : ∀ phase,
      |actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time phase| ≤ C) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      actualPhaseModalNormSq m observed p q time phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
        physlibMatchedChargeTwoStepMoment
            m kappa beta g radius time observed +
          ∫ phase : UnitAddTorus (Lattice.Site N),
            actualPostSecondPicardEnergyCorrection
              m kappa beta g observed q radius time phase
            ∂finitePhaseHaarLaw (Lattice.Site N) ∧
      |∫ phase : UnitAddTorus (Lattice.Site N),
        actualPostSecondPicardEnergyCorrection
          m kappa beta g observed q radius time phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤ C := by
  have hintegrable := integrable_actualCorrection_of_measurable_of_bound
    (actualPostSecondPicardEnergyCorrection
      m kappa beta g observed q radius time) hmeasurable hbound
  exact ⟨
    integral_actualPhaseModalNormSq_eq_matchedCharge_add_correction
      m kappa beta g observed p q hp hq hHamilton radius homega hinitial
        time hintegrable,
    abs_integral_actualCorrection_le _ hintegrable hbound⟩

end

end ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
