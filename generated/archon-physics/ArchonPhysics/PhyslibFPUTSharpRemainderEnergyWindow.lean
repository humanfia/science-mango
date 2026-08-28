import ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
import ArchonPhysics.PhyslibHamiltonianFirstLayerBridge
import ArchonPhysics.FreeFPUTA0DirectCubicBridge
import ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift

/-!
# Sharpened short-window bounds for the actual FPUT Picard remainder

The energy-only post-second-Picard envelope previously bounded the actual
history defect by `actualL1 + freeL1`.  That estimate is order one even at
time zero and creates a spurious order-`|g| T` remainder after the first
Picard term has already been extracted.

Here the exact first-Duhamel estimate is converted back from the complex
interaction-picture amplitude to the real modal-position history.  On a
finite time window this gives an explicit `O((|g| + g^2) t)` defect.  The
bound retains every finite-volume tensor mass and inverse positive-mode
frequency factor.  The translation mode is handled by an explicit
zero-frequency history-matching hypothesis because the complex oscillator
amplitude is intentionally undefined there as a faithful coordinate.
-/

namespace ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow

open MeasureTheory
open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.ReducedModeTransform
open scoped Interval ComplexConjugate

noncomputable section

/-! ## Exact conversion from interaction-picture amplitude to position -/

/-- The singleton positive phase character carries the frequency of its
selected mode. -/
theorem chargeFrequency_freeInitialPhaseCharge_sharp
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (frequency : Lattice.Site N → Real) :
    chargeFrequency (freeInitialPhaseCharge observed 0) frequency =
      frequency observed := by
  classical
  unfold chargeFrequency freeInitialPhaseCharge binarySignedMode
    binaryPhaseSign SignedMode.charge
  simp only [if_pos, PhaseSign.exponent_phase]
  rw [Fintype.sum_eq_single observed]
  · simp
  · intro other hne
    simp [hne]

/-- The first unit-circle character along the physical free phase flow is
exactly multiplication by `exp (-i omega t)`. -/
theorem unitPhase_physicalFreePhaseEvolution
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) (mode : Lattice.Site N) :
    unitPhase (physicalFreePhaseEvolution frequency time phase mode) =
      phaseFactor (-(frequency mode * time)) * unitPhase (phase mode) := by
  have h := mFourier_physicalFreePhaseEvolution
    (freeInitialPhaseCharge mode 0) frequency time phase
  rw [mFourier_freeInitialPhaseCharge mode 0
      (physicalFreePhaseEvolution frequency time phase),
    mFourier_freeInitialPhaseCharge mode 0 phase,
    chargeFrequency_freeInitialPhaseCharge_sharp] at h
  rw [h]
  unfold phaseFactor
  congr 1
  push_cast
  ring

/-- `interactionPictureCorrectionCoordinate` is real-linear. -/
theorem interactionPictureCorrectionCoordinate_sub
    (omega time : Real) (left right : Complex) :
    interactionPictureCorrectionCoordinate omega time (left - right) =
      interactionPictureCorrectionCoordinate omega time left -
        interactionPictureCorrectionCoordinate omega time right := by
  unfold interactionPictureCorrectionCoordinate phaseRenormalize
  simp only [mul_sub, Complex.sub_re]
  ring

/-- Real scalar multiplication commutes with coordinate reconstruction. -/
theorem interactionPictureCorrectionCoordinate_real_smul
    (omega time g : Real) (correction : Complex) :
    interactionPictureCorrectionCoordinate omega time
        ((g : Complex) * correction) =
      g * interactionPictureCorrectionCoordinate omega time correction := by
  unfold interactionPictureCorrectionCoordinate phaseRenormalize
  rw [show phaseFactor (-(omega * time)) * ((g : Complex) * correction) =
      (g : Complex) * (phaseFactor (-(omega * time)) * correction) by ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- Coordinate reconstruction is bounded by the norm of the supplied
interaction-picture amplitude, with the exact positive-frequency factor. -/
theorem abs_interactionPictureCorrectionCoordinate_le
    {omega time : Real} (homega : 0 < omega) (correction : Complex) :
    |interactionPictureCorrectionCoordinate omega time correction| ≤
      (Real.sqrt (2 * omega) / omega) * ‖correction‖ := by
  unfold interactionPictureCorrectionCoordinate
  rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos homega]
  calc
    Real.sqrt (2 * omega) *
          |(phaseRenormalize (-(omega * time)) correction).re| / omega ≤
        Real.sqrt (2 * omega) *
          ‖phaseRenormalize (-(omega * time)) correction‖ / omega := by
      apply div_le_div_of_nonneg_right _ homega.le
      exact mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (2 * omega) / omega) * ‖correction‖ := by
      rw [norm_phaseRenormalize]
      ring

/-- Applying coordinate reconstruction to the canonical free initial
amplitude gives the freely evolved real modal coordinate. -/
theorem interactionPictureCorrectionCoordinate_canonicalFreeInitial
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (mode : Lattice.Site N) (hfrequency : 0 < frequency mode) :
    interactionPictureCorrectionCoordinate (frequency mode) time
        (canonicalFreeComplexInitialAmplitude radius frequency phase mode) =
      freeWeightedConfiguration radius frequency time phase mode := by
  rw [canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase]
  unfold interactionPictureCorrectionCoordinate phaseRenormalize
  rw [show phaseFactor (-(frequency mode * time)) *
        (((frequency mode * radius mode /
          Real.sqrt (2 * frequency mode) : Real) : Complex) *
            unitPhase (phase mode)) =
      (((frequency mode * radius mode /
          Real.sqrt (2 * frequency mode) : Real) : Complex) *
        (phaseFactor (-(frequency mode * time)) * unitPhase (phase mode))) by
      ring]
  rw [← unitPhase_physicalFreePhaseEvolution frequency time phase mode]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [freeWeightedConfiguration_apply]
  unfold freeRealModeCoordinate realPhaseModeCoordinate
  have hsqrt : Real.sqrt (2 * frequency mode) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two hfrequency)
  field_simp [hfrequency.ne', hsqrt]

/-- Exact bridge: on a positive mode, the real actual-minus-free history is
the coordinate reconstructed from the interaction-picture amplitude
difference. -/
theorem physlibModalHistoryDefect_apply_eq_interactionPictureCorrectionCoordinate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mode : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hfrequency : 0 < modeFrequency m mode)
    (hinitial : physlibModeAmplitude m mode p q 0 =
      canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase mode) :
    physlibModalHistoryDefect m q radius phase time mode =
      interactionPictureCorrectionCoordinate (modeFrequency m mode) time
        (phaseRenormalize (modeFrequency m mode * time)
            (physlibModeAmplitude m mode p q time) -
          physlibModeAmplitude m mode p q 0) := by
  rw [interactionPictureCorrectionCoordinate_sub]
  change physlibModePosition m mode q time -
      freeWeightedConfiguration radius (modeFrequency m) time phase mode =
    interactionPictureCorrectionCoordinate (modeFrequency m mode) time
        (phaseRenormalize (modeFrequency m mode * time)
          (complexModeAmplitude (modeFrequency m mode)
            (physlibModePosition m mode q time)
            (physlibModeMomentum m mode p time))) -
      interactionPictureCorrectionCoordinate (modeFrequency m mode) time
        (physlibModeAmplitude m mode p q 0)
  rw [interactionPictureCorrectionCoordinate_phaseRenormalize_complexModeAmplitude
    hfrequency]
  rw [hinitial,
    interactionPictureCorrectionCoordinate_canonicalFreeInitial
      radius (modeFrequency m) phase time mode hfrequency]

/-! ## First-Duhamel control of the complete real modal-history defect -/

/-- Exact norm-to-position recovery factor on a positive mode.  Its totalized
value is zero at the translation mode. -/
def positiveModeCoordinateRecoveryFactor
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mode : Lattice.Site N) : Real :=
  Real.sqrt (2 * modeFrequency m mode) / modeFrequency m mode

theorem positiveModeCoordinateRecoveryFactor_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mode : Lattice.Site N) :
    0 ≤ positiveModeCoordinateRecoveryFactor m mode := by
  unfold positiveModeCoordinateRecoveryFactor
  exact div_nonneg (Real.sqrt_nonneg _) (modeFrequency_nonneg m mode)

/-- Finite-volume `l1` rate obtained by applying the exact coordinate recovery
factor to the first-Duhamel source envelope of every mode. -/
def sharpHistoryDefectL1Rate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g actualBound : Real) : Real :=
  ∑ mode, positiveModeCoordinateRecoveryFactor m mode *
    firstDuhamelWindowEnvelope m kappa beta g mode actualBound

theorem firstDuhamelWindowEnvelope_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g actualBound : Real)
    (mode : Lattice.Site N) (hactualBound : 0 ≤ actualBound) :
    0 ≤ firstDuhamelWindowEnvelope
      m kappa beta g mode actualBound := by
  unfold firstDuhamelWindowEnvelope
  apply div_nonneg
  · have hM2 : 0 ≤ observedInteractionTensorAbsMass (n := 2) m mode := by
      unfold observedInteractionTensorAbsMass
      positivity
    have hM3 : 0 ≤ observedInteractionTensorAbsMass (n := 3) m mode := by
      unfold observedInteractionTensorAbsMass
      positivity
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg kappa) (abs_nonneg g)) hM2)
        (sq_nonneg actualBound))
      (mul_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg beta) (sq_nonneg g)) hM3)
        (pow_nonneg hactualBound 3))
  · exact Real.sqrt_nonneg _

theorem sharpHistoryDefectL1Rate_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g actualBound : Real)
    (hactualBound : 0 ≤ actualBound) :
    0 ≤ sharpHistoryDefectL1Rate m kappa beta g actualBound := by
  unfold sharpHistoryDefectL1Rate
  exact Finset.sum_nonneg fun mode _ ↦ mul_nonneg
    (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    (firstDuhamelWindowEnvelope_nonneg
      m kappa beta g actualBound mode hactualBound)

/-- Sharp short-window history bound.  The positive modes follow from the
exact first-Duhamel amplitude estimate.  The explicit zero-mode hypothesis is
the missing physical-coordinate datum not visible to `complexModeAmplitude`;
it is satisfied when the actual and reference translation histories match. -/
theorem modalAbsSum_physlibModalHistoryDefect_le_sharpRate_mul_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T time : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (htime : time ∈ Icc 0 T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    modalAbsSum (physlibModalHistoryDefect m q radius phase time) ≤
      sharpHistoryDefectL1Rate m kappa beta g
        (actualModalEnergyL1Envelope N mUpper kappa beta H) * time := by
  classical
  unfold modalAbsSum sharpHistoryDefectL1Rate
  calc
    ∑ mode, |physlibModalHistoryDefect m q radius phase time mode| ≤
        ∑ mode, (positiveModeCoordinateRecoveryFactor m mode *
          firstDuhamelWindowEnvelope m kappa beta g mode
            (actualModalEnergyL1Envelope N mUpper kappa beta H)) * time := by
      apply Finset.sum_le_sum
      intro mode hmode
      by_cases hfrequency : 0 < modeFrequency m mode
      · rw [physlibModalHistoryDefect_apply_eq_interactionPictureCorrectionCoordinate
          m mode p q radius phase time hfrequency (hinitial mode)]
        have hduhamel :=
          norm_interactionPicture_physlibMode_sub_initial_le_energyWindow
            m hmUpper0 hmassUpper hbeta mode p q hp hq hHamilton hfrequency
              htime.1
              (fun s hs ↦ hgauge s ⟨hs.1, hs.2.trans htime.2⟩)
              (fun s hs ↦ henergy s ⟨hs.1, hs.2.trans htime.2⟩)
        exact (abs_interactionPictureCorrectionCoordinate_le hfrequency _).trans
          ((mul_le_mul_of_nonneg_left hduhamel
            (positiveModeCoordinateRecoveryFactor_nonneg m mode)).trans_eq
              (by unfold positiveModeCoordinateRecoveryFactor; ring))
      · have hzero : modeFrequency m mode = 0 :=
          le_antisymm (le_of_not_gt hfrequency) (modeFrequency_nonneg m mode)
        rw [hzeroHistory time htime mode hzero]
        simp [positiveModeCoordinateRecoveryFactor, hzero]
    _ = (∑ mode, positiveModeCoordinateRecoveryFactor m mode *
          firstDuhamelWindowEnvelope m kappa beta g mode
            (actualModalEnergyL1Envelope N mUpper kappa beta H)) * time := by
      rw [Finset.sum_mul]

/-! ## The history remaining after subtracting the true first Picard term -/

/-- Exact positive-mode bridge for the remainder after subtracting `g A1`.
It is the coordinate reconstructed from the two literal nonlinear-history
integrals in the exact Hamiltonian first-layer decomposition. -/
theorem physlibModalHistoryAfterFirstPicardRemainder_apply_eq_coordinate_integrals
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (mode : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (hfrequency : 0 < modeFrequency m mode)
    (hinitial : physlibModeAmplitude m mode p q 0 =
      canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase mode) :
    physlibModalHistoryAfterFirstPicardRemainder
        m kappa g q radius phase time mode =
      interactionPictureCorrectionCoordinate (modeFrequency m mode) time
        ((∫ s in (0 : Real)..time,
            physlibQuadraticHistoryDifference
              m kappa g mode q radius phase s) +
          ∫ s in (0 : Real)..time,
            physlibCubicRotatedSource m beta g mode q s) := by
  rw [physlibModalHistoryAfterFirstPicardRemainder]
  change physlibModalHistoryDefect m q radius phase time mode -
      g * physlibQuadraticFirstPicardModalHistory
        m kappa radius phase time mode = _
  rw [physlibModalHistoryDefect_apply_eq_interactionPictureCorrectionCoordinate
      m mode p q radius phase time hfrequency hinitial,
    physlibQuadraticFirstPicardModalHistory_apply,
    ← interactionPictureCorrectionCoordinate_real_smul,
    ← interactionPictureCorrectionCoordinate_sub]
  congr 1
  have hexact :=
    interactionPicture_physlibMode_eq_initial_add_firstPicard_add_remainders
      m kappa beta g mode p q hp hq hHamilton hfrequency radius phase time
  rw [freeQuadraticCorrection_eq_g_mul_firstPicardCoefficient] at hexact
  rw [hexact]
  ring

/-- Supplied-bound estimate for the exact quadratic actual-minus-free history
source.  The right side vanishes with the real history defect. -/
theorem norm_physlibQuadraticHistoryDifference_le_of_l1_bounds
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed)
    {freeBound defectBound : Real}
    (hfreeBound : 0 ≤ freeBound)
    (hfree : freeHistoryL1 m radius phase time ≤ freeBound)
    (hdefect : modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) ≤ defectBound) :
    ‖physlibQuadraticHistoryDifference
        m kappa g observed q radius phase time‖ ≤
      (|kappa| * |g| *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          (2 * freeBound * defectBound + defectBound ^ 2))) /
        Real.sqrt (2 * modeFrequency m observed) := by
  have hfree0 : 0 ≤ freeHistoryL1 m radius phase time := by
    unfold freeHistoryL1
    exact modalAbsSum_nonneg _
  have hdefect0 : 0 ≤ modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) :=
    modalAbsSum_nonneg _
  have hM2 :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hcross := abs_quadraticTensorCrossContraction_le m observed
    (freeWeightedConfiguration radius (modeFrequency m) time phase)
    (physlibModalHistoryDefect m q radius phase time)
  have hcrossBound :
      |quadraticTensorCrossContraction m observed
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          (physlibModalHistoryDefect m q radius phase time)| ≤
        2 * observedInteractionTensorAbsMass (n := 2) m observed *
          freeBound * defectBound := by
    exact hcross.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hfree
        (mul_nonneg (by norm_num) hM2)) hdefect hdefect0
      (mul_nonneg (mul_nonneg (by norm_num) hM2) hfreeBound))
  have hsquare := abs_distinguishedTensorContraction_le m observed
    (physlibModalHistoryDefect m q radius phase time) (n := 2)
  have hsquarePow : modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) ^ 2 ≤
        defectBound ^ 2 := pow_le_pow_left₀ hdefect0 hdefect 2
  have hsquareBound :
      |distinguishedTensorContraction m
          (physlibModalHistoryDefect m q radius phase time) observed 2| ≤
        observedInteractionTensorAbsMass (n := 2) m observed *
          defectBound ^ 2 :=
    hsquare.trans (mul_le_mul_of_nonneg_left hsquarePow hM2)
  rw [physlibQuadraticHistoryDifference_eq_linear_add_defectSquare]
  calc
    ‖physlibQuadraticLinearHistoryRotatedSource
          m kappa g observed q radius phase time +
        physlibQuadraticDefectSquareRotatedSource
          m kappa g observed q radius phase time‖ ≤
      ‖physlibQuadraticLinearHistoryRotatedSource
          m kappa g observed q radius phase time‖ +
        ‖physlibQuadraticDefectSquareRotatedSource
          m kappa g observed q radius phase time‖ := norm_add_le _ _
    _ ≤ (|kappa| * |g| *
          (2 * observedInteractionTensorAbsMass (n := 2) m observed *
            freeBound * defectBound)) /
            Real.sqrt (2 * modeFrequency m observed) +
        (|kappa| * |g| *
          (observedInteractionTensorAbsMass (n := 2) m observed *
            defectBound ^ 2)) /
            Real.sqrt (2 * modeFrequency m observed) := by
      apply add_le_add
      · unfold physlibQuadraticLinearHistoryRotatedSource
        rw [norm_mul, norm_phaseFactor, one_mul,
          norm_forcedModeSource homega, abs_neg, abs_mul, abs_mul]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcrossBound (by positivity))
          (Real.sqrt_nonneg _)
      · unfold physlibQuadraticDefectSquareRotatedSource
        rw [norm_mul, norm_phaseFactor, one_mul,
          norm_forcedModeSource homega, abs_neg, abs_mul, abs_mul]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsquareBound (by positivity))
          (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Uniform pointwise source envelope for the amplitude left after the first
Picard correction.  Writing `D` for the first-Duhamel history-defect rate,
its quadratic-history part contains `|g| (D T + (D T)^2)` and its actual
cubic part starts at `g^2`. -/
def sharpFirstPicardRemainderSourceWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (freeBound actualBound defectRate T : Real) : Real :=
  ((|kappa| * |g| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        (2 * freeBound * (defectRate * T) + (defectRate * T) ^ 2))) +
    (|beta| * g ^ 2 *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        actualBound ^ 3))) /
    Real.sqrt (2 * modeFrequency m observed)

/-- The corresponding finite modal `l1` rate after converting every positive
output-mode amplitude remainder back to a real coordinate. -/
def sharpAfterFirstPicardHistoryL1Rate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (freeBound actualBound defectRate T : Real) : Real :=
  ∑ mode, positiveModeCoordinateRecoveryFactor m mode *
    sharpFirstPicardRemainderSourceWindowEnvelope
      m kappa beta g mode freeBound actualBound defectRate T

/-- Energy-window bound for the two exact amplitude integrals remaining after
the first Picard correction. -/
theorem norm_firstPicardAmplitudeRemainder_le_sharpWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T time : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T) (htime : time ∈ Icc 0 T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖(∫ s in (0 : Real)..time,
        physlibQuadraticHistoryDifference
          m kappa g observed q radius phase s) +
      ∫ s in (0 : Real)..time,
        physlibCubicRotatedSource m beta g observed q s‖ ≤
      sharpFirstPicardRemainderSourceWindowEnvelope
        m kappa beta g observed (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H)) T * time := by
  let actualBound := actualModalEnergyL1Envelope N mUpper kappa beta H
  let defectRate := sharpHistoryDefectL1Rate m kappa beta g actualBound
  let quadraticEnvelope :=
    (|kappa| * |g| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        (2 * radiusL1 radius * (defectRate * T) +
          (defectRate * T) ^ 2))) /
      Real.sqrt (2 * modeFrequency m observed)
  let cubicEnvelope :=
    (|beta| * g ^ 2 *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        actualBound ^ 3)) /
      Real.sqrt (2 * modeFrequency m observed)
  have henergy0 := henergy 0 ⟨le_rfl, hT⟩
  have hH : 0 ≤ H :=
    (CoerciveLatticeEnergy.hamiltonian_nonneg m hbeta g
      (asConfiguration ((realReparametrize p) 0))
      (asConfiguration ((realReparametrize q) 0))).trans henergy0
  have hactualBound0 : 0 ≤ actualBound := by
    dsimp only [actualBound]
    unfold actualModalEnergyL1Envelope
    exact mul_nonneg (by positivity) (add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hmUpper0) (by positivity))
        (div_nonneg hH
          (CoerciveCubicPotential.coercivityConstant_pos hbeta).le))
      (by norm_num))
  have hdefectRate0 : 0 ≤ defectRate :=
    sharpHistoryDefectL1Rate_nonneg
      m kappa beta g actualBound hactualBound0
  have hradius0 : 0 ≤ radiusL1 radius := by
    unfold radiusL1
    positivity
  have hquadraticPoint : ∀ s ∈ Icc 0 time,
      ‖physlibQuadraticHistoryDifference
          m kappa g observed q radius phase s‖ ≤ quadraticEnvelope := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans htime.2⟩
    have hdefect :=
      modalAbsSum_physlibModalHistoryDefect_le_sharpRate_mul_time
        m hmUpper0 hmassUpper hbeta p q hp hq hHamilton radius phase
          hinitial hsT hgauge henergy hzeroHistory
    have hdefectWindow : modalAbsSum
        (physlibModalHistoryDefect m q radius phase s) ≤ defectRate * T :=
      hdefect.trans (mul_le_mul_of_nonneg_left hsT.2 hdefectRate0)
    apply norm_physlibQuadraticHistoryDifference_le_of_l1_bounds
      m kappa g observed q radius phase s homega hradius0
    · exact modalAbsSum_freeWeightedConfiguration_le
        radius (modeFrequency m) s phase
    · exact hdefectWindow
  have hcubicPoint : ∀ s ∈ Icc 0 time,
      ‖physlibCubicRotatedSource m beta g observed q s‖ ≤
        cubicEnvelope := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans htime.2⟩
    have hactual := actualHistoryL1_le_energyEnvelope
      m hmUpper0 hmassUpper hbeta p q s (hgauge s hsT) (henergy s hsT)
    have hcurrent0 : 0 ≤ actualHistoryL1 m q s := by
      unfold actualHistoryL1
      exact modalAbsSum_nonneg _
    have hpow : actualHistoryL1 m q s ^ 3 ≤ actualBound ^ 3 :=
      pow_le_pow_left₀ hcurrent0 hactual 3
    exact (norm_physlibCubicRotatedSource_le
      m beta g observed q s homega).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow (by
              unfold observedInteractionTensorAbsMass
              positivity)) (by positivity))
          (Real.sqrt_nonneg _))
  have hquadraticIntegral :
      ‖∫ s in (0 : Real)..time,
        physlibQuadraticHistoryDifference
          m kappa g observed q radius phase s‖ ≤
        quadraticEnvelope * time := by
    calc
      _ ≤ quadraticEnvelope * |time - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        have hsIcc : s ∈ Icc 0 time := by
          simpa only [uIcc_of_le htime.1] using Set.uIoc_subset_uIcc hs
        exact hquadraticPoint s hsIcc
      _ = _ := by rw [sub_zero, abs_of_nonneg htime.1]
  have hcubicIntegral :
      ‖∫ s in (0 : Real)..time,
        physlibCubicRotatedSource m beta g observed q s‖ ≤
        cubicEnvelope * time := by
    calc
      _ ≤ cubicEnvelope * |time - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        have hsIcc : s ∈ Icc 0 time := by
          simpa only [uIcc_of_le htime.1] using Set.uIoc_subset_uIcc hs
        exact hcubicPoint s hsIcc
      _ = _ := by rw [sub_zero, abs_of_nonneg htime.1]
  calc
    _ ≤ ‖∫ s in (0 : Real)..time,
          physlibQuadraticHistoryDifference
            m kappa g observed q radius phase s‖ +
        ‖∫ s in (0 : Real)..time,
          physlibCubicRotatedSource m beta g observed q s‖ := norm_add_le _ _
    _ ≤ quadraticEnvelope * time + cubicEnvelope * time :=
      add_le_add hquadraticIntegral hcubicIntegral
    _ = sharpFirstPicardRemainderSourceWindowEnvelope
        m kappa beta g observed (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H)) T * time := by
      dsimp only [quadraticEnvelope, cubicEnvelope, defectRate, actualBound]
      unfold sharpFirstPicardRemainderSourceWindowEnvelope
      ring

/-- The real modal history remaining after subtracting `g Q1` is bounded by
the finite sum of the sharpened source envelopes.  Thus the previous
order-one `actualBound + radiusL1` term has disappeared. -/
theorem modalAbsSum_afterFirstPicardRemainder_le_sharpRate_mul_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T time : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (hT : 0 ≤ T) (htime : time ∈ Icc 0 T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    modalAbsSum
        (physlibModalHistoryAfterFirstPicardRemainder
          m kappa g q radius phase time) ≤
      sharpAfterFirstPicardHistoryL1Rate
        m kappa beta g (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H)) T * time := by
  classical
  unfold modalAbsSum sharpAfterFirstPicardHistoryL1Rate
  calc
    ∑ mode, |physlibModalHistoryAfterFirstPicardRemainder
        m kappa g q radius phase time mode| ≤
      ∑ mode, (positiveModeCoordinateRecoveryFactor m mode *
        sharpFirstPicardRemainderSourceWindowEnvelope
          m kappa beta g mode (radiusL1 radius)
            (actualModalEnergyL1Envelope N mUpper kappa beta H)
            (sharpHistoryDefectL1Rate m kappa beta g
              (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) * time := by
      apply Finset.sum_le_sum
      intro mode hmode
      by_cases hfrequency : 0 < modeFrequency m mode
      · rw [physlibModalHistoryAfterFirstPicardRemainder_apply_eq_coordinate_integrals
          m kappa beta g mode p q hp hq hHamilton radius phase time
            hfrequency (hinitial mode)]
        have hamplitude := norm_firstPicardAmplitudeRemainder_le_sharpWindow
          m hmUpper0 hmassUpper hbeta mode p q hp hq hHamilton radius phase
            hinitial hfrequency hT htime hgauge henergy hzeroHistory
        exact (abs_interactionPictureCorrectionCoordinate_le hfrequency _).trans
          ((mul_le_mul_of_nonneg_left hamplitude
            (positiveModeCoordinateRecoveryFactor_nonneg m mode)).trans_eq
              (by unfold positiveModeCoordinateRecoveryFactor; ring))
      · have hzero : modeFrequency m mode = 0 :=
          le_antisymm (le_of_not_gt hfrequency) (modeFrequency_nonneg m mode)
        unfold physlibModalHistoryAfterFirstPicardRemainder
        change |physlibModalHistoryDefect m q radius phase time mode -
            g * physlibQuadraticFirstPicardModalHistory
              m kappa radius phase time mode| ≤ _
        rw [hzeroHistory time htime mode hzero,
          physlibQuadraticFirstPicardModalHistory_eq_zero_of_modeFrequency_eq_zero
            m kappa radius phase time mode hzero]
        simp [positiveModeCoordinateRecoveryFactor, hzero]
    _ = (∑ mode, positiveModeCoordinateRecoveryFactor m mode *
        sharpFirstPicardRemainderSourceWindowEnvelope
          m kappa beta g mode (radiusL1 radius)
            (actualModalEnergyL1Envelope N mUpper kappa beta H)
            (sharpHistoryDefectL1Rate m kappa beta g
              (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) * time := by
      rw [Finset.sum_mul]

/-! ## Sharpened post-second-Picard remainder -/

theorem norm_quadraticLinearHistoryRemainder_le_of_l1_bounds
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed)
    {freeBound remainderBound : Real}
    (hfreeBound : 0 ≤ freeBound)
    (hfree : freeHistoryL1 m radius phase time ≤ freeBound)
    (hremainder : modalAbsSum
      (physlibModalHistoryAfterFirstPicardRemainder
        m kappa g q radius phase time) ≤ remainderBound) :
    ‖physlibQuadraticLinearHistoryRemainderRotatedSource
        m kappa g observed q radius phase time‖ ≤
      (|kappa| * |g| *
        (2 * observedInteractionTensorAbsMass (n := 2) m observed *
          freeBound * remainderBound)) /
        Real.sqrt (2 * modeFrequency m observed) := by
  have hM2 :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hfree0 : 0 ≤ freeHistoryL1 m radius phase time := by
    unfold freeHistoryL1
    exact modalAbsSum_nonneg _
  have hremainder0 : 0 ≤ modalAbsSum
      (physlibModalHistoryAfterFirstPicardRemainder
        m kappa g q radius phase time) := modalAbsSum_nonneg _
  have hcross := abs_quadraticTensorCrossContraction_le m observed
    (freeWeightedConfiguration radius (modeFrequency m) time phase)
    (physlibModalHistoryAfterFirstPicardRemainder
      m kappa g q radius phase time)
  have hcrossBound :
      |quadraticTensorCrossContraction m observed
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          (physlibModalHistoryAfterFirstPicardRemainder
            m kappa g q radius phase time)| ≤
        2 * observedInteractionTensorAbsMass (n := 2) m observed *
          freeBound * remainderBound :=
    hcross.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hfree
        (mul_nonneg (by norm_num) hM2)) hremainder hremainder0
      (mul_nonneg (mul_nonneg (by norm_num) hM2) hfreeBound))
  unfold physlibQuadraticLinearHistoryRemainderRotatedSource
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega, abs_neg, abs_mul, abs_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcrossBound (by positivity))
    (Real.sqrt_nonneg _)

theorem norm_quadraticDefectSquare_le_of_l1_bound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed)
    {defectBound : Real}
    (hdefect : modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) ≤ defectBound) :
    ‖physlibQuadraticDefectSquareRotatedSource
        m kappa g observed q radius phase time‖ ≤
      (|kappa| * |g| *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          defectBound ^ 2)) /
        Real.sqrt (2 * modeFrequency m observed) := by
  have hM2 :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hdefect0 : 0 ≤ modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) := modalAbsSum_nonneg _
  have hsquare := abs_distinguishedTensorContraction_le m observed
    (physlibModalHistoryDefect m q radius phase time) (n := 2)
  have hpow := pow_le_pow_left₀ hdefect0 hdefect 2
  have hsquareBound :
      |distinguishedTensorContraction m
          (physlibModalHistoryDefect m q radius phase time) observed 2| ≤
        observedInteractionTensorAbsMass (n := 2) m observed *
          defectBound ^ 2 :=
    hsquare.trans (mul_le_mul_of_nonneg_left hpow hM2)
  unfold physlibQuadraticDefectSquareRotatedSource
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega, abs_neg, abs_mul, abs_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsquareBound (by positivity))
    (Real.sqrt_nonneg _)

theorem norm_cubicHistoryRemainder_le_of_l1_bounds
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed)
    {actualBound freeBound : Real}
    (hactual : actualHistoryL1 m q time ≤ actualBound)
    (hfree : freeHistoryL1 m radius phase time ≤ freeBound) :
    ‖physlibCubicHistoryRemainderRotatedSource
        m beta g observed q radius phase time‖ ≤
      (|beta| * g ^ 2 *
        (observedInteractionTensorAbsMass (n := 3) m observed *
          (actualBound ^ 3 + freeBound ^ 3))) /
        Real.sqrt (2 * modeFrequency m observed) := by
  have hactual0 : 0 ≤ actualHistoryL1 m q time := by
    unfold actualHistoryL1
    exact modalAbsSum_nonneg _
  have hfree0 : 0 ≤ freeHistoryL1 m radius phase time := by
    unfold freeHistoryL1
    exact modalAbsSum_nonneg _
  have hactualPow := pow_le_pow_left₀ hactual0 hactual 3
  have hfreePow := pow_le_pow_left₀ hfree0 hfree 3
  have hpowers := add_le_add hactualPow hfreePow
  have hM3 :
      0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  exact (norm_cubicHistoryRemainderRotatedSource_le
    m beta g observed q radius phase time homega).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpowers hM3) (by positivity))
        (Real.sqrt_nonneg _))

/-- Sharpened source envelope after extracting the complete second Picard
coefficient.  Unlike `afterSecondPicardWindowEnvelope`, it contains no
order-one history defect. -/
def sharpAfterSecondPicardSourceWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (freeBound actualBound defectRate afterFirstRate T : Real) : Real :=
  ((|kappa| * |g| *
      (2 * observedInteractionTensorAbsMass (n := 2) m observed *
        freeBound * (afterFirstRate * T))) +
    (|kappa| * |g| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        (defectRate * T) ^ 2)) +
    (|beta| * g ^ 2 *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        (actualBound ^ 3 + freeBound ^ 3)))) /
    Real.sqrt (2 * modeFrequency m observed)

theorem sharpFirstPicardRemainderSourceWindowEnvelope_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    {freeBound actualBound defectRate T : Real}
    (hfreeBound : 0 ≤ freeBound) (hactualBound : 0 ≤ actualBound)
    (hdefectRate : 0 ≤ defectRate) (hT : 0 ≤ T) :
    0 ≤ sharpFirstPicardRemainderSourceWindowEnvelope
      m kappa beta g observed freeBound actualBound defectRate T := by
  unfold sharpFirstPicardRemainderSourceWindowEnvelope
  apply div_nonneg
  · have hM2 :
        0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
      unfold observedInteractionTensorAbsMass
      positivity
    have hM3 :
        0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
      unfold observedInteractionTensorAbsMass
      positivity
    have hDT : 0 ≤ defectRate * T := mul_nonneg hdefectRate hT
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg kappa) (abs_nonneg g))
        (mul_nonneg hM2 (add_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hfreeBound) hDT)
          (sq_nonneg (defectRate * T)))))
      (mul_nonneg
        (mul_nonneg (abs_nonneg beta) (sq_nonneg g))
        (mul_nonneg hM3 (pow_nonneg hactualBound 3)))
  · exact Real.sqrt_nonneg _

theorem sharpAfterFirstPicardHistoryL1Rate_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    {freeBound actualBound defectRate T : Real}
    (hfreeBound : 0 ≤ freeBound) (hactualBound : 0 ≤ actualBound)
    (hdefectRate : 0 ≤ defectRate) (hT : 0 ≤ T) :
    0 ≤ sharpAfterFirstPicardHistoryL1Rate
      m kappa beta g freeBound actualBound defectRate T := by
  unfold sharpAfterFirstPicardHistoryL1Rate
  exact Finset.sum_nonneg fun mode _ ↦ mul_nonneg
    (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    (sharpFirstPicardRemainderSourceWindowEnvelope_nonneg
      m kappa beta g mode hfreeBound hactualBound hdefectRate hT)

/-- Pointwise sharpened post-second-Picard source estimate on the actual
Hamiltonian energy window. -/
theorem norm_afterSecondPicardRemainderRotatedSource_le_sharpWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T time : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T) (htime : time ∈ Icc 0 T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖physlibFPUTAfterSecondPicardRemainderRotatedSource
        m kappa beta g observed q radius phase time‖ ≤
      sharpAfterSecondPicardSourceWindowEnvelope
        m kappa beta g observed (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H))
          (sharpAfterFirstPicardHistoryL1Rate
            m kappa beta g (radiusL1 radius)
              (actualModalEnergyL1Envelope N mUpper kappa beta H)
              (sharpHistoryDefectL1Rate m kappa beta g
                (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T := by
  let actualBound := actualModalEnergyL1Envelope N mUpper kappa beta H
  let defectRate := sharpHistoryDefectL1Rate m kappa beta g actualBound
  let afterFirstRate := sharpAfterFirstPicardHistoryL1Rate
    m kappa beta g (radiusL1 radius) actualBound defectRate T
  have henergy0 := henergy 0 ⟨le_rfl, hT⟩
  have hH : 0 ≤ H :=
    (CoerciveLatticeEnergy.hamiltonian_nonneg m hbeta g
      (asConfiguration ((realReparametrize p) 0))
      (asConfiguration ((realReparametrize q) 0))).trans henergy0
  have hactualBound0 : 0 ≤ actualBound := by
    dsimp only [actualBound]
    unfold actualModalEnergyL1Envelope
    exact mul_nonneg (by positivity) (add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hmUpper0) (by positivity))
        (div_nonneg hH
          (CoerciveCubicPotential.coercivityConstant_pos hbeta).le))
      (by norm_num))
  have hdefectRate0 : 0 ≤ defectRate :=
    sharpHistoryDefectL1Rate_nonneg
      m kappa beta g actualBound hactualBound0
  have hradius0 : 0 ≤ radiusL1 radius := by
    unfold radiusL1
    positivity
  have hafterFirstRate0 : 0 ≤ afterFirstRate :=
    sharpAfterFirstPicardHistoryL1Rate_nonneg
      m kappa beta g hradius0 hactualBound0 hdefectRate0 hT
  have hfree := modalAbsSum_freeWeightedConfiguration_le
    radius (modeFrequency m) time phase
  have hactual := actualHistoryL1_le_energyEnvelope
    m hmUpper0 hmassUpper hbeta p q time
      (hgauge time htime) (henergy time htime)
  have hdefect :=
    modalAbsSum_physlibModalHistoryDefect_le_sharpRate_mul_time
      m hmUpper0 hmassUpper hbeta p q hp hq hHamilton radius phase
        hinitial htime hgauge henergy hzeroHistory
  have hdefectWindow : modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) ≤ defectRate * T :=
    hdefect.trans (mul_le_mul_of_nonneg_left htime.2 hdefectRate0)
  have hafterFirst :=
    modalAbsSum_afterFirstPicardRemainder_le_sharpRate_mul_time
      m hmUpper0 hmassUpper hbeta p q hp hq hHamilton radius phase
        hinitial hT htime hgauge henergy hzeroHistory
  have hafterFirstWindow : modalAbsSum
      (physlibModalHistoryAfterFirstPicardRemainder
        m kappa g q radius phase time) ≤ afterFirstRate * T :=
    hafterFirst.trans
      (mul_le_mul_of_nonneg_left htime.2 hafterFirstRate0)
  have hlinear := norm_quadraticLinearHistoryRemainder_le_of_l1_bounds
    m kappa g observed q radius phase time homega hradius0 hfree
      hafterFirstWindow
  have hsquare := norm_quadraticDefectSquare_le_of_l1_bound
    m kappa g observed q radius phase time homega hdefectWindow
  have hcubic := norm_cubicHistoryRemainder_le_of_l1_bounds
    m beta g observed q radius phase time homega hactual hfree
  unfold physlibFPUTAfterSecondPicardRemainderRotatedSource
  calc
    ‖physlibQuadraticLinearHistoryRemainderRotatedSource
          m kappa g observed q radius phase time +
        physlibQuadraticDefectSquareRotatedSource
          m kappa g observed q radius phase time +
        physlibCubicHistoryRemainderRotatedSource
          m beta g observed q radius phase time‖ ≤
      ‖physlibQuadraticLinearHistoryRemainderRotatedSource
          m kappa g observed q radius phase time‖ +
        ‖physlibQuadraticDefectSquareRotatedSource
          m kappa g observed q radius phase time‖ +
        ‖physlibCubicHistoryRemainderRotatedSource
          m beta g observed q radius phase time‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤
      (|kappa| * |g| *
        (2 * observedInteractionTensorAbsMass (n := 2) m observed *
          radiusL1 radius * (afterFirstRate * T))) /
          Real.sqrt (2 * modeFrequency m observed) +
      (|kappa| * |g| *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          (defectRate * T) ^ 2)) /
          Real.sqrt (2 * modeFrequency m observed) +
      (|beta| * g ^ 2 *
        (observedInteractionTensorAbsMass (n := 3) m observed *
          (actualBound ^ 3 + radiusL1 radius ^ 3))) /
          Real.sqrt (2 * modeFrequency m observed) :=
      add_le_add (add_le_add hlinear hsquare) hcubic
    _ = sharpAfterSecondPicardSourceWindowEnvelope
        m kappa beta g observed (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H))
          (sharpAfterFirstPicardHistoryL1Rate
            m kappa beta g (radiusL1 radius)
              (actualModalEnergyL1Envelope N mUpper kappa beta H)
              (sharpHistoryDefectL1Rate m kappa beta g
                (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T := by
      dsimp only [actualBound, defectRate, afterFirstRate]
      unfold sharpAfterSecondPicardSourceWindowEnvelope
      ring

/-- Fully explicit integrated sharpened remainder envelope. -/
def sharpAfterSecondPicardCoefficientEnergyWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  sharpAfterSecondPicardSourceWindowEnvelope
      m kappa beta g observed (radiusL1 radius)
        (actualModalEnergyL1Envelope N mUpper kappa beta H)
        (sharpHistoryDefectL1Rate m kappa beta g
          (actualModalEnergyL1Envelope N mUpper kappa beta H))
        (sharpAfterFirstPicardHistoryL1Rate
          m kappa beta g (radiusL1 radius)
            (actualModalEnergyL1Envelope N mUpper kappa beta H)
            (sharpHistoryDefectL1Rate m kappa beta g
              (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T * T

/-- The actual post-second-Picard coefficient now has no spurious
`O(|g| T)` term.  Its displayed source begins with the genuine cubic
`g^2` contribution; all quadratic-history pieces contain the sharp
first-Duhamel defect or after-first-Picard remainder. -/
theorem norm_afterSecondPicardRemainderCoefficient_le_sharpEnergyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed q radius phase T‖ ≤
      sharpAfterSecondPicardCoefficientEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed := by
  unfold physlibFPUTAfterSecondPicardRemainderCoefficient
    sharpAfterSecondPicardCoefficientEnergyWindowEnvelope
  calc
    ‖∫ time in (0 : Real)..T,
        physlibFPUTAfterSecondPicardRemainderRotatedSource
          m kappa beta g observed q radius phase time‖ ≤
      sharpAfterSecondPicardSourceWindowEnvelope
          m kappa beta g observed (radiusL1 radius)
            (actualModalEnergyL1Envelope N mUpper kappa beta H)
            (sharpHistoryDefectL1Rate m kappa beta g
              (actualModalEnergyL1Envelope N mUpper kappa beta H))
            (sharpAfterFirstPicardHistoryL1Rate
              m kappa beta g (radiusL1 radius)
                (actualModalEnergyL1Envelope N mUpper kappa beta H)
                (sharpHistoryDefectL1Rate m kappa beta g
                  (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T *
        |T - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro time htime
      have htimeIcc : time ∈ Icc 0 T := by
        simpa only [uIcc_of_le hT] using Set.uIoc_subset_uIcc htime
      exact norm_afterSecondPicardRemainderRotatedSource_le_sharpWindow
        m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
          hinitial homega hT htimeIcc hgauge henergy hzeroHistory
    _ = _ := by rw [sub_zero, abs_of_nonneg hT]

/-- Energy-correction envelope obtained from the sharpened coefficient norm. -/
def physlibHaarSharpEnergyCorrectionEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  2 * finiteCharacterTwoStepAbsMass g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m kappa radius T observed)
      (completeSecondPicardCoefficient m kappa beta radius observed T) *
      sharpAfterSecondPicardCoefficientEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed +
    sharpAfterSecondPicardCoefficientEnergyWindowEnvelope
      m mUpper kappa beta g H radius T observed ^ 2

/-- Actual one-block Haar energy drift with the sharpened nonlinear correction.
The matched-charge part still starts exactly at `g^2`, and the new correction
contains no order-one history-defect substitution. -/
theorem abs_integral_actualPhaseModalNormSq_sub_initial_le_sharpEnergyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergy : ∀ phase, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) ≤ H)
    (hzeroHistory : ∀ phase, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q phase) radius phase s mode = 0)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T)) :
    |(∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q T phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) -
      ∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q 0 phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤
      g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius T observed +
          |g| * physlibHaarEnergyDriftC3 m kappa beta radius T observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius T observed) +
        physlibHaarSharpEnergyCorrectionEnvelope
          m mUpper kappa beta g H radius T observed := by
  apply abs_integral_actualPhaseModalNormSq_sub_initial_le_of_correction_bound
    m kappa beta g observed p q hp hq hHamilton radius homega
      (fun phase ↦ hinitial phase observed) T
      (physlibHaarSharpEnergyCorrectionEnvelope
        m mUpper kappa beta g H radius T observed) hmeasurable
  intro phase
  apply abs_actualPostSecondPicardEnergyCorrection_le
    m kappa beta g observed q radius T phase homega
  exact norm_afterSecondPicardRemainderCoefficient_le_sharpEnergyWindow
    m hmUpper0 hmassUpper hbeta observed (p phase) (q phase)
      (hp phase) (hq phase) (hHamilton phase) radius phase (hinitial phase)
      homega hT (hgauge phase) (henergy phase) (hzeroHistory phase)

end

end ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
