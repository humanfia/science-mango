import ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
import ArchonPhysics.FreeFPUTA0DirectCubicBridge
import ArchonPhysics.RandomPhaseMoments

/-!
# Short-time nonlinear RPA moment stability for an actual Physlib block

The exact first-Duhamel energy window bounds one interaction-picture modal
amplitude by its initial value with an error of order `|g| T + g^2 T`.
This module turns that pointwise amplitude estimate into honest second- and
fourth-product moment estimates.

The deterministic algebraic constants are `2 M epsilon` for two factors and
`4 M^3 epsilon` for four factors, assuming every amplitude is bounded by `M`
and every corresponding perturbation by `epsilon`.  The final theorem applies
these bounds to a genuine phase-indexed family of Physlib Hamilton solutions
whose initial observed-mode amplitude is the canonical radial/Haar amplitude.

Measurability of the selected nonlinear flow, its uniform amplitude bound,
the positive-frequency condition, the translation gauge, and the energy
window are all explicit hypotheses.  This is one finite short-time nonlinear
block.  It neither propagates RPA to successive blocks nor reaches the
kinetic scale `T ~ g^(-2)`.
-/

namespace ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/- Use exactly the normalized product Haar law from `RandomPhaseMoments`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

/-! ## Deterministic product perturbation algebra -/

/-- A two-factor product is Lipschitz with constant `2 M` on the radius-`M`
ball. -/
theorem norm_mul_sub_mul_le_two_mul
    {a b A B : Complex} {M epsilon : Real}
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (_ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M)
    (hA : ‖A‖ ≤ M) (_hB : ‖B‖ ≤ M)
    (haA : ‖a - A‖ ≤ epsilon) (hbB : ‖b - B‖ ≤ epsilon) :
    ‖a * b - A * B‖ ≤ 2 * M * epsilon := by
  rw [show a * b - A * B = (a - A) * b + A * (b - B) by ring]
  calc
    ‖(a - A) * b + A * (b - B)‖ ≤
        ‖(a - A) * b‖ + ‖A * (b - B)‖ := norm_add_le _ _
    _ = ‖a - A‖ * ‖b‖ + ‖A‖ * ‖b - B‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ epsilon * M + M * epsilon := by
      exact add_le_add
        (mul_le_mul haA hb (norm_nonneg _) hepsilon)
        (mul_le_mul hA hbB (norm_nonneg _) hM)
    _ = 2 * M * epsilon := by ring

/-- The RPA two-point product `z₁ conjugate(z₂)`. -/
def twoPointProduct (z₁ z₂ : Complex) : Complex :=
  z₁ * starRingEnd Complex z₂

/-- Two-point product stability with the explicit constant `2 M epsilon`. -/
theorem norm_twoPointProduct_sub_le
    {z₁ z₂ w₁ w₂ : Complex} {M epsilon : Real}
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M)
    (hw₁ : ‖w₁‖ ≤ M) (hw₂ : ‖w₂‖ ≤ M)
    (h₁ : ‖z₁ - w₁‖ ≤ epsilon)
    (h₂ : ‖z₂ - w₂‖ ≤ epsilon) :
    ‖twoPointProduct z₁ z₂ - twoPointProduct w₁ w₂‖ ≤
      2 * M * epsilon := by
  apply norm_mul_sub_mul_le_two_mul hM hepsilon hz₁
    (by simpa using hz₂) hw₁ (by simpa using hw₂) h₁
  calc
    ‖(starRingEnd Complex) z₂ - (starRingEnd Complex) w₂‖ =
        ‖(starRingEnd Complex) (z₂ - w₂)‖ := by rw [map_sub]
    _ = ‖z₂ - w₂‖ := norm_star _
    _ ≤ epsilon := h₂

/-- The standard four-point RPA product. -/
def fourPointProduct (z₁ z₂ z₃ z₄ : Complex) : Complex :=
  twoPointProduct z₁ z₂ * twoPointProduct z₃ z₄

/-- Four-point product stability with the explicit constant
`4 M^3 epsilon`. -/
theorem norm_fourPointProduct_sub_le
    {z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ : Complex}
    {M epsilon : Real}
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M)
    (hz₃ : ‖z₃‖ ≤ M) (hz₄ : ‖z₄‖ ≤ M)
    (hw₁ : ‖w₁‖ ≤ M) (hw₂ : ‖w₂‖ ≤ M)
    (hw₃ : ‖w₃‖ ≤ M) (hw₄ : ‖w₄‖ ≤ M)
    (h₁ : ‖z₁ - w₁‖ ≤ epsilon)
    (h₂ : ‖z₂ - w₂‖ ≤ epsilon)
    (h₃ : ‖z₃ - w₃‖ ≤ epsilon)
    (h₄ : ‖z₄ - w₄‖ ≤ epsilon) :
    ‖fourPointProduct z₁ z₂ z₃ z₄ -
        fourPointProduct w₁ w₂ w₃ w₄‖ ≤
      4 * M ^ 3 * epsilon := by
  have hzLeft : ‖twoPointProduct z₁ z₂‖ ≤ M ^ 2 := by
    calc
      ‖twoPointProduct z₁ z₂‖ = ‖z₁‖ * ‖z₂‖ := by
        simp [twoPointProduct]
      _ ≤ M * M := mul_le_mul hz₁ hz₂ (norm_nonneg _) hM
      _ = M ^ 2 := by ring
  have hzRight : ‖twoPointProduct z₃ z₄‖ ≤ M ^ 2 := by
    calc
      ‖twoPointProduct z₃ z₄‖ = ‖z₃‖ * ‖z₄‖ := by
        simp [twoPointProduct]
      _ ≤ M * M := mul_le_mul hz₃ hz₄ (norm_nonneg _) hM
      _ = M ^ 2 := by ring
  have hwLeft : ‖twoPointProduct w₁ w₂‖ ≤ M ^ 2 := by
    calc
      ‖twoPointProduct w₁ w₂‖ = ‖w₁‖ * ‖w₂‖ := by
        simp [twoPointProduct]
      _ ≤ M * M := mul_le_mul hw₁ hw₂ (norm_nonneg _) hM
      _ = M ^ 2 := by ring
  have hwRight : ‖twoPointProduct w₃ w₄‖ ≤ M ^ 2 := by
    calc
      ‖twoPointProduct w₃ w₄‖ = ‖w₃‖ * ‖w₄‖ := by
        simp [twoPointProduct]
      _ ≤ M * M := mul_le_mul hw₃ hw₄ (norm_nonneg _) hM
      _ = M ^ 2 := by ring
  have hLeft := norm_twoPointProduct_sub_le hM hepsilon
    hz₁ hz₂ hw₁ hw₂ h₁ h₂
  have hRight := norm_twoPointProduct_sub_le hM hepsilon
    hz₃ hz₄ hw₃ hw₄ h₃ h₄
  have hproduct := norm_mul_sub_mul_le_two_mul
    (sq_nonneg M) (mul_nonneg (mul_nonneg (by positivity) hM) hepsilon)
    hzLeft hzRight hwLeft hwRight hLeft hRight
  unfold fourPointProduct
  calc
    _ ≤ 2 * M ^ 2 * (2 * M * epsilon) := hproduct
    _ = 4 * M ^ 3 * epsilon := by ring

/-! ## Single-amplitude second and fourth moments -/

theorem abs_normSq_sub_normSq_le
    {z w : Complex} {M epsilon : Real}
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M)
    (hdist : ‖z - w‖ ≤ epsilon) :
    |Complex.normSq z - Complex.normSq w| ≤ 2 * M * epsilon := by
  have hproduct := norm_twoPointProduct_sub_le hM hepsilon
    hz hz hw hw hdist hdist
  have heq :
      (((Complex.normSq z - Complex.normSq w : Real) : Complex)) =
        twoPointProduct z z - twoPointProduct w w := by
    push_cast
    simp [twoPointProduct, Complex.normSq_eq_conj_mul_self, mul_comm]
  calc
    |Complex.normSq z - Complex.normSq w| =
        ‖((Complex.normSq z - Complex.normSq w : Real) : Complex)‖ := by
      exact ((Complex.norm_real
        (Complex.normSq z - Complex.normSq w)).trans
          (Real.norm_eq_abs _)).symm
    _ = ‖twoPointProduct z z - twoPointProduct w w‖ := by rw [heq]
    _ ≤ 2 * M * epsilon := hproduct

theorem abs_normSq_sq_sub_normSq_sq_le
    {z w : Complex} {M epsilon : Real}
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M)
    (hdist : ‖z - w‖ ≤ epsilon) :
    |Complex.normSq z ^ 2 - Complex.normSq w ^ 2| ≤
      4 * M ^ 3 * epsilon := by
  have hproduct := norm_fourPointProduct_sub_le hM hepsilon
    hz hz hz hz hw hw hw hw hdist hdist hdist hdist
  have heq :
      (((Complex.normSq z ^ 2 - Complex.normSq w ^ 2 : Real) : Complex)) =
        fourPointProduct z z z z - fourPointProduct w w w w := by
    push_cast
    simp [fourPointProduct, twoPointProduct,
      Complex.normSq_eq_conj_mul_self, mul_comm, pow_two]
  calc
    |Complex.normSq z ^ 2 - Complex.normSq w ^ 2| =
        ‖((Complex.normSq z ^ 2 - Complex.normSq w ^ 2 : Real) : Complex)‖ := by
      exact ((Complex.norm_real
        (Complex.normSq z ^ 2 - Complex.normSq w ^ 2)).trans
          (Real.norm_eq_abs _)).symm
    _ = ‖fourPointProduct z z z z - fourPointProduct w w w w‖ := by
      rw [heq]
    _ ≤ 4 * M ^ 3 * epsilon := hproduct

/-! ## Canonical Haar initial moments -/

/-- Deterministic norm of the canonical radial/Haar initial amplitude. -/
def canonicalHaarInitialMagnitude
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) : Real :=
  |frequency observed * radius observed /
    Real.sqrt (2 * frequency observed)|

theorem norm_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real)
    (phase : UnitAddTorus (Site N)) (observed : Site N) :
    ‖canonicalFreeComplexInitialAmplitude radius frequency phase observed‖ =
      canonicalHaarInitialMagnitude radius frequency observed := by
  rw [canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase,
    norm_mul, norm_unitPhase]
  simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
  rfl

theorem normSq_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real)
    (phase : UnitAddTorus (Site N)) (observed : Site N) :
    Complex.normSq
        (canonicalFreeComplexInitialAmplitude radius frequency phase observed) =
      canonicalHaarInitialMagnitude radius frequency observed ^ 2 := by
  rw [Complex.normSq_eq_norm_sq,
    norm_canonicalFreeComplexInitialAmplitude]

theorem integral_normSq_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    (∫ phase : UnitAddTorus (Site N),
      Complex.normSq
        (canonicalFreeComplexInitialAmplitude radius frequency phase observed)
      ∂finitePhaseHaarLaw (Site N)) =
      canonicalHaarInitialMagnitude radius frequency observed ^ 2 := by
  simp_rw [normSq_canonicalFreeComplexInitialAmplitude]
  simp

theorem integral_normSq_sq_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    (∫ phase : UnitAddTorus (Site N),
      Complex.normSq
          (canonicalFreeComplexInitialAmplitude radius frequency phase observed) ^ 2
      ∂finitePhaseHaarLaw (Site N)) =
      canonicalHaarInitialMagnitude radius frequency observed ^ 4 := by
  simp_rw [normSq_canonicalFreeComplexInitialAmplitude]
  rw [← pow_mul]
  simp

/-! ## Bounded measurable moment transfer -/

theorem measurable_canonicalFreeComplexInitialAmplitude
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    Measurable (fun phase : UnitAddTorus (Site N) ↦
      canonicalFreeComplexInitialAmplitude radius frequency phase observed) := by
  rw [show (fun phase : UnitAddTorus (Site N) ↦
      canonicalFreeComplexInitialAmplitude radius frequency phase observed) =
      fun phase ↦
        ((frequency observed * radius observed /
          Real.sqrt (2 * frequency observed) : Real) : Complex) *
          unitPhase (phase observed) by
    funext phase
    exact canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase
      radius frequency phase observed]
  exact measurable_const.mul
    (continuous_unitPhase.measurable.comp (measurable_pi_apply observed))

theorem integrable_normSq_of_measurable_of_uniform_norm
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (amplitude : Omega → Complex) (hmeasurable : Measurable amplitude)
    {M : Real} (_hM : 0 ≤ M) (hbound : ∀ omega, ‖amplitude omega‖ ≤ M) :
    Integrable (fun omega ↦ Complex.normSq (amplitude omega)) mu := by
  apply Integrable.of_bound
    ((Complex.continuous_normSq.measurable.comp hmeasurable).aestronglyMeasurable)
    (M ^ 2)
  filter_upwards with omega
  change |Complex.normSq (amplitude omega)| ≤ M ^ 2
  rw [abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound omega) 2

theorem integrable_normSq_sq_of_measurable_of_uniform_norm
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (amplitude : Omega → Complex) (hmeasurable : Measurable amplitude)
    {M : Real} (_hM : 0 ≤ M) (hbound : ∀ omega, ‖amplitude omega‖ ≤ M) :
    Integrable (fun omega ↦ Complex.normSq (amplitude omega) ^ 2) mu := by
  have hmomentMeasurable : Measurable (fun omega ↦
      Complex.normSq (amplitude omega) ^ 2) :=
    (Complex.continuous_normSq.measurable.comp hmeasurable).pow_const 2
  apply Integrable.of_bound hmomentMeasurable.aestronglyMeasurable (M ^ 4)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Complex.normSq_eq_norm_sq]
  have hpow := pow_le_pow_left₀ (norm_nonneg (amplitude omega))
    (hbound omega) 4
  calc
    (‖amplitude omega‖ ^ 2) ^ 2 = ‖amplitude omega‖ ^ 4 := by ring
    _ ≤ M ^ 4 := hpow

/-- Expectation-level second- and fourth-moment stability on any probability
space.  Measurability and uniform boundedness are explicit. -/
theorem integral_second_and_fourth_moment_stability
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (actual initial : Omega → Complex)
    (hactualMeasurable : Measurable actual)
    (hinitialMeasurable : Measurable initial)
    {M epsilon : Real} (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hactualBound : ∀ omega, ‖actual omega‖ ≤ M)
    (hinitialBound : ∀ omega, ‖initial omega‖ ≤ M)
    (hdistance : ∀ omega, ‖actual omega - initial omega‖ ≤ epsilon) :
    |∫ omega, Complex.normSq (actual omega) ∂mu -
        ∫ omega, Complex.normSq (initial omega) ∂mu| ≤
          2 * M * epsilon ∧
      |∫ omega, Complex.normSq (actual omega) ^ 2 ∂mu -
        ∫ omega, Complex.normSq (initial omega) ^ 2 ∂mu| ≤
          4 * M ^ 3 * epsilon := by
  have hactualSecond := integrable_normSq_of_measurable_of_uniform_norm
    (mu := mu) actual hactualMeasurable hM hactualBound
  have hinitialSecond := integrable_normSq_of_measurable_of_uniform_norm
    (mu := mu) initial hinitialMeasurable hM hinitialBound
  have hactualFourth := integrable_normSq_sq_of_measurable_of_uniform_norm
    (mu := mu) actual hactualMeasurable hM hactualBound
  have hinitialFourth := integrable_normSq_sq_of_measurable_of_uniform_norm
    (mu := mu) initial hinitialMeasurable hM hinitialBound
  constructor
  · rw [← integral_sub hactualSecond hinitialSecond]
    have h := norm_integral_le_of_norm_le_const
      (μ := mu)
      (f := fun omega ↦
        Complex.normSq (actual omega) - Complex.normSq (initial omega))
      (C := 2 * M * epsilon)
      (Filter.Eventually.of_forall fun omega ↦ by
        simpa only [Real.norm_eq_abs] using
          abs_normSq_sub_normSq_le hM hepsilon
            (hactualBound omega) (hinitialBound omega) (hdistance omega))
    rw [Measure.real, measure_univ] at h
    norm_num at h
    simpa only [Real.norm_eq_abs] using h
  · rw [← integral_sub hactualFourth hinitialFourth]
    have h := norm_integral_le_of_norm_le_const
      (μ := mu)
      (f := fun omega ↦
        Complex.normSq (actual omega) ^ 2 -
          Complex.normSq (initial omega) ^ 2)
      (C := 4 * M ^ 3 * epsilon)
      (Filter.Eventually.of_forall fun omega ↦ by
        simpa only [Real.norm_eq_abs] using
          abs_normSq_sq_sub_normSq_sq_le hM hepsilon
            (hactualBound omega) (hinitialBound omega) (hdistance omega))
    rw [Measure.real, measure_univ] at h
    norm_num at h
    simpa only [Real.norm_eq_abs] using h

/-! ## Actual one-block Physlib endpoint -/

/-- Interaction-picture amplitude of one actual phase-indexed Physlib orbit. -/
def actualInteractionPictureHaarAmplitude
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (T : Real) (phase : UnitAddTorus (Site N)) : Complex :=
  phaseRenormalize (modeFrequency m observed * T)
    (physlibModeAmplitude m observed (p phase) (q phase) T)

/-- The explicit first-Duhamel error used by the approximate-RPA block. -/
def shortTimeRPABlockError
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (observed : Site N) (T : Real) : Real :=
  firstDuhamelWindowEnvelope m kappa beta g observed
      (actualModalEnergyL1Envelope N mUpper kappa beta H) * T

theorem measurable_actualInteractionPictureHaarAmplitude
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (T : Real)
    (hmeasurable : Measurable (fun phase : UnitAddTorus (Site N) ↦
      physlibModeAmplitude m observed (p phase) (q phase) T)) :
    Measurable (actualInteractionPictureHaarAmplitude m observed p q T) := by
  unfold actualInteractionPictureHaarAmplitude phaseRenormalize
  exact measurable_const.mul hmeasurable

/-- Direct pointwise bridge from the exact Hamilton orbit to its canonical
Haar initial amplitude. -/
theorem norm_actualInteractionPictureHaarAmplitude_sub_initial_le
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T →
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (radius : Site N → Real)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (phase : UnitAddTorus (Site N)) :
    ‖actualInteractionPictureHaarAmplitude m observed p q T phase -
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed‖ ≤
      shortTimeRPABlockError m mUpper kappa beta g H observed T := by
  simpa [actualInteractionPictureHaarAmplitude, shortTimeRPABlockError,
    hinitial phase] using
    norm_interactionPicture_physlibMode_sub_initial_le_energyWindow
      m hmUpper0 hmassUpper hbeta observed (p phase) (q phase)
        (hp phase) (hq phase) (hHamilton phase) homega hT
        (hgauge phase) (henergy phase)

/-- A genuine one-block nonlinear approximate-RPA theorem.  The actual
second and fourth modal moments remain within the deterministic Duhamel error
of their exact canonical Haar initial values.  The uniform amplitude bound
`M`, nonlinear-flow measurability, gauge, energy window, and positive
frequency are explicit assumptions. -/
theorem actual_physlib_shortTime_approximateRPA_moments
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T M : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T →
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (radius : Site N → Real)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (hactualMeasurable : Measurable
      (fun phase : UnitAddTorus (Site N) ↦
        physlibModeAmplitude m observed (p phase) (q phase) T))
    (hM : 0 ≤ M)
    (hactualBound : ∀ phase,
      ‖actualInteractionPictureHaarAmplitude m observed p q T phase‖ ≤ M)
    (hinitialBound : canonicalHaarInitialMagnitude
      radius (modeFrequency m) observed ≤ M) :
    |∫ phase : UnitAddTorus (Site N),
        Complex.normSq
          (actualInteractionPictureHaarAmplitude m observed p q T phase)
        ∂finitePhaseHaarLaw (Site N) -
      canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 2| ≤
        2 * M * shortTimeRPABlockError
          m mUpper kappa beta g H observed T ∧
    |∫ phase : UnitAddTorus (Site N),
        Complex.normSq
            (actualInteractionPictureHaarAmplitude m observed p q T phase) ^ 2
        ∂finitePhaseHaarLaw (Site N) -
      canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 4| ≤
        4 * M ^ 3 * shortTimeRPABlockError
          m mUpper kappa beta g H observed T := by
  let epsilon := shortTimeRPABlockError
    m mUpper kappa beta g H observed T
  have hdistance : ∀ phase : UnitAddTorus (Site N),
      ‖actualInteractionPictureHaarAmplitude m observed p q T phase -
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed‖ ≤ epsilon :=
    norm_actualInteractionPictureHaarAmplitude_sub_initial_le
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
        hgauge henergy radius hinitial
  have hepsilon : 0 ≤ epsilon :=
    (norm_nonneg
      (actualInteractionPictureHaarAmplitude m observed p q T 0 -
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) 0 observed)).trans (hdistance 0)
  have hinitialPointwise : ∀ phase : UnitAddTorus (Site N),
      ‖canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase observed‖ ≤ M := by
    intro phase
    rw [norm_canonicalFreeComplexInitialAmplitude]
    exact hinitialBound
  have hmoments := integral_second_and_fourth_moment_stability
    (finitePhaseHaarLaw (Site N))
    (actualInteractionPictureHaarAmplitude m observed p q T)
    (fun phase ↦ canonicalFreeComplexInitialAmplitude
      radius (modeFrequency m) phase observed)
    (measurable_actualInteractionPictureHaarAmplitude
      m observed p q T hactualMeasurable)
    (measurable_canonicalFreeComplexInitialAmplitude
      radius (modeFrequency m) observed)
    hM hepsilon hactualBound hinitialPointwise hdistance
  rw [integral_normSq_canonicalFreeComplexInitialAmplitude,
    integral_normSq_sq_canonicalFreeComplexInitialAmplitude] at hmoments
  exact hmoments

end


end ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
