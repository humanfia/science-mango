import ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder

/-!
# Polynomial growth and mesoscopic scales for the cubic endpoint envelope

This module audits the explicit time growth hidden in
`physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope`.

For fixed finite-volume data it constructs literal constants `Abar` and
`Sbar`.  On the mesoscopic region `1 ≤ T`, `|g| ≤ 1`,
`|g| T ≤ 1`, the unit endpoint envelope is bounded by
`2 Abar Sbar T^3 + |g|^3 Sbar^2 T^6`.  Without the last smallness
condition the globally valid polynomial is
`2 Abar Sbar T^6 + |g|^3 Sbar^2 T^8`.

Consequently, for `T(epsilon) = epsilon^(-alpha)`, the actual
`epsilon^3`-weighted endpoint envelope tends to zero for
`0 ≤ alpha < 1`.  The kinetic choice `alpha = 2` is outside that
range: the global polynomial, after multiplication by `epsilon^3`,
has exact powers `epsilon^(-9)` and `epsilon^(-10)`, and diverges
when the fixed cubic coefficient constant is positive.  This is an
audit of the endpoint estimate, not a claim about the underlying exact
dynamics.
-/

namespace ArchonPhysics.PhyslibFPUTCubicLipschitzEnvelopeMesoscopicScale

noncomputable section
open MeasureTheory Set
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion


theorem norm_nestedOscillatoryIntegral_le_sq_time
    (deltaOut deltaIn T : Real) (hT : 0 <= T) :
    ‖nestedOscillatoryIntegral deltaOut deltaIn T‖ <= T ^ 2 := by
  unfold nestedOscillatoryIntegral
  calc
    ‖∫ s in (0 : Real)..T,
        Complex.exp ((Complex.I * deltaOut) * s) *
          oscillatoryIntegral deltaIn s‖ <= T * |T - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      have hsIcc : s ∈ Icc 0 T := by
        simpa only [uIcc_of_le hT] using Set.uIoc_subset_uIcc hs
      rw [norm_mul]
      have hexp : ‖Complex.exp ((Complex.I * deltaOut) * s)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [hexp, one_mul]
      exact (norm_oscillatoryIntegral_le_abs_time deltaIn s).trans
        (by simpa only [abs_of_nonneg hsIcc.1] using hsIcc.2)
    _ = T ^ 2 := by rw [sub_zero, abs_of_nonneg hT]; ring

theorem finiteCharacterCoefficientAbsMass_oscillatory_le
    {J : Type*} [Fintype J]
    (coefficient : J -> Complex) (mismatch : J -> Real)
    (T : Real) :
    finiteCharacterCoefficientAbsMass
        (oscillatoryCoefficient coefficient mismatch T) <=
      |T| * finiteCharacterCoefficientAbsMass coefficient := by
  classical
  unfold finiteCharacterCoefficientAbsMass oscillatoryCoefficient
  calc
    (∑ j, ‖coefficient j * oscillatoryIntegral (mismatch j) T‖) <=
        ∑ j, ‖coefficient j‖ * |T| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_oscillatoryIntegral_le_abs_time (mismatch j) T)
        (norm_nonneg _)
    _ = |T| * ∑ j, ‖coefficient j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem finiteCharacterCoefficientAbsMass_nested_le_sq_time
    {J : Type*} [Fintype J]
    (coefficient : J -> Complex)
    (deltaOut deltaIn : J -> Real) (T : Real) (hT : 0 <= T) :
    finiteCharacterCoefficientAbsMass
        (fun j => coefficient j *
          nestedOscillatoryIntegral (deltaOut j) (deltaIn j) T) <=
      T ^ 2 * finiteCharacterCoefficientAbsMass coefficient := by
  classical
  unfold finiteCharacterCoefficientAbsMass
  calc
    (∑ j, ‖coefficient j *
        nestedOscillatoryIntegral (deltaOut j) (deltaIn j) T‖) <=
        ∑ j, ‖coefficient j‖ * T ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_nestedOscillatoryIntegral_le_sq_time
          (deltaOut j) (deltaIn j) T hT)
        (norm_nonneg _)
    _ = T ^ 2 * ∑ j, ‖coefficient j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

def referenceMassConstant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N) : Real :=
  finiteCharacterCoefficientAbsMass
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed) +
    finiteCharacterCoefficientAbsMass
      (freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 observed) m observed radius) +
    finiteCharacterCoefficientAbsMass
      (iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed) +
    finiteCharacterCoefficientAbsMass
      (cubicDuhamelCoefficient
        (physicalCubicUnitCoupling (modeFrequency m observed) beta)
        m observed radius)

theorem completeMass_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (T : Real) (hT : 0 <= T) :
    finiteCharacterCoefficientAbsMass
        (completeSecondPicardCoefficient m kappa beta radius observed T) <=
      T ^ 2 * finiteCharacterCoefficientAbsMass
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed) +
      T * finiteCharacterCoefficientAbsMass
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (modeFrequency m observed) beta)
          m observed radius) := by
  classical
  unfold finiteCharacterCoefficientAbsMass
  rw [Fintype.sum_sum_type]
  apply add_le_add
  · simpa only [finiteCharacterCoefficientAbsMass,
      completeSecondPicardCoefficient_inl,
      iteratedQuadraticSecondPicardNestedCoefficient,
      abs_of_nonneg hT] using
      finiteCharacterCoefficientAbsMass_nested_le_sq_time
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed)
        (iteratedQuadraticOuterMismatch m observed)
        (iteratedQuadraticInnerMismatch m) T hT
  · simpa only [finiteCharacterCoefficientAbsMass,
      completeSecondPicardCoefficient_inr,
      abs_of_nonneg hT, mul_comm] using
      finiteCharacterCoefficientAbsMass_oscillatory_le
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (modeFrequency m observed) beta)
          m observed radius)
        (cubicPhaseMismatch (modeFrequency m) observed) T

open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion


def referenceMassTimePolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  finiteCharacterCoefficientAbsMass
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed) +
    |g| * (T * finiteCharacterCoefficientAbsMass
      (freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 observed) m observed radius)) +
    g ^ 2 *
      (T ^ 2 * finiteCharacterCoefficientAbsMass
          (iteratedQuadraticSecondPicardStaticCoefficient
            m kappa radius observed) +
        T * finiteCharacterCoefficientAbsMass
          (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (modeFrequency m observed) beta)
            m observed radius))

theorem quadraticMass_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) (hT : 0 <= T) :
    finiteCharacterCoefficientAbsMass
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius T observed) <=
      T * finiteCharacterCoefficientAbsMass
        (freeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 observed) m observed radius) := by
  simpa only [physlibQuadraticFirstPicardCharacterCoefficient,
    abs_of_nonneg hT, mul_comm] using
    finiteCharacterCoefficientAbsMass_oscillatory_le
      (freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 observed) m observed radius)
      (quadraticPhaseMismatch (modeFrequency m) observed) T

theorem twoStepMass_le_timePolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) (hT : 0 <= T) :
    finiteCharacterTwoStepAbsMass g
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius T observed)
        (completeSecondPicardCoefficient
          m kappa beta radius observed T) <=
      referenceMassTimePolynomial m kappa beta g radius T observed := by
  unfold finiteCharacterTwoStepAbsMass referenceMassTimePolynomial
  exact add_le_add
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        (quadraticMass_le m kappa radius T observed hT) (abs_nonneg g)))
    (mul_le_mul_of_nonneg_left
      (completeMass_le m kappa beta radius observed T hT) (sq_nonneg g))

theorem referenceMassTimePolynomial_le_constant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hT : 0 <= T) (hg : |g| <= 1) (hgT : |g| * T <= 1) :
    referenceMassTimePolynomial m kappa beta g radius T observed <=
      referenceMassConstant m kappa beta radius observed := by
  let Z := finiteCharacterCoefficientAbsMass
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
  let W := finiteCharacterCoefficientAbsMass
    (freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling m kappa 1 observed) m observed radius)
  let Q := finiteCharacterCoefficientAbsMass
    (iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed)
  let C := finiteCharacterCoefficientAbsMass
    (cubicDuhamelCoefficient
      (physicalCubicUnitCoupling (modeFrequency m observed) beta)
      m observed radius)
  have hW : 0 <= W := by
    dsimp only [W, finiteCharacterCoefficientAbsMass]
    positivity
  have hQ : 0 <= Q := by
    dsimp only [Q, finiteCharacterCoefficientAbsMass]
    positivity
  have hC : 0 <= C := by
    dsimp only [C, finiteCharacterCoefficientAbsMass]
    positivity
  have hg0 : 0 <= |g| := abs_nonneg g
  have hgt0 : 0 <= |g| * T := mul_nonneg hg0 hT
  have hgt2 : (|g| * T) ^ 2 <= 1 := by nlinarith
  have hlinear : |g| * (T * W) <= W := by nlinarith
  have hquadratic : |g| ^ 2 * (T ^ 2 * Q) <= Q := by nlinarith
  have hcubic : |g| ^ 2 * (T * C) <= C := by
    have hx : |g| ^ 2 * T <= 1 := by nlinarith
    nlinarith
  change Z + |g| * (T * W) + g ^ 2 * (T ^ 2 * Q + T * C) <=
    Z + W + Q + C
  rw [← sq_abs]
  nlinarith

open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow


def defectUnitConstant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta actualBound : Real) : Real :=
  sharpHistoryDefectL1UnitRate m kappa beta 1 actualBound

def afterFirstUnitConstant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (freeBound actualBound : Real) : Real :=
  sharpAfterFirstPicardHistoryL1UnitRate m kappa beta 1
    freeBound actualBound
    (defectUnitConstant m kappa beta actualBound) 1

theorem afterFirst_algebra
    (K2 K3 F A D Db x T : Real)
    (hK2 : 0 <= K2) (hK3 : 0 <= K3) (hF : 0 <= F)
    (hA : 0 <= A) (hT : 0 <= T)
    (hlin : D * T <= Db * T)
    (hquad : x * (D * T) ^ 2 <= Db ^ 2 * T)
    (hconst : A ^ 3 <= A ^ 3 * T) :
    K2 * (2 * F * (D * T) + x * (D * T) ^ 2) + K3 * A ^ 3 <=
      (K2 * (2 * F * Db + Db ^ 2) + K3 * A ^ 3) * T := by
  have hlinTerm : K2 * (2 * F * (D * T)) <=
      (K2 * (2 * F * Db)) * T := by
    calc
      K2 * (2 * F * (D * T)) <= K2 * (2 * F * (Db * T)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlin (by positivity)) hK2
      _ = (K2 * (2 * F * Db)) * T := by ring
  have hquadTerm : K2 * (x * (D * T) ^ 2) <=
      (K2 * Db ^ 2) * T := by
    calc
      _ <= K2 * (Db ^ 2 * T) := mul_le_mul_of_nonneg_left hquad hK2
      _ = _ := by ring
  have hconstTerm : K3 * A ^ 3 <= (K3 * A ^ 3) * T := by
    calc
      _ <= K3 * (A ^ 3 * T) := mul_le_mul_of_nonneg_left hconst hK3
      _ = _ := by ring
  rw [show K2 * (2 * F * (D * T) + x * (D * T) ^ 2) + K3 * A ^ 3 =
      K2 * (2 * F * (D * T)) + K2 * (x * (D * T) ^ 2) +
        K3 * A ^ 3 by ring]
  rw [show (K2 * (2 * F * Db + Db ^ 2) + K3 * A ^ 3) * T =
      (K2 * (2 * F * Db)) * T + (K2 * Db ^ 2) * T +
        (K3 * A ^ 3) * T by ring]
  exact add_le_add (add_le_add hlinTerm hquadTerm) hconstTerm

theorem sharpHistoryDefectL1UnitRate_le_constant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g actualBound : Real)
    (hactual : 0 <= actualBound) (hg : |g| <= 1) :
    sharpHistoryDefectL1UnitRate m kappa beta g actualBound <=
      defectUnitConstant m kappa beta actualBound := by
  classical
  unfold defectUnitConstant sharpHistoryDefectL1UnitRate
  apply Finset.sum_le_sum
  intro mode hmode
  apply mul_le_mul_of_nonneg_left _
    (positiveModeCoordinateRecoveryFactor_nonneg m mode)
  unfold firstDuhamelWindowUnitCouplingEnvelope
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hterm : 0 <= |beta| *
      observedInteractionTensorAbsMass (n := 3) m mode *
        actualBound ^ 3 := by
    exact mul_nonneg (mul_nonneg (abs_nonneg beta) hM3)
      (pow_nonneg hactual 3)
  simp only [abs_one]
  nlinarith

theorem defectUnitConstant_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta actualBound : Real)
    (hactual : 0 <= actualBound) :
    0 <= defectUnitConstant m kappa beta actualBound := by
  classical
  unfold defectUnitConstant sharpHistoryDefectL1UnitRate
    firstDuhamelWindowUnitCouplingEnvelope
  simp only [abs_one, mul_one]
  apply Finset.sum_nonneg
  intro mode hmode
  apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
  apply div_nonneg
  · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
      unfold observedInteractionTensorAbsMass
      positivity
    have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
      unfold observedInteractionTensorAbsMass
      positivity
    exact add_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg kappa) hM2)
        (sq_nonneg actualBound))
      (mul_nonneg (mul_nonneg (abs_nonneg beta) hM3)
        (pow_nonneg hactual 3))
  · exact Real.sqrt_nonneg _

theorem afterFirstUnitConstant_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (freeBound actualBound : Real)
    (hfree : 0 <= freeBound) (hactual : 0 <= actualBound) :
    0 <= afterFirstUnitConstant m kappa beta freeBound actualBound := by
  classical
  have hD := defectUnitConstant_nonneg m kappa beta actualBound hactual
  unfold afterFirstUnitConstant sharpAfterFirstPicardHistoryL1UnitRate
    sharpFirstPicardRemainderSourceWindowUnitEnvelope
  simp only [abs_one, one_mul, mul_one]
  apply Finset.sum_nonneg
  intro mode hmode
  apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
  apply div_nonneg
  · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
      unfold observedInteractionTensorAbsMass
      positivity
    have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
      unfold observedInteractionTensorAbsMass
      positivity
    exact add_nonneg
      (mul_nonneg (abs_nonneg kappa)
        (mul_nonneg hM2 (add_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hfree) hD)
          (sq_nonneg (defectUnitConstant m kappa beta actualBound)))))
      (mul_nonneg (abs_nonneg beta)
        (mul_nonneg hM3 (pow_nonneg hactual 3)))
  · exact Real.sqrt_nonneg _

theorem sharpAfterFirstPicardHistoryL1UnitRate_le_constant_mul_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (freeBound actualBound T : Real)
    (hfree : 0 <= freeBound) (hactual : 0 <= actualBound)
    (hT : 1 <= T) (hg : |g| <= 1) (hgT : |g| * T <= 1) :
    sharpAfterFirstPicardHistoryL1UnitRate m kappa beta g
        freeBound actualBound
        (sharpHistoryDefectL1UnitRate m kappa beta g actualBound) T <=
      afterFirstUnitConstant m kappa beta freeBound actualBound * T := by
  classical
  let D := sharpHistoryDefectL1UnitRate m kappa beta g actualBound
  let Dbar := defectUnitConstant m kappa beta actualBound
  have hD0 : 0 <= D := by
    unfold D sharpHistoryDefectL1UnitRate
      firstDuhamelWindowUnitCouplingEnvelope
    apply Finset.sum_nonneg
    intro mode hmode
    apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    apply div_nonneg
    · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      exact add_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg kappa) hM2)
          (sq_nonneg actualBound))
        (mul_nonneg (mul_nonneg
          (mul_nonneg (abs_nonneg beta) (abs_nonneg g)) hM3)
          (pow_nonneg hactual 3))
    · exact Real.sqrt_nonneg _
  have hDbar0 : 0 <= Dbar :=
    defectUnitConstant_nonneg m kappa beta actualBound hactual
  have hD : D <= Dbar :=
    sharpHistoryDefectL1UnitRate_le_constant
      m kappa beta g actualBound hactual hg
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hg0 : 0 <= |g| := abs_nonneg g
  unfold afterFirstUnitConstant sharpAfterFirstPicardHistoryL1UnitRate
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro mode hmode
  rw [show positiveModeCoordinateRecoveryFactor m mode *
      sharpFirstPicardRemainderSourceWindowUnitEnvelope m kappa beta 1 mode
        freeBound actualBound
          (defectUnitConstant m kappa beta actualBound) 1 * T =
      positiveModeCoordinateRecoveryFactor m mode *
        (sharpFirstPicardRemainderSourceWindowUnitEnvelope m kappa beta 1 mode
          freeBound actualBound
            (defectUnitConstant m kappa beta actualBound) 1 * T) by ring]
  apply mul_le_mul_of_nonneg_left _
    (positiveModeCoordinateRecoveryFactor_nonneg m mode)
  unfold sharpFirstPicardRemainderSourceWindowUnitEnvelope
  simp only [abs_one, one_mul, mul_one]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hlin : D * T <= Dbar * T :=
    mul_le_mul_of_nonneg_right hD hT0
  have hsq : D ^ 2 <= Dbar ^ 2 := (sq_le_sq₀ hD0 hDbar0).2 hD
  have hquad : |g| * (D * T) ^ 2 <= Dbar ^ 2 * T := by
    calc
      |g| * (D * T) ^ 2 = (D ^ 2 * T) * (|g| * T) := by ring
      _ <= (Dbar ^ 2 * T) * 1 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hsq hT0) hgT
          (mul_nonneg hg0 hT0) (mul_nonneg (sq_nonneg Dbar) hT0)
      _ = Dbar ^ 2 * T := by ring
  have hconst : actualBound ^ 3 <= actualBound ^ 3 * T := by
    have hA3 : 0 <= actualBound ^ 3 := pow_nonneg hactual 3
    nlinarith
  change
    |kappa| * (observedInteractionTensorAbsMass (n := 2) m mode *
      (2 * freeBound * (D * T) + |g| * (D * T) ^ 2)) +
      |beta| * (observedInteractionTensorAbsMass (n := 3) m mode *
        actualBound ^ 3) <=
    (|kappa| * (observedInteractionTensorAbsMass (n := 2) m mode *
      (2 * freeBound * Dbar + Dbar ^ 2)) +
      |beta| * (observedInteractionTensorAbsMass (n := 3) m mode *
        actualBound ^ 3)) * T
  simpa only [mul_assoc] using afterFirst_algebra
    (|kappa| * observedInteractionTensorAbsMass (n := 2) m mode)
    (|beta| * observedInteractionTensorAbsMass (n := 3) m mode)
    freeBound actualBound D Dbar |g| T
    (mul_nonneg (abs_nonneg kappa) hM2)
    (mul_nonneg (abs_nonneg beta) hM3) hfree hactual hT0
    hlin hquad hconst

open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow


def coefficientUnitCubicConstant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta H : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N) : Real :=
  cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
    m kappa beta observed (radiusL1 radius)
      (actualModalEnergyL1Envelope N mUpper kappa beta H)
      (defectUnitConstant m kappa beta
        (actualModalEnergyL1Envelope N mUpper kappa beta H))
      (afterFirstUnitConstant m kappa beta (radiusL1 radius)
        (actualModalEnergyL1Envelope N mUpper kappa beta H)) 1

private theorem source_algebra
    (K2 K3 F C D Db P Pb T : Real)
    (hK2 : 0 <= K2) (hK3 : 0 <= K3) (hF : 0 <= F) (hC : 0 <= C)
    (hD0 : 0 <= D) (hDb0 : 0 <= Db)
    (hD : D <= Db) (hP : P <= Pb * T) (hT : 1 <= T) :
    K2 * (2 * F * (P * T)) + K2 * (D * T) ^ 2 +
        K3 * ((D * T) * C) <=
      (K2 * (2 * F * Pb) + K2 * Db ^ 2 + K3 * (Db * C)) * T ^ 2 := by
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hTsq : T <= T ^ 2 := by nlinarith
  have hPT : P * T <= Pb * T ^ 2 := by
    calc
      P * T <= (Pb * T) * T := mul_le_mul_of_nonneg_right hP hT0
      _ = Pb * T ^ 2 := by ring
  have hDT : D * T <= Db * T := mul_le_mul_of_nonneg_right hD hT0
  have hDT0 : 0 <= D * T := mul_nonneg hD0 hT0
  have hDbT0 : 0 <= Db * T := mul_nonneg hDb0 hT0
  have hDsq : (D * T) ^ 2 <= Db ^ 2 * T ^ 2 := by
    calc
      (D * T) ^ 2 <= (Db * T) ^ 2 := (sq_le_sq₀ hDT0 hDbT0).2 hDT
      _ = Db ^ 2 * T ^ 2 := by ring
  have hDTsq : D * T <= Db * T ^ 2 := by
    exact hDT.trans (mul_le_mul_of_nonneg_left hTsq hDb0)
  have hlinear : K2 * (2 * F * (P * T)) <=
      (K2 * (2 * F * Pb)) * T ^ 2 := by
    calc
      _ <= K2 * (2 * F * (Pb * T ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hPT (by positivity)) hK2
      _ = _ := by ring
  have hsquare : K2 * (D * T) ^ 2 <= (K2 * Db ^ 2) * T ^ 2 := by
    calc
      _ <= K2 * (Db ^ 2 * T ^ 2) := mul_le_mul_of_nonneg_left hDsq hK2
      _ = _ := by ring
  have hcubic : K3 * ((D * T) * C) <=
      (K3 * (Db * C)) * T ^ 2 := by
    calc
      _ <= K3 * ((Db * T ^ 2) * C) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hDTsq hC) hK3
      _ = _ := by ring
  nlinarith

theorem coefficientUnitCubicConstant_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta H : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) :
    0 <= coefficientUnitCubicConstant m mUpper kappa beta H radius observed := by
  classical
  have hA : 0 <= actualModalEnergyL1Envelope N mUpper kappa beta H := by
    have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
      CoerciveCubicPotential.coercivityConstant_pos hbeta
    unfold actualModalEnergyL1Envelope
    positivity
  have hF : 0 <= radiusL1 radius := by
    unfold radiusL1
    positivity
  have hD := defectUnitConstant_nonneg m kappa beta
    (actualModalEnergyL1Envelope N mUpper kappa beta H) hA
  have hP := afterFirstUnitConstant_nonneg m kappa beta (radiusL1 radius)
    (actualModalEnergyL1Envelope N mUpper kappa beta H) hF hA
  unfold coefficientUnitCubicConstant
    cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
  apply div_nonneg
  · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m observed := by
      unfold observedInteractionTensorAbsMass
      positivity
    have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m observed := by
      unfold observedInteractionTensorAbsMass
      positivity
    positivity
  · exact Real.sqrt_nonneg _

theorem coefficientUnitEnergyWindow_le_constant_mul_cube
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (hT : 1 <= T) (hg : |g| <= 1)
    (hgT : |g| * T <= 1) :
    cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed <=
      coefficientUnitCubicConstant m mUpper kappa beta H radius observed * T ^ 3 := by
  classical
  let A := actualModalEnergyL1Envelope N mUpper kappa beta H
  let F := radiusL1 radius
  let D := sharpHistoryDefectL1UnitRate m kappa beta g A
  let Db := defectUnitConstant m kappa beta A
  let P := sharpAfterFirstPicardHistoryL1UnitRate m kappa beta g F A D T
  let Pb := afterFirstUnitConstant m kappa beta F A
  have hA : 0 <= A := by
    dsimp only [A]
    have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
      CoerciveCubicPotential.coercivityConstant_pos hbeta
    unfold actualModalEnergyL1Envelope
    positivity
  have hF : 0 <= F := by
    dsimp only [F]
    unfold radiusL1
    positivity
  have hD0 : 0 <= D := by
    dsimp only [D]
    unfold sharpHistoryDefectL1UnitRate firstDuhamelWindowUnitCouplingEnvelope
    apply Finset.sum_nonneg
    intro mode hmode
    apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    apply div_nonneg
    · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      exact add_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg kappa) hM2) (sq_nonneg A))
        (mul_nonneg (mul_nonneg
          (mul_nonneg (abs_nonneg beta) (abs_nonneg g)) hM3)
          (pow_nonneg hA 3))
    · exact Real.sqrt_nonneg _
  have hDb0 : 0 <= Db := by
    exact defectUnitConstant_nonneg m kappa beta A hA
  have hD : D <= Db := by
    exact sharpHistoryDefectL1UnitRate_le_constant m kappa beta g A hA hg
  have hP : P <= Pb * T := by
    exact sharpAfterFirstPicardHistoryL1UnitRate_le_constant_mul_time
      m kappa beta g F A T hF hA hT hg hgT
  have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hC : 0 <= A ^ 2 + A * F + F ^ 2 := by positivity
  unfold cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
    coefficientUnitCubicConstant
  change
    cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
        m kappa beta observed F A D P T * T <=
      cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
        m kappa beta observed F A Db Pb 1 * T ^ 3
  rw [show T ^ 3 = T ^ 2 * T by ring]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hT)
  unfold cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hsource := source_algebra
    (|kappa| * observedInteractionTensorAbsMass (n := 2) m observed)
    (|beta| * observedInteractionTensorAbsMass (n := 3) m observed)
    F (A ^ 2 + A * F + F ^ 2) D Db P Pb T
    (mul_nonneg (abs_nonneg kappa) hM2)
    (mul_nonneg (abs_nonneg beta) hM3) hF hC hD0 hDb0 hD hP hT
  nlinarith [hsource]

open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow


theorem referenceMassConstant_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N) :
    0 <= referenceMassConstant m kappa beta radius observed := by
  classical
  unfold referenceMassConstant finiteCharacterCoefficientAbsMass
  positivity

theorem coefficientUnitEnergyWindow_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (hT : 0 <= T) :
    0 <= cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
      m mUpper kappa beta g H radius T observed := by
  classical
  let A := actualModalEnergyL1Envelope N mUpper kappa beta H
  let F := radiusL1 radius
  let D := sharpHistoryDefectL1UnitRate m kappa beta g A
  let P := sharpAfterFirstPicardHistoryL1UnitRate m kappa beta g F A D T
  have hA : 0 <= A := by
    dsimp only [A]
    have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
      CoerciveCubicPotential.coercivityConstant_pos hbeta
    unfold actualModalEnergyL1Envelope
    positivity
  have hF : 0 <= F := by
    dsimp only [F]
    unfold radiusL1
    positivity
  have hD : 0 <= D := by
    dsimp only [D]
    unfold sharpHistoryDefectL1UnitRate firstDuhamelWindowUnitCouplingEnvelope
    apply Finset.sum_nonneg
    intro mode hmode
    apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    apply div_nonneg
    · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      exact add_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg kappa) hM2) (sq_nonneg A))
        (mul_nonneg (mul_nonneg
          (mul_nonneg (abs_nonneg beta) (abs_nonneg g)) hM3)
          (pow_nonneg hA 3))
    · exact Real.sqrt_nonneg _
  have hP : 0 <= P := by
    dsimp only [P]
    unfold sharpAfterFirstPicardHistoryL1UnitRate
      sharpFirstPicardRemainderSourceWindowUnitEnvelope
    apply Finset.sum_nonneg
    intro mode hmode
    apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    apply div_nonneg
    · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      positivity
    · exact Real.sqrt_nonneg _
  unfold cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
  change 0 <= cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
      m kappa beta observed F A D P T * T
  apply mul_nonneg
  · unfold cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
    apply div_nonneg
    · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m observed := by
        unfold observedInteractionTensorAbsMass
        positivity
      have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m observed := by
        unfold observedInteractionTensorAbsMass
        positivity
      positivity
    · exact Real.sqrt_nonneg _
  · exact hT

def mesoscopicHaarCubicUnitPolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  2 * referenceMassConstant m kappa beta radius observed *
      coefficientUnitCubicConstant m mUpper kappa beta H radius observed * T ^ 3 +
    |g| ^ 3 *
      coefficientUnitCubicConstant m mUpper kappa beta H radius observed ^ 2 * T ^ 6

theorem haarCubicUnitEnvelope_le_mesoscopicPolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (hT : 1 <= T) (hg : |g| <= 1)
    (hgT : |g| * T <= 1) :
    physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
        m mUpper kappa beta g H radius T observed <=
      mesoscopicHaarCubicUnitPolynomial
        m mUpper kappa beta g H radius T observed := by
  classical
  let M := finiteCharacterTwoStepAbsMass g
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
    (physlibQuadraticFirstPicardCharacterCoefficient m kappa radius T observed)
    (completeSecondPicardCoefficient m kappa beta radius observed T)
  let R := referenceMassConstant m kappa beta radius observed
  let C := cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    m mUpper kappa beta g H radius T observed
  let S := coefficientUnitCubicConstant m mUpper kappa beta H radius observed
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hM0 : 0 <= M := by
    dsimp only [M]
    unfold finiteCharacterTwoStepAbsMass finiteCharacterCoefficientAbsMass
    positivity
  have hR0 : 0 <= R := referenceMassConstant_nonneg m kappa beta radius observed
  have hC0 : 0 <= C := by
    exact coefficientUnitEnergyWindow_nonneg
      m mUpper kappa beta g H radius T observed hmUpper hbeta hH hT0
  have hS0 : 0 <= S := by
    exact coefficientUnitCubicConstant_nonneg
      m mUpper kappa beta H radius observed hmUpper hbeta hH
  have hM : M <= R := by
    exact (twoStepMass_le_timePolynomial m kappa beta g radius T observed hT0).trans
      (referenceMassTimePolynomial_le_constant
        m kappa beta g radius T observed hT0 hg hgT)
  have hC : C <= S * T ^ 3 := by
    exact coefficientUnitEnergyWindow_le_constant_mul_cube
      m mUpper kappa beta g H radius T observed
        hmUpper hbeta hH hT hg hgT
  have hST0 : 0 <= S * T ^ 3 := mul_nonneg hS0 (pow_nonneg hT0 3)
  have hproduct : M * C <= R * (S * T ^ 3) :=
    mul_le_mul hM hC hC0 hR0
  have hsquare : C ^ 2 <= (S * T ^ 3) ^ 2 :=
    (sq_le_sq₀ hC0 hST0).2 hC
  have hweightedSquare : |g| ^ 3 * C ^ 2 <=
      |g| ^ 3 * (S * T ^ 3) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare (pow_nonneg (abs_nonneg g) 3)
  unfold physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
    mesoscopicHaarCubicUnitPolynomial
  change 2 * M * C + |g| ^ 3 * C ^ 2 <=
    2 * R * S * T ^ 3 + |g| ^ 3 * S ^ 2 * T ^ 6
  nlinarith [hproduct, hweightedSquare]

open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow


private theorem afterFirst_global_algebra
    (K2 K3 F A D Db x T : Real)
    (hK2 : 0 <= K2) (hK3 : 0 <= K3) (hF : 0 <= F)
    (hlin : D * T <= Db * T ^ 2)
    (hquad : x * (D * T) ^ 2 <= Db ^ 2 * T ^ 2)
    (hconst : A ^ 3 <= A ^ 3 * T ^ 2) :
    K2 * (2 * F * (D * T) + x * (D * T) ^ 2) + K3 * A ^ 3 <=
      (K2 * (2 * F * Db + Db ^ 2) + K3 * A ^ 3) * T ^ 2 := by
  have hlinTerm : K2 * (2 * F * (D * T)) <=
      (K2 * (2 * F * Db)) * T ^ 2 := by
    calc
      K2 * (2 * F * (D * T)) <= K2 * (2 * F * (Db * T ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlin (by positivity)) hK2
      _ = _ := by ring
  have hquadTerm : K2 * (x * (D * T) ^ 2) <=
      (K2 * Db ^ 2) * T ^ 2 := by
    calc
      _ <= K2 * (Db ^ 2 * T ^ 2) := mul_le_mul_of_nonneg_left hquad hK2
      _ = _ := by ring
  have hconstTerm : K3 * A ^ 3 <= (K3 * A ^ 3) * T ^ 2 := by
    calc
      _ <= K3 * (A ^ 3 * T ^ 2) := mul_le_mul_of_nonneg_left hconst hK3
      _ = _ := by ring
  nlinarith

theorem sharpAfterFirstPicardHistoryL1UnitRate_le_constant_mul_sq_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (freeBound actualBound T : Real)
    (hfree : 0 <= freeBound) (hactual : 0 <= actualBound)
    (hT : 1 <= T) (hg : |g| <= 1) :
    sharpAfterFirstPicardHistoryL1UnitRate m kappa beta g
        freeBound actualBound
        (sharpHistoryDefectL1UnitRate m kappa beta g actualBound) T <=
      afterFirstUnitConstant m kappa beta freeBound actualBound * T ^ 2 := by
  classical
  let D := sharpHistoryDefectL1UnitRate m kappa beta g actualBound
  let Db := defectUnitConstant m kappa beta actualBound
  have hD0 : 0 <= D := by
    unfold D sharpHistoryDefectL1UnitRate
      firstDuhamelWindowUnitCouplingEnvelope
    apply Finset.sum_nonneg
    intro mode hmode
    apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    apply div_nonneg
    · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
        unfold observedInteractionTensorAbsMass
        positivity
      exact add_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg kappa) hM2)
          (sq_nonneg actualBound))
        (mul_nonneg (mul_nonneg
          (mul_nonneg (abs_nonneg beta) (abs_nonneg g)) hM3)
          (pow_nonneg hactual 3))
    · exact Real.sqrt_nonneg _
  have hDb0 : 0 <= Db :=
    defectUnitConstant_nonneg m kappa beta actualBound hactual
  have hD : D <= Db :=
    sharpHistoryDefectL1UnitRate_le_constant
      m kappa beta g actualBound hactual hg
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hTsq : 1 <= T ^ 2 := by nlinarith
  have hTle : T <= T ^ 2 := by nlinarith
  have hDT : D * T <= Db * T := mul_le_mul_of_nonneg_right hD hT0
  have hlin : D * T <= Db * T ^ 2 :=
    hDT.trans (mul_le_mul_of_nonneg_left hTle hDb0)
  have hDsq : (D * T) ^ 2 <= Db ^ 2 * T ^ 2 := by
    calc
      (D * T) ^ 2 <= (Db * T) ^ 2 :=
        (sq_le_sq₀ (mul_nonneg hD0 hT0) (mul_nonneg hDb0 hT0)).2 hDT
      _ = Db ^ 2 * T ^ 2 := by ring
  have hquad : |g| * (D * T) ^ 2 <= Db ^ 2 * T ^ 2 := by
    calc
      _ <= 1 * (D * T) ^ 2 :=
        mul_le_mul_of_nonneg_right hg (sq_nonneg (D * T))
      _ <= _ := by simpa only [one_mul] using hDsq
  have hconst : actualBound ^ 3 <= actualBound ^ 3 * T ^ 2 := by
    nlinarith [pow_nonneg hactual 3]
  unfold afterFirstUnitConstant sharpAfterFirstPicardHistoryL1UnitRate
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro mode hmode
  rw [show positiveModeCoordinateRecoveryFactor m mode *
      sharpFirstPicardRemainderSourceWindowUnitEnvelope m kappa beta 1 mode
        freeBound actualBound (defectUnitConstant m kappa beta actualBound) 1 * T ^ 2 =
      positiveModeCoordinateRecoveryFactor m mode *
        (sharpFirstPicardRemainderSourceWindowUnitEnvelope m kappa beta 1 mode
          freeBound actualBound (defectUnitConstant m kappa beta actualBound) 1 *
            T ^ 2) by ring]
  apply mul_le_mul_of_nonneg_left _
    (positiveModeCoordinateRecoveryFactor_nonneg m mode)
  unfold sharpFirstPicardRemainderSourceWindowUnitEnvelope
  simp only [abs_one, one_mul, mul_one]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hbound := afterFirst_global_algebra
    (|kappa| * observedInteractionTensorAbsMass (n := 2) m mode)
    (|beta| * observedInteractionTensorAbsMass (n := 3) m mode)
    freeBound actualBound D Db |g| T
    (mul_nonneg (abs_nonneg kappa) hM2)
    (mul_nonneg (abs_nonneg beta) hM3) hfree hlin hquad hconst
  change
    |kappa| * (observedInteractionTensorAbsMass (n := 2) m mode *
      (2 * freeBound * (D * T) + |g| * (D * T) ^ 2)) +
      |beta| * (observedInteractionTensorAbsMass (n := 3) m mode *
        actualBound ^ 3) <=
    (|kappa| * (observedInteractionTensorAbsMass (n := 2) m mode *
      (2 * freeBound * Db + Db ^ 2)) +
      |beta| * (observedInteractionTensorAbsMass (n := 3) m mode *
        actualBound ^ 3)) * T ^ 2
  nlinarith [hbound]

theorem referenceMassTimePolynomial_le_constant_mul_sq_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) (hT : 1 <= T) (hg : |g| <= 1) :
    referenceMassTimePolynomial m kappa beta g radius T observed <=
      referenceMassConstant m kappa beta radius observed * T ^ 2 := by
  let Z := finiteCharacterCoefficientAbsMass
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
  let W := finiteCharacterCoefficientAbsMass
    (freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling m kappa 1 observed) m observed radius)
  let Q := finiteCharacterCoefficientAbsMass
    (iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed)
  let C := finiteCharacterCoefficientAbsMass
    (cubicDuhamelCoefficient
      (physicalCubicUnitCoupling (modeFrequency m observed) beta)
      m observed radius)
  have hZ : 0 <= Z := by dsimp only [Z, finiteCharacterCoefficientAbsMass]; positivity
  have hW : 0 <= W := by dsimp only [W, finiteCharacterCoefficientAbsMass]; positivity
  have hQ : 0 <= Q := by dsimp only [Q, finiteCharacterCoefficientAbsMass]; positivity
  have hC : 0 <= C := by dsimp only [C, finiteCharacterCoefficientAbsMass]; positivity
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hTle : T <= T ^ 2 := by nlinarith
  have hOneSq : 1 <= T ^ 2 := by nlinarith
  have hg2 : g ^ 2 <= 1 := by rw [<- sq_abs]; nlinarith [abs_nonneg g]
  have hZterm : Z <= Z * T ^ 2 := by nlinarith
  have hWterm : |g| * (T * W) <= W * T ^ 2 := by
    have : |g| * T <= T ^ 2 := by nlinarith [abs_nonneg g]
    nlinarith
  have hQterm : g ^ 2 * (T ^ 2 * Q) <= Q * T ^ 2 := by
    calc
      _ <= 1 * (T ^ 2 * Q) :=
        mul_le_mul_of_nonneg_right hg2 (mul_nonneg (sq_nonneg T) hQ)
      _ = _ := by ring
  have hCterm : g ^ 2 * (T * C) <= C * T ^ 2 := by
    calc
      _ <= 1 * (T * C) :=
        mul_le_mul_of_nonneg_right hg2 (mul_nonneg hT0 hC)
      _ <= C * T ^ 2 := by nlinarith
  change Z + |g| * (T * W) + g ^ 2 * (T ^ 2 * Q + T * C) <=
    (Z + W + Q + C) * T ^ 2
  nlinarith

private theorem source_global_algebra
    (K2 K3 F C D Db P Pb T : Real)
    (hK2 : 0 <= K2) (hK3 : 0 <= K3) (hF : 0 <= F) (hC : 0 <= C)
    (hD0 : 0 <= D) (hDb0 : 0 <= Db)
    (hD : D <= Db) (hP : P <= Pb * T ^ 2) (hT : 1 <= T) :
    K2 * (2 * F * (P * T)) + K2 * (D * T) ^ 2 + K3 * ((D * T) * C) <=
      (K2 * (2 * F * Pb) + K2 * Db ^ 2 + K3 * (Db * C)) * T ^ 3 := by
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hT2le3 : T ^ 2 <= T ^ 3 := by nlinarith
  have hPT : P * T <= Pb * T ^ 3 := by
    calc
      _ <= (Pb * T ^ 2) * T := mul_le_mul_of_nonneg_right hP hT0
      _ = _ := by ring
  have hDT : D * T <= Db * T := mul_le_mul_of_nonneg_right hD hT0
  have hDsq : (D * T) ^ 2 <= Db ^ 2 * T ^ 2 := by
    calc
      _ <= (Db * T) ^ 2 :=
        (sq_le_sq₀ (mul_nonneg hD0 hT0) (mul_nonneg hDb0 hT0)).2 hDT
      _ = _ := by ring
  have hDsq3 : (D * T) ^ 2 <= Db ^ 2 * T ^ 3 :=
    hDsq.trans (mul_le_mul_of_nonneg_left hT2le3 (sq_nonneg Db))
  have hTle3 : T <= T ^ 3 := by nlinarith
  have hDT3 : D * T <= Db * T ^ 3 :=
    hDT.trans (mul_le_mul_of_nonneg_left hTle3 hDb0)
  have hlinear : K2 * (2 * F * (P * T)) <=
      (K2 * (2 * F * Pb)) * T ^ 3 := by
    calc
      _ <= K2 * (2 * F * (Pb * T ^ 3)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hPT (by positivity)) hK2
      _ = _ := by ring
  have hsquare : K2 * (D * T) ^ 2 <= (K2 * Db ^ 2) * T ^ 3 := by
    calc
      _ <= K2 * (Db ^ 2 * T ^ 3) := mul_le_mul_of_nonneg_left hDsq3 hK2
      _ = _ := by ring
  have hcubic : K3 * ((D * T) * C) <= (K3 * (Db * C)) * T ^ 3 := by
    calc
      _ <= K3 * ((Db * T ^ 3) * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDT3 hC) hK3
      _ = _ := by ring
  nlinarith

theorem coefficientUnitEnergyWindow_le_constant_mul_fourth
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (hT : 1 <= T) (hg : |g| <= 1) :
    cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed <=
      coefficientUnitCubicConstant m mUpper kappa beta H radius observed * T ^ 4 := by
  classical
  let A := actualModalEnergyL1Envelope N mUpper kappa beta H
  let F := radiusL1 radius
  let D := sharpHistoryDefectL1UnitRate m kappa beta g A
  let Db := defectUnitConstant m kappa beta A
  let P := sharpAfterFirstPicardHistoryL1UnitRate m kappa beta g F A D T
  let Pb := afterFirstUnitConstant m kappa beta F A
  have hA : 0 <= A := by
    dsimp only [A]
    have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
      CoerciveCubicPotential.coercivityConstant_pos hbeta
    unfold actualModalEnergyL1Envelope
    positivity
  have hF : 0 <= F := by dsimp only [F]; unfold radiusL1; positivity
  have hD0 : 0 <= D := by
    dsimp only [D]
    unfold sharpHistoryDefectL1UnitRate firstDuhamelWindowUnitCouplingEnvelope
    apply Finset.sum_nonneg
    intro mode hmode
    apply mul_nonneg (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    apply div_nonneg
    · have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m mode := by
        unfold observedInteractionTensorAbsMass; positivity
      have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m mode := by
        unfold observedInteractionTensorAbsMass; positivity
      exact add_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg kappa) hM2) (sq_nonneg A))
        (mul_nonneg (mul_nonneg
          (mul_nonneg (abs_nonneg beta) (abs_nonneg g)) hM3)
          (pow_nonneg hA 3))
    · exact Real.sqrt_nonneg _
  have hDb0 : 0 <= Db := defectUnitConstant_nonneg m kappa beta A hA
  have hD : D <= Db :=
    sharpHistoryDefectL1UnitRate_le_constant m kappa beta g A hA hg
  have hP : P <= Pb * T ^ 2 :=
    sharpAfterFirstPicardHistoryL1UnitRate_le_constant_mul_sq_time
      m kappa beta g F A T hF hA hT hg
  have hM2 : 0 <= observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass; positivity
  have hM3 : 0 <= observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass; positivity
  have hC : 0 <= A ^ 2 + A * F + F ^ 2 := by positivity
  unfold cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
    coefficientUnitCubicConstant
  change cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
      m kappa beta observed F A D P T * T <=
    cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
      m kappa beta observed F A Db Pb 1 * T ^ 4
  rw [show T ^ 4 = T ^ 3 * T by ring, <- mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hT)
  unfold cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hsource := source_global_algebra
    (|kappa| * observedInteractionTensorAbsMass (n := 2) m observed)
    (|beta| * observedInteractionTensorAbsMass (n := 3) m observed)
    F (A ^ 2 + A * F + F ^ 2) D Db P Pb T
    (mul_nonneg (abs_nonneg kappa) hM2)
    (mul_nonneg (abs_nonneg beta) hM3) hF hC hD0 hDb0 hD hP hT
  nlinarith [hsource]

def globalHaarCubicUnitPolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  2 * referenceMassConstant m kappa beta radius observed *
      coefficientUnitCubicConstant m mUpper kappa beta H radius observed * T ^ 6 +
    |g| ^ 3 * coefficientUnitCubicConstant
      m mUpper kappa beta H radius observed ^ 2 * T ^ 8

theorem haarCubicUnitEnvelope_le_globalPolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (hT : 1 <= T) (hg : |g| <= 1) :
    physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
        m mUpper kappa beta g H radius T observed <=
      globalHaarCubicUnitPolynomial m mUpper kappa beta g H radius T observed := by
  let M := finiteCharacterTwoStepAbsMass g
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
    (physlibQuadraticFirstPicardCharacterCoefficient m kappa radius T observed)
    (completeSecondPicardCoefficient m kappa beta radius observed T)
  let R := referenceMassConstant m kappa beta radius observed
  let C := cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    m mUpper kappa beta g H radius T observed
  let S := coefficientUnitCubicConstant m mUpper kappa beta H radius observed
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hM0 : 0 <= M := by
    dsimp only [M]
    unfold finiteCharacterTwoStepAbsMass finiteCharacterCoefficientAbsMass
    positivity
  have hR0 : 0 <= R := referenceMassConstant_nonneg m kappa beta radius observed
  have hC0 : 0 <= C := coefficientUnitEnergyWindow_nonneg
    m mUpper kappa beta g H radius T observed hmUpper hbeta hH hT0
  have hS0 : 0 <= S := coefficientUnitCubicConstant_nonneg
    m mUpper kappa beta H radius observed hmUpper hbeta hH
  have hM : M <= R * T ^ 2 :=
    (twoStepMass_le_timePolynomial m kappa beta g radius T observed hT0).trans
      (referenceMassTimePolynomial_le_constant_mul_sq_time
        m kappa beta g radius T observed hT hg)
  have hC : C <= S * T ^ 4 :=
    coefficientUnitEnergyWindow_le_constant_mul_fourth
      m mUpper kappa beta g H radius T observed hmUpper hbeta hH hT hg
  have hRT0 : 0 <= R * T ^ 2 := mul_nonneg hR0 (pow_nonneg hT0 2)
  have hST0 : 0 <= S * T ^ 4 := mul_nonneg hS0 (pow_nonneg hT0 4)
  have hproduct : M * C <= (R * T ^ 2) * (S * T ^ 4) :=
    mul_le_mul hM hC hC0 hRT0
  have hsquare : C ^ 2 <= (S * T ^ 4) ^ 2 :=
    (sq_le_sq₀ hC0 hST0).2 hC
  have hweighted : |g| ^ 3 * C ^ 2 <= |g| ^ 3 * (S * T ^ 4) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare (pow_nonneg (abs_nonneg g) 3)
  unfold physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
    globalHaarCubicUnitPolynomial
  change 2 * M * C + |g| ^ 3 * C ^ 2 <=
    2 * R * S * T ^ 6 + |g| ^ 3 * S ^ 2 * T ^ 8
  nlinarith [hproduct, hweighted]

open Filter Set Topology
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder


theorem haarCubicUnitEnvelope_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (hT : 0 <= T) :
    0 <= physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
      m mUpper kappa beta g H radius T observed := by
  let M := finiteCharacterTwoStepAbsMass g
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
    (physlibQuadraticFirstPicardCharacterCoefficient m kappa radius T observed)
    (completeSecondPicardCoefficient m kappa beta radius observed T)
  let C := cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    m mUpper kappa beta g H radius T observed
  have hM : 0 <= M := by
    dsimp only [M]
    unfold finiteCharacterTwoStepAbsMass finiteCharacterCoefficientAbsMass
    positivity
  have hC : 0 <= C := coefficientUnitEnergyWindow_nonneg
    m mUpper kappa beta g H radius T observed hmUpper hbeta hH hT
  unfold physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
  change 0 <= 2 * M * C + |g| ^ 3 * C ^ 2
  positivity

private theorem positive_rpow_tendsto_zero
    {q : Real} (hq : 0 < q) :
    Tendsto (fun epsilon : Real => epsilon ^ q)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hfull := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto
  have hfull' : Tendsto (fun epsilon : Real => epsilon ^ q)
      (nhds 0) (nhds 0) := by
    simpa only [Real.zero_rpow hq.ne'] using hfull
  exact hfull'.mono_left inf_le_left

theorem haarCubicAbsCubeEnvelope_tendsto_zero_mesoscopic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta H : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (alpha : Real) (halpha0 : 0 <= alpha)
    (halpha1 : alpha < 1) :
    Tendsto
      (fun epsilon : Real => epsilon ^ 3 *
        physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
          m mUpper kappa beta epsilon H radius
            (epsilon ^ (-alpha)) observed)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let R := referenceMassConstant m kappa beta radius observed
  let S := coefficientUnitCubicConstant m mUpper kappa beta H radius observed
  let x := fun epsilon : Real => epsilon ^ (1 - alpha)
  let B := fun epsilon : Real =>
    2 * R * S * (x epsilon) ^ 3 + S ^ 2 * (x epsilon) ^ 6
  have hq : 0 < 1 - alpha := sub_pos.mpr halpha1
  have hx : Tendsto x (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    exact positive_rpow_tendsto_zero hq
  have hB : Tendsto B (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h3 := (hx.pow 3).const_mul (2 * R * S)
    have h6 := (hx.pow 6).const_mul (S ^ 2)
    simpa only [B, zero_pow (by norm_num : 3 ≠ 0),
      zero_pow (by norm_num : 6 ≠ 0), mul_zero, add_zero] using h3.add h6
  have hpos : ∀ᶠ epsilon in nhdsWithin (0 : Real) (Ioi 0), 0 < epsilon := by
    exact self_mem_nhdsWithin
  have hleOne : ∀ᶠ epsilon in nhdsWithin (0 : Real) (Ioi 0),
      epsilon <= 1 := by
    exact (eventually_le_nhds (show (0 : Real) < 1 by norm_num)).filter_mono
      inf_le_left
  apply squeeze_zero'
  · filter_upwards [hpos] with epsilon hepsilon
    exact mul_nonneg (pow_nonneg hepsilon.le 3)
      (haarCubicUnitEnvelope_nonneg m mUpper kappa beta epsilon H radius
        (epsilon ^ (-alpha)) observed hmUpper hbeta hH (Real.rpow_nonneg hepsilon.le (-alpha)))
  · filter_upwards [hpos, hleOne] with epsilon hepsilon hepsilonOne
    have hT : 1 <= epsilon ^ (-alpha) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hepsilon hepsilonOne (neg_nonpos.mpr halpha0)
    have hepsilonAbs : |epsilon| <= 1 := by
      rw [abs_of_pos hepsilon]
      exact hepsilonOne
    have hschedule : epsilon * epsilon ^ (-alpha) =
        epsilon ^ (1 - alpha) := by
      calc
        epsilon * epsilon ^ (-alpha) =
            epsilon ^ 1 * epsilon ^ (-alpha) := by rw [Real.rpow_one]
        _ = epsilon ^ (1 + (-alpha)) :=
          (Real.rpow_add hepsilon 1 (-alpha)).symm
        _ = epsilon ^ (1 - alpha) := by ring_nf
    have hepsilonT : |epsilon| * epsilon ^ (-alpha) <= 1 := by
      rw [abs_of_pos hepsilon, hschedule]
      exact Real.rpow_le_one hepsilon.le hepsilonOne hq.le
    have hpoint := haarCubicUnitEnvelope_le_mesoscopicPolynomial
      m mUpper kappa beta epsilon H radius (epsilon ^ (-alpha)) observed
        hmUpper hbeta hH hT hepsilonAbs hepsilonT
    calc
      epsilon ^ 3 *
          physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta epsilon H radius
              (epsilon ^ (-alpha)) observed <=
        epsilon ^ 3 * mesoscopicHaarCubicUnitPolynomial
          m mUpper kappa beta epsilon H radius
            (epsilon ^ (-alpha)) observed :=
          mul_le_mul_of_nonneg_left hpoint (pow_nonneg hepsilon.le 3)
      _ = B epsilon := by
        unfold mesoscopicHaarCubicUnitPolynomial B x R S
        rw [abs_of_pos hepsilon, <- hschedule]
        ring
  · exact hB

open Filter Set Topology
open ArchonPhysics


private theorem kinetic_power_eq
    (epsilon : Real) (hepsilon : 0 < epsilon) (p q : Nat) :
    epsilon ^ p * (epsilon ^ (-(2 : Real))) ^ q =
      epsilon ^ ((p : Real) - 2 * (q : Real)) := by
  rw [<- Real.rpow_natCast epsilon p]
  rw [<- Real.rpow_natCast (epsilon ^ (-(2 : Real))) q]
  rw [<- Real.rpow_mul hepsilon.le]
  rw [<- Real.rpow_add hepsilon]
  congr 1
  ring

theorem kineticScaleCouplingTime_tendsto_atTop :
    Tendsto (fun epsilon : Real => epsilon * epsilon ^ (-(2 : Real)))
      (nhdsWithin 0 (Ioi 0)) atTop := by
  have hbase :=
    tendsto_rpow_neg_nhdsGT_zero (show (-(1 : Real)) < 0 by norm_num)
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  calc
    epsilon ^ (-(1 : Real)) = epsilon ^ (1 + (-(2 : Real))) := by norm_num
    _ = epsilon ^ 1 * epsilon ^ (-(2 : Real)) :=
      Real.rpow_add hepsilon 1 (-(2 : Real))
    _ = epsilon * epsilon ^ (-(2 : Real)) := by rw [Real.rpow_one]

theorem globalHaarCubicUnitPolynomial_kineticScale_identity
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta H : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    epsilon ^ 3 * globalHaarCubicUnitPolynomial
        m mUpper kappa beta epsilon H radius
          (epsilon ^ (-(2 : Real))) observed =
      2 * referenceMassConstant m kappa beta radius observed *
          coefficientUnitCubicConstant m mUpper kappa beta H radius observed *
            epsilon ^ (-(9 : Real)) +
        coefficientUnitCubicConstant
            m mUpper kappa beta H radius observed ^ 2 *
          epsilon ^ (-(10 : Real)) := by
  have h9 : epsilon ^ 3 * (epsilon ^ (-(2 : Real))) ^ 6 =
      epsilon ^ (-(9 : Real)) := by
    convert kinetic_power_eq epsilon hepsilon 3 6 using 1 <;> norm_num
  have h10 : epsilon ^ 3 * epsilon ^ 3 *
      (epsilon ^ (-(2 : Real))) ^ 8 = epsilon ^ (-(10 : Real)) := by
    rw [show epsilon ^ 3 * epsilon ^ 3 = epsilon ^ 6 by ring]
    convert kinetic_power_eq epsilon hepsilon 6 8 using 1 <;> norm_num
  unfold globalHaarCubicUnitPolynomial
  rw [abs_of_pos hepsilon]
  rw [show epsilon ^ 3 *
      (2 * referenceMassConstant m kappa beta radius observed *
          coefficientUnitCubicConstant m mUpper kappa beta H radius observed *
            (epsilon ^ (-(2 : Real))) ^ 6 +
        epsilon ^ 3 * coefficientUnitCubicConstant
            m mUpper kappa beta H radius observed ^ 2 *
          (epsilon ^ (-(2 : Real))) ^ 8) =
      2 * referenceMassConstant m kappa beta radius observed *
          coefficientUnitCubicConstant m mUpper kappa beta H radius observed *
            (epsilon ^ 3 * (epsilon ^ (-(2 : Real))) ^ 6) +
        coefficientUnitCubicConstant
            m mUpper kappa beta H radius observed ^ 2 *
          (epsilon ^ 3 * epsilon ^ 3 *
            (epsilon ^ (-(2 : Real))) ^ 8) by ring]
  rw [h9, h10]

theorem globalHaarCubicUnitPolynomial_kineticScale_tendsto_atTop
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mUpper kappa beta H : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H)
    (hS : 0 < coefficientUnitCubicConstant
      m mUpper kappa beta H radius observed) :
    Tendsto
      (fun epsilon : Real => epsilon ^ 3 * globalHaarCubicUnitPolynomial
        m mUpper kappa beta epsilon H radius
          (epsilon ^ (-(2 : Real))) observed)
      (nhdsWithin 0 (Ioi 0)) atTop := by
  let R := referenceMassConstant m kappa beta radius observed
  let S := coefficientUnitCubicConstant m mUpper kappa beta H radius observed
  let G := fun epsilon : Real =>
    2 * R * S * epsilon ^ (-(9 : Real)) +
      S ^ 2 * epsilon ^ (-(10 : Real))
  have hR : 0 <= R := referenceMassConstant_nonneg m kappa beta radius observed
  have hS' : 0 < S := hS
  have hten :=
    tendsto_rpow_neg_nhdsGT_zero (show (-(10 : Real)) < 0 by norm_num)
  have hscaled : Tendsto (fun epsilon : Real =>
      S ^ 2 * epsilon ^ (-(10 : Real)))
      (nhdsWithin 0 (Ioi 0)) atTop :=
    hten.const_mul_atTop (sq_pos_of_pos hS')
  have hG : Tendsto G (nhdsWithin 0 (Ioi 0)) atTop := by
    apply Filter.tendsto_atTop_mono' (nhdsWithin 0 (Ioi 0)) _ hscaled
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    unfold G
    have hfirst : 0 <= 2 * R * S * epsilon ^ (-(9 : Real)) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR) hS'.le)
        (Real.rpow_nonneg hepsilon.le (-(9 : Real)))
    linarith
  apply hG.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  exact (globalHaarCubicUnitPolynomial_kineticScale_identity
    m mUpper kappa beta H radius observed epsilon hepsilon).symm
end
end ArchonPhysics.PhyslibFPUTCubicLipschitzEnvelopeMesoscopicScale
