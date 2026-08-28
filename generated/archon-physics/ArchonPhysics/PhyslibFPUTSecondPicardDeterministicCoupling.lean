import ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor
import ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder

/-!
# A deterministic second-Picard coupling for a genuine FPUT block

The exact Hamiltonian Duhamel identity writes the interaction-picture block
endpoint as the two-step Picard amplitude plus an equality remainder.  The
cubic-history Lipschitz estimate bounds that same remainder by an explicit
`|g|^3` envelope.  Combining those two results with the empty-exception-set
coupling constructor gives a common-source coupling with `bad = ∅` and
failure probability zero.

Measurability of the two endpoint maps and a uniform radius for the reference
amplitude remain explicit ensemble inputs.  Pointwise closeness, in contrast,
is derived here from the Physlib Hamilton equations; it is not a coupling
hypothesis.
-/

namespace ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling

open MeasureTheory
open Set
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-! ## The two amplitudes and their cubic coupling scale -/

/-- Exact interaction-picture amplitude at the end of a Hamiltonian block. -/
def physlibSecondPicardActualAmplitude
    {Omega : Type*} {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N) (T : Real) :
    Omega → Complex :=
  fun omega ↦ phaseRenormalize (modeFrequency m observed * T)
    (physlibModeAmplitude m observed (p omega) (q omega) T)

/-- The two-step Picard amplitude driven by the same initial phase sample. -/
def physlibSecondPicardReferenceAmplitude
    {Omega : Type*} {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (kappa beta g : Real)
    (observed : Site N) (radius : Site N → Real)
    (phase : Omega → UnitAddTorus (Site N)) (T : Real) : Omega → Complex :=
  fun omega ↦
    twoStepPerturbedAmplitude g
      (canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) (phase omega) observed)
      (physlibQuadraticFirstPicardCoefficient
        m kappa radius (phase omega) T observed)
      (physlibFPUTSecondPicardCoefficient
        m kappa beta observed radius (phase omega) T)

/-- Cubic deterministic displacement between the exact and two-step
amplitudes on the supplied energy window. -/
def physlibSecondPicardCouplingDelta
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Site N → Real) (T : Real) (observed : Site N) : Real :=
  |g| ^ 3 *
    cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
      m mUpper kappa beta g H radius T observed

/-! ## Positivity of the extracted unit envelope -/

private theorem firstDuhamelWindowUnitCouplingEnvelope_nonneg
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (kappa beta g actualBound : Real)
    (observed : Site N) (hactualBound : 0 ≤ actualBound) :
    0 ≤ firstDuhamelWindowUnitCouplingEnvelope
      m kappa beta g observed actualBound := by
  unfold firstDuhamelWindowUnitCouplingEnvelope
  have hM2 :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 :
      0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  apply div_nonneg
  · exact add_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg kappa) hM2)
        (sq_nonneg actualBound))
      (mul_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg beta) (abs_nonneg g)) hM3)
        (pow_nonneg hactualBound 3))
  · exact Real.sqrt_nonneg _

private theorem sharpHistoryDefectL1UnitRate_nonneg
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (kappa beta g actualBound : Real)
    (hactualBound : 0 ≤ actualBound) :
    0 ≤ sharpHistoryDefectL1UnitRate m kappa beta g actualBound := by
  unfold sharpHistoryDefectL1UnitRate
  exact Finset.sum_nonneg fun mode _ ↦ mul_nonneg
    (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    (firstDuhamelWindowUnitCouplingEnvelope_nonneg
      m kappa beta g actualBound mode hactualBound)

private theorem sharpFirstPicardRemainderSourceWindowUnitEnvelope_nonneg
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (kappa beta g : Real)
    (observed : Site N)
    {freeBound actualBound defectUnit T : Real}
    (hfreeBound : 0 ≤ freeBound) (hactualBound : 0 ≤ actualBound)
    (hdefectUnit : 0 ≤ defectUnit) (hT : 0 ≤ T) :
    0 ≤ sharpFirstPicardRemainderSourceWindowUnitEnvelope
      m kappa beta g observed freeBound actualBound defectUnit T := by
  unfold sharpFirstPicardRemainderSourceWindowUnitEnvelope
  have hM2 :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 :
      0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hDT : 0 ≤ defectUnit * T := mul_nonneg hdefectUnit hT
  apply div_nonneg
  · exact add_nonneg
      (mul_nonneg (abs_nonneg kappa)
        (mul_nonneg hM2 (add_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hfreeBound) hDT)
          (mul_nonneg (abs_nonneg g) (sq_nonneg (defectUnit * T))))))
      (mul_nonneg (abs_nonneg beta)
        (mul_nonneg hM3 (pow_nonneg hactualBound 3)))
  · exact Real.sqrt_nonneg _

private theorem sharpAfterFirstPicardHistoryL1UnitRate_nonneg
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (kappa beta g : Real)
    {freeBound actualBound defectUnit T : Real}
    (hfreeBound : 0 ≤ freeBound) (hactualBound : 0 ≤ actualBound)
    (hdefectUnit : 0 ≤ defectUnit) (hT : 0 ≤ T) :
    0 ≤ sharpAfterFirstPicardHistoryL1UnitRate
      m kappa beta g freeBound actualBound defectUnit T := by
  unfold sharpAfterFirstPicardHistoryL1UnitRate
  exact Finset.sum_nonneg fun mode _ ↦ mul_nonneg
    (positiveModeCoordinateRecoveryFactor_nonneg m mode)
    (sharpFirstPicardRemainderSourceWindowUnitEnvelope_nonneg
      m kappa beta g mode hfreeBound hactualBound hdefectUnit hT)

private theorem cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope_nonneg
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (kappa beta : Real)
    (observed : Site N)
    {freeBound actualBound defectUnit afterFirstUnit T : Real}
    (hfreeBound : 0 ≤ freeBound) (hactualBound : 0 ≤ actualBound)
    (hdefectUnit : 0 ≤ defectUnit)
    (hafterFirstUnit : 0 ≤ afterFirstUnit) (hT : 0 ≤ T) :
    0 ≤ cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
      m kappa beta observed freeBound actualBound defectUnit afterFirstUnit T := by
  unfold cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
  have hM2 :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 :
      0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hDT : 0 ≤ defectUnit * T := mul_nonneg hdefectUnit hT
  have hAT : 0 ≤ afterFirstUnit * T := mul_nonneg hafterFirstUnit hT
  have hpoly :
      0 ≤ actualBound ^ 2 + actualBound * freeBound + freeBound ^ 2 := by
    positivity
  apply div_nonneg
  · exact add_nonneg
      (add_nonneg
        (mul_nonneg (abs_nonneg kappa)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) hM2) hfreeBound) hAT))
        (mul_nonneg (abs_nonneg kappa)
          (mul_nonneg hM2 (sq_nonneg (defectUnit * T)))))
      (mul_nonneg (abs_nonneg beta)
        (mul_nonneg hM3 (mul_nonneg hDT hpoly)))
  · exact Real.sqrt_nonneg _

/-- The extracted coefficient unit, and hence the complete cubic coupling
radius, is nonnegative under the physical energy-window hypotheses. -/
theorem physlibSecondPicardCouplingDelta_nonneg
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 ≤ H) (hT : 0 ≤ T)
    (radius : Site N → Real) (observed : Site N) :
    0 ≤ physlibSecondPicardCouplingDelta
      m mUpper kappa beta g H radius T observed := by
  have hactual :
      0 ≤ actualModalEnergyL1Envelope N mUpper kappa beta H :=
    actualModalEnergyL1Envelope_nonneg_of_nonneg
      N hmUpper0 hbeta hH
  have hfree : 0 ≤ radiusL1 radius := by
    unfold radiusL1
    positivity
  have hdefect :
      0 ≤ sharpHistoryDefectL1UnitRate
        m kappa beta g
          (actualModalEnergyL1Envelope N mUpper kappa beta H) :=
    sharpHistoryDefectL1UnitRate_nonneg
      m kappa beta g _ hactual
  have hfirst :
      0 ≤ sharpAfterFirstPicardHistoryL1UnitRate
        m kappa beta g (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1UnitRate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H)) T :=
    sharpAfterFirstPicardHistoryL1UnitRate_nonneg
      m kappa beta g hfree hactual hdefect hT
  unfold physlibSecondPicardCouplingDelta
    cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
  exact mul_nonneg (pow_nonneg (abs_nonneg g) 3)
    (mul_nonneg
      (cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope_nonneg
        m kappa beta observed hfree hactual hdefect hfirst hT) hT)

/-! ## Exact Hamiltonian closeness and the block-zero certificate -/

/-- The exact Hamiltonian endpoint differs from its two-step Picard reference
by precisely the post-second-Picard equality remainder. -/
theorem physlibSecondPicard_actual_sub_reference_eq_remainder
    {Omega : Type*} {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (kappa beta g : Real)
    (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations m kappa beta g (p omega) (q omega))
    (radius : Site N → Real)
    (phase : Omega → UnitAddTorus (Site N))
    (hinitial : ∀ omega mode,
      physlibModeAmplitude m mode (p omega) (q omega) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) (phase omega) mode)
    (homega : 0 < modeFrequency m observed) (T : Real) (omega : Omega) :
    physlibSecondPicardActualAmplitude m observed p q T omega -
        physlibSecondPicardReferenceAmplitude
          m kappa beta g observed radius phase T omega =
      physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed (q omega) radius (phase omega) T := by
  have hexact := interactionPicture_physlibMode_eq_twoStep_add_remainder
    m kappa beta g observed (p omega) (q omega) (hp omega) (hq omega)
      (hHamilton omega) homega radius (phase omega) T
  rw [hinitial omega observed] at hexact
  unfold physlibSecondPicardActualAmplitude
    physlibSecondPicardReferenceAmplitude
  rw [hexact]
  abel

/-- The common-source displacement bound is a consequence of the exact
Hamiltonian Duhamel formula and the cubic remainder theorem. -/
theorem physlibSecondPicard_uniformApproximation
    {Omega : Type*} {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations m kappa beta g (p omega) (q omega))
    (radius : Site N → Real)
    (phase : Omega → UnitAddTorus (Site N))
    (hinitial : ∀ omega mode,
      physlibModeAmplitude m mode (p omega) (q omega) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) (phase omega) mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ omega, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q omega)) s) i = 0)
    (henergy : ∀ omega, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p omega)) s))
        (asConfiguration ((realReparametrize (q omega)) s)) ≤ H)
    (hzeroHistory : ∀ omega, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q omega) radius (phase omega) s mode = 0) :
    ∀ omega,
      ‖physlibSecondPicardActualAmplitude m observed p q T omega -
          physlibSecondPicardReferenceAmplitude
            m kappa beta g observed radius phase T omega‖ ≤
        physlibSecondPicardCouplingDelta
          m mUpper kappa beta g H radius T observed := by
  intro omega
  rw [physlibSecondPicard_actual_sub_reference_eq_remainder
    m kappa beta g observed p q hp hq hHamilton radius phase hinitial
      homega T omega]
  exact norm_afterSecondPicardRemainderCoefficient_le_abs_cube_mul_unit
    m hmUpper0 hmassUpper hbeta observed (p omega) (q omega)
      (hp omega) (hq omega) (hHamilton omega) radius (phase omega)
      (hinitial omega) homega hT (hgauge omega) (henergy omega)
        (hzeroHistory omega)

/-- A zero-failure, block-zero coupling between the genuine Hamiltonian
endpoint and its two-step Picard reference. -/
def physlibSecondPicardBlockZeroCouplingCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T referenceRadius : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (hH : 0 ≤ H)
    (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations m kappa beta g (p omega) (q omega))
    (radius : Site N → Real)
    (phase : Omega → UnitAddTorus (Site N))
    (hinitial : ∀ omega mode,
      physlibModeAmplitude m mode (p omega) (q omega) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) (phase omega) mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ omega, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q omega)) s) i = 0)
    (henergy : ∀ omega, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p omega)) s))
        (asConfiguration ((realReparametrize (q omega)) s)) ≤ H)
    (hzeroHistory : ∀ omega, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q omega) radius (phase omega) s mode = 0)
    (hreferenceRadius : 0 ≤ referenceRadius)
    (hactualMeasurable : Measurable
      (physlibSecondPicardActualAmplitude m observed p q T))
    (hreferenceMeasurable : Measurable
      (physlibSecondPicardReferenceAmplitude
        m kappa beta g observed radius phase T))
    (hreferenceBound : ∀ omega,
      ‖physlibSecondPicardReferenceAmplitude
          m kappa beta g observed radius phase T omega‖ ≤ referenceRadius) :
    AmplitudeCouplingRestartCertificate mu
      (referenceRadius + physlibSecondPicardCouplingDelta
        m mUpper kappa beta g H radius T observed) :=
  AmplitudeCouplingRestartCertificate.ofBlockZeroUniformApproximation
    mu referenceRadius
      (physlibSecondPicardActualAmplitude m observed p q T)
      (physlibSecondPicardReferenceAmplitude
        m kappa beta g observed radius phase T)
      (physlibSecondPicardCouplingDelta
        m mUpper kappa beta g H radius T observed)
      hreferenceRadius
      (physlibSecondPicardCouplingDelta_nonneg
        m hmUpper0 hbeta hH hT radius observed)
      hactualMeasurable hreferenceMeasurable
      (physlibSecondPicard_uniformApproximation
        m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
          hinitial homega hT hgauge henergy hzeroHistory)
      hreferenceBound

/-! ## Explicit moment cost -/

/-- At block zero the second-moment coupling cost is exactly of cubic order:
`2 M |g|^3 unit`, with `M = referenceRadius + |g|^3 unit`. -/
theorem physlibSecondPicardBlockZero_secondMomentError
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T referenceRadius : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (hH : 0 ≤ H)
    (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations m kappa beta g (p omega) (q omega))
    (radius : Site N → Real)
    (phase : Omega → UnitAddTorus (Site N))
    (hinitial : ∀ omega mode,
      physlibModeAmplitude m mode (p omega) (q omega) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) (phase omega) mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ omega, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q omega)) s) i = 0)
    (henergy : ∀ omega, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p omega)) s))
        (asConfiguration ((realReparametrize (q omega)) s)) ≤ H)
    (hzeroHistory : ∀ omega, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q omega) radius (phase omega) s mode = 0)
    (hreferenceRadius : 0 ≤ referenceRadius)
    (hactualMeasurable : Measurable
      (physlibSecondPicardActualAmplitude m observed p q T))
    (hreferenceMeasurable : Measurable
      (physlibSecondPicardReferenceAmplitude
        m kappa beta g observed radius phase T))
    (hreferenceBound : ∀ omega,
      ‖physlibSecondPicardReferenceAmplitude
          m kappa beta g observed radius phase T omega‖ ≤ referenceRadius) :
    let certificate := physlibSecondPicardBlockZeroCouplingCertificate
      mu m hmUpper0 hmassUpper hbeta hH observed p q hp hq hHamilton radius
        phase hinitial homega hT hgauge henergy hzeroHistory hreferenceRadius
          hactualMeasurable hreferenceMeasurable hreferenceBound
    |∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
        ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
      2 *
        (referenceRadius + physlibSecondPicardCouplingDelta
          m mUpper kappa beta g H radius T observed) *
        (|g| ^ 3 *
          cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
            m mUpper kappa beta g H radius T observed) := by
  dsimp only
  have hmoment :=
    AmplitudeCouplingRestartCertificate.ofBlockZeroUniformApproximation_second_fourth_moment_errors
      mu referenceRadius
      (physlibSecondPicardActualAmplitude m observed p q T)
      (physlibSecondPicardReferenceAmplitude
        m kappa beta g observed radius phase T)
      (physlibSecondPicardCouplingDelta
        m mUpper kappa beta g H radius T observed)
      hreferenceRadius
      (physlibSecondPicardCouplingDelta_nonneg
        m hmUpper0 hbeta hH hT radius observed)
      hactualMeasurable hreferenceMeasurable
      (physlibSecondPicard_uniformApproximation
        m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
          hinitial homega hT hgauge henergy hzeroHistory)
      hreferenceBound
  exact hmoment.1.trans_eq (by
    unfold physlibSecondPicardCouplingDelta
    rfl)

end

end ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling
