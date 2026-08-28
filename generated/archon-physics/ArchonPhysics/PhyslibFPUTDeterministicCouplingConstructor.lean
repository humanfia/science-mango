import ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
import ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow

/-!
# Deterministic constructors for Physlib FPUT restart couplings

An `AmplitudeCouplingRestartCertificate` allows an exceptional set at every
block.  This file supplies the important zero-exception specialization.  A
measurable, pointwise uniform approximation immediately gives a certificate
with empty bad sets and zero failure probabilities.  Consequently its
second- and fourth-moment costs contain only the deterministic displacement.

The second part pads one genuine Hamiltonian-to-free Duhamel comparison into
block zero.  It does not assert a multiblock RPA restart: all later blocks are
the zero amplitude.  Thus the adapter records exactly what the existing
one-block Hamiltonian estimate proves, without silently adding a stochastic
mixing hypothesis.
-/

namespace ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor

open MeasureTheory
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.Lattice
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
open ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-! ## Empty-bad-set constructors -/

namespace AmplitudeCouplingRestartCertificate

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A pointwise uniform approximation on every block is a coupling
certificate with no exceptional samples and zero failure probability. -/
def ofUniformApproximation
    (mu : Measure Omega) {M : Real}
    (actual reference : Nat → Omega → Complex) (delta : Nat → Real)
    (actual_measurable : ∀ j, Measurable (actual j))
    (reference_measurable : ∀ j, Measurable (reference j))
    (delta_nonneg : ∀ j, 0 ≤ delta j)
    (near : ∀ j omega, ‖actual j omega - reference j omega‖ ≤ delta j)
    (actual_bound : ∀ j omega, ‖actual j omega‖ ≤ M)
    (reference_bound : ∀ j omega, ‖reference j omega‖ ≤ M) :
    AmplitudeCouplingRestartCertificate mu M where
  actual := actual
  reference := reference
  bad := fun _ ↦ ∅
  delta := delta
  failureProbability := fun _ ↦ 0
  actual_measurable := actual_measurable
  reference_measurable := reference_measurable
  bad_measurable := fun _ ↦ MeasurableSet.empty
  delta_nonneg := delta_nonneg
  bad_probability := by simp
  near_on_good := fun j omega _ ↦ near j omega
  actual_bound := actual_bound
  reference_bound := reference_bound

@[simp] theorem ofUniformApproximation_bad
    (mu : Measure Omega) {M : Real}
    (actual reference : Nat → Omega → Complex) (delta : Nat → Real)
    (hactual : ∀ j, Measurable (actual j))
    (hreference : ∀ j, Measurable (reference j))
    (hdelta : ∀ j, 0 ≤ delta j)
    (hnear : ∀ j omega, ‖actual j omega - reference j omega‖ ≤ delta j)
    (hactualBound : ∀ j omega, ‖actual j omega‖ ≤ M)
    (hreferenceBound : ∀ j omega, ‖reference j omega‖ ≤ M)
    (j : Nat) :
    (ofUniformApproximation mu actual reference delta hactual hreference
      hdelta hnear hactualBound hreferenceBound).bad j = ∅ := rfl

@[simp] theorem ofUniformApproximation_failureProbability
    (mu : Measure Omega) {M : Real}
    (actual reference : Nat → Omega → Complex) (delta : Nat → Real)
    (hactual : ∀ j, Measurable (actual j))
    (hreference : ∀ j, Measurable (reference j))
    (hdelta : ∀ j, 0 ≤ delta j)
    (hnear : ∀ j omega, ‖actual j omega - reference j omega‖ ≤ delta j)
    (hactualBound : ∀ j omega, ‖actual j omega‖ ≤ M)
    (hreferenceBound : ∀ j omega, ‖reference j omega‖ ≤ M)
    (j : Nat) :
    (ofUniformApproximation mu actual reference delta hactual hreference
      hdelta hnear hactualBound hreferenceBound).failureProbability j = 0 := rfl

/-- Moment consequence of the empty-bad-set construction.  In particular,
the probability terms from the general coupling theorem vanish exactly. -/
theorem ofUniformApproximation_second_fourth_moment_errors
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (actual reference : Nat → Omega → Complex) (delta : Nat → Real)
    (hactual : ∀ j, Measurable (actual j))
    (hreference : ∀ j, Measurable (reference j))
    (hdelta : ∀ j, 0 ≤ delta j)
    (hnear : ∀ j omega, ‖actual j omega - reference j omega‖ ≤ delta j)
    (hactualBound : ∀ j omega, ‖actual j omega‖ ≤ M)
    (hreferenceBound : ∀ j omega, ‖reference j omega‖ ≤ M)
    (j : Nat) :
    |∫ z, Complex.normSq z
          ∂(ofUniformApproximation mu actual reference delta hactual hreference
            hdelta hnear hactualBound hreferenceBound).actualLaw j -
        ∫ z, Complex.normSq z
          ∂(ofUniformApproximation mu actual reference delta hactual hreference
            hdelta hnear hactualBound hreferenceBound).referenceLaw j| ≤
        2 * M * delta j ∧
    |∫ z, Complex.normSq z ^ 2
          ∂(ofUniformApproximation mu actual reference delta hactual hreference
            hdelta hnear hactualBound hreferenceBound).actualLaw j -
        ∫ z, Complex.normSq z ^ 2
          ∂(ofUniformApproximation mu actual reference delta hactual hreference
            hdelta hnear hactualBound hreferenceBound).referenceLaw j| ≤
        4 * M ^ 3 * delta j := by
  simpa [ofUniformApproximation, couplingSecondMomentDefect,
    couplingFourthMomentDefect] using
    certificate_pushforward_second_fourth_moment_errors mu hM
      (ofUniformApproximation mu actual reference delta hactual hreference
        hdelta hnear hactualBound hreferenceBound) j

/-- Put one uniformly coupled pair at block zero and put the zero amplitude
at every later block.  The common radius `referenceRadius + delta` follows
from the reference bound and the triangle inequality, so an actual-amplitude
bound is not an additional hypothesis. -/
def ofBlockZeroUniformApproximation
    (mu : Measure Omega) (referenceRadius : Real)
    (actual reference : Omega → Complex) (delta : Real)
    (hreferenceRadius : 0 ≤ referenceRadius) (hdelta : 0 ≤ delta)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (hnear : ∀ omega, ‖actual omega - reference omega‖ ≤ delta)
    (hreferenceBound : ∀ omega, ‖reference omega‖ ≤ referenceRadius) :
    AmplitudeCouplingRestartCertificate mu (referenceRadius + delta) := by
  let actualBlocks : Nat → Omega → Complex :=
    fun j ↦ if j = 0 then actual else fun _ ↦ 0
  let referenceBlocks : Nat → Omega → Complex :=
    fun j ↦ if j = 0 then reference else fun _ ↦ 0
  let deltaBlocks : Nat → Real := fun j ↦ if j = 0 then delta else 0
  apply ofUniformApproximation mu actualBlocks referenceBlocks deltaBlocks
  · intro j
    by_cases hj : j = 0
    · simpa [actualBlocks, hj] using hactual
    · simp [actualBlocks, hj]
  · intro j
    by_cases hj : j = 0
    · simpa [referenceBlocks, hj] using hreference
    · simp [referenceBlocks, hj]
  · intro j
    by_cases hj : j = 0
    · simpa [deltaBlocks, hj] using hdelta
    · simp [deltaBlocks, hj]
  · intro j omega
    by_cases hj : j = 0
    · simpa [actualBlocks, referenceBlocks, deltaBlocks, hj] using hnear omega
    · simp [actualBlocks, referenceBlocks, deltaBlocks, hj]
  · intro j omega
    by_cases hj : j = 0
    · have htriangle :
          ‖actual omega‖ ≤
            ‖actual omega - reference omega‖ + ‖reference omega‖ := by
          calc
            ‖actual omega‖ =
                ‖(actual omega - reference omega) + reference omega‖ := by
              congr 1
              abel
            _ ≤ ‖actual omega - reference omega‖ + ‖reference omega‖ :=
              norm_add_le _ _
      simpa [actualBlocks, hj, add_comm] using
        htriangle.trans (add_le_add (hnear omega) (hreferenceBound omega))
    · simp [actualBlocks, hj, add_nonneg hreferenceRadius hdelta]
  · intro j omega
    by_cases hj : j = 0
    · simpa [referenceBlocks, hj] using
        (hreferenceBound omega).trans
          (le_add_of_nonneg_right hdelta)
    · simp [referenceBlocks, hj, add_nonneg hreferenceRadius hdelta]

@[simp] theorem ofBlockZeroUniformApproximation_actual_zero
    (mu : Measure Omega) (referenceRadius : Real)
    (actual reference : Omega → Complex) (delta : Real)
    (hreferenceRadius : 0 ≤ referenceRadius) (hdelta : 0 ≤ delta)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (hnear : ∀ omega, ‖actual omega - reference omega‖ ≤ delta)
    (hreferenceBound : ∀ omega, ‖reference omega‖ ≤ referenceRadius)
    (omega : Omega) :
    (ofBlockZeroUniformApproximation mu referenceRadius actual reference delta
      hreferenceRadius hdelta hactual hreference hnear hreferenceBound).actual
        0 omega = actual omega := by
  simp [ofBlockZeroUniformApproximation, ofUniformApproximation]

@[simp] theorem ofBlockZeroUniformApproximation_reference_zero
    (mu : Measure Omega) (referenceRadius : Real)
    (actual reference : Omega → Complex) (delta : Real)
    (hreferenceRadius : 0 ≤ referenceRadius) (hdelta : 0 ≤ delta)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (hnear : ∀ omega, ‖actual omega - reference omega‖ ≤ delta)
    (hreferenceBound : ∀ omega, ‖reference omega‖ ≤ referenceRadius)
    (omega : Omega) :
    (ofBlockZeroUniformApproximation mu referenceRadius actual reference delta
      hreferenceRadius hdelta hactual hreference hnear hreferenceBound).reference
        0 omega = reference omega := by
  simp [ofBlockZeroUniformApproximation, ofUniformApproximation]

@[simp] theorem ofBlockZeroUniformApproximation_delta_zero
    (mu : Measure Omega) (referenceRadius : Real)
    (actual reference : Omega → Complex) (delta : Real)
    (hreferenceRadius : 0 ≤ referenceRadius) (hdelta : 0 ≤ delta)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (hnear : ∀ omega, ‖actual omega - reference omega‖ ≤ delta)
    (hreferenceBound : ∀ omega, ‖reference omega‖ ≤ referenceRadius) :
    (ofBlockZeroUniformApproximation mu referenceRadius actual reference delta
      hreferenceRadius hdelta hactual hreference hnear hreferenceBound).delta 0 =
        delta := by
  simp [ofBlockZeroUniformApproximation, ofUniformApproximation]

@[simp] theorem ofBlockZeroUniformApproximation_failureProbability_zero
    (mu : Measure Omega) (referenceRadius : Real)
    (actual reference : Omega → Complex) (delta : Real)
    (hreferenceRadius : 0 ≤ referenceRadius) (hdelta : 0 ≤ delta)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (hnear : ∀ omega, ‖actual omega - reference omega‖ ≤ delta)
    (hreferenceBound : ∀ omega, ‖reference omega‖ ≤ referenceRadius) :
    (ofBlockZeroUniformApproximation mu referenceRadius actual reference delta
      hreferenceRadius hdelta hactual hreference hnear hreferenceBound
        ).failureProbability 0 = 0 := by
  simp [ofBlockZeroUniformApproximation, ofUniformApproximation]

/-- At block zero the padded deterministic certificate has precisely the
expected `2 M delta` and `4 M³ delta` moment errors. -/
theorem ofBlockZeroUniformApproximation_second_fourth_moment_errors
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (referenceRadius : Real)
    (actual reference : Omega → Complex) (delta : Real)
    (hreferenceRadius : 0 ≤ referenceRadius) (hdelta : 0 ≤ delta)
    (hactual : Measurable actual) (hreference : Measurable reference)
    (hnear : ∀ omega, ‖actual omega - reference omega‖ ≤ delta)
    (hreferenceBound : ∀ omega, ‖reference omega‖ ≤ referenceRadius) :
    let certificate := ofBlockZeroUniformApproximation mu referenceRadius
      actual reference delta hreferenceRadius hdelta hactual hreference hnear
        hreferenceBound
    |∫ z, Complex.normSq z ∂certificate.actualLaw 0 -
        ∫ z, Complex.normSq z ∂certificate.referenceLaw 0| ≤
          2 * (referenceRadius + delta) * delta ∧
    |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw 0 -
        ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw 0| ≤
          4 * (referenceRadius + delta) ^ 3 * delta := by
  dsimp only
  have hmoment := certificate_pushforward_second_fourth_moment_errors
    mu (add_nonneg hreferenceRadius hdelta)
      (ofBlockZeroUniformApproximation mu referenceRadius actual reference delta
        hreferenceRadius hdelta hactual hreference hnear hreferenceBound) 0
  simpa [couplingSecondMomentDefect, couplingFourthMomentDefect] using hmoment

end AmplitudeCouplingRestartCertificate

/-! ## One exact Physlib Duhamel block -/

/-- Actual block-end amplitude after removing its free phase. -/
def physlibFirstDuhamelActualAmplitude
    {Omega : Type*} {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N) (T : Real) :
    Omega → Complex :=
  fun omega ↦ phaseRenormalize (modeFrequency m observed * T)
    (physlibModeAmplitude m observed (p omega) (q omega) T)

/-- The freely rotating reference is constant in the interaction picture and
therefore equals the initial modal amplitude. -/
def physlibFirstDuhamelReferenceAmplitude
    {Omega : Type*} {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (observed : Site N)
    (p q : Omega → Time → HilbertConfiguration N) : Omega → Complex :=
  fun omega ↦ physlibModeAmplitude m observed (p omega) (q omega) 0

/-- Explicit deterministic coupling radius supplied by the first-Duhamel
energy-window estimate. -/
def physlibFirstDuhamelCouplingRadius
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (observed : Site N) (T : Real) : Real :=
  firstDuhamelWindowEnvelope m kappa beta g observed
    (actualModalEnergyL1Envelope N mUpper kappa beta H) * T

theorem actualModalEnergyL1Envelope_nonneg_of_nonneg
    (N : Nat) {mUpper kappa beta H : Real}
    (hmUpper : 0 ≤ mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 ≤ H) :
    0 ≤ actualModalEnergyL1Envelope N mUpper kappa beta H := by
  have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
    CoerciveCubicPotential.coercivityConstant_pos hbeta
  unfold actualModalEnergyL1Envelope
  positivity

theorem physlibFirstDuhamelCouplingRadius_nonneg
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) {mUpper kappa beta g H T : Real}
    (hmUpper : 0 ≤ mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (observed : Site N) :
    0 ≤ physlibFirstDuhamelCouplingRadius
      m mUpper kappa beta g H observed T := by
  have hactual := actualModalEnergyL1Envelope_nonneg_of_nonneg
    N hmUpper hbeta hH
  unfold physlibFirstDuhamelCouplingRadius firstDuhamelWindowEnvelope
  have hM2 : 0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 : 0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  apply mul_nonneg
  · apply div_nonneg
    · exact add_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (abs_nonneg kappa) (abs_nonneg g)) hM2)
            (sq_nonneg _))
        (mul_nonneg
          (mul_nonneg (mul_nonneg (abs_nonneg beta) (sq_nonneg g)) hM3)
            (pow_nonneg hactual 3))
    · exact Real.sqrt_nonneg _
  · exact hT

/-- The exact Hamiltonian Duhamel formula gives the pointwise uniform
coupling premise for an arbitrary measurable ensemble of trajectories. -/
theorem physlibFirstDuhamel_uniformApproximation
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
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ omega, ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q omega)) time) i = 0)
    (henergy : ∀ omega, ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p omega)) time))
        (asConfiguration ((realReparametrize (q omega)) time)) ≤ H) :
    ∀ omega,
      ‖physlibFirstDuhamelActualAmplitude m observed p q T omega -
          physlibFirstDuhamelReferenceAmplitude m observed p q omega‖ ≤
        physlibFirstDuhamelCouplingRadius
          m mUpper kappa beta g H observed T := by
  intro omega
  exact norm_interactionPicture_physlibMode_sub_initial_le_energyWindow
    m hmUpper0 hmassUpper hbeta observed (p omega) (q omega)
      (hp omega) (hq omega) (hHamilton omega) homega hT
      (hgauge omega) (henergy omega)

/-- Concrete block-zero coupling certificate obtained from the exact Physlib
Hamilton equations.  The only ensemble-level inputs not supplied by the ODE
estimate are measurability and a uniform bound on the initial amplitude. -/
def physlibFirstDuhamelBlockZeroCouplingCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
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
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ omega, ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q omega)) time) i = 0)
    (henergy : ∀ omega, ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p omega)) time))
        (asConfiguration ((realReparametrize (q omega)) time)) ≤ H)
    (hreferenceRadius : 0 ≤ referenceRadius)
    (hactualMeasurable : Measurable
      (physlibFirstDuhamelActualAmplitude m observed p q T))
    (hreferenceMeasurable : Measurable
      (physlibFirstDuhamelReferenceAmplitude m observed p q))
    (hreferenceBound : ∀ omega,
      ‖physlibFirstDuhamelReferenceAmplitude m observed p q omega‖ ≤
        referenceRadius) :
    AmplitudeCouplingRestartCertificate mu
      (referenceRadius + physlibFirstDuhamelCouplingRadius
        m mUpper kappa beta g H observed T) :=
  AmplitudeCouplingRestartCertificate.ofBlockZeroUniformApproximation
    mu referenceRadius
      (physlibFirstDuhamelActualAmplitude m observed p q T)
      (physlibFirstDuhamelReferenceAmplitude m observed p q)
      (physlibFirstDuhamelCouplingRadius
        m mUpper kappa beta g H observed T)
      hreferenceRadius
      (physlibFirstDuhamelCouplingRadius_nonneg
        m hmUpper0 hbeta hH hT observed)
      hactualMeasurable hreferenceMeasurable
      (physlibFirstDuhamel_uniformApproximation
        m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
          hgauge henergy)
      hreferenceBound

end

end ArchonPhysics.PhyslibFPUTDeterministicCouplingConstructor
