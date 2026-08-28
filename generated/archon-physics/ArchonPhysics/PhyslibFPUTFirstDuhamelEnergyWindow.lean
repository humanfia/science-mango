import ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope

/-!
# First-Duhamel energy-window control for the actual FPUT orbit

The exact Physlib Hamilton trajectory obeys a one-mode interaction-picture
Duhamel formula.  This file bounds its complete nonlinear source directly by
the conserved-energy modal `l1` envelope.  The result gives an unconditional
finite-volume, finite-time estimate of the distance from free propagation.

The bound is deliberately explicit: its leading size is `|g| T`.  It is
therefore useful for a short nonlinear block and also shows why an absolute
energy estimate alone cannot reach the kinetic scale `T ~ g⁻²`.
-/

namespace ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow

open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Uniform source envelope for one observed positive-frequency mode when the
actual modal `l1` history is at most `actualBound`. -/
def firstDuhamelWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N) (actualBound : Real) : Real :=
  ((|kappa| * |g| *
      observedInteractionTensorAbsMass (n := 2) m observed *
        actualBound ^ 2) +
    (|beta| * g ^ 2 *
      observedInteractionTensorAbsMass (n := 3) m observed *
        actualBound ^ 3)) /
    Real.sqrt (2 * modeFrequency m observed)

/-- Pointwise source bound using only the actual modal `l1` envelope. -/
theorem norm_physlibModeRotatedSource_le_firstDuhamelWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (time : Real)
    {actualBound : Real}
    (homega : 0 < modeFrequency m observed)
    (hactual : actualHistoryL1 m q time ≤ actualBound) :
    ‖physlibModeRotatedSource m kappa beta g observed q time‖ ≤
      firstDuhamelWindowEnvelope m kappa beta g observed actualBound := by
  have hactualCurrent0 : 0 ≤ actualHistoryL1 m q time := by
    unfold actualHistoryL1
    exact modalAbsSum_nonneg _
  have hquadratic := abs_distinguishedTensorContraction_le
    m observed (physlibActualModalHistory m q time) (n := 2)
  have hcubic := abs_distinguishedTensorContraction_le
    m observed (physlibActualModalHistory m q time) (n := 3)
  have hpow2 : actualHistoryL1 m q time ^ 2 ≤ actualBound ^ 2 :=
    pow_le_pow_left₀ hactualCurrent0 hactual 2
  have hpow3 : actualHistoryL1 m q time ^ 3 ≤ actualBound ^ 3 :=
    pow_le_pow_left₀ hactualCurrent0 hactual 3
  have hM2 : 0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 : 0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hquadraticBound :
      |distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 2| ≤
        observedInteractionTensorAbsMass (n := 2) m observed *
          actualBound ^ 2 := by
    exact hquadratic.trans (mul_le_mul_of_nonneg_left hpow2 hM2)
  have hcubicBound :
      |distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 3| ≤
        observedInteractionTensorAbsMass (n := 3) m observed *
          actualBound ^ 3 := by
    exact hcubic.trans (mul_le_mul_of_nonneg_left hpow3 hM3)
  unfold physlibModeRotatedSource firstDuhamelWindowEnvelope
    physlibModeTensorForce tensorNonlinearForce
  rw [norm_mul, norm_phaseFactor, one_mul, norm_forcedModeSource homega]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc
    |-(kappa * g * distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 2) -
        beta * g ^ 2 * distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 3| ≤
      |kappa * g * distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 2| +
        |beta * g ^ 2 * distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 3| := by
        rw [show
          -(kappa * g * distinguishedTensorContraction m
              (physlibActualModalHistory m q time) observed 2) -
              beta * g ^ 2 * distinguishedTensorContraction m
                (physlibActualModalHistory m q time) observed 3 =
            -(kappa * g * distinguishedTensorContraction m
                (physlibActualModalHistory m q time) observed 2 +
              beta * g ^ 2 * distinguishedTensorContraction m
                (physlibActualModalHistory m q time) observed 3) by ring,
          abs_neg]
        exact abs_add_le _ _
    _ = |kappa| * |g| *
          |distinguishedTensorContraction m
            (physlibActualModalHistory m q time) observed 2| +
        |beta| * g ^ 2 *
          |distinguishedTensorContraction m
            (physlibActualModalHistory m q time) observed 3| := by
      simp only [abs_mul, abs_pow, sq_abs]
    _ ≤ |kappa| * |g| *
          (observedInteractionTensorAbsMass (n := 2) m observed *
            actualBound ^ 2) +
        |beta| * g ^ 2 *
          (observedInteractionTensorAbsMass (n := 3) m observed *
            actualBound ^ 3) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hquadraticBound (by positivity))
        (mul_le_mul_of_nonneg_left hcubicBound (by positivity))
    _ = _ := by ring

/-- Hamiltonian energy and the translation gauge instantiate the pointwise
source envelope at every time in the supplied window. -/
theorem norm_physlibModeRotatedSource_le_energyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H time : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (homega : 0 < modeFrequency m observed)
    (hgauge : ∑ i, m.mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖physlibModeRotatedSource m kappa beta g observed q time‖ ≤
      firstDuhamelWindowEnvelope m kappa beta g observed
        (actualModalEnergyL1Envelope N mUpper kappa beta H) := by
  apply norm_physlibModeRotatedSource_le_firstDuhamelWindowEnvelope
    m kappa beta g observed q time homega
  exact actualHistoryL1_le_energyEnvelope
    m hmUpper0 hmassUpper hbeta p q time hgauge henergy

/-- Exact Hamiltonian-to-free one-block estimate in the interaction picture.
No RPA or kinetic equation is used. -/
theorem norm_interactionPicture_physlibMode_sub_initial_le_energyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖phaseRenormalize (modeFrequency m observed * T)
          (physlibModeAmplitude m observed p q T) -
        physlibModeAmplitude m observed p q 0‖ ≤
      firstDuhamelWindowEnvelope m kappa beta g observed
          (actualModalEnergyL1Envelope N mUpper kappa beta H) * T := by
  have hexact :=
    interactionPicture_physlibMode_eq_initial_add_integral_of_differentiable
      m kappa beta g observed p q hp hq hHamilton homega T
  rw [hexact]
  simp only [add_sub_cancel_left]
  calc
    ‖∫ time in (0 : Real)..T,
        physlibModeRotatedSource m kappa beta g observed q time‖ ≤
      firstDuhamelWindowEnvelope m kappa beta g observed
          (actualModalEnergyL1Envelope N mUpper kappa beta H) * |T - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro time htime
      have htimeIcc : time ∈ Icc 0 T := by
        simpa only [uIcc_of_le hT] using Set.uIoc_subset_uIcc htime
      exact norm_physlibModeRotatedSource_le_energyWindow
        m hmUpper0 hmassUpper hbeta observed p q homega
          (hgauge time htimeIcc) (henergy time htimeIcc)
    _ = _ := by rw [sub_zero, abs_of_nonneg hT]

/-- Algebraic form of the leading short-block scale. -/
theorem firstDuhamelWindowEnvelope_mul_time_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {g : Real} (hg : 0 ≤ g) (observed : Lattice.Site N)
    (actualBound T : Real) :
    firstDuhamelWindowEnvelope m kappa beta g observed actualBound * T =
      ((|kappa| * g *
          observedInteractionTensorAbsMass (n := 2) m observed *
            actualBound ^ 2) +
        (|beta| * g ^ 2 *
          observedInteractionTensorAbsMass (n := 3) m observed *
            actualBound ^ 3)) /
        Real.sqrt (2 * modeFrequency m observed) * T := by
  unfold firstDuhamelWindowEnvelope
  rw [abs_of_nonneg hg]

end

end ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
