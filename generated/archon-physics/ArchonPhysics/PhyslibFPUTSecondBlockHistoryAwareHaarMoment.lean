import ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation
import ArchonPhysics.PhyslibHamiltonTwoTimeDuhamel

/-!
# The second physical FPUT block with its Hamiltonian history retained

The same canonical Haar phases are used for one genuine Hamiltonian orbit
from time zero through `2 * T`; there is no restart or re-Haarization input.
The correct two-step reference for the interval `[T, 2T]` is therefore the
difference of the two global Picard references based at time zero.

Its order-two term is

`g^2 * (K(2T) - K(T))`.

This is a history-aware collision coefficient.  In particular, it retains
the equal-charge cross terms between the first-Picard history accumulated on
`[0,T]` and the new first-Picard contribution on `[T,2T]`; initial Haar charge
selection does not turn it into a fresh independent Haar block.

The actual endpoint increment is nevertheless cubically close to this
history-aware reference increment.  This is a genuine two-block consequence
of the Hamiltonian Duhamel/Picard expansion, not a restart certificate.
-/

namespace ArchonPhysics.PhyslibFPUTSecondBlockHistoryAwareHaarMoment

open MeasureTheory
open Set
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonTwoTimeDuhamel
open ArchonPhysics.QuadraticTensorHistoryExpansion

noncomputable section

/-- Exact second-block expansion of the canonical initial-Haar reference.
The displayed order-two coefficient is the whole history-aware block
collision term; the remaining reference terms start at order three. -/
theorem physlibReference_secondBlockIncrement_eq_historyAwareKinetic_add_highOrder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) (g : Real)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
          m kappa beta g radius (2 * T) observed -
        physlibReferenceTwoStepHaarMoment
          m kappa beta g radius T observed =
      g ^ 2 *
          (physlibHaarFiniteTimeKineticCoefficient
              m kappa beta radius (2 * T) observed -
            physlibHaarFiniteTimeKineticCoefficient
              m kappa beta radius T observed) +
        g ^ 3 *
          (equalChargeFamilyInterference
              (physlibQuadraticFirstPicardCharacterCoefficient
                m kappa radius (2 * T) observed)
              quadraticPhaseCharge
              (completeSecondPicardCoefficient
                m kappa beta radius observed (2 * T))
              completeSecondPicardCharge -
            equalChargeFamilyInterference
              (physlibQuadraticFirstPicardCharacterCoefficient
                m kappa radius T observed)
              quadraticPhaseCharge
              (completeSecondPicardCoefficient
                m kappa beta radius observed T)
              completeSecondPicardCharge) +
        g ^ 4 *
          (sameChargeFamilySquare
              (completeSecondPicardCoefficient
                m kappa beta radius observed (2 * T))
              completeSecondPicardCharge -
            sameChargeFamilySquare
              (completeSecondPicardCoefficient
                m kappa beta radius observed T)
              completeSecondPicardCharge) := by
  have htwo :=
    physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
      m kappa beta radius (2 * T) observed g homega
  have hone :=
    physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
      m kappa beta radius T observed g homega
  linarith

/-- On the same physical Hamiltonian orbit, the actual quadratic modal-moment
increment over `[T,2T]` is cubically close to the history-aware reference
increment.  Both endpoint comparisons use the original canonical Haar phase;
no law at time `T` is assumed to be Haar. -/
theorem abs_actualHaarModalMoment_secondBlockIncrement_sub_historyAwareReference_le_abs_cube
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 <= mUpper) (hmassUpper : forall i, m.mass i <= mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) -> Time -> HilbertConfiguration N)
    (hp : forall phase, Differentiable Real (p phase))
    (hq : forall phase, Differentiable Real (q phase))
    (hHamilton : forall phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N -> Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : forall phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (hT : 0 <= T)
    (hgauge : forall phase s, s ∈ Icc 0 (2 * T) -> ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergy : forall phase s, s ∈ Icc 0 (2 * T) ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) <= H)
    (hzeroHistory : forall phase s, s ∈ Icc 0 (2 * T) -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q phase) radius phase s mode = 0)
    (hmeasurableT : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T))
    (hmeasurable2T : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius (2 * T))) :
    |(actualHaarModalMoment m observed p q (2 * T) -
          actualHaarModalMoment m observed p q T) -
        (physlibReferenceTwoStepHaarMoment
            m kappa beta g radius (2 * T) observed -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius T observed)| <=
      |g| ^ 3 *
        (physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta g H radius (2 * T) observed +
          physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta g H radius T observed) := by
  have h2T : 0 <= 2 * T := mul_nonneg (by norm_num) hT
  have hgaugeT : forall phase s, s ∈ Icc 0 T -> ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0 := by
    intro phase s hs
    apply hgauge phase s
    exact ⟨hs.1, by nlinarith [hs.2, hT]⟩
  have henergyT : forall phase s, s ∈ Icc 0 T ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) <= H := by
    intro phase s hs
    apply henergy phase s
    exact ⟨hs.1, by nlinarith [hs.2, hT]⟩
  have hzeroHistoryT : forall phase s, s ∈ Icc 0 T -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q phase) radius phase s mode = 0 := by
    intro phase s hs mode hmode
    exact hzeroHistory phase s ⟨hs.1, by nlinarith [hs.2, hT]⟩ mode hmode
  have hfirst :=
    abs_actualHaarModalMoment_firstShift_sub_twoStepReference_le_abs_cube
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius
        homega hinitial hT hgaugeT henergyT hzeroHistoryT hmeasurableT
  have hsecond :=
    abs_actualHaarModalMoment_firstShift_sub_twoStepReference_le_abs_cube
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius
        homega hinitial h2T hgauge henergy hzeroHistory hmeasurable2T
  calc
    |(actualHaarModalMoment m observed p q (2 * T) -
          actualHaarModalMoment m observed p q T) -
        (physlibReferenceTwoStepHaarMoment
            m kappa beta g radius (2 * T) observed -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius T observed)| =
      |(actualHaarModalMoment m observed p q (2 * T) -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius (2 * T) observed) -
        (actualHaarModalMoment m observed p q T -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius T observed)| := by congr 1 <;> ring
    _ <=
        |actualHaarModalMoment m observed p q (2 * T) -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius (2 * T) observed| +
        |actualHaarModalMoment m observed p q T -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius T observed| := abs_sub _ _
    _ <=
        |g| ^ 3 *
            physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
              m mUpper kappa beta g H radius (2 * T) observed +
          |g| ^ 3 *
            physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
              m mUpper kappa beta g H radius T observed :=
      add_le_add hsecond hfirst
    _ = _ := by ring

end

end ArchonPhysics.PhyslibFPUTSecondBlockHistoryAwareHaarMoment
