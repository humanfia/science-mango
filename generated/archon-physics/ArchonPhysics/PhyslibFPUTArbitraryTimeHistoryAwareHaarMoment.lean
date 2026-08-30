import ArchonPhysics.PhyslibFPUTSecondBlockHistoryAwareHaarMoment

/-!
# Arbitrary-time history-aware Haar moment increments

The second-block identity at `T` and `2 * T` is not tied to that particular
partition.  For any two times `s` and `t`, the reference increment based on
the same canonical Haar initial phase is the difference of the two global
Picard references.  Consequently its quadratic term is the full
history-aware difference `g^2 * (K(t) - K(s))`, followed by the exact cubic
and quartic endpoint differences.

For a genuine Hamiltonian orbit, comparing the actual moment with the same
initial-Haar reference at each endpoint gives an increment discrepancy
bounded by the sum of the two endpoint cubic envelopes.  No ordering between
`s` and `t`, restart, or Haar hypothesis at an intermediate time is used.
-/

namespace ArchonPhysics.PhyslibFPUTArbitraryTimeHistoryAwareHaarMoment

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
open ArchonPhysics.QuadraticTensorHistoryExpansion

noncomputable section

/-- Exact history-aware reference increment between arbitrary times.  The
identity is algebraic and therefore needs neither nonnegativity nor an
ordering assumption on the two endpoints. -/
theorem physlibReference_arbitraryTimeIncrement_eq_historyAwareKinetic_add_highOrder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (s t : Real)
    (observed : Lattice.Site N) (g : Real)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
          m kappa beta g radius t observed -
        physlibReferenceTwoStepHaarMoment
          m kappa beta g radius s observed =
      g ^ 2 *
          (physlibHaarFiniteTimeKineticCoefficient
              m kappa beta radius t observed -
            physlibHaarFiniteTimeKineticCoefficient
              m kappa beta radius s observed) +
        g ^ 3 *
          (equalChargeFamilyInterference
              (physlibQuadraticFirstPicardCharacterCoefficient
                m kappa radius t observed)
              quadraticPhaseCharge
              (completeSecondPicardCoefficient
                m kappa beta radius observed t)
              completeSecondPicardCharge -
            equalChargeFamilyInterference
              (physlibQuadraticFirstPicardCharacterCoefficient
                m kappa radius s observed)
              quadraticPhaseCharge
              (completeSecondPicardCoefficient
                m kappa beta radius observed s)
              completeSecondPicardCharge) +
        g ^ 4 *
          (sameChargeFamilySquare
              (completeSecondPicardCoefficient
                m kappa beta radius observed t)
              completeSecondPicardCharge -
            sameChargeFamilySquare
              (completeSecondPicardCoefficient
                m kappa beta radius observed s)
              completeSecondPicardCharge) := by
  have ht :=
    physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
      m kappa beta radius t observed g homega
  have hs :=
    physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
      m kappa beta radius s observed g homega
  linarith

/-- On one Hamiltonian orbit with one canonical Haar initial phase, the
actual increment between arbitrary nonnegative endpoints is cubically close
to the history-aware reference increment.  A common energy-window hypothesis
through `max s t` supplies both endpoint estimates, so no ordering of the
endpoints is required. -/
theorem abs_actualHaarModalMoment_arbitraryTimeIncrement_sub_historyAwareReference_le_abs_cube
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H s t : Real}
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
    (hs : 0 <= s) (ht : 0 <= t)
    (hgauge : forall phase u, u ∈ Icc 0 (max s t) -> ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) u) i = 0)
    (henergy : forall phase u, u ∈ Icc 0 (max s t) ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) u))
        (asConfiguration ((realReparametrize (q phase)) u)) <= H)
    (hzeroHistory : forall phase u, u ∈ Icc 0 (max s t) -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q phase) radius phase u mode = 0)
    (hmeasurableS : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius s))
    (hmeasurableT : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius t)) :
    |(actualHaarModalMoment m observed p q t -
          actualHaarModalMoment m observed p q s) -
        (physlibReferenceTwoStepHaarMoment
            m kappa beta g radius t observed -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius s observed)| <=
      |g| ^ 3 *
        (physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta g H radius t observed +
          physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta g H radius s observed) := by
  have hgaugeS : forall phase u, u ∈ Icc 0 s -> ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) u) i = 0 := by
    intro phase u hu
    exact hgauge phase u ⟨hu.1, hu.2.trans (le_max_left s t)⟩
  have henergyS : forall phase u, u ∈ Icc 0 s ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) u))
        (asConfiguration ((realReparametrize (q phase)) u)) <= H := by
    intro phase u hu
    exact henergy phase u ⟨hu.1, hu.2.trans (le_max_left s t)⟩
  have hzeroHistoryS : forall phase u, u ∈ Icc 0 s -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q phase) radius phase u mode = 0 := by
    intro phase u hu mode hmode
    exact hzeroHistory phase u ⟨hu.1, hu.2.trans (le_max_left s t)⟩ mode hmode
  have hgaugeT : forall phase u, u ∈ Icc 0 t -> ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) u) i = 0 := by
    intro phase u hu
    exact hgauge phase u ⟨hu.1, hu.2.trans (le_max_right s t)⟩
  have henergyT : forall phase u, u ∈ Icc 0 t ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) u))
        (asConfiguration ((realReparametrize (q phase)) u)) <= H := by
    intro phase u hu
    exact henergy phase u ⟨hu.1, hu.2.trans (le_max_right s t)⟩
  have hzeroHistoryT : forall phase u, u ∈ Icc 0 t -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q phase) radius phase u mode = 0 := by
    intro phase u hu mode hmode
    exact hzeroHistory phase u ⟨hu.1, hu.2.trans (le_max_right s t)⟩ mode hmode
  have hendpointS :=
    abs_actualHaarModalMoment_firstShift_sub_twoStepReference_le_abs_cube
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius
        homega hinitial hs hgaugeS henergyS hzeroHistoryS hmeasurableS
  have hendpointT :=
    abs_actualHaarModalMoment_firstShift_sub_twoStepReference_le_abs_cube
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius
        homega hinitial ht hgaugeT henergyT hzeroHistoryT hmeasurableT
  calc
    |(actualHaarModalMoment m observed p q t -
          actualHaarModalMoment m observed p q s) -
        (physlibReferenceTwoStepHaarMoment
            m kappa beta g radius t observed -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius s observed)| =
      |(actualHaarModalMoment m observed p q t -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius t observed) -
        (actualHaarModalMoment m observed p q s -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius s observed)| := by congr 1 <;> ring
    _ <=
        |actualHaarModalMoment m observed p q t -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius t observed| +
        |actualHaarModalMoment m observed p q s -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius s observed| := abs_sub _ _
    _ <=
        |g| ^ 3 *
            physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
              m mUpper kappa beta g H radius t observed +
          |g| ^ 3 *
            physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
              m mUpper kappa beta g H radius s observed :=
      add_le_add hendpointT hendpointS
    _ = _ := by ring

end

end ArchonPhysics.PhyslibFPUTArbitraryTimeHistoryAwareHaarMoment
