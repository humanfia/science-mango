import ArchonPhysics.PhyslibFPUTArbitraryTimeHistoryAwareHaarMoment

/-!
# History-aware Haar moments on a natural block partition

This module specializes the arbitrary-endpoint initial-Haar identity to the
block `[j * T, (j + 1) * T]`.  These are differences of one global reference
based at time zero; they are not freshly Haarized block references.

The reference increments telescope exactly over the first `K` blocks.  The
corresponding actual/reference cumulative estimate is proved by comparing
only the two global endpoints `0` and `K * T`.  Thus its cubic bound contains
the two endpoint envelopes, not a sum of `K` independent restart errors.
-/

namespace ArchonPhysics.PhyslibFPUTHistoryAwareNatBlockHaarMoment

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
open ArchonPhysics.PhyslibFPUTArbitraryTimeHistoryAwareHaarMoment
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
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

/-- Exact history-aware reference increment on the natural block
`[j * T, (j + 1) * T]`.  No sign condition on `T` is needed for this
algebraic specialization. -/
theorem physlibReference_natBlockIncrement_eq_historyAwareKinetic_add_highOrder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (T : Real) (j : Nat)
    (observed : Lattice.Site N) (g : Real)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
          m kappa beta g radius (((j + 1 : Nat) : Real) * T) observed -
        physlibReferenceTwoStepHaarMoment
          m kappa beta g radius (j * T) observed =
      g ^ 2 *
          (physlibHaarFiniteTimeKineticCoefficient
              m kappa beta radius (((j + 1 : Nat) : Real) * T) observed -
            physlibHaarFiniteTimeKineticCoefficient
              m kappa beta radius (j * T) observed) +
        g ^ 3 *
          (equalChargeFamilyInterference
              (physlibQuadraticFirstPicardCharacterCoefficient
                m kappa radius (((j + 1 : Nat) : Real) * T) observed)
              quadraticPhaseCharge
              (completeSecondPicardCoefficient
                m kappa beta radius observed (((j + 1 : Nat) : Real) * T))
              completeSecondPicardCharge -
            equalChargeFamilyInterference
              (physlibQuadraticFirstPicardCharacterCoefficient
                m kappa radius (j * T) observed)
              quadraticPhaseCharge
              (completeSecondPicardCoefficient
                m kappa beta radius observed (j * T))
              completeSecondPicardCharge) +
        g ^ 4 *
          (sameChargeFamilySquare
              (completeSecondPicardCoefficient
                m kappa beta radius observed (((j + 1 : Nat) : Real) * T))
              completeSecondPicardCharge -
            sameChargeFamilySquare
              (completeSecondPicardCoefficient
                m kappa beta radius observed (j * T))
              completeSecondPicardCharge) := by
  simpa using
    physlibReference_arbitraryTimeIncrement_eq_historyAwareKinetic_add_highOrder
      m kappa beta radius (j * T) (((j + 1 : Nat) : Real) * T)
        observed g homega

/-- The first `K` history-aware reference blocks telescope to the single
global reference increment from `0` to `K * T`.  This identity is purely
algebraic and needs no frequency, positivity, or Haar-restart hypothesis. -/
theorem physlibReference_natBlockIncrements_sum_eq_endpointIncrement
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) (K : Nat) :
    (∑ j ∈ Finset.range K,
        (physlibReferenceTwoStepHaarMoment
            m kappa beta g radius (((j + 1 : Nat) : Real) * T) observed -
          physlibReferenceTwoStepHaarMoment
            m kappa beta g radius (j * T) observed)) =
      physlibReferenceTwoStepHaarMoment
          m kappa beta g radius (K * T) observed -
        physlibReferenceTwoStepHaarMoment
          m kappa beta g radius 0 observed := by
  simpa only [Nat.cast_zero, zero_mul] using
    (Finset.sum_range_sub
      (fun j : Nat =>
        physlibReferenceTwoStepHaarMoment
          m kappa beta g radius (j * T) observed) K)

/-- Endpoint-method cumulative discrepancy for the first `K` blocks.

Both the actual increments and the history-aware reference increments are
telescoped before applying the arbitrary-time endpoint theorem.  Therefore
only the cubic envelopes at `0` and `K * T` occur.  This is not a per-block
triangle estimate and makes no independent re-Haar assumption at any of the
`K - 1` intermediate endpoints. -/
theorem abs_sum_actual_natBlockIncrements_sub_historyAwareReferenceIncrements_le_endpoint_abs_cube
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
    (hT : 0 <= T) (K : Nat)
    (hgauge : forall phase u, u ∈ Icc 0 (K * T) -> ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) u) i = 0)
    (henergy : forall phase u, u ∈ Icc 0 (K * T) ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) u))
        (asConfiguration ((realReparametrize (q phase)) u)) <= H)
    (hzeroHistory : forall phase u, u ∈ Icc 0 (K * T) -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q phase) radius phase u mode = 0)
    (hmeasurable0 : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius 0))
    (hmeasurableK : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius (K * T))) :
    |(∑ j ∈ Finset.range K,
          (actualHaarModalMoment m observed p q
              (((j + 1 : Nat) : Real) * T) -
            actualHaarModalMoment m observed p q (j * T))) -
        (∑ j ∈ Finset.range K,
          (physlibReferenceTwoStepHaarMoment
              m kappa beta g radius (((j + 1 : Nat) : Real) * T) observed -
            physlibReferenceTwoStepHaarMoment
              m kappa beta g radius (j * T) observed))| <=
      |g| ^ 3 *
        (physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta g H radius (K * T) observed +
          physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta g H radius 0 observed) := by
  have hKT : 0 <= (K : Real) * T :=
    mul_nonneg (Nat.cast_nonneg K) hT
  have hgaugeMax : forall phase u, u ∈ Icc 0 (max 0 (K * T)) ->
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) u) i = 0 := by
    simpa only [max_eq_right hKT] using hgauge
  have henergyMax : forall phase u, u ∈ Icc 0 (max 0 (K * T)) ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) u))
        (asConfiguration ((realReparametrize (q phase)) u)) <= H := by
    simpa only [max_eq_right hKT] using henergy
  have hzeroHistoryMax :
      forall phase u, u ∈ Icc 0 (max 0 (K * T)) -> forall mode,
        modeFrequency m mode = 0 ->
          physlibModalHistoryDefect m (q phase) radius phase u mode = 0 := by
    simpa only [max_eq_right hKT] using hzeroHistory
  have hendpoint :=
    abs_actualHaarModalMoment_arbitraryTimeIncrement_sub_historyAwareReference_le_abs_cube
      (s := 0) (t := K * T) m hmUpper0 hmassUpper hbeta observed p q hp hq
        hHamilton radius homega hinitial (by positivity) hKT hgaugeMax
          henergyMax hzeroHistoryMax hmeasurable0 hmeasurableK
  have hactualTelescope :
      (∑ j ∈ Finset.range K,
          (actualHaarModalMoment m observed p q
              (((j + 1 : Nat) : Real) * T) -
            actualHaarModalMoment m observed p q (j * T))) =
        actualHaarModalMoment m observed p q (K * T) -
          actualHaarModalMoment m observed p q 0 := by
    simpa only [Nat.cast_zero, zero_mul] using
      (Finset.sum_range_sub
        (fun j : Nat =>
          actualHaarModalMoment m observed p q (j * T)) K)
  rw [hactualTelescope,
    physlibReference_natBlockIncrements_sum_eq_endpointIncrement]
  exact hendpoint

end

end ArchonPhysics.PhyslibFPUTHistoryAwareNatBlockHaarMoment
