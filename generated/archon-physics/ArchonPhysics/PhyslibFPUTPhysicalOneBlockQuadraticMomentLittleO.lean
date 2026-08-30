import ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
import ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

/-!
# A physical one-block quadratic collision moment has little-o residual

This module directly joins the actual finite-volume Hamiltonian/Haar theorem
to its explicit coupling-limit estimate.  No restart certificate and no
assumed `MomentKineticEulerResidual` occurs in the hypotheses.

For one fixed observed mode, the observable is the Haar-averaged quadratic
modal energy `|a_q|^2`.  Its order-two collision coefficient is the existing
`normalizedSecondOrderHaarBroadening`, whose construction uses the exact
finite Haar charge identities and fourth phase moments.  A family of genuine
Hamiltonian blocks with coupling `g_n -> 0` therefore has both

* the explicit one-block `MomentKineticEulerResidual`; and
* actual residual divided by `g_n^2 T` tending to zero.

The result is fixed-volume, fixed-positive-block-time, and for the singleton
observable family selected by `observed`.  It does not assert that a coherent
Hamiltonian trajectory regenerates the canonical Haar initial data at each
of `O(|g|^-2)` consecutive blocks.
-/

namespace ArchonPhysics.PhyslibFPUTPhysicalOneBlockQuadraticMomentLittleO

open Filter
open MeasureTheory
open Set
open Topology
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- A sequence of actual Hamiltonian/Haar blocks at fixed `N` and fixed
positive `T` supplies a quadratic modal-energy collision residual whose
ratio to the kinetic step tends to zero.

The first conjunct retains the exact residual API consumed downstream.  The
second conjunct is stronger than a bound on an auxiliary defect: it is the
normalized absolute residual of the physical Haar moment itself. -/
theorem physicalHamiltonian_quadraticCollisionMoment_residual_and_littleO
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta H : Real)
    (hmUpper0 : 0 <= mUpper) (hmassUpper : forall i, m.mass i <= mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N -> Real)
    (homega : 0 < modeFrequency m observed)
    {T : Real} (hT : 0 < T)
    (g : Nat -> Real)
    (p q : Nat -> UnitAddTorus (Lattice.Site N) ->
      Time -> HilbertConfiguration N)
    (hp : forall n phase, Differentiable Real (p n phase))
    (hq : forall n phase, Differentiable Real (q n phase))
    (hHamilton : forall n phase,
      SatisfiesHamiltonEquations m kappa beta (g n)
        (p n phase) (q n phase))
    (hinitial : forall n phase mode,
      physlibModeAmplitude m mode (p n phase) (q n phase) 0 =
        canonicalFreeComplexInitialAmplitude
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) phase mode)
    (hgauge : forall n phase s, s ∈ Icc 0 T ->
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q n phase)) s) i = 0)
    (henergyWindow : forall n phase s, s ∈ Icc 0 T ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta (g n)
        (asConfiguration ((realReparametrize (p n phase)) s))
        (asConfiguration ((realReparametrize (q n phase)) s)) <= H)
    (hzeroHistory : forall n phase s, s ∈ Icc 0 T -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q n phase)
          (phaseEnergyRadius energy (modeFrequency m)) phase s mode = 0)
    (hmeasurable : forall n, Measurable
      (actualPostSecondPicardEnergyCorrection m kappa beta (g n) observed
        (q n) (phaseEnergyRadius energy (modeFrequency m)) T))
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    (forall n,
      MomentKineticEulerResidual
        (actualHaarModalMoment m observed (p n) (q n) 0)
        (actualHaarModalMoment m observed (p n) (q n) T)
        (g n ^ 2 * T)
        (normalizedSecondOrderHaarBroadening
          m kappa beta energy observed T)
        (physlibFPUTKineticLittleORhs m mUpper kappa beta H
          (phaseEnergyRadius energy (modeFrequency m)) T observed (g n))) /\
      Tendsto
        (fun n =>
          |actualHaarModalMoment m observed (p n) (q n) T -
              actualHaarModalMoment m observed (p n) (q n) 0 -
              (g n ^ 2 * T) *
                normalizedSecondOrderHaarBroadening
                  m kappa beta energy observed T| /
            (g n ^ 2 * T))
        atTop (nhds 0) := by
  have hresidual : forall n,
      MomentKineticEulerResidual
        (actualHaarModalMoment m observed (p n) (q n) 0)
        (actualHaarModalMoment m observed (p n) (q n) T)
        (g n ^ 2 * T)
        (normalizedSecondOrderHaarBroadening
          m kappa beta energy observed T)
        (physlibFPUTKineticLittleORhs m mUpper kappa beta H
          (phaseEnergyRadius energy (modeFrequency m)) T observed (g n)) := by
    intro n
    simpa only [MomentKineticEulerResidual, actualHaarModalMoment] using
      abs_actual_Haar_drift_sub_finiteTimeKineticStep_le_cubicLittleORhs
        m hmUpper0 hmassUpper hbeta observed (p n) (q n)
          (hp n) (hq n) (hHamilton n) energy homega (hinitial n) hT
          (hgauge n) (henergyWindow n) (hzeroHistory n) (hmeasurable n)
  refine ⟨hresidual, ?_⟩
  have hbound : forall n,
      |actualHaarModalMoment m observed (p n) (q n) T -
          actualHaarModalMoment m observed (p n) (q n) 0 -
          (g n ^ 2 * T) *
            normalizedSecondOrderHaarBroadening
              m kappa beta energy observed T| <=
        physlibFPUTKineticLittleORhs m mUpper kappa beta H
          (phaseEnergyRadius energy (modeFrequency m)) T observed (g n) := by
    intro n
    simpa only [MomentKineticEulerResidual] using hresidual n
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _)
        (mul_nonneg (sq_nonneg (g n)) hT.le)
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right (hbound n)
        (mul_nonneg (sq_nonneg (g n)) hT.le)
  · exact
      physlibFPUTKineticLittleORhs_sequence_div_kineticScale_tendsto_zero
        m mUpper kappa beta H
          (phaseEnergyRadius energy (modeFrequency m)) hT observed
          g hg hg0

end

end ArchonPhysics.PhyslibFPUTPhysicalOneBlockQuadraticMomentLittleO
