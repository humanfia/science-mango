import ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling
import ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation

/-!
# Full-state endpoint propagation from the FPUT second-Picard theorem

`ReHaarizedEndpointPropagationData` uses scalar block maps `ℂ → ℂ`.  A
genuine FPUT endpoint in one observed mode, however, depends on the complete
multimode initial state.  This module therefore gives the type-correct
adapter with a full state space `E`: the block maps have type `E → ℂ`.

The consistency of the exact block at a reference state with its two-step
Picard approximation is not assumed as an inequality.  It follows from the
Hamilton equations, the exact Duhamel identity, and the cubic remainder
theorem in `PhyslibFPUTSecondPicardDeterministicCoupling`.  The only bridge
fields are equalities identifying the abstract full-state block maps with
those two physically constructed endpoint amplitudes.
-/

namespace ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter

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
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-! ## A type-correct full-state deterministic triangle -/

/-- Propagate a full-state initial coupling through an amplitude-valued
block map.  Domain and codomain are deliberately different: `E` contains
all modes, while the endpoint observable is one complex mode amplitude. -/
theorem norm_fullStateBlock_sub_referenceBlock_le
    {E : Type*} [SeminormedAddCommGroup E]
    (actualBlock referenceBlock : E → Complex) (x y : E)
    {initialDelta flowAmplification picardDelta : Real}
    (hflowAmplification : 0 ≤ flowAmplification)
    (hinitial : ‖x - y‖ ≤ initialDelta)
    (hflow : ‖actualBlock x - actualBlock y‖ ≤
      flowAmplification * ‖x - y‖)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta) :
    ‖actualBlock x - referenceBlock y‖ ≤
      flowAmplification * initialDelta + picardDelta := by
  calc
    ‖actualBlock x - referenceBlock y‖ =
        ‖(actualBlock x - actualBlock y) +
          (actualBlock y - referenceBlock y)‖ := by
      congr 1
      abel
    _ ≤ ‖actualBlock x - actualBlock y‖ +
        ‖actualBlock y - referenceBlock y‖ := norm_add_le _ _
    _ ≤ flowAmplification * ‖x - y‖ + picardDelta :=
      add_le_add hflow hpicard
    _ ≤ flowAmplification * initialDelta + picardDelta :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinitial hflowAmplification) le_rfl

/-! ## The Hamiltonian theorem supplies reference consistency -/

/-- On full reference states, the abstract block maps inherit the genuine
Hamiltonian-versus-second-Picard estimate.  The two realization hypotheses
are equalities, not error bounds. -/
theorem physlibSecondPicard_fullState_reference_consistent
    {Omega E : Type*} {N : Nat} [NeZero N]
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
          m (q omega) radius (phase omega) s mode = 0)
    (referenceState : Omega → E)
    (actualBlock referenceBlock : E → Complex)
    (hactualRealization : ∀ omega,
      actualBlock (referenceState omega) =
        physlibSecondPicardActualAmplitude m observed p q T omega)
    (hreferenceRealization : ∀ omega,
      referenceBlock (referenceState omega) =
        physlibSecondPicardReferenceAmplitude
          m kappa beta g observed radius phase T omega) :
    ∀ omega,
      ‖actualBlock (referenceState omega) -
          referenceBlock (referenceState omega)‖ ≤
        physlibSecondPicardCouplingDelta
          m mUpper kappa beta g H radius T observed := by
  intro omega
  rw [hactualRealization omega, hreferenceRealization omega]
  exact physlibSecondPicard_uniformApproximation
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
      hinitial homega hT hgauge henergy hzeroHistory omega

/-- The extracted Picard radius is exactly cubic.  This is the bound required
by endpoint propagation, with no additional consistency-rate assumption. -/
theorem physlibSecondPicardCouplingDelta_le_unit_mul_abs_cube
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Site N → Real) (T : Real) (observed : Site N) :
    physlibSecondPicardCouplingDelta
        m mUpper kappa beta g H radius T observed ≤
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H radius T observed * |g| ^ 3 := by
  unfold physlibSecondPicardCouplingDelta
  rw [mul_comm]

/-! ## Direct full-state endpoint closure -/

/-- A full-state re-Haarized initial coupling propagates to the observed
endpoint with an explicit cubic radius.  The second-Picard part of the
estimate is derived inside the proof from the Hamiltonian dynamics theorem.
-/
theorem physlibSecondPicard_fullState_final_near_abs_cube
    {Omega E : Type*} [SeminormedAddCommGroup E]
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T initialDelta flowAmplification Cinitial : Real}
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
    (hcanonicalInitial : ∀ omega mode,
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
    (actualState referenceState : Omega → E)
    (actualBlock referenceBlock : E → Complex)
    (hflowAmplification : 0 ≤ flowAmplification)
    (hinitial : ∀ omega,
      ‖actualState omega - referenceState omega‖ ≤ initialDelta)
    (hinitialCubic : initialDelta ≤ Cinitial * |g| ^ 3)
    (hflow : ∀ omega,
      ‖actualBlock (actualState omega) -
          actualBlock (referenceState omega)‖ ≤
        flowAmplification *
          ‖actualState omega - referenceState omega‖)
    (hactualRealization : ∀ omega,
      actualBlock (referenceState omega) =
        physlibSecondPicardActualAmplitude m observed p q T omega)
    (hreferenceRealization : ∀ omega,
      referenceBlock (referenceState omega) =
        physlibSecondPicardReferenceAmplitude
          m kappa beta g observed radius phase T omega) :
    ∀ omega,
      ‖actualBlock (actualState omega) -
          referenceBlock (referenceState omega)‖ ≤
        (flowAmplification * Cinitial +
          cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
            m mUpper kappa beta g H radius T observed) * |g| ^ 3 := by
  intro omega
  have hpicard := physlibSecondPicard_fullState_reference_consistent
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
      hcanonicalInitial homega hT hgauge henergy hzeroHistory referenceState
      actualBlock referenceBlock hactualRealization hreferenceRealization omega
  calc
    ‖actualBlock (actualState omega) -
        referenceBlock (referenceState omega)‖ ≤
      flowAmplification * initialDelta +
        physlibSecondPicardCouplingDelta
          m mUpper kappa beta g H radius T observed :=
      norm_fullStateBlock_sub_referenceBlock_le
        actualBlock referenceBlock (actualState omega) (referenceState omega)
          hflowAmplification (hinitial omega) (hflow omega) hpicard
    _ ≤ flowAmplification * (Cinitial * |g| ^ 3) +
        cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
            m mUpper kappa beta g H radius T observed * |g| ^ 3 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinitialCubic hflowAmplification)
        (physlibSecondPicardCouplingDelta_le_unit_mul_abs_cube
          m mUpper kappa beta g H radius T observed)
    _ = (flowAmplification * Cinitial +
          cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
            m mUpper kappa beta g H radius T observed) * |g| ^ 3 := by ring

end

end ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter
