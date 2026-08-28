import ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
import ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter

/-!
# Physical constructor for a full-state FPUT endpoint block

This module removes the abstract second-Picard consistency radius from one
full-state endpoint block.  Its input is physical Hamiltonian trajectory
data together with the still-conditional full-state RPA coupling.  The
output is `FullStateEndpointPropagationData` whose

* `picardDelta` is the radius extracted from the proved second-Picard
  Hamiltonian estimate, and
* `reference_consistent` is a theorem, not an input inequality.

Thus this adapter does not solve nonlinear RPA generation.  It isolates
that open input in `initial_state_near` while deriving the deterministic
Hamiltonian-to-Picard edge and its exact cubic coefficient.
-/

namespace ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockData

open MeasureTheory
open Set
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
open ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling
open ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Physical data for one independently re-Haarized FPUT block.

The only proximity field is `initial_state_near`, the quantitative RPA
coupling at the beginning of the block.  In particular there is no
`reference_consistent` field and no separately chosen `picardDelta`.
-/
structure PhysicalFullStateBlockData
    (Omega X : Type*) [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) (M : Real)
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    (mUpper kappa beta g H T : Real) (observed : Site N) where
  actualInitial : Omega → X
  referenceInitial : Omega → X
  initialAmplitude : X → Complex
  actualBlock : X → Complex
  referenceBlock : X → Complex
  stateDelta : Real
  initialObservableAmplification : NNReal
  flowAmplification : NNReal
  radius : Site N → Real
  phase : Omega → UnitAddTorus (Site N)
  p : Omega → Time → HilbertConfiguration N
  q : Omega → Time → HilbertConfiguration N
  M_nonneg : 0 ≤ M
  stateDelta_nonneg : 0 ≤ stateDelta
  mUpper_nonneg : 0 ≤ mUpper
  mass_upper : ∀ i, m.mass i ≤ mUpper
  beta_coercive : 2 * kappa ^ 2 / 9 < beta
  H_nonneg : 0 ≤ H
  T_nonneg : 0 ≤ T
  p_differentiable : ∀ omega, Differentiable Real (p omega)
  q_differentiable : ∀ omega, Differentiable Real (q omega)
  hamiltonian : ∀ omega,
    SatisfiesHamiltonEquations m kappa beta g (p omega) (q omega)
  canonical_initial : ∀ omega mode,
    physlibModeAmplitude m mode (p omega) (q omega) 0 =
      canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) (phase omega) mode
  observed_frequency_pos : 0 < modeFrequency m observed
  gauge : ∀ omega, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
    asConfiguration ((realReparametrize (q omega)) s) i = 0
  energy_window : ∀ omega, ∀ s ∈ Icc 0 T,
    CoerciveLatticeEnergy.hamiltonian m kappa beta g
      (asConfiguration ((realReparametrize (p omega)) s))
      (asConfiguration ((realReparametrize (q omega)) s)) ≤ H
  zero_mode_history : ∀ omega, ∀ s ∈ Icc 0 T, ∀ mode,
    modeFrequency m mode = 0 →
      physlibModalHistoryDefect m (q omega) radius (phase omega) s mode = 0
  actual_realization : ∀ omega,
    actualBlock (referenceInitial omega) =
      physlibSecondPicardActualAmplitude m observed p q T omega
  reference_realization : ∀ omega,
    referenceBlock (referenceInitial omega) =
      physlibSecondPicardReferenceAmplitude
        m kappa beta g observed radius phase T omega
  actualInitial_measurable : Measurable actualInitial
  referenceInitial_measurable : Measurable referenceInitial
  initialAmplitude_lipschitz :
    LipschitzWith initialObservableAmplification initialAmplitude
  actualBlock_lipschitz : LipschitzWith flowAmplification actualBlock
  referenceBlock_measurable : Measurable referenceBlock
  initial_state_near : ∀ omega,
    dist (actualInitial omega) (referenceInitial omega) ≤ stateDelta
  actualInitial_bound : ∀ omega,
    ‖initialAmplitude (actualInitial omega)‖ ≤ M
  referenceInitial_bound : ∀ omega,
    ‖initialAmplitude (referenceInitial omega)‖ ≤ M
  actualFinal_bound : ∀ omega,
    ‖actualBlock (actualInitial omega)‖ ≤ M
  referenceFinal_bound : ∀ omega,
    ‖referenceBlock (referenceInitial omega)‖ ≤ M

namespace PhysicalFullStateBlockData

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} {M : Real}
  {N : Nat} [NeZero N]
  {m : PositiveMassConfig N}
  {mUpper kappa beta g H T : Real} {observed : Site N}

/-- The deterministic Picard radius selected by the physical block. -/
def picardDelta
    (_data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed) : Real :=
  physlibSecondPicardCouplingDelta
    m mUpper kappa beta g H _data.radius T observed

theorem picardDelta_nonneg
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed) :
    0 ≤ data.picardDelta := by
  exact physlibSecondPicardCouplingDelta_nonneg
    m data.mUpper_nonneg data.beta_coercive data.H_nonneg data.T_nonneg
      data.radius observed

/-- The physical Hamiltonian theorem supplies the consistency edge at every
reference sample. -/
theorem reference_consistent
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed) (omega : Omega) :
    ‖data.actualBlock (data.referenceInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      data.picardDelta := by
  exact physlibSecondPicard_fullState_reference_consistent
    m data.mUpper_nonneg data.mass_upper data.beta_coercive observed
      data.p data.q data.p_differentiable data.q_differentiable
      data.hamiltonian data.radius data.phase data.canonical_initial
      data.observed_frequency_pos data.T_nonneg data.gauge data.energy_window
      data.zero_mode_history data.referenceInitial data.actualBlock
      data.referenceBlock data.actual_realization data.reference_realization
      omega

/-- Construct the generic endpoint datum.  Its Picard consistency field is
now derived from the Hamilton equations and exact Duhamel/Picard theorem. -/
def toFullStateEndpointPropagationData
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed) :
    FullStateEndpointPropagationData Omega X mu M where
  actualInitial := data.actualInitial
  referenceInitial := data.referenceInitial
  initialAmplitude := data.initialAmplitude
  actualBlock := data.actualBlock
  referenceBlock := data.referenceBlock
  stateDelta := data.stateDelta
  initialObservableAmplification := data.initialObservableAmplification
  flowAmplification := data.flowAmplification
  picardDelta := data.picardDelta
  M_nonneg := data.M_nonneg
  stateDelta_nonneg := data.stateDelta_nonneg
  picardDelta_nonneg := data.picardDelta_nonneg
  actualInitial_measurable := data.actualInitial_measurable
  referenceInitial_measurable := data.referenceInitial_measurable
  initialAmplitude_lipschitz := data.initialAmplitude_lipschitz
  actualBlock_lipschitz := data.actualBlock_lipschitz
  referenceBlock_measurable := data.referenceBlock_measurable
  initial_state_near := data.initial_state_near
  reference_consistent := data.reference_consistent
  actualInitial_bound := data.actualInitial_bound
  referenceInitial_bound := data.referenceInitial_bound
  actualFinal_bound := data.actualFinal_bound
  referenceFinal_bound := data.referenceFinal_bound

@[simp] theorem toFullStateEndpointPropagationData_picardDelta
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed) :
    data.toFullStateEndpointPropagationData.picardDelta =
      physlibSecondPicardCouplingDelta
        m mUpper kappa beta g H data.radius T observed := rfl

/-- The family-level `picardDelta_cubic` obligation has the physical
second-Picard coefficient as an explicit witness. -/
theorem toFullStateEndpointPropagationData_picardDelta_cubic
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed) :
    data.toFullStateEndpointPropagationData.picardDelta ≤
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H data.radius T observed * |g| ^ 3 := by
  exact physlibSecondPicardCouplingDelta_le_unit_mul_abs_cube
    m mUpper kappa beta g H data.radius T observed

/-- A uniform upper bound on the physical coefficient directly discharges
the `Cpicard` version used by a blockwise family. -/
theorem toFullStateEndpointPropagationData_picardDelta_cubic_of_coefficient_le
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed)
    {Cpicard : Real}
    (hcoefficient :
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H data.radius T observed ≤ Cpicard) :
    data.toFullStateEndpointPropagationData.picardDelta ≤
      Cpicard * |g| ^ 3 := by
  exact data.toFullStateEndpointPropagationData_picardDelta_cubic.trans
    (mul_le_mul_of_nonneg_right hcoefficient
      (pow_nonneg (abs_nonneg g) 3))

end PhysicalFullStateBlockData

end

end ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockData
