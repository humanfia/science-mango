import ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual

/-!
# Consumer: the canonical FPUT reference block derives its kinetic residual

This gate exposes the exact finite-character/Haar derivation for the
canonical two-step Picard reference block.  Its order-two term is the
finite-time collision step; only explicit order-three and order-four terms
remain.  Thus no independent reference-residual hypothesis is needed by a
coupling transfer theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTReferenceBlockKineticResidual

open Filter
open MeasureTheory
open Set
open Topology
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer endpoint: the literal Haar integral used for the reference
block is the finite matched-charge polynomial, including charge collisions. -/
theorem reference_Haar_integral_eq_matchedCharge_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
        m kappa beta g radius T observed =
      physlibMatchedChargeTwoStepMoment
        m kappa beta g radius T observed :=
  physlibReferenceTwoStepHaarMoment_eq_matchedCharge
    m kappa beta g radius T observed homega

/-- Consumer endpoint: the reference block itself constructs the precise
`MomentKineticEulerResidual` required by the coupling/shadowing layer. -/
theorem reference_block_kinetic_residual_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {T : Real} (hT : 0 < T)
    (homega : 0 < modeFrequency m observed) :
    MomentKineticEulerResidual
      (physlibReferenceInitialHaarMoment m
        (phaseEnergyRadius energy (modeFrequency m)) observed)
      (physlibReferenceTwoStepHaarMoment m kappa beta g
        (phaseEnergyRadius energy (modeFrequency m)) T observed)
      (g ^ 2 * T)
      (normalizedSecondOrderHaarBroadening
        m kappa beta energy observed T)
      (physlibReferenceBlockKineticDefect m kappa beta
        (phaseEnergyRadius energy (modeFrequency m)) T observed g) :=
  physlibReferenceBlock_is_momentKineticEulerResidual
    m kappa beta g energy observed hT homega

/-- Consumer endpoint: for `|g| ≤ 1`, the reference residual has a fixed
finite `C |g|^3` bound. -/
theorem reference_block_fixed_cubic_bound_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) {g : Real} (hg : |g| ≤ 1) :
    physlibReferenceBlockKineticDefect
        m kappa beta radius T observed g ≤
      |g| ^ 3 *
        (physlibHaarEnergyDriftC3 m kappa beta radius T observed +
          physlibHaarEnergyDriftC4 m kappa beta radius T observed) :=
  physlibReferenceBlockKineticDefect_le_abs_cube_mul_fixedEnvelope
    m kappa beta radius T observed hg

/-- Consumer endpoint: the derived reference residual is little-o of one
kinetic block scale along every nonzero weak-coupling sequence. -/
theorem reference_block_residual_ratio_tendsto_zero_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) {T : Real} (hT : 0 < T)
    (observed : Lattice.Site N)
    (g : Nat → Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    Tendsto
      (fun n ↦
        physlibReferenceBlockKineticDefect
          m kappa beta radius T observed (g n) / (g n ^ 2 * T))
      atTop (nhds 0) :=
  physlibReferenceBlockKineticDefect_sequence_div_kineticScale_tendsto_zero
    m kappa beta radius hT observed g hg hg0

#print axioms physlibReferenceTwoStepHaarMoment_eq_matchedCharge
#print axioms physlibReferenceBlock_sub_kineticCoefficient_eq_highOrder
#print axioms abs_physlibReferenceBlock_sub_kineticCoefficient_le
#print axioms physlibReferenceBlock_is_momentKineticEulerResidual
#print axioms physlibReferenceBlockKineticDefect_div_kineticScale_tendsto_zero
#print axioms reference_Haar_integral_eq_matchedCharge_contract
#print axioms reference_block_kinetic_residual_contract
#print axioms reference_block_fixed_cubic_bound_contract
#print axioms reference_block_residual_ratio_tendsto_zero_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTReferenceBlockKineticResidual
