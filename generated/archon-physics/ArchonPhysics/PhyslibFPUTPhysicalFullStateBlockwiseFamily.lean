import ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockData
import ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing

/-!
# A physical full-state family constructs blockwise FPUT shadowing data

This module performs the family-level assembly left after the one-block
physical constructor.  At every `(n,j)` it takes a
`PhysicalFullStateBlockData`, hence an actual Hamiltonian trajectory and the
proved second-Picard comparison.  The resulting
`FPUTFullStateBlockwiseMomentFamily` uses
`PhysicalFullStateBlockData.toFullStateEndpointPropagationData` as its block
datum.

In particular, neither second-Picard consistency nor an abstract Picard
radius is a field below.  The family only assumes a uniform upper bound on
the explicit physical second-Picard coefficient; the required cubic Picard
radius estimate is then a theorem of the constructor.  The still-open input
is displayed separately as the initial full-state RPA coupling
`stateDelta_cubic`, together with the endpoint-law, collision, and envelope
identifications needed by the kinetic theorem.
-/

namespace ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockwiseFamily

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
open ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockData
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

noncomputable section

/-- Physical Hamiltonian data for every independently re-Haarized block.

`physicalBlock n j` contains the actual Hamiltonian realization and the
initial full-state RPA coupling for that block.  The only family-level bound
on the deterministic Picard edge is `secondPicardCoefficient_le`, a bound on
the explicit coefficient produced by the physical second-Picard theorem.
-/
structure FPUTPhysicalFullStateBlockwiseMomentFamily
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Real)
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta H T : Real)
    (observed : Site N)
    (g : Nat → Real) (E : Nat → Nat → Real) (Q : Real → Real)
    (Cref Cstate Cpicard : Real)
    (Ainitial Aflow : NNReal) where
  energy : Nat → Nat → Site N → Real
  physicalBlock : ∀ n _j,
    PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta (g n) H T observed
  Cstate_nonneg : 0 ≤ Cstate
  Cpicard_nonneg : 0 ≤ Cpicard
  couplingWindow : ∀ n, |g n| ≤ 1
  /-- The transparent nonlinear RPA input at the beginning of each block. -/
  stateDelta_cubic : ∀ n j,
    (physicalBlock n j).stateDelta ≤ Cstate * |g n| ^ 3
  /-- Uniform control of the explicit, physically derived Picard
  coefficient.  There is no generic Picard-radius hypothesis. -/
  secondPicardCoefficient_le : ∀ n j,
    cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta (g n) H (physicalBlock n j).radius T observed ≤
      Cpicard
  initialObservableAmplification_le : ∀ n j,
    (physicalBlock n j).initialObservableAmplification ≤ Ainitial
  flowAmplification_le : ∀ n j,
    (physicalBlock n j).flowAmplification ≤ Aflow
  actualInitialMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        ((physicalBlock n j).toFullStateEndpointPropagationData
          |>.toAmplitudeCouplingRestartCertificate.actualLaw 0) =
      E n j
  actualFinalMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        ((physicalBlock n j).toFullStateEndpointPropagationData
          |>.toAmplitudeCouplingRestartCertificate.actualLaw 1) =
      E n (j + 1)
  referenceInitialMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        ((physicalBlock n j).toFullStateEndpointPropagationData
          |>.toAmplitudeCouplingRestartCertificate.referenceLaw 0) =
      canonicalHaarBlockInitial m (energy n j) observed
  referenceFinalMoment : ∀ n j,
    ∫ z, Complex.normSq z ∂
        ((physicalBlock n j).toFullStateEndpointPropagationData
          |>.toAmplitudeCouplingRestartCertificate.referenceLaw 1) =
      canonicalHaarBlockFinal
        m kappa beta (g n) (energy n j) T observed
  collision_compatibility : ∀ n j,
    Q (canonicalHaarBlockInitial m (energy n j) observed) =
      normalizedSecondOrderHaarBroadening
        m kappa beta (energy n j) observed T
  finiteCharacterEnvelope : ∀ n j,
    physlibHaarEnergyDriftC3 m kappa beta
          (phaseEnergyRadius (energy n j) (modeFrequency m)) T observed +
        physlibHaarEnergyDriftC4 m kappa beta
          (phaseEnergyRadius (energy n j) (modeFrequency m)) T observed ≤
      Cref

namespace FPUTPhysicalFullStateBlockwiseMomentFamily

variable {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Real}
  {N : Nat} [NeZero N]
  {m : PositiveMassConfig N} {mUpper kappa beta H T : Real}
  {observed : Site N}
  {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
  {Cref Cstate Cpicard : Real}
  {Ainitial Aflow : NNReal}

/-- The block selected by the generic family is definitionally the endpoint
datum constructed from the physical Hamiltonian block. -/
def endpointData
    (family : FPUTPhysicalFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m mUpper kappa beta H T observed
        g E Q Cref Cstate Cpicard Ainitial Aflow)
    (n j : Nat) : FullStateEndpointPropagationData Omega X mu M :=
  (family.physicalBlock n j).toFullStateEndpointPropagationData

/-- Assemble the residual-free full-state kinetic family.  Its Picard cubic
field is proved from the explicit physical coefficient bound. -/
def toFullStateBlockwiseMomentFamily
    (family : FPUTPhysicalFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m mUpper kappa beta H T observed
        g E Q Cref Cstate Cpicard Ainitial Aflow) :
    FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow where
  energy := family.energy
  blockData := family.endpointData
  Cstate_nonneg := family.Cstate_nonneg
  Cpicard_nonneg := family.Cpicard_nonneg
  couplingWindow := family.couplingWindow
  stateDelta_cubic := family.stateDelta_cubic
  picardDelta_cubic := fun n j ↦
    (family.physicalBlock n j)
      |>.toFullStateEndpointPropagationData_picardDelta_cubic_of_coefficient_le
        (family.secondPicardCoefficient_le n j)
  initialObservableAmplification_le :=
    family.initialObservableAmplification_le
  flowAmplification_le := family.flowAmplification_le
  actualInitialMoment := family.actualInitialMoment
  actualFinalMoment := family.actualFinalMoment
  referenceInitialMoment := family.referenceInitialMoment
  referenceFinalMoment := family.referenceFinalMoment
  collision_compatibility := family.collision_compatibility
  finiteCharacterEnvelope := family.finiteCharacterEnvelope

@[simp] theorem toFullStateBlockwiseMomentFamily_blockData
    (family : FPUTPhysicalFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m mUpper kappa beta H T observed
        g E Q Cref Cstate Cpicard Ainitial Aflow)
    (n j : Nat) :
    family.toFullStateBlockwiseMomentFamily.blockData n j =
      (family.physicalBlock n j).toFullStateEndpointPropagationData := rfl

/-- The constructed generic Picard radius has the requested uniform cubic
bound without any family-level consistency assumption. -/
theorem constructed_picardDelta_cubic
    (family : FPUTPhysicalFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m mUpper kappa beta H T observed
        g E Q Cref Cstate Cpicard Ainitial Aflow)
    (n j : Nat) :
    (family.toFullStateBlockwiseMomentFamily.blockData n j).picardDelta ≤
      Cpicard * |g n| ^ 3 :=
  family.toFullStateBlockwiseMomentFamily.picardDelta_cubic n j

end FPUTPhysicalFullStateBlockwiseMomentFamily

end

end ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockwiseFamily
