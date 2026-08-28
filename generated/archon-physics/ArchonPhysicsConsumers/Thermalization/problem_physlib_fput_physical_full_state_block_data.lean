import ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockData

/-!
# Consumer: physical full-state FPUT block constructor

This gate checks that one Hamiltonian block constructs the generic endpoint
certificate with no independently assumed Picard consistency inequality.
It also exposes the exact cubic coefficient and its uniform-envelope form
needed by blockwise kinetic shadowing.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalFullStateBlockData

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTFullStateEndpointCertificate
open ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockData

noncomputable section

#check PhysicalFullStateBlockData
#check PhysicalFullStateBlockData.toFullStateEndpointPropagationData
#check PhysicalFullStateBlockData.reference_consistent
#check PhysicalFullStateBlockData.toFullStateEndpointPropagationData_picardDelta_cubic
#check
  PhysicalFullStateBlockData.toFullStateEndpointPropagationData_picardDelta_cubic_of_coefficient_le

/-- The generic structure's consistency projection is backed by the
physical Hamiltonian-to-second-Picard theorem through the constructor. -/
theorem constructed_block_reference_consistent
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : MeasureTheory.Measure Omega} {M : Real}
    {N : Nat} [NeZero N]
    {m : PositiveMassConfig N}
    {mUpper kappa beta g H T : Real} {observed : Site N}
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed) (omega : Omega) :
    ‖data.toFullStateEndpointPropagationData.actualBlock
          (data.toFullStateEndpointPropagationData.referenceInitial omega) -
        data.toFullStateEndpointPropagationData.referenceBlock
          (data.toFullStateEndpointPropagationData.referenceInitial omega)‖ ≤
      data.toFullStateEndpointPropagationData.picardDelta :=
  data.toFullStateEndpointPropagationData.reference_consistent omega

/-- A common coefficient envelope is sufficient for the family-level cubic
Picard field; the error radius itself is fixed by the physical theorem. -/
theorem constructed_block_picard_delta_cubic
    {Omega X : Type*} [MeasurableSpace Omega]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu : MeasureTheory.Measure Omega} {M : Real}
    {N : Nat} [NeZero N]
    {m : PositiveMassConfig N}
    {mUpper kappa beta g H T Cpicard : Real} {observed : Site N}
    (data : PhysicalFullStateBlockData Omega X mu M m
      mUpper kappa beta g H T observed)
    (hcoefficient :
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H data.radius T observed ≤ Cpicard) :
    data.toFullStateEndpointPropagationData.picardDelta ≤
      Cpicard * |g| ^ 3 :=
  data.toFullStateEndpointPropagationData_picardDelta_cubic_of_coefficient_le
    hcoefficient

#print axioms PhysicalFullStateBlockData.reference_consistent
#print axioms PhysicalFullStateBlockData.toFullStateEndpointPropagationData
#print axioms PhysicalFullStateBlockData.toFullStateEndpointPropagationData_picardDelta_cubic
#print axioms
  PhysicalFullStateBlockData.toFullStateEndpointPropagationData_picardDelta_cubic_of_coefficient_le
#print axioms constructed_block_reference_consistent
#print axioms constructed_block_picard_delta_cubic

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalFullStateBlockData
