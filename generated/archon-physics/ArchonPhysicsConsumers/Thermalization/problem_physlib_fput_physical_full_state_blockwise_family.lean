import ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockwiseFamily

/-!
# Consumer: physical full-state FPUT family constructor

This gate verifies that a per-block physical Hamiltonian realization builds
the residual-free full-state kinetic family.  In particular the generic
Picard radius is fixed by the physical second-Picard theorem, and its cubic
bound follows solely from a uniform bound on the displayed physical
coefficient.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalFullStateBlockwiseFamily

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockwiseFamily

noncomputable section

#check FPUTPhysicalFullStateBlockwiseMomentFamily
#check FPUTPhysicalFullStateBlockwiseMomentFamily.endpointData
#check FPUTPhysicalFullStateBlockwiseMomentFamily.toFullStateBlockwiseMomentFamily
#check FPUTPhysicalFullStateBlockwiseMomentFamily.toFullStateBlockwiseMomentFamily_blockData
#check FPUTPhysicalFullStateBlockwiseMomentFamily.constructed_picardDelta_cubic

/-- The family-level cubic Picard field is recovered from the physical
coefficient bound by construction. -/
theorem physical_family_supplies_generic_picard_bound
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M : Real}
    {N : Nat} [NeZero N]
    {m : PositiveMassConfig N} {mUpper kappa beta H T : Real}
    {observed : Site N}
    {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
    {Cref Cstate Cpicard : Real} {Ainitial Aflow : NNReal}
    (family : FPUTPhysicalFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m mUpper kappa beta H T observed
        g E Q Cref Cstate Cpicard Ainitial Aflow)
    (n j : Nat) :
    (family.toFullStateBlockwiseMomentFamily.blockData n j).picardDelta ≤
      Cpicard * |g n| ^ 3 :=
  family.constructed_picardDelta_cubic n j

/-- The generic block really is the committed one-block physical
constructor, not a second independently supplied endpoint datum. -/
theorem physical_family_uses_physical_block
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M : Real}
    {N : Nat} [NeZero N]
    {m : PositiveMassConfig N} {mUpper kappa beta H T : Real}
    {observed : Site N}
    {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
    {Cref Cstate Cpicard : Real} {Ainitial Aflow : NNReal}
    (family : FPUTPhysicalFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m mUpper kappa beta H T observed
        g E Q Cref Cstate Cpicard Ainitial Aflow)
    (n j : Nat) :
    family.toFullStateBlockwiseMomentFamily.blockData n j =
      (family.physicalBlock n j).toFullStateEndpointPropagationData := by
  rfl

#print axioms
  FPUTPhysicalFullStateBlockwiseMomentFamily.toFullStateBlockwiseMomentFamily
#print axioms
  FPUTPhysicalFullStateBlockwiseMomentFamily.constructed_picardDelta_cubic
#print axioms physical_family_supplies_generic_picard_bound
#print axioms physical_family_uses_physical_block

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalFullStateBlockwiseFamily
