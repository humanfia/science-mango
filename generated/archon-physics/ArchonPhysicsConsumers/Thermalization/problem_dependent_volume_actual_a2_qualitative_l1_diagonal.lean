import ArchonPhysics.DependentVolumeActualA2QualitativeL1Diagonal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.DependentVolumeActualA2QualitativeL1Diagonal
open Filter
open scoped Topology

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Nat -> DependentActualA2ChannelDatum Omega)
    (certificate : forall n,
      StaticL1Certificate (datum n) ensemble) :
    exists coupling : Nat -> Real,
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (datum n).externalWeakCouplingAccumulation ensemble (coupling n))
        atTop (nhds 0) := by
  obtain ⟨coupling, _hpositive, _hupper, _hbound,
      hcoupling, haccumulation⟩ :=
    exists_positive_diagonal_of_actualA2_pointwiseL1
      ensemble datum certificate
  exact ⟨coupling, hcoupling, haccumulation⟩

#print axioms exists_positive_diagonal_of_actualA2_pointwiseL1

end

end ArchonPhysicsConsumers.Thermalization
