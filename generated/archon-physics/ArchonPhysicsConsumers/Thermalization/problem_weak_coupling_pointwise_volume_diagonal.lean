import ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal
open Filter Set
open scoped Topology

noncomputable section

example (finiteVolumeError : Nat -> Real -> Real)
    (hfixed : forall n,
      Tendsto (finiteVolumeError n) (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    exists coupling : Nat -> Real,
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto (fun n => finiteVolumeError n (coupling n))
        atTop (nhds 0) := by
  obtain ⟨coupling, _hpositive, _hupper, _herror,
      hcoupling, hdiagonal⟩ :=
    exists_positive_diagonal_of_pointwise_nhdsGT_zero
      finiteVolumeError hfixed
  exact ⟨coupling, hcoupling, hdiagonal⟩

#print axioms exists_positive_diagonal_of_pointwise_nhdsGT_zero

end

end ArchonPhysicsConsumers.Thermalization
