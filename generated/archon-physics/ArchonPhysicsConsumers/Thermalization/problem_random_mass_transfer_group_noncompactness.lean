import ArchonPhysics.RandomMassTransferGroupNoncompactness

/-!
# Consumer: concrete random-mass transfer-group certificate

This consumer bundles the nontrivial relative shear, its unbounded powers,
and absence of a common invariant real line for two distinct frozen-support
masses.  The stronger absence of every finite invariant projective family
remains a separate goal; no Lyapunov, EFC, or localization theorem is used.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassTransferGroupNoncompactness

noncomputable section

theorem frozen_twoMass_transfer_group_local_certificate
    {lambda mass1 mass2 : Real} (hlambda : 0 < lambda)
    (hmass1 : mass1 ∈ RandomEnsemble.massSupport)
    (hmass2 : mass2 ∈ RandomEnsemble.massSupport)
    (hmass : mass1 ≠ mass2) :
    ((↑(andersonTransferUnit lambda mass1 *
      (andersonTransferUnit lambda mass2)⁻¹) :
        Matrix (Fin 2) (Fin 2) Real)) =
      upperUnipotentShear (lambda * (mass2 - mass1)) ∧
    (∀ bound : Real, ∃ n : Nat, bound <
      |((andersonTransferMatrix lambda mass1 *
        andersonTransferMatrixInverse lambda mass2) ^ n) 0 1|) ∧
    ¬HasCommonInvariantRealLine lambda mass1 mass2 := by
  refine ⟨coe_andersonTransferUnit_mul_inv_eq_upperUnipotentShear
      lambda mass1 mass2, ?_,
    not_hasCommonInvariantRealLine (ne_of_gt hlambda) hmass⟩
  exact (frozenSupport_twoMass_unbounded_relativeTransfer_entry
    hlambda hmass1 hmass2 hmass).2.2

#print axioms upperUnipotentShear_pow
#print axioms not_hasCommonInvariantRealLine
#print axioms frozen_twoMass_transfer_group_local_certificate

end

end ArchonPhysicsConsumers.Thermalization
