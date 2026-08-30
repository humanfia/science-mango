import ArchonPhysics.RandomMassTransferProjectiveStrongIrreducibility

/-!
# Consumer: the finite two-mass projective group criterion

For two distinct frozen-support masses and positive spectral parameter, this
consumer bundles the explicit relative shear, unbounded relative-transfer
powers, and absence of every nonempty finite invariant family of real
projective lines.  These are the concrete algebraic group inputs only: no
Furstenberg theorem, positive Lyapunov exponent, EFC, or localization result
is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassTransferGroupNoncompactness
open ArchonPhysics.RandomMassTransferProjectiveStrongIrreducibility

noncomputable section

theorem frozen_twoMass_projective_group_criterion_certificate
    {lambda mass1 mass2 : Real} (hlambda : 0 < lambda)
    (hmass1 : mass1 ∈ RandomEnsemble.massSupport)
    (hmass2 : mass2 ∈ RandomEnsemble.massSupport)
    (hmass : mass1 ≠ mass2) :
    andersonTransferSL lambda mass1 *
        (andersonTransferSL lambda mass2)⁻¹ =
      upperUnipotentShearSL (lambda * (mass2 - mass1)) ∧
    (∀ bound : Real, ∃ n : Nat, bound <
      |((andersonTransferMatrix lambda mass1 *
        andersonTransferMatrixInverse lambda mass2) ^ n) 0 1|) ∧
    IsProjectivelyStronglyIrreducible lambda mass1 mass2 := by
  refine ⟨andersonTransferSL_mul_inv_eq_upperUnipotentShearSL
      lambda mass1 mass2, ?_,
    twoMass_isProjectivelyStronglyIrreducible
      (ne_of_gt hlambda) hmass⟩
  exact (frozenSupport_twoMass_unbounded_relativeTransfer_entry
    hlambda hmass1 hmass2 hmass).2.2

#print axioms finite_mapsTo_inverse
#print axioms twoMass_isProjectivelyStronglyIrreducible
#print axioms frozen_twoMass_projective_group_criterion_certificate

end


end ArchonPhysicsConsumers.Thermalization
