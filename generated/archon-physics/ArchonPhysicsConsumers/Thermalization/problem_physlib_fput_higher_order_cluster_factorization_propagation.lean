import ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation

/-!
# Consumer: actual full-FPUT higher-order cluster factorization propagation
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation

noncomputable section

/-- Arbitrary finite joint order, actual five-site full alpha-beta paths. -/
theorem fiveSite_actual_higherOrder_clusterFactorization_consumer
    {Omega I : Type*} [Fintype Omega]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig 5)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site 5)
    (p q : Omega → Time → HilbertConfiguration 5)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (left right : Finset I)
    (hzero : actualFiniteCoerciveClusterFactorizationDefect
      weight mass entry p q left right 0 = 0)
    (time epsilon : Real)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q left right s‖ ≤ epsilon) :
    ‖actualFiniteCoerciveClusterFactorizationDefect
      weight mass entry p q left right time‖ ≤ epsilon * |time| :=
  norm_actualFiniteCoerciveClusterFactorizationDefect_le
    weight mass kappa beta g entry p q hp hq hHamilton homega
    left right hzero time epsilon hsource

#print axioms fiveSite_actual_higherOrder_clusterFactorization_consumer

end

end ArchonPhysicsConsumers.Thermalization
