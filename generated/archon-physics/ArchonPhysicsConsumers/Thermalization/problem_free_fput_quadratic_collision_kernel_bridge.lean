import ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge

/-!
# Consumer: free FPUT quadratic term and finite-time collision kernel

The endpoint below locks the termwise bridge used by the forthcoming exact
gain--loss decomposition.  It retains the positive-frequency and
nonnegative-energy hypotheses explicitly.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition

noncomputable section

theorem problem_physicalQuadraticSameTermPairValue_eq_collisionKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    freeQuadraticSameChargePairValue
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time term term =
      ((finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign term) time
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) : Real) : Complex) :=
  physicalQuadraticSameTermPairValue_eq_collisionKernel_mul_actions
    m kappa time observed energy term henergy hpositive

#print axioms problem_physicalQuadraticSameTermPairValue_eq_collisionKernel

end


end ArchonPhysicsConsumers.Thermalization
