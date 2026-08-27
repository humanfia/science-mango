import ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss

/-!
# Consumer: local all-distinct signed gain--loss identity

The conclusions below concern the literal eight-tree connected-return image
for one fixed ordered quadratic term.  They do not assert surjectivity onto a
complete connected fiber or discard sectors outside this local image.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

/-- Pairwise mode distinctness gives a two-element input-swap orbit. -/
theorem problem_card_quadraticSwapOrbit_eq_two_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    (quadraticSwapOrbit q).card = 2 :=
  card_quadraticSwapOrbit_eq_two_of_observedQuadraticAllDistinct
    observed q hDistinct

/-- The explicit eight-tree feedback sum. -/
theorem problem_allDistinctConnectedReturnTreeFeedbackSum_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    allDistinctConnectedReturnTreeFeedbackSum
        m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        ((quadraticCollisionSign q (Fin.succ (0 : Fin 2))).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 1) +
          (quadraticCollisionSign q (Fin.succ (1 : Fin 2))).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 0)) :=
  allDistinctConnectedReturnTreeFeedbackSum_eq
    m kappa time energy observed q hDistinct hEnergy hPositive

/-- The local gain plus feedback is four copies of the signed collision
flux. -/
theorem problem_allDistinctLocalSignedGainLoss_eq_signedCollisionFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    allDistinctLocalSignedGainLoss m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed :=
  allDistinctLocalSignedGainLoss_eq_signedCollisionFlux
    m kappa time energy observed q hDistinct hEnergy hPositive

/-- Phase--phase specialization to the standard collision flux. -/
theorem problem_allDistinctLocalSignedGainLoss_eq_collisionFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q))
    (hzero : binaryPhaseSign q.2.1 = .phase)
    (hone : binaryPhaseSign q.2.2 = .phase) :
    allDistinctLocalSignedGainLoss m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        collisionFlux
          (modeAction energy (modeFrequency m) observed)
          (modeAction energy (modeFrequency m) (q.1 0))
          (modeAction energy (modeFrequency m) (q.1 1)) :=
  allDistinctLocalSignedGainLoss_eq_collisionFlux_of_phase_phase
    m kappa time energy observed q hDistinct hEnergy hPositive hzero hone

#print axioms problem_card_quadraticSwapOrbit_eq_two_of_allDistinct
#print axioms problem_allDistinctConnectedReturnTreeFeedbackSum_eq
#print axioms problem_allDistinctLocalSignedGainLoss_eq_signedCollisionFlux
#print axioms problem_allDistinctLocalSignedGainLoss_eq_collisionFlux

end

end ArchonPhysicsConsumers.Thermalization
