import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber

/-!
# Consumer: the eight explicit all-distinct connected return trees

This consumer exposes only the finite image of the canonical local
constructor.  It does not identify that image with a complete positive
connected representative fiber.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- Pairwise distinctness makes the three binary constructor choices
injective. -/
theorem problem_allDistinctConnectedReturnMap_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    Function.Injective (allDistinctConnectedReturnMap observed q) :=
  allDistinctConnectedReturnMap_injective observed q hDistinct

/-- The local image contains exactly eight matched connected trees. -/
theorem problem_card_allDistinctConnectedReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    (allDistinctConnectedReturnImage observed q).card = 8 :=
  card_allDistinctConnectedReturnImage observed q hDistinct

/-- Generic exact reindex over the literal eight-tree image. -/
theorem problem_sum_allDistinctConnectedReturnImage
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ allDistinctConnectedReturnImage observed q, weight term) =
      ∑ index : AllDistinctConnectedReturnIndex,
        weight (allDistinctConnectedReturnMap observed q index) :=
  sum_allDistinctConnectedReturnImage observed q hDistinct weight

/-- Exact feedback sum over the eight explicit local trees. -/
theorem problem_sum_allDistinctConnectedReturnImage_feedback_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    (∑ term ∈ allDistinctConnectedReturnImage observed q,
      compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        ((quadraticCollisionSign q (Fin.succ (0 : Fin 2))).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 1) +
          (quadraticCollisionSign q (Fin.succ (1 : Fin 2))).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 0)) :=
  sum_allDistinctConnectedReturnImage_feedback_eq
    m kappa time energy observed q hDistinct hEnergy hPositive

#print axioms problem_allDistinctConnectedReturnMap_injective
#print axioms problem_card_allDistinctConnectedReturnImage
#print axioms problem_sum_allDistinctConnectedReturnImage
#print axioms problem_sum_allDistinctConnectedReturnImage_feedback_eq

end

end ArchonPhysicsConsumers.Thermalization
