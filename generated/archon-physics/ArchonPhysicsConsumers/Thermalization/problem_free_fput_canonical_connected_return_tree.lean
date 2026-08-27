import ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree

/-!
# Consumer: canonical local connected return trees
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

theorem problem_connectedReturnTree_chargeMatched
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge
        (Sum.inl (connectedReturnTree observed q r outerSlot innerSlot)) :=
  connectedReturnTree_chargeMatched observed q r outerSlot innerSlot

theorem problem_connectedReturnTree_connectedChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    MatchedIteratedQuadraticConnectedChannel observed
      (connectedReturnTree observed q r outerSlot innerSlot) :=
  connectedReturnTree_connectedChannel observed q r outerSlot innerSlot

theorem problem_connectedReturnTree_connectedPairing
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    ConnectedReturnModePairing observed
      (connectedReturnTree observed q r outerSlot innerSlot) :=
  connectedReturnTree_connectedPairing observed q r outerSlot innerSlot

theorem problem_connectedReturnTree_innerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticInnerMismatch m
        (connectedReturnTree observed q r outerSlot innerSlot) =
      -quadraticPhaseMismatch (modeFrequency m) observed q :=
  connectedReturnTree_innerMismatch m observed q r outerSlot innerSlot

theorem problem_connectedReturnTree_feedbackSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    -firstPicardCoordinateBranchSign
        (iteratedQuadraticInnerEntry
          (connectedReturnTree observed q r outerSlot innerSlot)).2 =
      (quadraticCollisionSign q (Fin.succ r)).coefficient :=
  connectedReturnTree_feedbackSign observed q r outerSlot innerSlot

theorem problem_finiteTimeCollisionKernel_connectedReturnInnerTerm_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (r innerSlot : Fin 2) :
    finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign
          (connectedReturnInnerTerm observed q r innerSlot)) time
        (quadraticCollisionModes (q.1 r)
          (connectedReturnInnerTerm observed q r innerSlot)) =
      finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) :=
  finiteTimeCollisionKernel_connectedReturnInnerTerm_eq
    m kappa time observed q r innerSlot

theorem problem_connectedReturnTree_feedback_eq_signedKernel_mul_actions
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed
          (connectedReturnTree observed q r outerSlot innerSlot) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed q) time =
      (quadraticCollisionSign q (Fin.succ r)).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (q.1 (otherQuadraticSlot r))) :=
  connectedReturnTree_feedback_eq_signedKernel_mul_actions
    m kappa time energy observed q r outerSlot innerSlot hEnergy hPositive

theorem problem_connectedReturnTree_placement_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hObservedOther : observed ≠ q.1 (otherQuadraticSlot r)) :
    Function.Injective
      (fun placement : Fin 2 × Fin 2 ↦
        connectedReturnTree observed q r placement.1 placement.2) :=
  connectedReturnTree_placement_injective observed q r hObservedOther

theorem problem_connectedReturnTree_localIndex_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    Function.Injective
      (fun index : Fin 2 × (Fin 2 × Fin 2) ↦
        connectedReturnTree observed q index.1 index.2.1 index.2.2) :=
  connectedReturnTree_localIndex_injective observed q hDistinct

#print axioms problem_connectedReturnTree_chargeMatched
#print axioms problem_connectedReturnTree_connectedChannel
#print axioms problem_connectedReturnTree_connectedPairing
#print axioms problem_connectedReturnTree_innerMismatch
#print axioms problem_connectedReturnTree_feedbackSign
#print axioms problem_finiteTimeCollisionKernel_connectedReturnInnerTerm_eq
#print axioms problem_connectedReturnTree_feedback_eq_signedKernel_mul_actions
#print axioms problem_connectedReturnTree_placement_injective
#print axioms problem_connectedReturnTree_localIndex_injective

end

end ArchonPhysicsConsumers.Thermalization
