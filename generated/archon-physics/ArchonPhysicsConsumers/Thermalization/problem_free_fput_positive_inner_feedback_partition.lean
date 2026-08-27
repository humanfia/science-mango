import ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition

/-!
# Consumer gate: positive-inner feedback partition
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
open ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

theorem problem_positiveInnerCompactFeedbackSum_eq_allDistinct_add_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) =
      (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
        compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time) +
        positiveInnerNonAllDistinctFeedbackRemainder
          m kappa time radius observed :=
  positiveInnerCompactFeedbackSum_eq_allDistinct_add_remainder
    m kappa time radius observed

#print axioms
  problem_positiveInnerCompactFeedbackSum_eq_allDistinct_add_remainder

end

end ArchonPhysicsConsumers.Thermalization
