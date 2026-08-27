import ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge

/-!
# Consumer: zero-frequency connected-feedback deletion

The positive-inner canonical connected-tree base can contain a zero-frequency
free outer leg.  These consumer theorems expose the exact termwise vanishing
and the resulting weighted-sum restriction to the full three-mode positive
sector.  No equality between the unfiltered and filtered parameter sets is
claimed.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- The compact coefficient itself vanishes when the free outer coordinate
has zero frequency. -/
theorem problem_compactFeedbackWeight_eq_zero_of_freeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term))
    (hFreeZero : modeFrequency m
      (iteratedQuadraticFreeMode term) = 0) :
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term = 0 :=
  compactIteratedQuadraticStaticFeedbackWeight_eq_zero_of_freeFrequency_eq_zero
    m kappa radius observed term hObserved hInner hFreeZero

/-- For a positive-inner canonical parameter, failure of full three-leg
positivity kills its feedback against every real multiplier. -/
theorem problem_positiveCanonicalParameter_feedback_mul_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (parameter : PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) (multiplier : Real)
    (hObserved : 0 < modeFrequency m observed)
    (hNotPositive : ¬ PositiveModeTuple m
      (quadraticCollisionModes observed parameter.1.1.1)) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
          (positiveCanonicalAllDistinctConnectedRawTerm
            m observed parameter) * multiplier = 0 :=
  positiveCanonicalParameter_compactFeedback_mul_eq_zero_of_not_positiveModeTuple
    m kappa radius observed parameter multiplier hObserved hNotPositive

/-- The surviving filter is indexed by the existing positive all-distinct
quadratic representatives. -/
theorem problem_fullyPositiveCanonicalParameter_iff_positiveRepresentative
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) :
    parameter ∈
        fullyPositiveCanonicalAllDistinctConnectedReturnParameters
          m observed ↔
      parameter.1.1.1 ∈
        positiveAllDistinctQuadraticSwapRepresentatives m observed :=
  mem_fullyPositiveCanonicalParameters_iff_q_mem_positiveAllDistinctRepresentatives
    m observed parameter

/-- Exact finite-time feedback sum after deleting zero-frequency free legs.
This is an equality of weighted sums, not an equality of parameter sets. -/
theorem problem_sum_positiveCanonicalParameters_feedback_eq_fullyPositive
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ parameter :
        PositiveCanonicalAllDistinctConnectedReturnParameter N m observed,
      compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
          (positiveCanonicalAllDistinctConnectedRawTerm
            m observed parameter) *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m
            (positiveCanonicalAllDistinctConnectedRawTerm
              m observed parameter)) time) =
      ∑ parameter ∈
          fullyPositiveCanonicalAllDistinctConnectedReturnParameters
            m observed,
        compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
            (positiveCanonicalAllDistinctConnectedRawTerm
              m observed parameter) *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m
              (positiveCanonicalAllDistinctConnectedRawTerm
                m observed parameter)) time :=
  sum_positiveCanonicalParameters_feedback_eq_fullyPositive
    m kappa time radius observed hObserved

#print axioms problem_compactFeedbackWeight_eq_zero_of_freeFrequency_eq_zero
#print axioms problem_positiveCanonicalParameter_feedback_mul_eq_zero
#print axioms problem_fullyPositiveCanonicalParameter_iff_positiveRepresentative
#print axioms problem_sum_positiveCanonicalParameters_feedback_eq_fullyPositive

end

end ArchonPhysicsConsumers.Thermalization
