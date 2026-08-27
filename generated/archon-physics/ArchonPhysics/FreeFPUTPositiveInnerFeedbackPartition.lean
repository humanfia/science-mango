import ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber

/-!
# Positive-inner feedback partition by mode distinctness

The exact second-order formula sums over every positive-inner matched return
tree.  This module partitions that finite base into the all-distinct connected
sector and its non-all-distinct complement.  The latter is retained as an
explicit physical feedback remainder containing all repeated-mode boundary
strata.
-/

namespace ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- Positive-inner matched trees outside the all-distinct sector. -/
def positiveInnerNonAllDistinctReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerMatchedIteratedQuadraticTerms m observed).filter
    fun term ↦ ¬ ConnectedReturnTreeAllDistinct observed term.1

@[simp] theorem mem_positiveInnerNonAllDistinctReturnTerms_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerNonAllDistinctReturnTerms m observed ↔
      term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed ∧
        ¬ ConnectedReturnTreeAllDistinct observed term.1 := by
  classical
  simp [positiveInnerNonAllDistinctReturnTerms]

/-- Generic exact finite partition into all-distinct and mode-degenerate
positive-inner terms. -/
theorem sum_positiveInnerMatched_eq_allDistinct_add_nonAllDistinct
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
        weight term) =
      (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
        weight term) +
      ∑ term ∈ positiveInnerNonAllDistinctReturnTerms m observed,
        weight term := by
  classical
  unfold positiveInnerAllDistinctConnectedReturnTerms
    positiveInnerNonAllDistinctReturnTerms
  exact (Finset.sum_filter_add_sum_filter_not
    (positiveInnerMatchedIteratedQuadraticTerms m observed)
    (fun term ↦ ConnectedReturnTreeAllDistinct observed term.1)
    weight).symm

/-- Physical finite-time feedback carried by all non-all-distinct
positive-inner return trees. -/
def positiveInnerNonAllDistinctFeedbackRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term ∈ positiveInnerNonAllDistinctReturnTerms m observed,
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Physical specialization of the exact all-distinct/non-all-distinct
feedback partition. -/
theorem positiveInnerCompactFeedbackSum_eq_allDistinct_add_remainder
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
          m kappa time radius observed := by
  exact sum_positiveInnerMatched_eq_allDistinct_add_nonAllDistinct
    m observed (fun term ↦
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time)

end

end ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
