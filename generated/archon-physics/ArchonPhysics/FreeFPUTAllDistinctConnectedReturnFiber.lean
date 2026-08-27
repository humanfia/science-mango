import ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree

/-!
# The eight explicit all-distinct connected return trees

For one fixed ordered quadratic phase term whose observed and two input
modes are pairwise distinct, the canonical connected-return constructor has
three binary choices: the distinguished input, its outer placement, and the
placement of the observed inner child.  This module packages their literal
eight-element image, proves the exact finite reindex, and evaluates its
physical feedback sum.

The image is deliberately local to the supplied ordered term.  No claim is
made that it is the full positive connected representative fiber, nor is any
injectivity asserted across distinct raw quadratic terms.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ResonanceWeightSinc

noncomputable section

/-- Distinguished input, outer placement, and inner observed placement. -/
abbrev AllDistinctConnectedReturnIndex := Fin 2 × (Fin 2 × Fin 2)

/-- The exact matched tree associated with one of the eight local indices. -/
def allDistinctConnectedReturnMap
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : AllDistinctConnectedReturnIndex) :
    FreeInitialMatchedIteratedQuadraticTerm N observed :=
  matchedConnectedReturnTree observed q index.1 index.2.1 index.2.2

@[simp] theorem allDistinctConnectedReturnMap_val
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : AllDistinctConnectedReturnIndex) :
    (allDistinctConnectedReturnMap observed q index).1 =
      connectedReturnTree observed q index.1 index.2.1 index.2.2 := rfl

/-- Every local image term satisfies one of the four connected-channel
predicates. -/
theorem allDistinctConnectedReturnMap_connectedChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : AllDistinctConnectedReturnIndex) :
    MatchedIteratedQuadraticConnectedChannel observed
        (allDistinctConnectedReturnMap observed q index).1 := by
  exact connectedReturnTree_connectedChannel observed q
    index.1 index.2.1 index.2.2

/-- Under pairwise mode distinctness, all eight matched constructor values
are different. -/
theorem allDistinctConnectedReturnMap_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    Function.Injective (allDistinctConnectedReturnMap observed q) := by
  intro left right htree
  apply connectedReturnTree_localIndex_injective observed q hDistinct
  exact congrArg Subtype.val htree

/-- Literal finite image of the eight local constructor indices. -/
def allDistinctConnectedReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact Finset.univ.image (allDistinctConnectedReturnMap observed q)

/-- Every explicitly constructed matched tree belongs to the local image. -/
@[simp] theorem allDistinctConnectedReturnMap_mem_image
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : AllDistinctConnectedReturnIndex) :
    allDistinctConnectedReturnMap observed q index ∈
      allDistinctConnectedReturnImage observed q := by
  classical
  simp [allDistinctConnectedReturnImage]

/-- The literal image has cardinality eight. -/
theorem card_allDistinctConnectedReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    (allDistinctConnectedReturnImage observed q).card = 8 := by
  classical
  unfold allDistinctConnectedReturnImage
  rw [Finset.card_image_of_injective _
    (allDistinctConnectedReturnMap_injective observed q hDistinct)]
  decide

/-- Exact finite reindex of any additive weight over the local image. -/
theorem sum_allDistinctConnectedReturnImage
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ allDistinctConnectedReturnImage observed q, weight term) =
      ∑ index : AllDistinctConnectedReturnIndex,
        weight (allDistinctConnectedReturnMap observed q index) := by
  classical
  unfold allDistinctConnectedReturnImage
  rw [Finset.sum_image]
  intro left _hleft right _hright htree
  exact allDistinctConnectedReturnMap_injective observed q hDistinct htree

/-- One mapped term with the physical feedback's own inner mismatch equals
the distinguished-input signed collision kernel contribution. -/
theorem allDistinctConnectedReturnMap_feedback_eq_signedKernel_mul_actions
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : AllDistinctConnectedReturnIndex)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed
          (allDistinctConnectedReturnMap observed q index).1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m
            (allDistinctConnectedReturnMap observed q index).1) time =
      (quadraticCollisionSign q (Fin.succ index.1)).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (q.1 (otherQuadraticSlot index.1))) := by
  rw [allDistinctConnectedReturnMap_val,
    connectedReturnTree_innerMismatch,
    finiteTimeResonanceWeight_neg]
  exact connectedReturnTree_feedback_eq_signedKernel_mul_actions
    m kappa time energy observed q index.1 index.2.1 index.2.2
      hEnergy hPositive

/-- Summing the eight explicit trees gives four copies of each of the two
distinguished-input feedback terms.  This is a local image identity, not a
surjectivity statement for a global connected representative fiber. -/
theorem sum_allDistinctConnectedReturnImage_feedback_eq
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
            modeAction energy (modeFrequency m) (q.1 0)) := by
  rw [sum_allDistinctConnectedReturnImage observed q hDistinct]
  simp_rw [allDistinctConnectedReturnMap_feedback_eq_signedKernel_mul_actions
    m kappa time energy observed q _ hEnergy hPositive]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    otherQuadraticSlot_zero, otherQuadraticSlot_one]
  ring

end

end ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
