import ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
import ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge

/-!
# Global reindex of the all-distinct connected FPUT feedback

The local eight-tree feedback formula is indexed by one canonical
representative of each quadratic input-swap orbit.  The exact second-order
formula, however, is indexed by the original positive-inner matched return
trees.  This module identifies those two finite weighted sums.

There are three logically separate steps.  First the global canonical
connected-return equivalence reindexes the original all-distinct fiber,
preventing double counting across swapped quadratic inputs.  Second the
zero-frequency bridge removes canonical parameters whose free input is not
positive: their physical feedback weight is exactly zero.  Finally the
surviving parameters are reindexed by a positive all-distinct quadratic
representative and the three binary constructor choices, and each local
eight-index sum is returned to its literal image.

Only the all-distinct part of the physical feedback is covered here.  The
original full feedback still has repeated-mode boundary strata, which are
not silently absorbed into this identity.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctGlobalConnectedFeedbackReindex

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- Physical finite-time feedback weight on a raw iterated quadratic tree. -/
def allDistinctPhysicalConnectedFeedbackWeight
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  compactIteratedQuadraticStaticFeedbackWeight m kappa
      (phaseEnergyRadius energy (modeFrequency m)) observed term *
    finiteTimeResonanceWeight
      (iteratedQuadraticInnerMismatch m term) time

/-- Package an element of the original positive-inner all-distinct finset as
the positive connected matched subtype used by the global equivalence. -/
def positiveAllDistinctConnectedMatchedReturnTermOfMem
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hTerm : term ∈
      positiveInnerAllDistinctConnectedReturnTerms m observed) :
    PositiveAllDistinctConnectedMatchedReturnTerm N m observed := by
  have hParts :=
    (mem_positiveInnerAllDistinctConnectedReturnTerms_iff
      m observed term).1 hTerm
  refine ⟨⟨term, hParts.2,
      connectedChannel_of_allDistinct_matched observed term hParts.2⟩, ?_⟩
  simpa [positiveInnerMatchedIteratedQuadraticTerms] using hParts.1

@[simp] theorem positiveAllDistinctConnectedMatchedReturnTermOfMem_val
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hTerm : term ∈
      positiveInnerAllDistinctConnectedReturnTerms m observed) :
    (positiveAllDistinctConnectedMatchedReturnTermOfMem
      m observed term hTerm).1.1 = term := rfl

/-- The canonical parameter associated by the global inverse to one member
of the original positive-inner all-distinct fiber. -/
def positiveInnerAllDistinctTermCanonicalParameter
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hTerm : term ∈
      positiveInnerAllDistinctConnectedReturnTerms m observed) :
    PositiveCanonicalAllDistinctConnectedReturnParameter N m observed :=
  positiveCanonicalAllDistinctConnectedReturnInverse m observed
    (positiveAllDistinctConnectedMatchedReturnTermOfMem
      m observed term hTerm)

/-- The inverse parameter reconstructs the literal raw tree with which it
started. -/
theorem positiveInnerAllDistinctTermCanonicalParameter_rawTerm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hTerm : term ∈
      positiveInnerAllDistinctConnectedReturnTerms m observed) :
    positiveCanonicalAllDistinctConnectedRawTerm m observed
        (positiveInnerAllDistinctTermCanonicalParameter
          m observed term hTerm) = term.1 := by
  have hMap := positiveCanonicalMap_inverse m observed
    (positiveAllDistinctConnectedMatchedReturnTermOfMem
      m observed term hTerm)
  exact congrArg
    (fun connected : PositiveAllDistinctConnectedMatchedReturnTerm
        N m observed ↦ connected.1.1.1) hMap

/-- The original finite all-distinct fiber is exactly reindexed by every
positive-inner canonical parameter.  This is where the global equivalence,
rather than only local eight-tree injectivity, removes input-swap double
counting. -/
theorem sum_positiveInnerAllDistinctConnectedReturnTerms_eq_canonicalParameters
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
      allDistinctPhysicalConnectedFeedbackWeight
        m kappa time energy observed term.1) =
      ∑ parameter :
          PositiveCanonicalAllDistinctConnectedReturnParameter N m observed,
        allDistinctPhysicalConnectedFeedbackWeight m kappa time energy
          observed
          (positiveCanonicalAllDistinctConnectedRawTerm
            m observed parameter) := by
  classical
  apply Finset.sum_bij
    (fun term hTerm ↦
      positiveInnerAllDistinctTermCanonicalParameter
        m observed term hTerm)
  · intro term hTerm
    simp
  · intro left hLeft right hRight hEqual
    have hConnected :
        positiveAllDistinctConnectedMatchedReturnTermOfMem
            m observed left hLeft =
          positiveAllDistinctConnectedMatchedReturnTermOfMem
            m observed right hRight := by
      rw [← positiveCanonicalMap_inverse m observed
          (positiveAllDistinctConnectedMatchedReturnTermOfMem
            m observed left hLeft),
        ← positiveCanonicalMap_inverse m observed
          (positiveAllDistinctConnectedMatchedReturnTermOfMem
            m observed right hRight)]
      exact congrArg
        (positiveCanonicalAllDistinctConnectedReturnMap m observed) hEqual
    exact congrArg
      (fun connected : PositiveAllDistinctConnectedMatchedReturnTerm
          N m observed ↦ connected.1.1) hConnected
  · intro parameter _hParameter
    let connected :=
      positiveCanonicalAllDistinctConnectedReturnMap m observed parameter
    let term : FreeInitialMatchedIteratedQuadraticTerm N observed :=
      connected.1.1
    have hTerm : term ∈
        positiveInnerAllDistinctConnectedReturnTerms m observed := by
      apply (mem_positiveInnerAllDistinctConnectedReturnTerms_iff
        m observed term).2
      exact ⟨positiveAllDistinctConnectedMatchedReturnTerm_mem_positiveInner
          m observed connected,
        connected.1.2.1⟩
    refine ⟨term, hTerm, ?_⟩
    change positiveCanonicalAllDistinctConnectedReturnInverse m observed
        (positiveAllDistinctConnectedMatchedReturnTermOfMem
          m observed term hTerm) = parameter
    have hPackaged :
        positiveAllDistinctConnectedMatchedReturnTermOfMem
            m observed term hTerm = connected := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    rw [hPackaged]
    exact
      (positiveCanonicalAllDistinctConnectedReturnEquiv
        m observed).symm_apply_apply parameter
  · intro term hTerm
    rw [positiveInnerAllDistinctTermCanonicalParameter_rawTerm
      m observed term hTerm]

/-- Forgetting proof fields maps a fully positive canonical parameter to its
canonical quadratic representative and its three binary local choices. -/
def fullyPositiveCanonicalParameterPair
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) : QuadraticPhaseTerm N × AllDistinctConnectedReturnIndex :=
  (parameter.1.1.1, parameter.1.1.2)

/-- The fully positive canonical parameter filter is exactly the product of
the positive all-distinct representative finset and the eight local binary
indices. -/
theorem sum_fullyPositiveCanonicalParameters_eq_representativeIndices
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ parameter ∈
        fullyPositiveCanonicalAllDistinctConnectedReturnParameters
          m observed,
      allDistinctPhysicalConnectedFeedbackWeight m kappa time energy
        observed
        (positiveCanonicalAllDistinctConnectedRawTerm
          m observed parameter)) =
      ∑ q ∈ positiveAllDistinctQuadraticSwapRepresentatives m observed,
        ∑ index : AllDistinctConnectedReturnIndex,
          allDistinctPhysicalConnectedFeedbackWeight m kappa time energy
            observed (allDistinctConnectedReturnMap observed q index).1 := by
  classical
  rw [← Finset.sum_product'
    (positiveAllDistinctQuadraticSwapRepresentatives m observed)
    (Finset.univ : Finset AllDistinctConnectedReturnIndex)]
  apply Finset.sum_bij
    (fun parameter _hParameter ↦
      fullyPositiveCanonicalParameterPair m observed parameter)
  · intro parameter hParameter
    exact Finset.mem_product.mpr ⟨
      (mem_fullyPositiveCanonicalParameters_iff_q_mem_positiveAllDistinctRepresentatives
        m observed parameter).1 hParameter,
      Finset.mem_univ _⟩
  · intro left _hLeft right _hRight hEqual
    apply Subtype.ext
    apply Subtype.ext
    exact hEqual
  · intro pair hPair
    rcases Finset.mem_product.mp hPair with ⟨hq, _hIndex⟩
    have hqParts :=
      (mem_positiveAllDistinctQuadraticSwapRepresentatives_iff
        m observed pair.1).1 hq
    have hInner :
        0 < modeFrequency m (pair.1.1 pair.2.1) := by
      simpa [quadraticCollisionModes] using hqParts.2.2 (Fin.succ pair.2.1)
    let parameter :
        PositiveCanonicalAllDistinctConnectedReturnParameter
          N m observed :=
      ⟨⟨pair, hqParts.1, hqParts.2.1⟩, hInner⟩
    have hParameter : parameter ∈
        fullyPositiveCanonicalAllDistinctConnectedReturnParameters
          m observed :=
      (mem_fullyPositiveCanonicalParameters_iff_q_mem_positiveAllDistinctRepresentatives
        m observed parameter).2 hq
    exact ⟨parameter, hParameter, rfl⟩
  · intro parameter _hParameter
    rfl

/-- Exact global identification of the original positive-inner all-distinct
physical feedback with the nested representative-level local images.  The
strict positivity of the observed frequency is used only by the
zero-frequency deletion bridge. -/
theorem sum_positiveInnerAllDistinctConnectedFeedback_eq_representative
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
      compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) =
      allDistinctRepresentativeConnectedFeedbackSum
        m kappa time energy observed := by
  change
    (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
      allDistinctPhysicalConnectedFeedbackWeight
        m kappa time energy observed term.1) = _
  rw [sum_positiveInnerAllDistinctConnectedReturnTerms_eq_canonicalParameters]
  unfold allDistinctPhysicalConnectedFeedbackWeight
  rw [sum_positiveCanonicalParameters_feedback_eq_fullyPositive
    m kappa time (phaseEnergyRadius energy (modeFrequency m)) observed
      hObserved]
  change
    (∑ parameter ∈
        fullyPositiveCanonicalAllDistinctConnectedReturnParameters
          m observed,
      allDistinctPhysicalConnectedFeedbackWeight m kappa time energy
        observed
        (positiveCanonicalAllDistinctConnectedRawTerm
          m observed parameter)) = _
  rw [sum_fullyPositiveCanonicalParameters_eq_representativeIndices]
  unfold allDistinctRepresentativeConnectedFeedbackSum
  apply Finset.sum_congr rfl
  intro q hq
  have hDistinct :=
    (mem_positiveAllDistinctQuadraticSwapRepresentatives_iff
      m observed q).1 hq |>.2.1
  unfold allDistinctConnectedReturnTreeFeedbackSum
  rw [sum_allDistinctConnectedReturnImage observed q hDistinct]
  rfl

/-- The same physical identity expressed through the four original
canonical connected selector fibers.  Repeated-mode terms in the unfiltered
full fibers remain outside this statement. -/
theorem sum_fourAllDistinctCanonicalConnectedFibers_feedback_eq_representative
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ channel ∈ canonicalConnectedReturnChannels,
      ∑ term ∈ positiveInnerAllDistinctCanonicalReturnChannelTerms
          m observed channel,
        compactIteratedQuadraticStaticFeedbackWeight m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time) =
      allDistinctRepresentativeConnectedFeedbackSum
        m kappa time energy observed := by
  rw [← sum_positiveInnerAllDistinctConnectedReturnTerms_eq_fourFibers
    m observed
      (fun term ↦
        compactIteratedQuadraticStaticFeedbackWeight m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time)]
  exact sum_positiveInnerAllDistinctConnectedFeedback_eq_representative
    m kappa time energy observed hObserved

end

end ArchonPhysics.FreeFPUTAllDistinctGlobalConnectedFeedbackReindex
