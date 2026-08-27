import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
import ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss

/-!
# Removing zero-frequency free legs from connected FPUT feedback

The positive-inner return-tree base used by the exact second-order formula
only requires the carrier of the inserted first-Picard coordinate to have
positive frequency.  On an all-distinct connected tree, the other quadratic
input is the free outer coordinate, so it can still lie at zero frequency.

This module proves that such a term has exactly zero compact physical
feedback weight.  The proof does not cancel a totalized zero denominator:
it passes back through the positive-frequency compact-weight identity and
uses the already established theorem that a zero-frequency free coordinate
kills the original second-Picard static coefficient.

Consequently a sum over all positive-inner canonical parameters may be
filtered to the full three-leg `PositiveModeTuple` sector.  This is a
weighted-sum deletion statement, not an assertion that the two underlying
parameter sets are equal.  Membership in the surviving filter is also
identified with `positiveAllDistinctQuadraticSwapRepresentatives`.
-/

namespace ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

noncomputable section

/-- On the positive observed/inner branch where the compact formula is
faithful to the original coefficient, a zero-frequency free coordinate
kills the compact feedback weight exactly. -/
theorem compactIteratedQuadraticStaticFeedbackWeight_eq_zero_of_freeFrequency_eq_zero
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
        m kappa radius observed term = 0 := by
  rw [← iteratedQuadraticFeedbackStaticWeight_eq_compact_of_pos
    m kappa radius observed term hObserved hInner]
  exact
    re_freeInitial_mul_star_iteratedStaticCoefficient_eq_zero_of_freeFrequency_eq_zero
      m kappa radius observed term hFreeZero

/-- Spectral nonnegativity turns failure of strict free-leg positivity into
the exact zero-frequency hypothesis used by the coefficient theorem. -/
theorem compactIteratedQuadraticStaticFeedbackWeight_eq_zero_of_not_freeFrequency_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term))
    (hNotFree : ¬ 0 < modeFrequency m
      (iteratedQuadraticFreeMode term)) :
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term = 0 := by
  have hFreeZero :
      modeFrequency m (iteratedQuadraticFreeMode term) = 0 :=
    le_antisymm (not_lt.mp hNotFree) (modeFrequency_nonneg m _)
  exact
    compactIteratedQuadraticStaticFeedbackWeight_eq_zero_of_freeFrequency_eq_zero
      m kappa radius observed term hObserved hInner hFreeZero

/-- Positivity of the observed leg, one selected input, and the opposite
input is exactly positivity of the three collision modes. -/
theorem positiveModeTuple_quadraticCollisionModes_of_selected_other
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hObserved : 0 < modeFrequency m observed)
    (hSelected : 0 < modeFrequency m (q.1 selected))
    (hOther : 0 < modeFrequency m
      (q.1 (otherQuadraticSlot selected))) :
    PositiveModeTuple m (quadraticCollisionModes observed q) := by
  intro leg
  refine Fin.cases ?_ ?_ leg
  · simpa [quadraticCollisionModes] using hObserved
  · intro input
    fin_cases selected <;> fin_cases input
    · simpa only [quadraticCollisionModes_succ] using hSelected
    · simpa [quadraticCollisionModes_succ,
        otherQuadraticSlot] using hOther
    · simpa [quadraticCollisionModes_succ,
        otherQuadraticSlot] using hOther
    · simpa only [quadraticCollisionModes_succ] using hSelected

/-- If the observed and selected input legs are positive but the complete
collision triple is not, the opposite (free) input has frequency zero. -/
theorem freeFrequency_eq_zero_of_not_positiveModeTuple
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hObserved : 0 < modeFrequency m observed)
    (hSelected : 0 < modeFrequency m (q.1 selected))
    (hNotPositive : ¬ PositiveModeTuple m
      (quadraticCollisionModes observed q)) :
    modeFrequency m (q.1 (otherQuadraticSlot selected)) = 0 := by
  have hNotOther :
      ¬ 0 < modeFrequency m (q.1 (otherQuadraticSlot selected)) := by
    intro hOther
    exact hNotPositive
      (positiveModeTuple_quadraticCollisionModes_of_selected_other
        m observed q selected hObserved hSelected hOther)
  exact le_antisymm (not_lt.mp hNotOther) (modeFrequency_nonneg m _)

/-- Constructor-level zero theorem: a positive-inner connected tree outside
the full three-leg positive sector has zero compact feedback weight. -/
theorem connectedReturnTree_compactFeedbackWeight_eq_zero_of_not_positiveModeTuple
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected outerSlot innerSlot : Fin 2)
    (hObserved : 0 < modeFrequency m observed)
    (hSelected : 0 < modeFrequency m (q.1 selected))
    (hNotPositive : ¬ PositiveModeTuple m
      (quadraticCollisionModes observed q)) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
        (connectedReturnTree observed q selected outerSlot innerSlot) = 0 := by
  apply
    compactIteratedQuadraticStaticFeedbackWeight_eq_zero_of_freeFrequency_eq_zero
      m kappa radius observed
        (connectedReturnTree observed q selected outerSlot innerSlot)
        hObserved
  · simpa using hSelected
  · simpa using
      (freeFrequency_eq_zero_of_not_positiveModeTuple
        m observed q selected hObserved hSelected hNotPositive)

/-- The same constructor-level deletion remains valid after multiplication
by an arbitrary real test weight.  In particular the multiplier may be the
finite-time resonance weight. -/
theorem connectedReturnTree_compactFeedbackWeight_mul_eq_zero_of_not_positiveModeTuple
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected outerSlot innerSlot : Fin 2)
    (multiplier : Real)
    (hObserved : 0 < modeFrequency m observed)
    (hSelected : 0 < modeFrequency m (q.1 selected))
    (hNotPositive : ¬ PositiveModeTuple m
      (quadraticCollisionModes observed q)) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
          (connectedReturnTree observed q selected outerSlot innerSlot) *
        multiplier = 0 := by
  rw [connectedReturnTree_compactFeedbackWeight_eq_zero_of_not_positiveModeTuple
    m kappa radius observed q selected outerSlot innerSlot
      hObserved hSelected hNotPositive]
  simp

/-- The dependent canonical parameter subtype is finite.  Keeping this
instance local to the present bridge avoids changing the structural
surjectivity module merely to state finite weighted sums. -/
noncomputable instance instFintypePositiveCanonicalAllDistinctConnectedReturnParameter
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Fintype (PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) :=
  Fintype.ofFinite _

/-- Canonical positive-inner parameters whose complete observed/input
three-mode tuple is positive.  The inner-positivity proof is retained in the
ambient subtype; this filter adds positivity of the remaining legs. -/
def fullyPositiveCanonicalAllDistinctConnectedReturnParameters
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) := by
  classical
  exact Finset.univ.filter fun parameter ↦
    PositiveModeTuple m
      (quadraticCollisionModes observed parameter.1.1.1)

@[simp] theorem mem_fullyPositiveCanonicalAllDistinctConnectedReturnParameters_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) :
    parameter ∈
        fullyPositiveCanonicalAllDistinctConnectedReturnParameters
          m observed ↔
      PositiveModeTuple m
        (quadraticCollisionModes observed parameter.1.1.1) := by
  classical
  simp [fullyPositiveCanonicalAllDistinctConnectedReturnParameters]

/-- The surviving parameter filter is precisely over the already defined
positive all-distinct quadratic representatives; the local binary index is
unchanged. -/
theorem mem_fullyPositiveCanonicalParameters_iff_q_mem_positiveAllDistinctRepresentatives
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) :
    parameter ∈
        fullyPositiveCanonicalAllDistinctConnectedReturnParameters
          m observed ↔
      parameter.1.1.1 ∈
        positiveAllDistinctQuadraticSwapRepresentatives m observed := by
  rw [mem_fullyPositiveCanonicalAllDistinctConnectedReturnParameters_iff,
    mem_positiveAllDistinctQuadraticSwapRepresentatives_iff]
  constructor
  · intro hPositive
    exact ⟨parameter.1.2.1, parameter.1.2.2, hPositive⟩
  · intro hmem
    exact hmem.2.2

/-- Raw tree underlying a positive-inner canonical parameter. -/
def positiveCanonicalAllDistinctConnectedRawTerm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) : IteratedQuadraticSecondPicardCharacterTerm N :=
  (positiveCanonicalAllDistinctConnectedReturnMap
    m observed parameter).1.1.1

@[simp] theorem positiveCanonicalAllDistinctConnectedRawTerm_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveCanonicalAllDistinctConnectedReturnParameter
      N m observed) :
    positiveCanonicalAllDistinctConnectedRawTerm m observed parameter =
      connectedReturnTree observed parameter.1.1.1 parameter.1.1.2.1
        parameter.1.1.2.2.1 parameter.1.1.2.2.2 := rfl

/-- Parameter-level strongest zero statement.  It makes no reference to a
particular summation base and permits an arbitrary multiplier. -/
theorem positiveCanonicalParameter_compactFeedback_mul_eq_zero_of_not_positiveModeTuple
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
            m observed parameter) * multiplier = 0 := by
  rw [positiveCanonicalAllDistinctConnectedRawTerm_eq]
  exact
    connectedReturnTree_compactFeedbackWeight_mul_eq_zero_of_not_positiveModeTuple
      m kappa radius observed parameter.1.1.1 parameter.1.1.2.1
        parameter.1.1.2.2.1 parameter.1.1.2.2.2 multiplier
        hObserved parameter.2 hNotPositive

/-- A generic weighted sum over the entire positive-inner canonical base can
be restricted to full three-leg positivity.  The multiplier may depend on
the parameter, so this applies directly to finite-time broadening. -/
theorem sum_positiveCanonicalParameters_compactFeedback_eq_fullyPositive
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (multiplier :
      PositiveCanonicalAllDistinctConnectedReturnParameter N m observed →
        Real)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ parameter :
        PositiveCanonicalAllDistinctConnectedReturnParameter N m observed,
      compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
          (positiveCanonicalAllDistinctConnectedRawTerm
            m observed parameter) * multiplier parameter) =
      ∑ parameter ∈
          fullyPositiveCanonicalAllDistinctConnectedReturnParameters
            m observed,
        compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
            (positiveCanonicalAllDistinctConnectedRawTerm
              m observed parameter) * multiplier parameter := by
  classical
  unfold fullyPositiveCanonicalAllDistinctConnectedReturnParameters
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro parameter _hparameter
  by_cases hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed parameter.1.1.1)
  · rw [if_pos hPositive]
  · rw [if_neg hPositive]
    exact
      positiveCanonicalParameter_compactFeedback_mul_eq_zero_of_not_positiveModeTuple
        m kappa radius observed parameter (multiplier parameter)
          hObserved hPositive

/-- Finite-time specialization of the generic deletion theorem. -/
theorem sum_positiveCanonicalParameters_feedback_eq_fullyPositive
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
                m observed parameter)) time := by
  exact sum_positiveCanonicalParameters_compactFeedback_eq_fullyPositive
    m kappa radius observed
      (fun parameter ↦
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m
            (positiveCanonicalAllDistinctConnectedRawTerm
              m observed parameter)) time)
      hObserved

end

end ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge
