import ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
import ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation

/-!
# Twist renormalization of the iterated/iterated A2 remainder

The rank-three `A2/A2` iterated/iterated square cannot be closed by the
absolute-value cutoff used for the mixed and direct sectors.  This module
tests the smallest exact algebraic groupings available in the actual
coefficient family.

Swapping the two histories conjugates the matched-pair kernel; it does not
negate it.  Simultaneously flipping the inner coordinate branch in both
histories also does not give a universal antisymmetry: on a diagonal pair its
two-cycle sum is the sum of two complex norm squares, and is strictly
positive whenever the original physical coefficient is nonzero.

The correct exact grouping is the four-element action obtained by flipping
the left and right histories independently.  Its block is the matched kernel
of the orbit-symmetrized coefficient

`cRen(term) = c(term) + c(flip term)`.

Since each raw pair occurs four times in the sum of four-element blocks, the
original iterated/iterated Haar remainder is exactly one quarter of the Haar
square of `cRen`.  For the actual physical coefficient the static factor is
odd under the flip, so `cRen` is one static factor times a difference of two
nested oscillatory integrals.  This final identity is intended for later
time-ordering or oscillatory estimates.  No vanishing of that difference,
no long-time estimate, and no kinetic closure is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-! ## Raw history twists and the matched-pair kernel -/

/-- The inner-branch flip as a self-equivalence of the complete raw
iterated-quadratic history type. -/
def iteratedA2InnerFlipEquiv {N : Nat} :
    IteratedQuadraticSecondPicardCharacterTerm N ≃
      IteratedQuadraticSecondPicardCharacterTerm N where
  toFun := flipIteratedQuadraticInnerBranch
  invFun := flipIteratedQuadraticInnerBranch
  left_inv := flipIteratedQuadraticInnerBranch_involutive
  right_inv := flipIteratedQuadraticInnerBranch_involutive

/-- Ordered pairs of complete iterated second-Picard histories. -/
abbrev IteratedA2HistoryPair (N : Nat) :=
  IteratedQuadraticSecondPicardCharacterTerm N ×
    IteratedQuadraticSecondPicardCharacterTerm N

/-- Flip only the left history of an ordered pair. -/
def flipIteratedA2HistoryPairLeft {N : Nat}
    (pair : IteratedA2HistoryPair N) : IteratedA2HistoryPair N :=
  (flipIteratedQuadraticInnerBranch pair.1, pair.2)

/-- Flip only the right history of an ordered pair. -/
def flipIteratedA2HistoryPairRight {N : Nat}
    (pair : IteratedA2HistoryPair N) : IteratedA2HistoryPair N :=
  (pair.1, flipIteratedQuadraticInnerBranch pair.2)

/-- Flip both histories simultaneously. -/
def flipIteratedA2HistoryPairBoth {N : Nat}
    (pair : IteratedA2HistoryPair N) : IteratedA2HistoryPair N :=
  (flipIteratedQuadraticInnerBranch pair.1,
    flipIteratedQuadraticInnerBranch pair.2)

/-- Left history flip as a pair self-equivalence. -/
def flipIteratedA2HistoryPairLeftEquiv {N : Nat} :
    IteratedA2HistoryPair N ≃ IteratedA2HistoryPair N :=
  Equiv.prodCongr iteratedA2InnerFlipEquiv (Equiv.refl _)

/-- Right history flip as a pair self-equivalence. -/
def flipIteratedA2HistoryPairRightEquiv {N : Nat} :
    IteratedA2HistoryPair N ≃ IteratedA2HistoryPair N :=
  Equiv.prodCongr (Equiv.refl _) iteratedA2InnerFlipEquiv

/-- Simultaneous history flip as a pair self-equivalence. -/
def flipIteratedA2HistoryPairBothEquiv {N : Nat} :
    IteratedA2HistoryPair N ≃ IteratedA2HistoryPair N :=
  Equiv.prodCongr iteratedA2InnerFlipEquiv iteratedA2InnerFlipEquiv

@[simp] theorem flipIteratedA2HistoryPairLeftEquiv_apply
    {N : Nat} (pair : IteratedA2HistoryPair N) :
    flipIteratedA2HistoryPairLeftEquiv pair =
      flipIteratedA2HistoryPairLeft pair := rfl

@[simp] theorem flipIteratedA2HistoryPairRightEquiv_apply
    {N : Nat} (pair : IteratedA2HistoryPair N) :
    flipIteratedA2HistoryPairRightEquiv pair =
      flipIteratedA2HistoryPairRight pair := rfl

@[simp] theorem flipIteratedA2HistoryPairBothEquiv_apply
    {N : Nat} (pair : IteratedA2HistoryPair N) :
    flipIteratedA2HistoryPairBothEquiv pair =
      flipIteratedA2HistoryPairBoth pair := rfl

/-- Complex contribution of one ordered pair after the exact Haar charge
selector. -/
def iteratedA2MatchedPairKernel
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex)
    (pair : IteratedA2HistoryPair N) : Complex :=
  if iteratedQuadraticSecondPicardCharge pair.1 =
      iteratedQuadraticSecondPicardCharge pair.2 then
    coefficient pair.1 * starRingEnd Complex (coefficient pair.2)
  else 0

/-- Reversing history order gives a conjugate kernel, rather than an
antisymmetric kernel. -/
theorem iteratedA2MatchedPairKernel_swap_eq_star
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex)
    (left right : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedA2MatchedPairKernel coefficient (right, left) =
      starRingEnd Complex
        (iteratedA2MatchedPairKernel coefficient (left, right)) := by
  unfold iteratedA2MatchedPairKernel
  by_cases hcharge : iteratedQuadraticSecondPicardCharge left =
      iteratedQuadraticSecondPicardCharge right
  · rw [if_pos hcharge, if_pos hcharge.symm]
    simp only [map_mul, starRingEnd_apply, star_star]
    ring
  · have hcharge' : iteratedQuadraticSecondPicardCharge right ≠
        iteratedQuadraticSecondPicardCharge left := fun h ↦ hcharge h.symm
    rw [if_neg hcharge, if_neg hcharge', map_zero]

/-! ## Exact obstruction to a two-cycle antisymmetry -/

/-- Actual integrated physical iterated-`A2` coefficient, named for the
twist adapter below. -/
def physicalIteratedA2Coefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    IteratedQuadraticSecondPicardCharacterTerm N → Complex :=
  iteratedQuadraticSecondPicardNestedCoefficient
    m kappa radius observed time

/-- On a diagonal history pair, the simultaneous-flip two-cycle is a sum of
two norm squares.  Hence it is not an exact antisymmetric cancellation. -/
theorem re_diagonal_kernel_add_simultaneousFlip_eq_normSq_add_normSq
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (iteratedA2MatchedPairKernel coefficient (term, term) +
      iteratedA2MatchedPairKernel coefficient
        (flipIteratedQuadraticInnerBranch term,
          flipIteratedQuadraticInnerBranch term)).re =
      Complex.normSq (coefficient term) +
        Complex.normSq
          (coefficient (flipIteratedQuadraticInnerBranch term)) := by
  simp [iteratedA2MatchedPairKernel, Complex.mul_conj]

/-- Concrete nonzero obstruction: whenever one actual diagonal coefficient
is nonzero, its simultaneous-twist two-cycle has strictly positive real
part. -/
theorem re_physicalDiagonalKernel_add_simultaneousFlip_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcoefficient : physicalIteratedA2Coefficient
      m kappa radius observed time term ≠ 0) :
    0 <
      (iteratedA2MatchedPairKernel
          (physicalIteratedA2Coefficient m kappa radius observed time)
          (term, term) +
        iteratedA2MatchedPairKernel
          (physicalIteratedA2Coefficient m kappa radius observed time)
          (flipIteratedQuadraticInnerBranch term,
            flipIteratedQuadraticInnerBranch term)).re := by
  rw [re_diagonal_kernel_add_simultaneousFlip_eq_normSq_add_normSq]
  exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hcoefficient)
    (Complex.normSq_nonneg _)

/-! ## Minimal four-twist grouping -/

/-- Sum of the four pair kernels obtained by flipping the two histories
independently. -/
def iteratedA2FourTwistBlock
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex)
    (pair : IteratedA2HistoryPair N) : Complex :=
  iteratedA2MatchedPairKernel coefficient pair +
    iteratedA2MatchedPairKernel coefficient
      (flipIteratedA2HistoryPairLeft pair) +
    iteratedA2MatchedPairKernel coefficient
      (flipIteratedA2HistoryPairRight pair) +
    iteratedA2MatchedPairKernel coefficient
      (flipIteratedA2HistoryPairBoth pair)

/-- Orbit-symmetrized coefficient selected by the four-history block. -/
def twistRenormalizedIteratedA2Coefficient
    {N : Nat}
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  coefficient term +
    coefficient (flipIteratedQuadraticInnerBranch term)

@[simp] theorem twistRenormalizedIteratedA2Coefficient_flip
    {N : Nat}
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    twistRenormalizedIteratedA2Coefficient coefficient
        (flipIteratedQuadraticInnerBranch term) =
      twistRenormalizedIteratedA2Coefficient coefficient term := by
  simp [twistRenormalizedIteratedA2Coefficient, add_comm]

/-- Pointwise four-block identity: the entire twist orbit is one matched
kernel of the renormalized coefficients. -/
theorem iteratedA2FourTwistBlock_eq_renormalizedKernel
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex)
    (pair : IteratedA2HistoryPair N) :
    iteratedA2FourTwistBlock coefficient pair =
      iteratedA2MatchedPairKernel
        (twistRenormalizedIteratedA2Coefficient coefficient) pair := by
  rcases pair with ⟨left, right⟩
  unfold iteratedA2FourTwistBlock iteratedA2MatchedPairKernel
    flipIteratedA2HistoryPairLeft flipIteratedA2HistoryPairRight
    flipIteratedA2HistoryPairBoth
    twistRenormalizedIteratedA2Coefficient
  by_cases hcharge : iteratedQuadraticSecondPicardCharge left =
      iteratedQuadraticSecondPicardCharge right
  · simp [hcharge]
    ring
  · simp [hcharge]

/-- Reindexing by a left twist leaves the full matched-pair sum unchanged. -/
theorem sum_iteratedA2MatchedPairKernel_leftFlip_eq
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex) :
    (∑ pair : IteratedA2HistoryPair N,
      iteratedA2MatchedPairKernel coefficient
        (flipIteratedA2HistoryPairLeft pair)) =
      ∑ pair : IteratedA2HistoryPair N,
        iteratedA2MatchedPairKernel coefficient pair := by
  exact Equiv.sum_comp flipIteratedA2HistoryPairLeftEquiv
    (iteratedA2MatchedPairKernel coefficient)

/-- Reindexing by a right twist leaves the full matched-pair sum unchanged. -/
theorem sum_iteratedA2MatchedPairKernel_rightFlip_eq
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex) :
    (∑ pair : IteratedA2HistoryPair N,
      iteratedA2MatchedPairKernel coefficient
        (flipIteratedA2HistoryPairRight pair)) =
      ∑ pair : IteratedA2HistoryPair N,
        iteratedA2MatchedPairKernel coefficient pair := by
  exact Equiv.sum_comp flipIteratedA2HistoryPairRightEquiv
    (iteratedA2MatchedPairKernel coefficient)

/-- Reindexing by a simultaneous twist leaves the full matched-pair sum
unchanged. -/
theorem sum_iteratedA2MatchedPairKernel_bothFlip_eq
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex) :
    (∑ pair : IteratedA2HistoryPair N,
      iteratedA2MatchedPairKernel coefficient
        (flipIteratedA2HistoryPairBoth pair)) =
      ∑ pair : IteratedA2HistoryPair N,
        iteratedA2MatchedPairKernel coefficient pair := by
  exact Equiv.sum_comp flipIteratedA2HistoryPairBothEquiv
    (iteratedA2MatchedPairKernel coefficient)

/-- Every raw ordered pair occurs exactly once in each of the four reindexed
copies, so the full four-block sum is four times the raw kernel sum. -/
theorem sum_iteratedA2FourTwistBlock_eq_four_mul
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex) :
    (∑ pair : IteratedA2HistoryPair N,
      iteratedA2FourTwistBlock coefficient pair) =
      4 * ∑ pair : IteratedA2HistoryPair N,
        iteratedA2MatchedPairKernel coefficient pair := by
  unfold iteratedA2FourTwistBlock
  simp_rw [Finset.sum_add_distrib]
  rw [sum_iteratedA2MatchedPairKernel_leftFlip_eq,
    sum_iteratedA2MatchedPairKernel_rightFlip_eq,
    sum_iteratedA2MatchedPairKernel_bothFlip_eq]
  ring

/-- The existing ordered-pair selector is exactly the sum of the pair-kernel
presentation. -/
theorem equalChargeCrossPairSum_iterated_eq_pairKernelSum
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex) :
    equalChargeCrossPairSum coefficient iteratedQuadraticSecondPicardCharge
        coefficient iteratedQuadraticSecondPicardCharge =
      ∑ pair : IteratedA2HistoryPair N,
        iteratedA2MatchedPairKernel coefficient pair := by
  classical
  unfold equalChargeCrossPairSum iteratedA2MatchedPairKernel
  exact (Fintype.sum_prod_type
    (fun pair : IteratedA2HistoryPair N ↦
      if iteratedQuadraticSecondPicardCharge pair.1 =
          iteratedQuadraticSecondPicardCharge pair.2 then
        coefficient pair.1 * starRingEnd Complex (coefficient pair.2)
      else 0)).symm

/-- Exact complex coefficient identity behind the renormalized square. -/
theorem equalChargeCrossPairSum_twistRenormalized_eq_four_mul
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex) :
    equalChargeCrossPairSum
        (twistRenormalizedIteratedA2Coefficient coefficient)
        iteratedQuadraticSecondPicardCharge
        (twistRenormalizedIteratedA2Coefficient coefficient)
        iteratedQuadraticSecondPicardCharge =
      4 * equalChargeCrossPairSum coefficient
        iteratedQuadraticSecondPicardCharge coefficient
        iteratedQuadraticSecondPicardCharge := by
  rw [equalChargeCrossPairSum_iterated_eq_pairKernelSum,
    equalChargeCrossPairSum_iterated_eq_pairKernelSum]
  calc
    (∑ pair : IteratedA2HistoryPair N,
        iteratedA2MatchedPairKernel
          (twistRenormalizedIteratedA2Coefficient coefficient) pair) =
        ∑ pair : IteratedA2HistoryPair N,
          iteratedA2FourTwistBlock coefficient pair := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact (iteratedA2FourTwistBlock_eq_renormalizedKernel
        coefficient pair).symm
    _ = _ := sum_iteratedA2FourTwistBlock_eq_four_mul coefficient

/-- Exact real Haar-square version: twist renormalization multiplies the raw
same-charge square by four. -/
theorem sameChargeFamilySquare_twistRenormalized_eq_four_mul
    {N : Nat} [NeZero N]
    (coefficient : IteratedQuadraticSecondPicardCharacterTerm N → Complex) :
    sameChargeFamilySquare
        (twistRenormalizedIteratedA2Coefficient coefficient)
        iteratedQuadraticSecondPicardCharge =
      4 * sameChargeFamilySquare coefficient
        iteratedQuadraticSecondPicardCharge := by
  unfold sameChargeFamilySquare
  rw [equalChargeCrossPairSum_twistRenormalized_eq_four_mul]
  norm_num

/-! ## Physical phase-renormalized remainder and time-ordering identity -/

/-- Actual orbit-symmetrized iterated second-Picard coefficient. -/
def phaseRenormalizedPhysicalIteratedA2Coefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    IteratedQuadraticSecondPicardCharacterTerm N → Complex :=
  twistRenormalizedIteratedA2Coefficient
    (physicalIteratedA2Coefficient m kappa radius observed time)

/-- Flipping the two raw inner signs does not change their unsigned
quadratic coefficient. -/
@[simp] theorem freeQuadraticDuhamelCoefficient_flipRawSigns
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (innerObserved : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N) :
    freeQuadraticDuhamelCoefficient coupling m innerObserved radius
        (flipQuadraticPhaseTermRawSigns term) =
      freeQuadraticDuhamelCoefficient coupling m innerObserved radius term := by
  rcases term with ⟨modes, signZero, signOne⟩
  rfl

/-- A physical quadratic Duhamel coefficient is purely imaginary, so its
conjugate is its negative. -/
theorem star_physlibFreeQuadraticDuhamelCoefficient_eq_neg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (innerObserved : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    starRingEnd Complex
        (freeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 innerObserved)
          m innerObserved radius term) =
      -freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 innerObserved)
        m innerObserved radius term := by
  apply Complex.ext
  · simp [physlibFreeQuadraticDuhamelCoefficient_re]
  · simp

/-- The reconstructed static inner coordinate coefficient is odd under the
charge-preserving branch/sign flip. -/
theorem firstPicardCoordinateBranchStaticCoefficient_flip_eq_neg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    firstPicardCoordinateBranchStaticCoefficient m kappa radius innerObserved
        (flipQuadraticPhaseTermRawSigns entry.1,
          otherQuadraticSlot entry.2) =
      -firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved entry := by
  rcases entry with ⟨term, branch⟩
  fin_cases branch
  · unfold firstPicardCoordinateBranchStaticCoefficient
    by_cases hpositive : 0 < modeFrequency m innerObserved
    · rw [if_pos hpositive, if_pos hpositive]
      simp only [freeQuadraticDuhamelCoefficient_flipRawSigns]
      rw [star_physlibFreeQuadraticDuhamelCoefficient_eq_neg]
      simp [otherQuadraticSlot]
    · rw [if_neg hpositive, if_neg hpositive]
      ring
  · unfold firstPicardCoordinateBranchStaticCoefficient
    by_cases hpositive : 0 < modeFrequency m innerObserved
    · rw [if_pos hpositive, if_pos hpositive]
      simp only [freeQuadraticDuhamelCoefficient_flipRawSigns]
      rw [star_physlibFreeQuadraticDuhamelCoefficient_eq_neg]
      simp [otherQuadraticSlot]
    · rw [if_neg hpositive, if_neg hpositive]
      ring

/-- Consequently the complete physical static iterated tree coefficient is
odd under the inner flip. -/
theorem iteratedQuadraticSecondPicardStaticCoefficient_flip_eq_neg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
        (flipIteratedQuadraticInnerBranch term) =
      -iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term := by
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  split_ifs with hpositive
  · simp only [flipIteratedQuadraticInnerBranch_outerModes,
      flipIteratedQuadraticInnerBranch_freeMode,
      flipIteratedQuadraticInnerBranch_firstPicardMode,
      flipIteratedQuadraticInnerBranch_innerEntry,
      firstPicardCoordinateBranchStaticCoefficient_flip_eq_neg]
    ring
  · simp

/-- Exact time-ordering form of the phase-renormalized coefficient.  The
only surviving object is a difference of the two nested oscillatory
histories belonging to one twist orbit. -/
theorem phaseRenormalizedPhysicalIteratedA2Coefficient_eq_nestedDifference
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    phaseRenormalizedPhysicalIteratedA2Coefficient
        m kappa radius observed time term =
      iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term *
        (nestedOscillatoryIntegral
            (iteratedQuadraticOuterMismatch m observed term)
            (iteratedQuadraticInnerMismatch m term) time -
          nestedOscillatoryIntegral
            (iteratedQuadraticOuterMismatch m observed
              (flipIteratedQuadraticInnerBranch term))
            (iteratedQuadraticInnerMismatch m
              (flipIteratedQuadraticInnerBranch term)) time) := by
  unfold phaseRenormalizedPhysicalIteratedA2Coefficient
    twistRenormalizedIteratedA2Coefficient physicalIteratedA2Coefficient
    iteratedQuadraticSecondPicardNestedCoefficient
  rw [iteratedQuadraticSecondPicardStaticCoefficient_flip_eq_neg]
  ring

/-- Exact coefficient-level renormalization of the isolated physical
iterated/iterated remainder. -/
theorem sameChargeFamilySquare_phaseRenormalizedPhysical_eq_four_mul_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    sameChargeFamilySquare
        (phaseRenormalizedPhysicalIteratedA2Coefficient
          m kappa radius observed time)
        iteratedQuadraticSecondPicardCharge =
      4 * completeA2IteratedIteratedRemainder
        m kappa radius observed time := by
  exact sameChargeFamilySquare_twistRenormalized_eq_four_mul
    (physicalIteratedA2Coefficient m kappa radius observed time)

/-- Equivalent quarter-square identity, ready for an oscillatory estimate on
the explicit nested-integral differences. -/
theorem completeA2IteratedIteratedRemainder_eq_quarter_phaseRenormalizedSquare
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    completeA2IteratedIteratedRemainder m kappa radius observed time =
      (1 / 4 : Real) *
        sameChargeFamilySquare
          (phaseRenormalizedPhysicalIteratedA2Coefficient
            m kappa radius observed time)
          iteratedQuadraticSecondPicardCharge := by
  have h :=
    sameChargeFamilySquare_phaseRenormalizedPhysical_eq_four_mul_remainder
      m kappa radius observed time
  linarith

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
