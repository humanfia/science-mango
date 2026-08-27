import ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
import ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge

/-!
# Explicit physical weight of an A0/iterated-quadratic return tree

The return-tree identity isolates the real number

`Re (A0 * conj staticA2)`.

This module expands that number into the two physical quadratic couplings,
the outer and inner interaction tensors, and all four radial coordinate
factors.  The sign is retained exactly: the original inner coordinate branch
has a minus sign, while the conjugate branch has a plus sign.  No gain/loss
interpretation is imposed.

Both the observed and inner positive-frequency guards are explicit.  The
zero-frequency endpoints are therefore genuine tensor/guard identities and
do not use cancellation through a zero denominator.
-/

namespace ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight

open ArchonPhysics
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

noncomputable section

/-- The completely expanded real prefactor of one iterated return tree.

The leading minus sign is the product of the two imaginary quadratic source
coefficients.  `firstPicardCoordinateBranchSign` is `+1` on the original
inner branch and `-1` on its conjugate, so the two branches have opposite
feedback signs. -/
def iteratedQuadraticExpandedStaticFeedbackWeight
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  -firstPicardCoordinateBranchSign
      (iteratedQuadraticInnerEntry term).2 *
    (modeFrequency m observed * radius observed /
      Real.sqrt (2 * modeFrequency m observed)) *
    (kappa / Real.sqrt (2 * modeFrequency m observed)) *
    interactionTensor m 3
      (Fin.cons observed (iteratedQuadraticOuterModes term)) *
    (radius (iteratedQuadraticFreeMode term) / 2) *
    (physlibQuadraticFirstPicardCoordinateScale m
      (iteratedQuadraticFirstPicardMode term) / 2) *
    (kappa / Real.sqrt
      (2 * modeFrequency m (iteratedQuadraticFirstPicardMode term))) *
    interactionTensor m 3
      (Fin.cons (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1.1) *
    (radius ((iteratedQuadraticInnerEntry term).1.1 0) / 2) *
    (radius ((iteratedQuadraticInnerEntry term).1.1 1) / 2)

/-- Real outer factor before multiplication by the reconstructed first-Picard
coordinate. -/
def iteratedQuadraticOuterStaticFactor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  physlibIteratedQuadraticOuterCoupling m kappa observed *
    (interactionTensor m 3
      (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex) *
    ((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex)

@[simp] theorem forcedModeSource_neg_kappa_im (omega kappa : Real) :
    (forcedModeSource omega (-kappa)).im =
      -(kappa / Real.sqrt (2 * omega)) := by
  have hinv :
      (((Real.sqrt (2 * omega) : Real) : Complex)⁻¹) =
        (((Real.sqrt (2 * omega))⁻¹ : Real) : Complex) := by
    push_cast
    rfl
  unfold forcedModeSource
  rw [div_eq_mul_inv, hinv]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
  ring

@[simp] theorem quadraticPhaseCoefficient_re
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) :
    (quadraticPhaseCoefficient m observed radius term).re =
      interactionTensor m 3 (Fin.cons observed term.1) *
        (radius (term.1 0) / 2) * (radius (term.1 1) / 2) := by
  simp [quadraticPhaseCoefficient]

@[simp] theorem physicalFreeQuadraticDuhamelCoefficient_im
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    (freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling m kappa 1 observed)
      m observed radius term).im =
      -(kappa / Real.sqrt (2 * modeFrequency m observed)) *
        interactionTensor m 3 (Fin.cons observed term.1) *
        (radius (term.1 0) / 2) * (radius (term.1 1) / 2) := by
  unfold freeQuadraticDuhamelCoefficient physlibQuadraticCoupling
  rw [Complex.mul_im, forcedModeSource_re,
    forcedModeSource_neg_kappa_im, quadraticPhaseCoefficient_re,
    quadraticPhaseCoefficient_im]
  ring

/-- Exact imaginary component of either reconstructed inner-coordinate
branch. -/
theorem firstPicardCoordinateBranchStaticCoefficient_im_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N)
    (hInner : 0 < modeFrequency m innerObserved) :
    (firstPicardCoordinateBranchStaticCoefficient
      m kappa radius innerObserved entry).im =
      firstPicardCoordinateBranchSign entry.2 *
        (physlibQuadraticFirstPicardCoordinateScale m innerObserved / 2) *
        (-(kappa / Real.sqrt (2 * modeFrequency m innerObserved))) *
        interactionTensor m 3 (Fin.cons innerObserved entry.1.1) *
        (radius (entry.1.1 0) / 2) * (radius (entry.1.1 1) / 2) := by
  rcases entry with ⟨innerTerm, branch⟩
  by_cases hbranch : branch = 0
  · subst branch
    unfold firstPicardCoordinateBranchStaticCoefficient
    rw [if_pos hInner]
    simp only [Fin.isValue, if_true, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      firstPicardCoordinateBranchSign_zero, one_mul,
      physicalFreeQuadraticDuhamelCoefficient_im]
    ring
  · have hbranchOne : branch = 1 := Fin.eq_one_of_ne_zero branch hbranch
    subst branch
    unfold firstPicardCoordinateBranchStaticCoefficient
    rw [if_pos hInner]
    simp only [Fin.isValue, one_ne_zero, if_false, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      firstPicardCoordinateBranchSign_one, Complex.conj_im,
      physicalFreeQuadraticDuhamelCoefficient_im]
    ring

@[simp] theorem iteratedQuadraticOuterStaticFactor_re
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (iteratedQuadraticOuterStaticFactor
      m kappa radius observed term).re = 0 := by
  unfold iteratedQuadraticOuterStaticFactor
    physlibIteratedQuadraticOuterCoupling
  simp [Complex.mul_re]

@[simp] theorem iteratedQuadraticOuterStaticFactor_im
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (iteratedQuadraticOuterStaticFactor
      m kappa radius observed term).im =
      -(kappa / Real.sqrt (2 * modeFrequency m observed)) *
        interactionTensor m 3
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        (radius (iteratedQuadraticFreeMode term) / 2) := by
  unfold iteratedQuadraticOuterStaticFactor
    physlibIteratedQuadraticOuterCoupling
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, forcedModeSource_re,
    forcedModeSource_neg_kappa_im]
  ring

/-- Real component of the complete static tree, before multiplication by
the free initial amplitude. -/
theorem iteratedQuadraticSecondPicardStaticCoefficient_re_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term)) :
    (iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed term).re =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
        (kappa / Real.sqrt (2 * modeFrequency m observed)) *
        interactionTensor m 3
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        (radius (iteratedQuadraticFreeMode term) / 2) *
        (physlibQuadraticFirstPicardCoordinateScale m
          (iteratedQuadraticFirstPicardMode term) / 2) *
        (kappa / Real.sqrt
          (2 * modeFrequency m (iteratedQuadraticFirstPicardMode term))) *
        interactionTensor m 3
          (Fin.cons (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1.1) *
        (radius ((iteratedQuadraticInnerEntry term).1.1 0) / 2) *
        (radius ((iteratedQuadraticInnerEntry term).1.1 1) / 2) := by
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  rw [if_pos hObserved]
  change
    (iteratedQuadraticOuterStaticFactor m kappa radius observed term *
      firstPicardCoordinateBranchStaticCoefficient m kappa radius
        (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term)).re = _
  rw [Complex.mul_re, iteratedQuadraticOuterStaticFactor_re,
    iteratedQuadraticOuterStaticFactor_im,
    firstPicardCoordinateBranchStaticCoefficient_im_of_pos
      m kappa radius (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term) hInner]
  ring

/-- At positive observed and inner frequencies, unfolding the two physical
quadratic Duhamel couplings gives the exact expanded real feedback weight. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_eq_expanded_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term)) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term)).re =
      iteratedQuadraticExpandedStaticFeedbackWeight
        m kappa radius observed term := by
  rw [Complex.mul_re]
  have hfreeIm :
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0).im = 0 :=
    rfl
  rw [hfreeIm, Complex.conj_re, Complex.conj_im]
  simp only [zero_mul, sub_zero]
  rw [iteratedQuadraticSecondPicardStaticCoefficient_re_of_pos
    m kappa radius observed term hObserved hInner]
  unfold freeInitialPhaseCoefficient
    iteratedQuadraticExpandedStaticFeedbackWeight
  simp only [Complex.ofReal_re]
  ring

/-- After cancelling the two positive-frequency oscillator normalizations,
the observed frequency drops out and the inner carrier contributes the sole
remaining frequency denominator. -/
theorem iteratedQuadraticExpandedStaticFeedbackWeight_eq_compact_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term)) :
    iteratedQuadraticExpandedStaticFeedbackWeight
        m kappa radius observed term =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 * kappa ^ 2 *
        interactionTensor m 3
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        interactionTensor m 3
          (Fin.cons (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1.1) *
        radius observed * radius (iteratedQuadraticFreeMode term) *
        radius ((iteratedQuadraticInnerEntry term).1.1 0) *
        radius ((iteratedQuadraticInnerEntry term).1.1 1) /
        (32 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term)) := by
  have hObservedSqrt :
      Real.sqrt (2 * modeFrequency m observed) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two hObserved)
  have hInnerSqrt :
      Real.sqrt
        (2 * modeFrequency m (iteratedQuadraticFirstPicardMode term)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two hInner)
  have hObservedSq :
      Real.sqrt (2 * modeFrequency m observed) ^ 2 =
        2 * modeFrequency m observed :=
    Real.sq_sqrt (mul_nonneg zero_le_two hObserved.le)
  have hInnerSq :
      Real.sqrt
          (2 * modeFrequency m
            (iteratedQuadraticFirstPicardMode term)) ^ 2 =
        2 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term) :=
    Real.sq_sqrt (mul_nonneg zero_le_two hInner.le)
  unfold iteratedQuadraticExpandedStaticFeedbackWeight
    physlibQuadraticFirstPicardCoordinateScale
  field_simp [hObserved.ne', hInner.ne', hObservedSqrt, hInnerSqrt]
  rw [show
    Real.sqrt (modeFrequency m observed * 2) ^ 2 =
        2 * modeFrequency m observed by
      simpa [mul_comm] using hObservedSq]
  ring

/-- Compact positive-frequency formula for the actual return-tree feedback
weight. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_eq_compact_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term)) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term)).re =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 * kappa ^ 2 *
        interactionTensor m 3
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        interactionTensor m 3
          (Fin.cons (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1.1) *
        radius observed * radius (iteratedQuadraticFreeMode term) *
        radius ((iteratedQuadraticInnerEntry term).1.1 0) *
        radius ((iteratedQuadraticInnerEntry term).1.1 1) /
        (32 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term)) := by
  rw [re_freeInitial_mul_star_iteratedStaticCoefficient_eq_expanded_of_pos
    m kappa radius observed term hObserved hInner]
  exact iteratedQuadraticExpandedStaticFeedbackWeight_eq_compact_of_pos
    m kappa radius observed term hObserved hInner

/-- On inner branch zero the compact physical feedback is negative relative
to the displayed signed product of the two real interaction tensors. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_branch_zero_compact
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (outerModes : Fin 2 → Lattice.Site N) (outerSlot freeSign : Fin 2)
    (innerTerm : QuadraticPhaseTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m (outerModes outerSlot)) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
          (outerModes, outerSlot, freeSign, innerTerm, 0))).re =
      -(kappa ^ 2 *
        interactionTensor m 3 (Fin.cons observed outerModes) *
        interactionTensor m 3
          (Fin.cons (outerModes outerSlot) innerTerm.1) *
        radius observed *
        radius (outerModes (otherQuadraticSlot outerSlot)) *
        radius (innerTerm.1 0) * radius (innerTerm.1 1) /
        (32 * modeFrequency m (outerModes outerSlot))) := by
  rw [re_freeInitial_mul_star_iteratedStaticCoefficient_eq_compact_of_pos
    m kappa radius observed
      (outerModes, outerSlot, freeSign, innerTerm, 0) hObserved hInner]
  simp only [iteratedQuadraticInnerEntry,
    firstPicardCoordinateBranchSign_zero,
    iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
    iteratedQuadraticFirstPicardMode,
    iteratedQuadraticFreeMode]
  ring

/-- On the conjugate inner branch the compact physical feedback has the
opposite, positive relative sign. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_branch_one_compact
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (outerModes : Fin 2 → Lattice.Site N) (outerSlot freeSign : Fin 2)
    (innerTerm : QuadraticPhaseTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m (outerModes outerSlot)) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
          (outerModes, outerSlot, freeSign, innerTerm, 1))).re =
      kappa ^ 2 *
        interactionTensor m 3 (Fin.cons observed outerModes) *
        interactionTensor m 3
          (Fin.cons (outerModes outerSlot) innerTerm.1) *
        radius observed *
        radius (outerModes (otherQuadraticSlot outerSlot)) *
        radius (innerTerm.1 0) * radius (innerTerm.1 1) /
        (32 * modeFrequency m (outerModes outerSlot)) := by
  rw [re_freeInitial_mul_star_iteratedStaticCoefficient_eq_compact_of_pos
    m kappa radius observed
      (outerModes, outerSlot, freeSign, innerTerm, 1) hObserved hInner]
  simp only [iteratedQuadraticInnerEntry,
    firstPicardCoordinateBranchSign_one,
    iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
    iteratedQuadraticFirstPicardMode,
    iteratedQuadraticFreeMode]
  ring

@[simp] theorem firstPicardCoordinateBranchSign_sq (branch : Fin 2) :
    firstPicardCoordinateBranchSign branch ^ 2 = 1 := by
  fin_cases branch <;> norm_num

/-- Selecting one of two ordered slots and its opposite preserves their
commutative product. -/
theorem mul_two_slots_eq_selected_mul_other
    {α M : Type*} [CommMonoid M]
    (value : α → M) (modes : Fin 2 → α) (slot : Fin 2) :
    value (modes 0) * value (modes 1) =
      value (modes slot) * value (modes (otherQuadraticSlot slot)) := by
  fin_cases slot <;> simp [mul_comm]

/-- With prescribed nonnegative modal energies, the square of the signed
static feedback is exactly the product of the two normalized three-leg
interaction weights and the four external harmonic actions.  This statement
does not identify the outer and inner vertices; their two weights remain
separate, as required for a general return tree. -/
theorem sq_re_freeInitial_mul_star_iteratedStaticCoefficient_phaseEnergyRadius_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hOuterPositive : PositiveModeTuple m
      (Fin.cons observed (iteratedQuadraticOuterModes term)))
    (hInnerPositive : PositiveModeTuple m
      (Fin.cons (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1.1)) :
    ((freeInitialPhaseCoefficient
        (phaseEnergyRadius energy (modeFrequency m))
        (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed term)).re) ^ 2 =
      kappa ^ 4 *
        normalizedInteractionWeight m
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        normalizedInteractionWeight m
          (Fin.cons (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1.1) *
        modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m)
          (iteratedQuadraticFreeMode term) *
        modeAction energy (modeFrequency m)
          ((iteratedQuadraticInnerEntry term).1.1 0) *
        modeAction energy (modeFrequency m)
          ((iteratedQuadraticInnerEntry term).1.1 1) := by
  have hObserved : 0 < modeFrequency m observed := by
    simpa only [Fin.cons_zero] using hOuterPositive (0 : Fin 3)
  have hInner :
      0 < modeFrequency m (iteratedQuadraticFirstPicardMode term) := by
    simpa only [Fin.cons_zero] using hInnerPositive (0 : Fin 3)
  have hFree :
      0 < modeFrequency m (iteratedQuadraticFreeMode term) := by
    simpa only [Fin.cons_succ, iteratedQuadraticFreeMode] using
      hOuterPositive
        (Fin.succ (otherQuadraticSlot
          (iteratedQuadraticFirstPicardSlot term)))
  have hChildZero :
      0 < modeFrequency m ((iteratedQuadraticInnerEntry term).1.1 0) := by
    simpa only [Fin.cons_succ] using
      hInnerPositive (Fin.succ (0 : Fin 2))
  have hChildOne :
      0 < modeFrequency m ((iteratedQuadraticInnerEntry term).1.1 1) := by
    simpa only [Fin.cons_succ] using
      hInnerPositive (Fin.succ (1 : Fin 2))
  have hEnergyObserved :
      Real.sqrt (2 * energy observed) ^ 2 = 2 * energy observed :=
    Real.sq_sqrt (mul_nonneg zero_le_two (hEnergy observed))
  have hEnergyFree :
      Real.sqrt (2 * energy (iteratedQuadraticFreeMode term)) ^ 2 =
        2 * energy (iteratedQuadraticFreeMode term) :=
    Real.sq_sqrt
      (mul_nonneg zero_le_two (hEnergy (iteratedQuadraticFreeMode term)))
  have hEnergyChildZero :
      Real.sqrt
          (2 * energy ((iteratedQuadraticInnerEntry term).1.1 0)) ^ 2 =
        2 * energy ((iteratedQuadraticInnerEntry term).1.1 0) :=
    Real.sq_sqrt (mul_nonneg zero_le_two
      (hEnergy ((iteratedQuadraticInnerEntry term).1.1 0)))
  have hEnergyChildOne :
      Real.sqrt
          (2 * energy ((iteratedQuadraticInnerEntry term).1.1 1)) ^ 2 =
        2 * energy ((iteratedQuadraticInnerEntry term).1.1 1) :=
    Real.sq_sqrt (mul_nonneg zero_le_two
      (hEnergy ((iteratedQuadraticInnerEntry term).1.1 1)))
  have hOuterInverseProduct :
      (2 * modeFrequency m (iteratedQuadraticOuterModes term 0))⁻¹ *
          (2 * modeFrequency m (iteratedQuadraticOuterModes term 1))⁻¹ =
        (2 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term))⁻¹ *
        (2 * modeFrequency m
          (iteratedQuadraticFreeMode term))⁻¹ := by
    simpa only [iteratedQuadraticFirstPicardMode,
      iteratedQuadraticFreeMode] using
      (mul_two_slots_eq_selected_mul_other
        (fun mode ↦ (2 * modeFrequency m mode)⁻¹)
        (iteratedQuadraticOuterModes term)
        (iteratedQuadraticFirstPicardSlot term))
  have hFinSuccZero : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
  rw [re_freeInitial_mul_star_iteratedStaticCoefficient_eq_compact_of_pos
    m kappa (phaseEnergyRadius energy (modeFrequency m)) observed term
      hObserved hInner]
  unfold phaseEnergyRadius normalizedInteractionWeight modeAction
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Fin.cons_zero, Fin.cons_succ, hFinSuccZero]
  rw [hOuterInverseProduct]
  field_simp [hObserved.ne', hInner.ne', hFree.ne',
    hChildZero.ne', hChildOne.ne']
  rw [hEnergyObserved, hEnergyFree,
    hEnergyChildZero, hEnergyChildOne,
    firstPicardCoordinateBranchSign_sq]
  ring

/-- Global guarded form of the expanded weight.  This statement covers all
totalized zero-frequency branches without ever dividing by a hypothesis that
could be zero. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_eq_guardedExpanded
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term)).re =
      if 0 < modeFrequency m observed ∧
          0 < modeFrequency m (iteratedQuadraticFirstPicardMode term) then
        iteratedQuadraticExpandedStaticFeedbackWeight
          m kappa radius observed term
      else 0 := by
  by_cases hObserved : 0 < modeFrequency m observed
  · by_cases hInner :
        0 < modeFrequency m (iteratedQuadraticFirstPicardMode term)
    · rw [if_pos ⟨hObserved, hInner⟩]
      exact
        re_freeInitial_mul_star_iteratedStaticCoefficient_eq_expanded_of_pos
          m kappa radius observed term hObserved hInner
    · rw [if_neg (fun h ↦ hInner h.2)]
      have hInnerZero :
          modeFrequency m (iteratedQuadraticFirstPicardMode term) = 0 :=
        le_antisymm (le_of_not_gt hInner)
          (modeFrequency_nonneg m _)
      rw [iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_innerFrequency_eq_zero
        m kappa radius observed term hInnerZero]
      simp
  · rw [if_neg (fun h ↦ hObserved h.1)]
    unfold iteratedQuadraticSecondPicardStaticCoefficient
    rw [if_neg hObserved]
    simp

/-- The original (`0`) inner-coordinate branch has the negative physical
prefactor. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_branch_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (outerModes : Fin 2 → Lattice.Site N) (outerSlot freeSign : Fin 2)
    (innerTerm : QuadraticPhaseTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m (outerModes outerSlot)) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
          (outerModes, outerSlot, freeSign, innerTerm, 0))).re =
      iteratedQuadraticExpandedStaticFeedbackWeight m kappa radius observed
        (outerModes, outerSlot, freeSign, innerTerm, 0) := by
  exact re_freeInitial_mul_star_iteratedStaticCoefficient_eq_expanded_of_pos
    m kappa radius observed
      (outerModes, outerSlot, freeSign, innerTerm, 0) hObserved hInner

/-- The conjugate (`1`) inner-coordinate branch has the opposite physical
prefactor. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_branch_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (outerModes : Fin 2 → Lattice.Site N) (outerSlot freeSign : Fin 2)
    (innerTerm : QuadraticPhaseTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m (outerModes outerSlot)) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
          (outerModes, outerSlot, freeSign, innerTerm, 1))).re =
      iteratedQuadraticExpandedStaticFeedbackWeight m kappa radius observed
        (outerModes, outerSlot, freeSign, innerTerm, 1) := by
  exact re_freeInitial_mul_star_iteratedStaticCoefficient_eq_expanded_of_pos
    m kappa radius observed
      (outerModes, outerSlot, freeSign, innerTerm, 1) hObserved hInner

/-- A zero observed frequency kills the feedback weight through the outer
positive-frequency guard. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_eq_zero_of_observedFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hzero : modeFrequency m observed = 0) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term)).re = 0 := by
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  simp [hzero]

/-- A zero inner carrier frequency kills the feedback coefficient through
the established interaction-tensor decoupling theorem. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_eq_zero_of_innerFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hzero : modeFrequency m
      (iteratedQuadraticFirstPicardMode term) = 0) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term)).re = 0 := by
  rw [iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_innerFrequency_eq_zero
    m kappa radius observed term hzero]
  simp

/-- A zero frequency on the free outer coordinate kills the outer
interaction tensor. -/
theorem iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_freeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hzero : modeFrequency m (iteratedQuadraticFreeMode term) = 0) :
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term = 0 := by
  have htensor := interactionTensor_cons_eq_zero_of_inputFrequency_eq_zero
    m observed (iteratedQuadraticOuterModes term)
      (otherQuadraticSlot (iteratedQuadraticFirstPicardSlot term))
      (by simpa only [iteratedQuadraticFreeMode] using hzero)
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  split_ifs
  · rw [htensor]
    simp
  · rfl

/-- A zero frequency on either child of the inner quadratic vertex kills the
inner interaction tensor and hence the full tree. -/
theorem iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_innerInputFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) (slot : Fin 2)
    (hzero : modeFrequency m
      ((iteratedQuadraticInnerEntry term).1.1 slot) = 0) :
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term = 0 := by
  have htensor := interactionTensor_cons_eq_zero_of_inputFrequency_eq_zero
    m (iteratedQuadraticFirstPicardMode term)
      (iteratedQuadraticInnerEntry term).1.1 slot hzero
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  by_cases hObserved : 0 < modeFrequency m observed
  · rw [if_pos hObserved]
    unfold firstPicardCoordinateBranchStaticCoefficient
    by_cases hInner :
        0 < modeFrequency m (iteratedQuadraticFirstPicardMode term)
    · rw [if_pos hInner]
      simp [freeQuadraticDuhamelCoefficient,
        quadraticPhaseCoefficient, htensor]
    · rw [if_neg hInner]
      simp
  · rw [if_neg hObserved]

/-- Feedback corollary for a zero free outer leg. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_eq_zero_of_freeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hzero : modeFrequency m (iteratedQuadraticFreeMode term) = 0) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term)).re = 0 := by
  rw [iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_freeFrequency_eq_zero
    m kappa radius observed term hzero]
  simp

/-- Feedback corollary for either zero-frequency child of the inner vertex. -/
theorem re_freeInitial_mul_star_iteratedStaticCoefficient_eq_zero_of_innerInputFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) (slot : Fin 2)
    (hzero : modeFrequency m
      ((iteratedQuadraticInnerEntry term).1.1 slot) = 0) :
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
      starRingEnd Complex
        (iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term)).re = 0 := by
  rw [iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_innerInputFrequency_eq_zero
    m kappa radius observed term slot hzero]
  simp

end

end ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
