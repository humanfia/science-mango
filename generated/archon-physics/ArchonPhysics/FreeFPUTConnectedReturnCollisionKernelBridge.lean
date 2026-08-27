import ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
import ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
import ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
import ArchonPhysics.ResonanceWeightSinc

/-!
# Connected iterated returns as three-wave collision kernels

For each of the four connected return channels, the outer and inner
quadratic vertices carry the same three modes up to permutation.  Hence the
compact return-tree feedback is a branch sign times the squared coefficient
of the inner quadratic Picard term.  Multiplying by its finite-time
resonance weight gives exactly the existing three-wave collision kernel times
the two external actions.

The raw inner quadratic term, including its sign pattern, is retained in the
kernel.  On the conjugate coordinate branch the nested mismatch is the
negative of the raw mismatch; only the evenness of the finite-time resonance
weight identifies the two weights.  Tadpole channels are not included, and
the connected alternatives are not assumed disjoint in the all-equal case.
-/

namespace ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ResonanceWeightSinc

noncomputable section

/-- The mode-only content common to the four connected return channels: the
two inner children are the observed and free outer modes, in either order. -/
def ConnectedReturnModePairing
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  (((iteratedQuadraticInnerEntry term).1.1 0 = observed ∧
      (iteratedQuadraticInnerEntry term).1.1 1 =
        iteratedQuadraticFreeMode term) ∨
    ((iteratedQuadraticInnerEntry term).1.1 1 = observed ∧
      (iteratedQuadraticInnerEntry term).1.1 0 =
        iteratedQuadraticFreeMode term))

/-- Permutation symmetry identifies the outer and inner tensors whenever the
connected mode pairing holds. -/
theorem interactionTensor_outer_eq_inner_of_connectedPairing
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (outerModes innerModes : Fin 2 → Lattice.Site N) (outerSlot : Fin 2)
    (hpair : (innerModes 0 = observed ∧
        innerModes 1 = outerModes (otherQuadraticSlot outerSlot)) ∨
      (innerModes 1 = observed ∧
        innerModes 0 = outerModes (otherQuadraticSlot outerSlot))) :
    interactionTensor m 3 (Fin.cons observed outerModes) =
      interactionTensor m 3
        (Fin.cons (outerModes outerSlot) innerModes) := by
  have hFinSuccZero : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
  rcases hpair with hpair | hpair
  · rcases hpair with ⟨hzero, hone⟩
    unfold interactionTensor
    apply Finset.sum_congr rfl
    intro site hsite
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero,
      Fin.cons_succ, mul_one, hFinSuccZero]
    rw [hzero, hone]
    fin_cases outerSlot <;> simp [otherQuadraticSlot] <;> ring
  · rcases hpair with ⟨hone, hzero⟩
    unfold interactionTensor
    apply Finset.sum_congr rfl
    intro site hsite
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero,
      Fin.cons_succ, mul_one, hFinSuccZero]
    rw [hone, hzero]
    fin_cases outerSlot <;> simp [otherQuadraticSlot] <;> ring

/-- The first connected channel implies the common connected mode pairing. -/
theorem connectedPairing_of_innerZeroObservedFreeCancelsInnerOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hchannel : InnerZeroObservedFreeCancelsInnerOne observed term) :
    ConnectedReturnModePairing observed term := by
  rcases hchannel with ⟨_hfree, _hinnerZero, _hinnerOne,
    hzero, hfree⟩
  left
  exact ⟨hzero, hfree.symm⟩

/-- The second connected channel implies the common connected mode pairing. -/
theorem connectedPairing_of_innerOneObservedFreeCancelsInnerZero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hchannel : InnerOneObservedFreeCancelsInnerZero observed term) :
    ConnectedReturnModePairing observed term := by
  rcases hchannel with ⟨_hfree, _hinnerZero, _hinnerOne,
    hone, hfree⟩
  right
  exact ⟨hone, hfree.symm⟩

/-- The third connected channel implies the common connected mode pairing. -/
theorem connectedPairing_of_innerZeroObservedInnerOneCancelsFree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hchannel : InnerZeroObservedInnerOneCancelsFree observed term) :
    ConnectedReturnModePairing observed term := by
  rcases hchannel with ⟨_hfree, _hinnerZero, _hinnerOne,
    hzero, hfree⟩
  left
  exact ⟨hzero, hfree⟩

/-- The fourth connected channel implies the common connected mode pairing. -/
theorem connectedPairing_of_innerOneObservedInnerZeroCancelsFree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hchannel : InnerOneObservedInnerZeroCancelsFree observed term) :
    ConnectedReturnModePairing observed term := by
  rcases hchannel with ⟨_hfree, _hinnerZero, _hinnerOne,
    hone, hfree⟩
  right
  exact ⟨hone, hfree⟩

/-- Every one of the four connected channels supplies the same unordered
mode pairing.  No disjointness of the four alternatives is used. -/
theorem connectedPairing_of_connectedChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hchannel : MatchedIteratedQuadraticConnectedChannel observed term) :
    ConnectedReturnModePairing observed term := by
  rcases hchannel with hchannel | hchannel | hchannel | hchannel
  · exact connectedPairing_of_innerZeroObservedFreeCancelsInnerOne
      observed term hchannel
  · exact connectedPairing_of_innerOneObservedFreeCancelsInnerZero
      observed term hchannel
  · exact connectedPairing_of_innerZeroObservedInnerOneCancelsFree
      observed term hchannel
  · exact connectedPairing_of_innerOneObservedInnerZeroCancelsFree
      observed term hchannel

/-- On a connected mode pairing, the compact return weight is the negative
branch sign times the squared modulus of the raw inner quadratic coefficient.
The raw inner sign pattern is not changed on the conjugate branch. -/
theorem compactIteratedQuadraticStaticFeedbackWeight_eq_neg_branchSign_mul_normSq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term))
    (hpair : ConnectedReturnModePairing observed term) :
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
        Complex.normSq
          (freeQuadraticDuhamelCoefficient
            (physlibQuadraticCoupling m kappa 1
              (iteratedQuadraticFirstPicardMode term))
            m (iteratedQuadraticFirstPicardMode term) radius
            (iteratedQuadraticInnerEntry term).1) := by
  have htensor :=
    interactionTensor_outer_eq_inner_of_connectedPairing
      m observed (iteratedQuadraticOuterModes term)
        (iteratedQuadraticInnerEntry term).1.1
        (iteratedQuadraticFirstPicardSlot term) hpair
  have hsqrt :
      Real.sqrt
          (2 * modeFrequency m
            (iteratedQuadraticFirstPicardMode term)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two hInner)
  have hsqrtSq :
      Real.sqrt
          (2 * modeFrequency m
            (iteratedQuadraticFirstPicardMode term)) ^ 2 =
        2 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term) :=
    Real.sq_sqrt (mul_nonneg zero_le_two hInner.le)
  rw [Complex.normSq_apply,
    physlibFreeQuadraticDuhamelCoefficient_re,
    physicalFreeQuadraticDuhamelCoefficient_im]
  simp only [zero_mul, zero_add]
  unfold compactIteratedQuadraticStaticFeedbackWeight
  rw [htensor]
  unfold ConnectedReturnModePairing at hpair
  rcases hpair with hpair | hpair
  · rcases hpair with ⟨hzero, hone⟩
    rw [hzero, hone]
    field_simp [hInner.ne', hsqrt]
    rw [show
      Real.sqrt
          (modeFrequency m
            (iteratedQuadraticFirstPicardMode term) * 2) ^ 2 =
        2 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term) by
      simpa [mul_comm] using hsqrtSq]
    unfold iteratedQuadraticFirstPicardMode
    ring
  · rcases hpair with ⟨hone, hzero⟩
    rw [hone, hzero]
    field_simp [hInner.ne', hsqrt]
    rw [show
      Real.sqrt
          (modeFrequency m
            (iteratedQuadraticFirstPicardMode term) * 2) ^ 2 =
        2 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term) by
      simpa [mul_comm] using hsqrtSq]
    unfold iteratedQuadraticFirstPicardMode
    ring

/-- The conjugate coordinate branch reverses the raw inner mismatch, but the
finite-time resonance weight is even, so the raw inner collision sign pattern
can be retained in the kernel. -/
theorem finiteTimeResonanceWeight_iteratedQuadraticInnerMismatch_eq_raw
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term) time =
      finiteTimeResonanceWeight
        (quadraticPhaseMismatch (modeFrequency m)
          (iteratedQuadraticFirstPicardMode term)
          (iteratedQuadraticInnerEntry term).1) time := by
  rcases term with ⟨outerModes, outerSlot, freeSign, innerTerm, branch⟩
  fin_cases branch <;>
    simp [iteratedQuadraticInnerMismatch,
      firstPicardCoordinateBranchMismatch,
      firstPicardCoordinateBranchSign,
      iteratedQuadraticFirstPicardMode,
      iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticOuterModes,
      iteratedQuadraticInnerEntry,
      finiteTimeResonanceWeight_neg]

/-- Generic connected-pairing bridge.  The sign outside the kernel is
negative on coordinate branch zero and positive on branch one.  The kernel
itself keeps the raw inner quadratic sign pattern, so rotating and
counter-rotating inner channels are not identified. -/
theorem compactWeight_mul_resonance_eq_collisionKernel_mul_actions_of_pairing
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m
      (quadraticCollisionModes
        (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1))
    (hpair : ConnectedReturnModePairing observed term) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed term *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term) time =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign
              (iteratedQuadraticInnerEntry term).1) time
            (quadraticCollisionModes
              (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term).1) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (iteratedQuadraticFreeMode term)) := by
  have hInner :
      0 < modeFrequency m (iteratedQuadraticFirstPicardMode term) := by
    simpa only [quadraticCollisionModes, Fin.cons_zero] using
      hPositive (0 : Fin 3)
  have hActions :
      (∏ r : Fin 2,
        modeAction energy (modeFrequency m)
          ((iteratedQuadraticInnerEntry term).1.1 r)) =
        modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (iteratedQuadraticFreeMode term) := by
    rw [Fin.prod_univ_two]
    unfold ConnectedReturnModePairing at hpair
    rcases hpair with hpair | hpair
    · rw [hpair.1, hpair.2]
    · rw [hpair.1, hpair.2]
      ring
  rw [compactIteratedQuadraticStaticFeedbackWeight_eq_neg_branchSign_mul_normSq
      m kappa (phaseEnergyRadius energy (modeFrequency m)) observed term
      hInner hpair,
    finiteTimeResonanceWeight_iteratedQuadraticInnerMismatch_eq_raw]
  rw [show
    (-firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
        Complex.normSq
          (freeQuadraticDuhamelCoefficient
            (physlibQuadraticCoupling m kappa 1
              (iteratedQuadraticFirstPicardMode term))
            m (iteratedQuadraticFirstPicardMode term)
              (phaseEnergyRadius energy (modeFrequency m))
              (iteratedQuadraticInnerEntry term).1)) *
      finiteTimeResonanceWeight
        (quadraticPhaseMismatch (modeFrequency m)
          (iteratedQuadraticFirstPicardMode term)
          (iteratedQuadraticInnerEntry term).1) time =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
        (Complex.normSq
            (freeQuadraticDuhamelCoefficient
              (physlibQuadraticCoupling m kappa 1
                (iteratedQuadraticFirstPicardMode term))
              m (iteratedQuadraticFirstPicardMode term)
                (phaseEnergyRadius energy (modeFrequency m))
                (iteratedQuadraticInnerEntry term).1) *
          finiteTimeResonanceWeight
            (quadraticPhaseMismatch (modeFrequency m)
              (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term).1) time) by ring,
    physicalQuadraticDiagonalTerm_eq_finiteTimeCollisionKernel_mul_actions
      m kappa time (iteratedQuadraticFirstPicardMode term) energy
        (iteratedQuadraticInnerEntry term).1
        (fun r ↦ hEnergy _) hPositive,
    hActions]
  ring

/-- Unified endpoint for all four connected return channels.  The channel
assumption is used only to obtain the unordered mode pairing, so overlapping
channels in the all-equal case cause no double counting or contradiction. -/
theorem compactWeight_mul_resonance_eq_collisionKernel_mul_actions_of_connectedChannel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m
      (quadraticCollisionModes
        (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1))
    (hchannel : MatchedIteratedQuadraticConnectedChannel observed term) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed term *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term) time =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign
              (iteratedQuadraticInnerEntry term).1) time
            (quadraticCollisionModes
              (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term).1) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (iteratedQuadraticFreeMode term)) := by
  exact
    compactWeight_mul_resonance_eq_collisionKernel_mul_actions_of_pairing
      m kappa time energy observed term hEnergy hPositive
        (connectedPairing_of_connectedChannel observed term hchannel)

end

end ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge
