import ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge

/-!
# Swap symmetry of the two quadratic FPUT input legs

The quadratic free-FPUT expansion is indexed by *ordered* pairs of input
modes and phase signs.  Exchanging both inputs preserves the phase charge,
frequency mismatch, tensor coefficient, collision mismatch, and physical
three-leg weight.  The ordered indexing nevertheless keeps the two exchanged
terms as distinct summands unless both input modes and both signs agree.

This distinction matters in a Haar second moment: a non-fixed swap orbit has
two equal coefficients which add coherently.  Its squared coherent sum is
four times one term, whereas the sum of its two literal diagonal squares is
only twice one term.  Thus input-swap partners must not be silently
diagonalized or deduplicated.

All statements are exact finite-volume algebra for the free first-Picard
terms.  No nonlinear random-phase propagation or kinetic limit is asserted.
-/

namespace ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry

open ArchonPhysics
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NormalizedModeCoupling

noncomputable section

/-- Exchange the two slots of a quadratic input pair. -/
def quadraticInputSlotSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

@[simp] theorem quadraticInputSlotSwap_zero :
    quadraticInputSlotSwap (0 : Fin 2) = 1 := by
  decide

@[simp] theorem quadraticInputSlotSwap_one :
    quadraticInputSlotSwap (1 : Fin 2) = 0 := by
  decide

/-- Fix the output leg and exchange the two input legs of a three-wave
collision tuple. -/
def quadraticCollisionLegSwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

@[simp] theorem quadraticCollisionLegSwap_zero :
    quadraticCollisionLegSwap (0 : Fin 3) = 0 := by
  decide

@[simp] theorem quadraticCollisionLegSwap_one :
    quadraticCollisionLegSwap (1 : Fin 3) = 2 := by
  decide

@[simp] theorem quadraticCollisionLegSwap_two :
    quadraticCollisionLegSwap (2 : Fin 3) = 1 := by
  decide

/-- Simultaneously exchange the two input modes and their phase signs. -/
def swapQuadraticPhaseTerm {N : Nat} [NeZero N]
    (term : QuadraticPhaseTerm N) : QuadraticPhaseTerm N :=
  (term.1 ∘ quadraticInputSlotSwap, (term.2.2, term.2.1))

@[simp] theorem swapQuadraticPhaseTerm_mode_zero
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    (swapQuadraticPhaseTerm term).1 0 = term.1 1 := by
  rfl

@[simp] theorem swapQuadraticPhaseTerm_mode_one
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    (swapQuadraticPhaseTerm term).1 1 = term.1 0 := by
  rfl

@[simp] theorem swapQuadraticPhaseTerm_leftSign
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    (swapQuadraticPhaseTerm term).2.1 = term.2.2 := rfl

@[simp] theorem swapQuadraticPhaseTerm_rightSign
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    (swapQuadraticPhaseTerm term).2.2 = term.2.1 := rfl

/-- Input exchange is an involution on ordered quadratic terms. -/
@[simp] theorem swapQuadraticPhaseTerm_involutive
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    swapQuadraticPhaseTerm (swapQuadraticPhaseTerm term) = term := by
  apply Prod.ext
  · funext r
    fin_cases r <;> rfl
  · rfl

/-- A term is fixed precisely when its two modes and its two binary phase
sectors coincide. -/
theorem swapQuadraticPhaseTerm_eq_self_iff
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    swapQuadraticPhaseTerm term = term ↔
      term.1 0 = term.1 1 ∧ term.2.1 = term.2.2 := by
  constructor
  · intro h
    have hmodes := congrArg (fun t : QuadraticPhaseTerm N ↦ t.1 0) h
    have hsigns := congrArg (fun t : QuadraticPhaseTerm N ↦ t.2.1) h
    exact ⟨(by simpa using hmodes.symm), (by simpa using hsigns.symm)⟩
  · rintro ⟨hmodes, hsigns⟩
    apply Prod.ext
    · funext r
      fin_cases r
      · simpa using hmodes.symm
      · simpa using hmodes
    · apply Prod.ext
      · simpa using hsigns.symm
      · simpa using hsigns

/-- The phase charge retains both input multiplicities and is invariant under
their simultaneous exchange. -/
@[simp] theorem quadraticPhaseCharge_swap
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    quadraticPhaseCharge (swapQuadraticPhaseTerm term) =
      quadraticPhaseCharge term := by
  unfold quadraticPhaseCharge
  simp only [swapQuadraticPhaseTerm_mode_zero,
    swapQuadraticPhaseTerm_mode_one,
    swapQuadraticPhaseTerm_leftSign,
    swapQuadraticPhaseTerm_rightSign]
  exact add_comm _ _

/-- The output-minus-input frequency mismatch is invariant under exchange of
the two ordered inputs. -/
@[simp] theorem quadraticPhaseMismatch_swap
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    quadraticPhaseMismatch frequency observed (swapQuadraticPhaseTerm term) =
      quadraticPhaseMismatch frequency observed term := by
  simp only [quadraticPhaseMismatch, quadraticPhaseCharge_swap]

/-- The three collision modes of a swapped quadratic term are the original
tuple composed with the leg permutation fixing the output. -/
theorem quadraticCollisionModes_swap
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    quadraticCollisionModes observed (swapQuadraticPhaseTerm term) =
      quadraticCollisionModes observed term ∘ quadraticCollisionLegSwap := by
  funext r
  fin_cases r <;> rfl

/-- Collision signs undergo the same simultaneous leg permutation. -/
theorem quadraticCollisionSign_swap
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    quadraticCollisionSign (swapQuadraticPhaseTerm term) =
      quadraticCollisionSign term ∘ quadraticCollisionLegSwap := by
  funext r
  fin_cases r <;> rfl

/-- The random-mass harmonic collision mismatch is unchanged by simultaneous
exchange of the two input signs and modes. -/
theorem phaseMismatch_quadraticCollision_swap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    phaseMismatch m (quadraticCollisionSign (swapQuadraticPhaseTerm term))
        (quadraticCollisionModes observed (swapQuadraticPhaseTerm term)) =
      phaseMismatch m (quadraticCollisionSign term)
        (quadraticCollisionModes observed term) := by
  rw [← quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch,
    quadraticPhaseMismatch_swap,
    quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch]

/-- The normalized three-leg interaction weight is invariant under exchange
of the two quadratic input legs. -/
theorem normalizedInteractionWeight_quadraticCollision_swap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    normalizedInteractionWeight m
        (quadraticCollisionModes observed (swapQuadraticPhaseTerm term)) =
      normalizedInteractionWeight m
        (quadraticCollisionModes observed term) := by
  rw [quadraticCollisionModes_swap,
    normalizedInteractionWeight_perm]

/-- Tensor symmetry and commutativity of the two radial factors make the raw
quadratic phase coefficient invariant under input exchange. -/
@[simp] theorem quadraticPhaseCoefficient_swap
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) :
    quadraticPhaseCoefficient m observed radius
        (swapQuadraticPhaseTerm term) =
      quadraticPhaseCoefficient m observed radius term := by
  have htensor :
      interactionTensor m 3
          (Fin.cons observed (swapQuadraticPhaseTerm term).1) =
        interactionTensor m 3 (Fin.cons observed term.1) := by
    change interactionTensor m 3
        (quadraticCollisionModes observed (swapQuadraticPhaseTerm term)) =
      interactionTensor m 3 (quadraticCollisionModes observed term)
    rw [quadraticCollisionModes_swap, interactionTensor_perm]
  unfold quadraticPhaseCoefficient
  rw [htensor]
  simp only [swapQuadraticPhaseTerm_mode_zero,
    swapQuadraticPhaseTerm_mode_one]
  ring

/-- The complete deterministic free-Duhamel coefficient has the same swap
symmetry. -/
@[simp] theorem freeQuadraticDuhamelCoefficient_swap
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N) :
    freeQuadraticDuhamelCoefficient coupling m observed radius
        (swapQuadraticPhaseTerm term) =
      freeQuadraticDuhamelCoefficient coupling m observed radius term := by
  unfold freeQuadraticDuhamelCoefficient
  rw [quadraticPhaseCoefficient_swap]

/-- Collision weight including the two input actions.  This is the physical
termwise factor appearing after energy normalization, without its global
coupling square and finite-time resonance factor. -/
def quadraticEnergyCollisionWeight
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) : Real :=
  normalizedInteractionWeight m (quadraticCollisionModes observed term) *
    ∏ r : Fin 2,
      modeAction energy (modeFrequency m) (term.1 r)

/-- The energy-normalized physical collision weight is unchanged by swapping
the two ordered inputs. -/
@[simp] theorem quadraticEnergyCollisionWeight_swap
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) :
    quadraticEnergyCollisionWeight m observed energy
        (swapQuadraticPhaseTerm term) =
      quadraticEnergyCollisionWeight m observed energy term := by
  unfold quadraticEnergyCollisionWeight
  rw [normalizedInteractionWeight_quadraticCollision_swap]
  congr 1
  change
    (∏ r, modeAction energy (modeFrequency m)
      (term.1 (quadraticInputSlotSwap r))) =
      ∏ r, modeAction energy (modeFrequency m) (term.1 r)
  exact Equiv.prod_comp quadraticInputSlotSwap
    (fun r ↦ modeAction energy (modeFrequency m) (term.1 r))

/-- The finite set underlying one input-swap orbit. -/
def quadraticSwapOrbit
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    Finset (QuadraticPhaseTerm N) :=
  {term, swapQuadraticPhaseTerm term}

/-- A non-fixed ordered term and its swapped partner form a two-element
orbit; they remain two indices in the original ordered expansion. -/
theorem card_quadraticSwapOrbit_eq_two_of_ne
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N)
    (hnotFixed : swapQuadraticPhaseTerm term ≠ term) :
    (quadraticSwapOrbit term).card = 2 := by
  simp [quadraticSwapOrbit, Ne.symm hnotFixed]
/-- A fixed term contributes one index to the deduplicated orbit finset. -/
theorem card_quadraticSwapOrbit_eq_one_of_fixed
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N)
    (hfixed : swapQuadraticPhaseTerm term = term) :
    (quadraticSwapOrbit term).card = 1 := by
  simp [quadraticSwapOrbit, hfixed]


/-- Coherent coefficient of the two ordered entries in an input-swap orbit.
For a fixed point this expression intentionally repeats the same ordered
coefficient; use the orbit finset when deduplicated indexing is desired. -/
def coherentQuadraticSwapPairCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N) : Complex :=
  freeQuadraticDuhamelCoefficient coupling m observed radius term +
    freeQuadraticDuhamelCoefficient coupling m observed radius
      (swapQuadraticPhaseTerm term)

/-- Swap partners have equal coefficients, so their coherent ordered-pair
coefficient is twice either one. -/
theorem coherentQuadraticSwapPairCoefficient_eq_two_mul
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (_hnotFixed : swapQuadraticPhaseTerm term ≠ term) :
    coherentQuadraticSwapPairCoefficient coupling m observed radius term =
      2 * freeQuadraticDuhamelCoefficient
        coupling m observed radius term := by
  unfold coherentQuadraticSwapPairCoefficient
  rw [freeQuadraticDuhamelCoefficient_swap]
  ring

/-- Coherent squaring retains both off-diagonal ordered cross terms: the
two-term swap-pair square is four times one literal diagonal square. -/
theorem normSq_coherentQuadraticSwapPairCoefficient_eq_four_mul
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (hnotFixed : swapQuadraticPhaseTerm term ≠ term) :
    Complex.normSq
        (coherentQuadraticSwapPairCoefficient
          coupling m observed radius term) =
      4 * Complex.normSq
        (freeQuadraticDuhamelCoefficient
          coupling m observed radius term) := by
  rw [coherentQuadraticSwapPairCoefficient_eq_two_mul
      coupling m observed radius term hnotFixed,
    Complex.normSq_mul]
  norm_num

/-- By contrast, the sum of the two literal diagonal squares is only twice
one square.  Comparing with the preceding theorem exhibits the additional
factor two supplied by the two ordered off-diagonal cross terms. -/
theorem diagonalNormSq_sum_swap_eq_two_mul
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (_hnotFixed : swapQuadraticPhaseTerm term ≠ term) :
    Complex.normSq
        (freeQuadraticDuhamelCoefficient coupling m observed radius term) +
      Complex.normSq
        (freeQuadraticDuhamelCoefficient coupling m observed radius
          (swapQuadraticPhaseTerm term)) =
      2 * Complex.normSq
        (freeQuadraticDuhamelCoefficient coupling m observed radius term) := by
  rw [freeQuadraticDuhamelCoefficient_swap]
  ring

end

end ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
