import ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge

/-!
# Diagonal collision part of the free FPUT Haar second moment

The exact finite Haar second moment of a character expansion contains every
ordered pair with equal charge.  This module separates that finite sum into
its literal diagonal and an explicit off-diagonal same-charge remainder.

For the freely evaluated quadratic FPUT first Picard correction, the diagonal
is the coefficient norm square times the finite-time resonance weight.  With
energy-normalized initial radii and the physical quadratic coupling, each
diagonal coefficient is then exactly the existing normalized three-leg
interaction weight times the two input actions and `(kappa * g)^2`.
The termwise collision bridge uses an explicit positive-frequency hypothesis.
The full formula applies it only on the filtered positive sector and retains
the complementary diagonal sector as a second remainder.  No cancellation,
nonlinear random-phase propagation, gain-loss equation, kinetic limit, or
thermalization claim is made.
-/

namespace ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTHaarResonanceReduction
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.RandomPhaseMoments

noncomputable section

variable {J Q : Type*} [Fintype J]

/-- The full finite ordered-pair sum selected by equality of charge. -/
def sameChargeOrderedPairSum
    (charge : J → Q) (pairValue : J → J → Complex) : Complex := by
  classical
  exact ∑ left, ∑ right,
    if charge left = charge right then pairValue left right else 0

/-- All distinct ordered pairs that survive the same-charge selector. -/
def offDiagonalSameChargeRemainder
    (charge : J → Q) (pairValue : J → J → Complex) : Complex := by
  classical
  exact ∑ left, ∑ right,
    if charge left = charge right ∧ left ≠ right then
      pairValue left right
    else 0

/-- Exact diagonal/off-diagonal decomposition of a finite same-charge
ordered-pair sum.  No injectivity or cancellation of charge fibers is used. -/
theorem sameChargeOrderedPairSum_eq_diagonal_add_offDiagonal
    (charge : J → Q) (pairValue : J → J → Complex) :
    sameChargeOrderedPairSum charge pairValue =
      (∑ term, pairValue term term) +
        offDiagonalSameChargeRemainder charge pairValue := by
  classical
  unfold sameChargeOrderedPairSum offDiagonalSameChargeRemainder
  calc
    (∑ left, ∑ right,
      if charge left = charge right then pairValue left right else 0) =
        ∑ left, ∑ right,
          ((if left = right then pairValue left right else 0) +
            (if charge left = charge right ∧ left ≠ right then
              pairValue left right
            else 0)) := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      by_cases hlr : left = right
      · subst right
        simp
      · by_cases hcharge : charge left = charge right
        · simp [hlr, hcharge]
        · simp [hlr, hcharge]
    _ =
        (∑ left, ∑ right,
          if left = right then pairValue left right else 0) +
        ∑ left, ∑ right,
          if charge left = charge right ∧ left ≠ right then
            pairValue left right
          else 0 := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ term, pairValue term term) +
        ∑ left, ∑ right,
          if charge left = charge right ∧ left ≠ right then
            pairValue left right
          else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro left hleft
      simp

/-- The real diagonal part of the normalized free-FPUT Haar first-Picard
second moment. -/
def freeQuadraticDiagonalResonanceSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Real :=
  ∑ term : QuadraticPhaseTerm N,
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          coupling m observed radius term) *
      finiteTimeResonanceWeight
        (quadraticPhaseMismatch frequency observed term) time

/-- The coherent same-charge off-diagonal remainder in the normalized
free-FPUT Haar first-Picard second moment. -/
def freeQuadraticOffDiagonalCoherentRemainder
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Complex :=
  offDiagonalSameChargeRemainder quadraticPhaseCharge fun left right ↦
    freeQuadraticDuhamelCoefficient coupling m observed radius left *
      starRingEnd Complex
        (freeQuadraticDuhamelCoefficient
          coupling m observed radius right) *
      (finiteTimeResonanceWeight
        (quadraticPhaseMismatch frequency observed left) time : Complex)

/-- Exact diagonal plus coherent-remainder formula for the positive-time
normalized free-FPUT Haar first-Picard second moment. -/
theorem normalized_integral_normSq_freeQuadraticCorrection_eq_diagonal_add_remainder
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              coupling m observed radius frequency time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      (freeQuadraticDiagonalResonanceSum
          coupling m observed radius frequency time : Complex) +
        freeQuadraticOffDiagonalCoherentRemainder
          coupling m observed radius frequency time := by
  rw [normalized_integral_normSq_freeQuadraticCorrection_eq_sameChargePairSum
    coupling m observed radius frequency htime]
  let pairValue : QuadraticPhaseTerm N → QuadraticPhaseTerm N → Complex :=
    fun left right ↦
      freeQuadraticDuhamelCoefficient coupling m observed radius left *
        starRingEnd Complex
          (freeQuadraticDuhamelCoefficient
            coupling m observed radius right) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch frequency observed left) time : Complex)
  calc
    _ = (∑ term, pairValue term term) +
        offDiagonalSameChargeRemainder quadraticPhaseCharge pairValue := by
      simpa only [sameChargeOrderedPairSum, pairValue] using
        (sameChargeOrderedPairSum_eq_diagonal_add_offDiagonal
          (charge := (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int)) pairValue)
    _ = (freeQuadraticDiagonalResonanceSum
          coupling m observed radius frequency time : Complex) +
        freeQuadraticOffDiagonalCoherentRemainder
          coupling m observed radius frequency time := by
      congr 1
      · unfold freeQuadraticDiagonalResonanceSum pairValue
        push_cast
        apply Finset.sum_congr rfl
        intro term hterm
        rw [Complex.mul_conj]

/-- One diagonal term with energy-normalized radii and the physical
quadratic coupling is exactly the normalized collision weight times the two
input actions and the finite-time resonance factor. -/
theorem physical_freeQuadraticDiagonalResonanceTerm_eq_collisionWeight
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (term : QuadraticPhaseTerm N)
    (time : Real)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed term) time =
      (kappa * g) ^ 2 *
        normalizedInteractionWeight m
          (quadraticCollisionModes observed term) *
        (∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r)) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed term) time := by
  rw [normSq_physicalQuadraticDuhamelCoefficient_eq
    kappa g m observed energy term henergy hpositive]

/-- Quadratic terms whose output and both input modes have strictly positive
frequencies.  This excludes zero-mode tuples instead of imposing an
impossible all-terms positivity hypothesis on a periodic chain. -/
def positiveQuadraticPhaseTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact Finset.univ.filter fun term ↦
    PositiveModeTuple m (quadraticCollisionModes observed term)

/-- The complementary finite set of terms containing at least one
nonpositive-frequency leg. -/
def nonpositiveQuadraticPhaseTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact Finset.univ.filter fun term ↦
    ¬ PositiveModeTuple m (quadraticCollisionModes observed term)

/-- The diagonal resonance sum restricted to genuinely positive-frequency
three-leg tuples. -/
def positiveFreeQuadraticDiagonalResonanceSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Real :=
  ∑ term ∈ positiveQuadraticPhaseTerms m observed,
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          coupling m observed radius term) *
      finiteTimeResonanceWeight
        (quadraticPhaseMismatch frequency observed term) time

/-- The diagonal contribution of tuples containing at least one
nonpositive-frequency leg.  It is retained as an explicit remainder. -/
def nonpositiveFreeQuadraticDiagonalRemainder
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) : Real :=
  ∑ term ∈ nonpositiveQuadraticPhaseTerms m observed,
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          coupling m observed radius term) *
      finiteTimeResonanceWeight
        (quadraticPhaseMismatch frequency observed term) time

/-- Positive and nonpositive frequency sectors exactly partition the full
diagonal sum. -/
theorem freeQuadraticDiagonalResonanceSum_eq_positive_add_nonpositive
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticDiagonalResonanceSum
        coupling m observed radius frequency time =
      positiveFreeQuadraticDiagonalResonanceSum
          coupling m observed radius frequency time +
        nonpositiveFreeQuadraticDiagonalRemainder
          coupling m observed radius frequency time := by
  classical
  simpa [freeQuadraticDiagonalResonanceSum,
    positiveFreeQuadraticDiagonalResonanceSum,
    nonpositiveFreeQuadraticDiagonalRemainder,
    positiveQuadraticPhaseTerms, nonpositiveQuadraticPhaseTerms] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun term : QuadraticPhaseTerm N ↦
        PositiveModeTuple m (quadraticCollisionModes observed term))
      (fun term ↦
        Complex.normSq
            (freeQuadraticDuhamelCoefficient
              coupling m observed radius term) *
          finiteTimeResonanceWeight
            (quadraticPhaseMismatch frequency observed term) time)).symm

/-- With nonnegative input energies, the positive-frequency diagonal sector
is exactly the corresponding normalized collision-weight sum. -/
theorem physical_positiveFreeQuadraticDiagonalResonanceSum_eq_collisionWeightSum
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (time : Real)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    positiveFreeQuadraticDiagonalResonanceSum
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time =
      ∑ term ∈ positiveQuadraticPhaseTerms m observed,
        (kappa * g) ^ 2 *
          normalizedInteractionWeight m
            (quadraticCollisionModes observed term) *
          (∏ r : Fin 2,
            modeAction energy (modeFrequency m) (term.1 r)) *
          finiteTimeResonanceWeight
            (quadraticPhaseMismatch (modeFrequency m) observed term) time := by
  unfold positiveFreeQuadraticDiagonalResonanceSum
  apply Finset.sum_congr rfl
  intro term hterm
  have hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term) := by
    simpa [positiveQuadraticPhaseTerms] using hterm
  exact physical_freeQuadraticDiagonalResonanceTerm_eq_collisionWeight
    kappa g m observed energy term time (fun r ↦ henergy (term.1 r))
      hpositive

/-- Full normalized free-FPUT first-Picard second moment.  The physically
positive diagonal is rewritten as a collision-weight sum; both the
nonpositive-frequency diagonal and same-charge off-diagonal coherent sectors
remain explicit remainders. -/
theorem normalized_physical_freeQuadraticCorrection_eq_collisionSum_add_remainders
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) (henergy : ∀ mode, 0 ≤ energy mode) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              (physicalQuadraticCoupling kappa g m observed) m observed
              (phaseEnergyRadius energy (modeFrequency m))
              (modeFrequency m) time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ((∑ term ∈ positiveQuadraticPhaseTerms m observed,
          (kappa * g) ^ 2 *
            normalizedInteractionWeight m
              (quadraticCollisionModes observed term) *
            (∏ r : Fin 2,
              modeAction energy (modeFrequency m) (term.1 r)) *
            finiteTimeResonanceWeight
              (quadraticPhaseMismatch (modeFrequency m) observed term) time :
          Real) : Complex) +
        (nonpositiveFreeQuadraticDiagonalRemainder
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) time : Complex) +
        freeQuadraticOffDiagonalCoherentRemainder
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) time := by
  rw [normalized_integral_normSq_freeQuadraticCorrection_eq_diagonal_add_remainder
    (physicalQuadraticCoupling kappa g m observed) m observed
    (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) htime]
  rw [freeQuadraticDiagonalResonanceSum_eq_positive_add_nonpositive]
  rw [physical_positiveFreeQuadraticDiagonalResonanceSum_eq_collisionWeightSum
    kappa g m observed energy time henergy]
  norm_cast

end

end ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
