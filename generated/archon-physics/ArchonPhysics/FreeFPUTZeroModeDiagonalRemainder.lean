import ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
import ArchonPhysics.FrozenCollisionMassPositivity

/-!
# Vanishing of the zero-mode free-FPUT diagonal remainder

The diagonal free first-Picard decomposition retains a remainder indexed by
three-leg tuples that are not strictly positive in frequency.  Harmonic mode
frequencies are nonnegative, so every such tuple contains a zero-frequency
leg.  The physical bond coefficient of a zero-frequency normal mode vanishes,
and hence every interaction tensor containing that leg is exactly zero.

It follows that every coefficient in the nonpositive diagonal sector is zero
and the whole remainder vanishes.  This conclusion is stronger than the
energy-normalized specialization: it holds for arbitrary coupling, radii,
frequency labels, and time.

In particular, the proof never evaluates or cancels `phaseEnergyRadius` at a
zero denominator.  Lean totalizes real division at zero, but that convention
plays no role here.  The result is still an exact finite-volume free
first-Picard statement; it does not remove the same-charge off-diagonal
coherent remainder or prove nonlinear random-phase propagation or a kinetic
limit.
-/

namespace ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder

open ArchonPhysics
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NormalizedModeCoupling

noncomputable section

/-- A mode tuple that is not strictly positive contains a leg whose harmonic
frequency is exactly zero.  This uses spectral nonnegativity, not any
division convention. -/
theorem exists_zeroFrequencyLeg_of_not_positiveModeTuple
    {N n : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N)
    (hnotPositive : ¬ PositiveModeTuple m modes) :
    ∃ r, modeFrequency m (modes r) = 0 := by
  simp only [PositiveModeTuple, not_forall] at hnotPositive
  obtain ⟨r, hr⟩ := hnotPositive
  exact ⟨r, le_antisymm (not_lt.mp hr) (modeFrequency_nonneg m _) ⟩

/-- Every interaction tensor indexed by a nonpositive-frequency tuple is
zero, because one physical bond-mode factor is zero. -/
theorem interactionTensor_eq_zero_of_not_positiveModeTuple
    {N n : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N)
    (hnotPositive : ¬ PositiveModeTuple m modes) :
    interactionTensor m n modes = 0 := by
  obtain ⟨r, hfrequency⟩ :=
    exists_zeroFrequencyLeg_of_not_positiveModeTuple m modes hnotPositive
  exact interactionTensor_eq_zero_of_modeFrequency_eq_zero
    m modes r hfrequency

/-- A freely evaluated quadratic phase coefficient is zero whenever its
observed/input three-leg tuple is not strictly positive.  The radii are
arbitrary; in particular no zero-frequency division is used. -/
theorem quadraticPhaseCoefficient_eq_zero_of_not_positive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (hnotPositive : ¬ PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    quadraticPhaseCoefficient m observed radius term = 0 := by
  have htensor : interactionTensor m 3
      (quadraticCollisionModes observed term) = 0 :=
    interactionTensor_eq_zero_of_not_positiveModeTuple
      m (quadraticCollisionModes observed term) hnotPositive
  simpa [quadraticPhaseCoefficient, quadraticCollisionModes] using
    congrArg (fun value : Real ↦
      (value : Complex) *
        ((radius (term.1 0) / 2 : Real) : Complex) *
        ((radius (term.1 1) / 2 : Real) : Complex)) htensor

/-- The corresponding deterministic free-Duhamel coefficient vanishes for
every coupling. -/
theorem freeQuadraticDuhamelCoefficient_eq_zero_of_not_positive
    {N : Nat} [NeZero N] (coupling : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : QuadraticPhaseTerm N)
    (hnotPositive : ¬ PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    freeQuadraticDuhamelCoefficient coupling m observed radius term = 0 := by
  rw [freeQuadraticDuhamelCoefficient,
    quadraticPhaseCoefficient_eq_zero_of_not_positive
      m observed radius term hnotPositive]
  simp

/-- The entire nonpositive-frequency diagonal remainder is identically zero.
This stronger statement does not require a positive observed mode or
energy-normalized radii. -/
theorem nonpositiveFreeQuadraticDiagonalRemainder_eq_zero
    {N : Nat} [NeZero N] (coupling : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    nonpositiveFreeQuadraticDiagonalRemainder
      coupling m observed radius frequency time = 0 := by
  classical
  unfold nonpositiveFreeQuadraticDiagonalRemainder
  apply Finset.sum_eq_zero
  intro term hterm
  have hnotPositive : ¬ PositiveModeTuple m
      (quadraticCollisionModes observed term) := by
    simpa [nonpositiveQuadraticPhaseTerms] using hterm
  rw [freeQuadraticDuhamelCoefficient_eq_zero_of_not_positive
    coupling m observed radius term hnotPositive]
  simp

/-- Therefore the full free quadratic diagonal sum is exactly its strictly
positive-frequency sector; there is no additional zero-mode diagonal term. -/
theorem freeQuadraticDiagonalResonanceSum_eq_positive
    {N : Nat} [NeZero N] (coupling : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticDiagonalResonanceSum
        coupling m observed radius frequency time =
      positiveFreeQuadraticDiagonalResonanceSum
        coupling m observed radius frequency time := by
  rw [freeQuadraticDiagonalResonanceSum_eq_positive_add_nonpositive,
    nonpositiveFreeQuadraticDiagonalRemainder_eq_zero]
  simp

/-- Physical quadratic coupling and prescribed-energy radii are a direct
specialization of the structural vanishing theorem.  No sign condition on
the energy profile and no evaluation of a zero denominator is needed. -/
theorem physical_nonpositiveFreeQuadraticDiagonalRemainder_eq_zero
    {N : Nat} [NeZero N] (kappa g : Real)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (time : Real) :
    nonpositiveFreeQuadraticDiagonalRemainder
      (physicalQuadraticCoupling kappa g m observed) m observed
      (phaseEnergyRadius energy (modeFrequency m))
      (modeFrequency m) time = 0 :=
  nonpositiveFreeQuadraticDiagonalRemainder_eq_zero
    (physicalQuadraticCoupling kappa g m observed) m observed
    (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time

end

end ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder
