import ArchonPhysics.FreeFPUTHaarResonanceReduction

/-!
# Charge-fiber aggregation for the free FPUT first Picard term

The exact Haar second moment of a finite character sum retains every ordered
pair of terms with the same integer charge.  This module rewrites that full
pair sum as the squared norm of the *coherent* coefficient obtained by adding
all coefficients in each realized charge fiber.  Thus all off-diagonal cross
terms inside a fiber are retained.

For the freely evaluated quadratic FPUT source, the frequency mismatch is a
function of the charge.  The coherent norm square in each realized fiber can
therefore be multiplied by that fiber's common finite-time resonance weight.
This is an exact finite-volume, free first-Picard identity.  It does not turn
the coherent fibers into termwise collision diagonals, propagate random
phases under the nonlinear flow, or prove a kinetic limit.
-/

namespace ArchonPhysics.FreeFPUTChargeFiberAggregation

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTHaarResonanceReduction
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

variable {J Q : Type*} [Fintype J]

/-- The finite set of charges actually realized by a finite family of terms. -/
def realizedCharges [DecidableEq Q] (charge : J → Q) : Finset Q :=
  Finset.univ.image charge

/-- The coherent sum of all coefficients in one charge fiber. -/
def coherentFiberCoefficient [DecidableEq Q]
    (charge : J → Q) (coefficient : J → Complex) (q : Q) : Complex :=
  ∑ j, if charge j = q then coefficient j else 0

@[simp] theorem mem_realizedCharges [DecidableEq Q]
    (charge : J → Q) (j : J) :
    charge j ∈ realizedCharges charge := by
  simp [realizedCharges]

/-- A full same-charge ordered-pair sum is exactly a sum of coherent fiber
norm squares.  In particular, this identity retains every cross term between
distinct indices carrying the same charge. -/
theorem sameChargePairSum_eq_realizedChargeFiberNormSqSum
    [DecidableEq Q] (charge : J → Q) (coefficient : J → Complex)
    (kernel : Q → Complex) :
    (∑ j, ∑ k,
      if charge j = charge k then
        coefficient j * starRingEnd Complex (coefficient k) * kernel (charge j)
      else 0) =
      ∑ q ∈ realizedCharges charge,
        (Complex.normSq (coherentFiberCoefficient charge coefficient q) : Complex) *
          kernel q := by
  classical
  let fiber : Q → Complex := coherentFiberCoefficient charge coefficient
  let distributed : J → Complex := fun j =>
    coefficient j * starRingEnd Complex (fiber (charge j)) *
      kernel (charge j)
  have hfiber : ∀ i ∈ (Finset.univ : Finset J),
      (Complex.normSq (fiber (charge i)) : Complex) * kernel (charge i) =
        ∑ j ∈ (Finset.univ : Finset J) with charge j = charge i,
          distributed j := by
    intro i hi
    rw [← Complex.mul_conj]
    simp only [fiber, coherentFiberCoefficient, map_sum, distributed]
    rw [Finset.sum_filter]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : charge j = charge i
    · simp [hji]
    · simp [hji]
  have haggregate :
      (∑ q ∈ realizedCharges charge,
        (Complex.normSq (fiber q) : Complex) * kernel q) =
        ∑ j, distributed j := by
    simpa only [realizedCharges] using
      (Finset.sum_image'
        (s := (Finset.univ : Finset J)) (g := charge)
        (f := fun q =>
          (Complex.normSq (fiber q) : Complex) * kernel q)
        (h := distributed) hfiber)
  rw [haggregate]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [distributed, fiber, coherentFiberCoefficient, map_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hjk : charge j = charge k
  · rw [if_pos hjk, if_pos hjk.symm]
  · have hkj : charge k ≠ charge j := Ne.symm hjk
    rw [if_neg hjk, if_neg hkj]
    simp

/-- Coherent free-FPUT coefficient carried by one integer phase charge. -/
def freeQuadraticChargeFiberCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (charge : Lattice.Site N → Int) : Complex :=
  coherentFiberCoefficient quadraticPhaseCharge
    (freeQuadraticDuhamelCoefficient coupling m observed radius) charge

/-- The normalized Haar second moment of the free quadratic first-Picard
correction is a sum over realized phase-charge fibers.  Each summand contains
the norm square of the complete coherent fiber coefficient, hence includes
all same-charge off-diagonal cross terms. -/
theorem normalized_integral_normSq_freeQuadraticCorrection_eq_chargeFiberSum
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
      ∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        (Complex.normSq
          (freeQuadraticChargeFiberCoefficient
            coupling m observed radius charge) : Complex) *
          (finiteTimeResonanceWeight
            (outputChargeMismatch (frequency observed) charge frequency) time :
              Complex) := by
  rw [normalized_integral_normSq_freeQuadraticCorrection_eq_sameChargePairSum
    coupling m observed radius frequency htime]
  simpa only [freeQuadraticChargeFiberCoefficient, quadraticPhaseMismatch] using
    (sameChargePairSum_eq_realizedChargeFiberNormSqSum
      (charge := (quadraticPhaseCharge :
        QuadraticPhaseTerm N → Lattice.Site N → Int))
      (coefficient :=
        freeQuadraticDuhamelCoefficient coupling m observed radius)
      (kernel := fun charge =>
        (finiteTimeResonanceWeight
          (outputChargeMismatch (frequency observed) charge frequency) time :
            Complex)))

end

end ArchonPhysics.FreeFPUTChargeFiberAggregation
