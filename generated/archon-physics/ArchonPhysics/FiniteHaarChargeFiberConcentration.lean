import ArchonPhysics.FiniteDuhamelPhaseAverage
import ArchonPhysics.FreeFPUTChargeFiberAggregation
import Mathlib.Algebra.Order.Chebyshev

/-!
# Charge-fiber concentration for finite Haar diagram sums

A finite Duhamel truncation is a deterministic sum of phase characters once
the masses and the non-phase data are frozen.  Haar orthogonality does not in
general diagonalize such a sum: every diagram carrying the same integer
charge remains coherent.  This module gives the exact charge-fiber second
moment and then bounds it by

`(largest charge-fiber multiplicity) * (coefficient l2 mass)`.

Markov's inequality turns that deterministic combinatorial estimate into an
explicit high-probability bound.  The result applies at arbitrary finite
diagram order and therefore isolates two concrete quantities that a
kinetic-time expansion must control: charge multiplicity and coefficient
square mass.  It does not assume either quantity is small and does not claim
nonlinear RPA propagation or a microscopic-to-kinetic limit.
-/

namespace ArchonPhysics.FiniteHaarChargeFiberConcentration

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.RandomPhaseMoments

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

variable {d J : Type*} [Fintype d] [Fintype J]

/-- The indices of a finite diagram family carrying one prescribed charge. -/
def chargeFiber (charge : J → d → Int) (q : d → Int) : Finset J :=
  Finset.univ.filter fun j ↦ charge j = q

/-- The coherent coefficient is literally the sum over its charge fiber. -/
theorem coherentFiberCoefficient_eq_sum_chargeFiber
    (coefficient : J → Complex) (charge : J → d → Int) (q : d → Int) :
    coherentFiberCoefficient charge coefficient q =
      ∑ j ∈ chargeFiber charge q, coefficient j := by
  classical
  unfold coherentFiberCoefficient chargeFiber
  rw [Finset.sum_filter]

/-- The charge fibers partition the finite diagram index set. -/
theorem sum_chargeFibers_eq_sum
    (coefficientMass : J → Real) (charge : J → d → Int) :
    (∑ q ∈ realizedCharges charge,
        ∑ j ∈ chargeFiber charge q, coefficientMass j) =
      ∑ j, coefficientMass j := by
  classical
  simp only [chargeFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [realizedCharges]

/-- Exact real-valued Haar second moment of an arbitrary finite character
family, grouped into complete coherent charge fibers. -/
theorem integral_normSq_finitePhaseCorrection_eq_chargeFiberSum
    (coefficient : J → Complex) (charge : J → d → Int) :
    (∫ phase : UnitAddTorus d,
        Complex.normSq (finitePhaseCorrection coefficient charge phase)
        ∂finitePhaseHaarLaw d) =
      ∑ q ∈ realizedCharges charge,
        Complex.normSq (coherentFiberCoefficient charge coefficient q) := by
  classical
  have hcomplex :
      (∫ phase : UnitAddTorus d,
          (Complex.normSq
            (finitePhaseCorrection coefficient charge phase) : Complex)
          ∂finitePhaseHaarLaw d) =
        ∑ q ∈ realizedCharges charge,
          (Complex.normSq
            (coherentFiberCoefficient charge coefficient q) : Complex) := by
    calc
      (∫ phase : UnitAddTorus d,
          (Complex.normSq
            (finitePhaseCorrection coefficient charge phase) : Complex)
          ∂finitePhaseHaarLaw d) =
          ∫ phase : UnitAddTorus d,
            finitePhaseCorrection coefficient charge phase *
              starRingEnd Complex
                (finitePhaseCorrection coefficient charge phase)
            ∂finitePhaseHaarLaw d := by
        apply integral_congr_ae
        filter_upwards [] with phase
        rw [Complex.mul_conj]
      _ = ∑ j, ∑ k,
          if charge j = charge k then
            coefficient j * starRingEnd Complex (coefficient k)
          else 0 :=
        integral_finitePhaseCorrection_mul_star_eq_equalChargePairSum
          coefficient charge
      _ = ∑ q ∈ realizedCharges charge,
          (Complex.normSq
            (coherentFiberCoefficient charge coefficient q) : Complex) := by
        simpa using
          (sameChargePairSum_eq_realizedChargeFiberNormSqSum
            (charge := charge) (coefficient := coefficient)
            (kernel := fun _ : d → Int ↦ (1 : Complex)))
  norm_cast at hcomplex

/-- Cauchy--Schwarz on one charge fiber.  The estimate retains the actual
fiber cardinality instead of replacing it by the total number of diagrams. -/
theorem normSq_coherentFiberCoefficient_le
    (coefficient : J → Complex) (charge : J → d → Int) (q : d → Int) :
    Complex.normSq (coherentFiberCoefficient charge coefficient q) ≤
      (chargeFiber charge q).card *
        ∑ j ∈ chargeFiber charge q, Complex.normSq (coefficient j) := by
  classical
  rw [coherentFiberCoefficient_eq_sum_chargeFiber,
    Complex.normSq_eq_norm_sq]
  calc
    ‖∑ j ∈ chargeFiber charge q, coefficient j‖ ^ 2 ≤
        (∑ j ∈ chargeFiber charge q, ‖coefficient j‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (chargeFiber charge q).card *
        ∑ j ∈ chargeFiber charge q, ‖coefficient j‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (chargeFiber charge q).card *
        ∑ j ∈ chargeFiber charge q, Complex.normSq (coefficient j) := by
      simp only [Complex.normSq_eq_norm_sq]

/-- If every realized charge fiber has at most `multiplicity` diagrams, the
full Haar second moment is controlled by that multiplicity times the
coefficient square mass. -/
theorem integral_normSq_finitePhaseCorrection_le_of_fiberCard
    (coefficient : J → Complex) (charge : J → d → Int)
    (multiplicity : Nat)
    (hmultiplicity : ∀ q ∈ realizedCharges charge,
      (chargeFiber charge q).card ≤ multiplicity) :
    (∫ phase : UnitAddTorus d,
        Complex.normSq (finitePhaseCorrection coefficient charge phase)
        ∂finitePhaseHaarLaw d) ≤
      multiplicity * ∑ j, Complex.normSq (coefficient j) := by
  classical
  rw [integral_normSq_finitePhaseCorrection_eq_chargeFiberSum]
  calc
    (∑ q ∈ realizedCharges charge,
        Complex.normSq (coherentFiberCoefficient charge coefficient q)) ≤
        ∑ q ∈ realizedCharges charge,
          multiplicity *
            ∑ j ∈ chargeFiber charge q,
              Complex.normSq (coefficient j) := by
      apply Finset.sum_le_sum
      intro q hq
      exact (normSq_coherentFiberCoefficient_le coefficient charge q).trans
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast hmultiplicity q hq)
          (Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _))
    _ = multiplicity *
        ∑ q ∈ realizedCharges charge,
          ∑ j ∈ chargeFiber charge q,
            Complex.normSq (coefficient j) := by
      rw [Finset.mul_sum]
    _ = multiplicity * ∑ j, Complex.normSq (coefficient j) := by
      rw [sum_chargeFibers_eq_sum]

/-- Squared-threshold Markov bound for an arbitrary finite Haar diagram sum.
It is useful without division, including at threshold zero. -/
theorem sq_mul_measureReal_norm_ge_le_of_fiberCard
    (coefficient : J → Complex) (charge : J → d → Int)
    (multiplicity : Nat)
    (hmultiplicity : ∀ q ∈ realizedCharges charge,
      (chargeFiber charge q).card ≤ multiplicity)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    epsilon ^ 2 *
        (finitePhaseHaarLaw d).real
          {phase | epsilon ≤
            ‖finitePhaseCorrection coefficient charge phase‖} ≤
      multiplicity * ∑ j, Complex.normSq (coefficient j) := by
  let secondMoment : UnitAddTorus d → Real := fun phase ↦
    Complex.normSq (finitePhaseCorrection coefficient charge phase)
  have hcontinuous : Continuous secondMoment := by
    exact Complex.continuous_normSq.comp
      (finitePhaseCorrection_continuous coefficient charge)
  have hintegrable : Integrable secondMoment (finitePhaseHaarLaw d) :=
    hcontinuous.integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := finitePhaseHaarLaw d)
    (Filter.Eventually.of_forall fun phase ↦ Complex.normSq_nonneg
      (finitePhaseCorrection coefficient charge phase))
    hintegrable (epsilon ^ 2)
  have hevent :
      {phase : UnitAddTorus d | epsilon ^ 2 ≤ secondMoment phase} =
        {phase | epsilon ≤
          ‖finitePhaseCorrection coefficient charge phase‖} := by
    ext phase
    dsimp [secondMoment]
    rw [Complex.normSq_eq_norm_sq]
    constructor <;> intro h
    · nlinarith [norm_nonneg
        (finitePhaseCorrection coefficient charge phase)]
    · nlinarith [norm_nonneg
        (finitePhaseCorrection coefficient charge phase)]
  rw [hevent] at hmarkov
  exact hmarkov.trans
    (integral_normSq_finitePhaseCorrection_le_of_fiberCard
      coefficient charge multiplicity hmultiplicity)

/-- Explicit probability bound at a positive norm threshold. -/
theorem measureReal_norm_ge_le_of_fiberCard
    (coefficient : J → Complex) (charge : J → d → Int)
    (multiplicity : Nat)
    (hmultiplicity : ∀ q ∈ realizedCharges charge,
      (chargeFiber charge q).card ≤ multiplicity)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    (finitePhaseHaarLaw d).real
        {phase | epsilon ≤
          ‖finitePhaseCorrection coefficient charge phase‖} ≤
      (multiplicity * ∑ j, Complex.normSq (coefficient j)) /
        epsilon ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hepsilon)).2
  simpa [mul_comm] using
    (sq_mul_measureReal_norm_ge_le_of_fiberCard
      coefficient charge multiplicity hmultiplicity hepsilon.le)

end

end ArchonPhysics.FiniteHaarChargeFiberConcentration
