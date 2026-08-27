import ArchonPhysics.FiniteSecondOrderPhaseExpansion

/-!
# Second-order Haar algebra for finite families of phase characters

The single-monomial expansion in `FiniteSecondOrderPhaseExpansion` is not
enough for a genuine Picard layer: each perturbative coefficient is normally
a finite sum of phase characters.  Squaring such a sum retains every ordered
pair of terms with equal charge, including distinct terms in the same charge
fiber.

This module treats the zeroth, first, and second supplied coefficients as
three independently indexed finite character families.  It proves that the
complete Haar-averaged coefficient at order two is

* the full equal-charge ordered-pair sum within the first correction, plus
* the full equal-charge interference between the zeroth and second
  corrections.

Thus no same-charge cross term is diagonalized or discarded.  The statements
are finite phase algebra for supplied coefficients.  They do not construct a
second Picard iterate from a Hamiltonian flow and do not identify a collision
operator, an FGR rate, or a kinetic limit.
-/

namespace ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.RandomPhaseMoments

noncomputable section

variable {d J K J0 J1 J2 : Type*}
variable [Fintype d] [Fintype J] [Fintype K]
variable [Fintype J0] [Fintype J1] [Fintype J2]

/-- The complete ordered-pair coefficient selected by equality of the charges
of two independently indexed finite character families. -/
def equalChargeCrossPairSum
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    Complex := by
  classical
  exact ∑ left, ∑ right,
    if leftCharge left = rightCharge right then
      leftCoefficient left * starRingEnd Complex (rightCoefficient right)
    else 0

/-- The real equal-charge interference of two finite character families.  It
contains every surviving ordered cross pair. -/
def equalChargeFamilyInterference
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    Real :=
  2 * (equalChargeCrossPairSum leftCoefficient leftCharge
    rightCoefficient rightCharge).re

/-- The full Haar square of one finite character family, represented as the
real part of its complete equal-charge ordered-pair sum. -/
def sameChargeFamilySquare
    (coefficient : J → Complex) (charge : J → d → Int) : Real :=
  (equalChargeCrossPairSum coefficient charge coefficient charge).re

/-- Complete finite-family coefficient at perturbative order two.  The first
summand is the entire `A1` square, not merely its literal diagonal; the second
is the entire `A0`/`A2` interference. -/
def finiteCharacterFamilySecondOrderCoefficient
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int) : Real :=
  sameChargeFamilySquare wCoefficient wCharge +
    equalChargeFamilyInterference zCoefficient zCharge uCoefficient uCharge

/-- Three independently indexed finite phase-character sums inserted into the
two-step perturbative amplitude. -/
def finiteCharacterFamilyTwoStepAmplitude
    (epsilon : Real)
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int)
    (phase : UnitAddTorus d) : Complex :=
  twoStepPerturbedAmplitude epsilon
    (finitePhaseCorrection zCoefficient zCharge phase)
    (finitePhaseCorrection wCoefficient wCharge phase)
    (finitePhaseCorrection uCoefficient uCharge phase)

/-- Exact Haar moment polynomial for three finite character families. -/
def finiteCharacterFamilyTwoStepMomentPolynomial
    (epsilon : Real)
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int) : Real :=
  sameChargeFamilySquare zCoefficient zCharge +
    epsilon * equalChargeFamilyInterference
      zCoefficient zCharge wCoefficient wCharge +
    epsilon ^ 2 * finiteCharacterFamilySecondOrderCoefficient
      zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge +
    epsilon ^ 3 * equalChargeFamilyInterference
      wCoefficient wCharge uCoefficient uCharge +
    epsilon ^ 4 * sameChargeFamilySquare uCoefficient uCharge

/-- The product of two independently indexed character sums is a character
sum indexed by all ordered cross pairs and carrying the charge difference. -/
theorem finitePhaseCorrection_mul_star_eq_crossPairCorrection
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int)
    (phase : UnitAddTorus d) :
    finitePhaseCorrection leftCoefficient leftCharge phase *
        starRingEnd Complex
          (finitePhaseCorrection rightCoefficient rightCharge phase) =
      finitePhaseCorrection
        (fun pair : J × K ↦
          leftCoefficient pair.1 *
            starRingEnd Complex (rightCoefficient pair.2))
        (fun pair : J × K ↦ leftCharge pair.1 - rightCharge pair.2)
        phase := by
  simp only [finitePhaseCorrection, map_sum, map_mul]
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left hleft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right hright
  calc
    (leftCoefficient left * mFourier (leftCharge left) phase) *
        (starRingEnd Complex (rightCoefficient right) *
          starRingEnd Complex (mFourier (rightCharge right) phase)) =
      (leftCoefficient left * starRingEnd Complex (rightCoefficient right)) *
        (mFourier (leftCharge left) phase *
          starRingEnd Complex (mFourier (rightCharge right) phase)) := by ring
    _ = (leftCoefficient left * starRingEnd Complex (rightCoefficient right)) *
        mFourier (leftCharge left - rightCharge right) phase := by
      rw [mFourier_mul_star_mFourier]

/-- The cross product of two finite character families is Haar integrable. -/
theorem integrable_finitePhaseCorrection_mul_star
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    Integrable (fun phase : UnitAddTorus d ↦
      finitePhaseCorrection leftCoefficient leftCharge phase *
        starRingEnd Complex
          (finitePhaseCorrection rightCoefficient rightCharge phase))
      (finitePhaseHaarLaw d) := by
  let pairCoefficient : J × K → Complex := fun pair ↦
    leftCoefficient pair.1 * starRingEnd Complex (rightCoefficient pair.2)
  let pairCharge : J × K → d → Int := fun pair ↦
    leftCharge pair.1 - rightCharge pair.2
  have hpair : Integrable
      (finitePhaseCorrection pairCoefficient pairCharge)
      (finitePhaseHaarLaw d) := by
    unfold finitePhaseCorrection
    exact integrable_finsetSum Finset.univ fun pair _hpair ↦
      (integrable_mFourier_finitePhaseHaarLaw
        (pairCharge pair)).const_mul (pairCoefficient pair)
  refine hpair.congr (Filter.Eventually.of_forall fun phase ↦ ?_)
  exact (finitePhaseCorrection_mul_star_eq_crossPairCorrection
    leftCoefficient leftCharge rightCoefficient rightCharge phase).symm

/-- Exact cross-family Haar selector: all and only equal-charge ordered pairs
survive. -/
theorem integral_finitePhaseCorrection_mul_star_eq_equalChargeCrossPairSum
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    (∫ phase : UnitAddTorus d,
      finitePhaseCorrection leftCoefficient leftCharge phase *
        starRingEnd Complex
          (finitePhaseCorrection rightCoefficient rightCharge phase)
      ∂finitePhaseHaarLaw d) =
      equalChargeCrossPairSum leftCoefficient leftCharge
        rightCoefficient rightCharge := by
  calc
    (∫ phase : UnitAddTorus d,
      finitePhaseCorrection leftCoefficient leftCharge phase *
        starRingEnd Complex
          (finitePhaseCorrection rightCoefficient rightCharge phase)
      ∂finitePhaseHaarLaw d) =
        ∫ phase : UnitAddTorus d,
          finitePhaseCorrection
            (fun pair : J × K ↦
              leftCoefficient pair.1 *
                starRingEnd Complex (rightCoefficient pair.2))
            (fun pair : J × K ↦ leftCharge pair.1 - rightCharge pair.2)
            phase ∂finitePhaseHaarLaw d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦
        finitePhaseCorrection_mul_star_eq_crossPairCorrection
          leftCoefficient leftCharge rightCoefficient rightCharge phase
    _ = ∑ pair : J × K,
        if leftCharge pair.1 - rightCharge pair.2 = 0 then
          leftCoefficient pair.1 *
            starRingEnd Complex (rightCoefficient pair.2)
        else 0 :=
      integral_finitePhaseCorrection_eq_zeroChargeSum
        (fun pair : J × K ↦
          leftCoefficient pair.1 *
            starRingEnd Complex (rightCoefficient pair.2))
        (fun pair : J × K ↦ leftCharge pair.1 - rightCharge pair.2)
    _ = equalChargeCrossPairSum leftCoefficient leftCharge
        rightCoefficient rightCharge := by
      unfold equalChargeCrossPairSum
      rw [Fintype.sum_prod_type]
      simp only [sub_eq_zero]

/-- The real first-moment interference of two finite character families is
integrable. -/
theorem integrable_secondMomentFirst_finitePhaseCorrections
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    Integrable (fun phase : UnitAddTorus d ↦
      secondMomentFirst
        (finitePhaseCorrection leftCoefficient leftCharge phase)
        (finitePhaseCorrection rightCoefficient rightCharge phase))
      (finitePhaseHaarLaw d) := by
  have hcross := integrable_finitePhaseCorrection_mul_star
    leftCoefficient leftCharge rightCoefficient rightCharge
  change Integrable (fun phase : UnitAddTorus d ↦
    2 * RCLike.re
      (finitePhaseCorrection leftCoefficient leftCharge phase *
        starRingEnd Complex
          (finitePhaseCorrection rightCoefficient rightCharge phase)))
    (finitePhaseHaarLaw d)
  exact hcross.re.const_mul 2

/-- Haar averaging the real interference keeps the full equal-charge cross
sum, including non-diagonal pairs. -/
theorem integral_secondMomentFirst_finitePhaseCorrections
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    (∫ phase : UnitAddTorus d,
      secondMomentFirst
        (finitePhaseCorrection leftCoefficient leftCharge phase)
        (finitePhaseCorrection rightCoefficient rightCharge phase)
      ∂finitePhaseHaarLaw d) =
      equalChargeFamilyInterference leftCoefficient leftCharge
        rightCoefficient rightCharge := by
  have hcross := integrable_finitePhaseCorrection_mul_star
    leftCoefficient leftCharge rightCoefficient rightCharge
  change (∫ phase : UnitAddTorus d,
    2 * RCLike.re
      (finitePhaseCorrection leftCoefficient leftCharge phase *
        starRingEnd Complex
          (finitePhaseCorrection rightCoefficient rightCharge phase))
    ∂finitePhaseHaarLaw d) = _
  rw [integral_const_mul, integral_re hcross,
    integral_finitePhaseCorrection_mul_star_eq_equalChargeCrossPairSum]
  rfl

/-- The squared magnitude of a finite character family is Haar integrable. -/
theorem integrable_secondMomentSecond_finitePhaseCorrection
    (coefficient : J → Complex) (charge : J → d → Int) :
    Integrable (fun phase : UnitAddTorus d ↦
      secondMomentSecond (finitePhaseCorrection coefficient charge phase))
      (finitePhaseHaarLaw d) := by
  have hcross := integrable_finitePhaseCorrection_mul_star
    coefficient charge coefficient charge
  refine hcross.re.congr (Filter.Eventually.of_forall fun phase ↦ ?_)
  change RCLike.re
      (finitePhaseCorrection coefficient charge phase *
        starRingEnd Complex (finitePhaseCorrection coefficient charge phase)) =
    Complex.normSq (finitePhaseCorrection coefficient charge phase)
  rw [Complex.mul_conj]
  exact RCLike.ofReal_re _

/-- The Haar square of a finite character family is its complete same-charge
ordered-pair square, not merely the sum of diagonal coefficient norms. -/
theorem integral_secondMomentSecond_finitePhaseCorrection
    (coefficient : J → Complex) (charge : J → d → Int) :
    (∫ phase : UnitAddTorus d,
      secondMomentSecond (finitePhaseCorrection coefficient charge phase)
      ∂finitePhaseHaarLaw d) =
      sameChargeFamilySquare coefficient charge := by
  have hcross := integrable_finitePhaseCorrection_mul_star
    coefficient charge coefficient charge
  calc
    (∫ phase : UnitAddTorus d,
      secondMomentSecond (finitePhaseCorrection coefficient charge phase)
      ∂finitePhaseHaarLaw d) =
        ∫ phase : UnitAddTorus d,
          RCLike.re
            (finitePhaseCorrection coefficient charge phase *
              starRingEnd Complex
                (finitePhaseCorrection coefficient charge phase))
          ∂finitePhaseHaarLaw d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        change Complex.normSq (finitePhaseCorrection coefficient charge phase) =
          RCLike.re
            (finitePhaseCorrection coefficient charge phase *
              starRingEnd Complex
                (finitePhaseCorrection coefficient charge phase))
        rw [Complex.mul_conj]
        exact (RCLike.ofReal_re _).symm
    _ = RCLike.re
        (∫ phase : UnitAddTorus d,
          finitePhaseCorrection coefficient charge phase *
            starRingEnd Complex
              (finitePhaseCorrection coefficient charge phase)
          ∂finitePhaseHaarLaw d) := integral_re hcross
    _ = sameChargeFamilySquare coefficient charge := by
      rw [integral_finitePhaseCorrection_mul_star_eq_equalChargeCrossPairSum]
      rfl

/-- Main second-order family theorem.  The first contribution contains every
same-charge `A1`/`A1` ordered pair, while the second contains every same-charge
`A0`/`A2` interference pair. -/
theorem integral_twoStepSecondCoefficient_finitePhaseCorrections
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int) :
    (∫ phase : UnitAddTorus d,
      twoStepSecondCoefficient
        (finitePhaseCorrection zCoefficient zCharge phase)
        (finitePhaseCorrection wCoefficient wCharge phase)
        (finitePhaseCorrection uCoefficient uCharge phase)
      ∂finitePhaseHaarLaw d) =
      finiteCharacterFamilySecondOrderCoefficient
        zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge := by
  unfold twoStepSecondCoefficient
    finiteCharacterFamilySecondOrderCoefficient
  rw [integral_add]
  · rw [integral_secondMomentSecond_finitePhaseCorrection,
      integral_secondMomentFirst_finitePhaseCorrections]
  · exact integrable_secondMomentSecond_finitePhaseCorrection
      wCoefficient wCharge
  · exact integrable_secondMomentFirst_finitePhaseCorrections
      zCoefficient zCharge uCoefficient uCharge

/-- First-order Haar interference selector for finite character families. -/
theorem integral_twoStepFirstCoefficient_finitePhaseCorrections
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int) :
    (∫ phase : UnitAddTorus d,
      secondMomentFirst
        (finitePhaseCorrection zCoefficient zCharge phase)
        (finitePhaseCorrection wCoefficient wCharge phase)
      ∂finitePhaseHaarLaw d) =
      equalChargeFamilyInterference
        zCoefficient zCharge wCoefficient wCharge :=
  integral_secondMomentFirst_finitePhaseCorrections
    zCoefficient zCharge wCoefficient wCharge

/-- Finite-term Bochner linearity for assembling the five exact perturbative
coefficients. -/
private theorem integral_add_five {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {f0 f1 f2 f3 f4 : Omega → Real}
    (h0 : Integrable f0 mu) (h1 : Integrable f1 mu) (h2 : Integrable f2 mu)
    (h3 : Integrable f3 mu) (h4 : Integrable f4 mu) :
    (∫ x, f0 x + f1 x + f2 x + f3 x + f4 x ∂mu) =
      (∫ x, f0 x ∂mu) + (∫ x, f1 x ∂mu) + (∫ x, f2 x ∂mu) +
        (∫ x, f3 x ∂mu) + (∫ x, f4 x ∂mu) := by
  calc
    _ = (∫ x, f0 x + f1 x + f2 x + f3 x ∂mu) + (∫ x, f4 x ∂mu) := by
      simpa only [Pi.add_apply] using integral_add (((h0.add h1).add h2).add h3) h4
    _ = ((∫ x, f0 x + f1 x + f2 x ∂mu) + (∫ x, f3 x ∂mu)) +
        (∫ x, f4 x ∂mu) := by
      congr 1
      simpa only [Pi.add_apply] using integral_add ((h0.add h1).add h2) h3
    _ = (((∫ x, f0 x + f1 x ∂mu) + (∫ x, f2 x ∂mu)) +
        (∫ x, f3 x ∂mu)) + (∫ x, f4 x ∂mu) := by
      congr 2
      simpa only [Pi.add_apply] using integral_add (h0.add h1) h2
    _ = _ := by
      congr 3
      simpa only [Pi.add_apply] using integral_add h0 h1

/-- Exact Haar average of the full two-step squared amplitude for three finite
character families.  The displayed polynomial retains all equal-charge cross
terms at every perturbative order. -/
theorem integral_normSq_finiteCharacterFamilyTwoStepAmplitude
    (epsilon : Real)
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int) :
    (∫ phase : UnitAddTorus d,
      Complex.normSq
        (finiteCharacterFamilyTwoStepAmplitude epsilon
          zCoefficient zCharge wCoefficient wCharge
          uCoefficient uCharge phase)
      ∂finitePhaseHaarLaw d) =
      finiteCharacterFamilyTwoStepMomentPolynomial epsilon
        zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge := by
  let z : UnitAddTorus d → Complex :=
    finitePhaseCorrection zCoefficient zCharge
  let w : UnitAddTorus d → Complex :=
    finitePhaseCorrection wCoefficient wCharge
  let u : UnitAddTorus d → Complex :=
    finitePhaseCorrection uCoefficient uCharge
  have h0 : Integrable (fun phase ↦ secondMomentZeroth (z phase))
      (finitePhaseHaarLaw d) := by
    simpa only [secondMomentZeroth, secondMomentSecond] using
      (integrable_secondMomentSecond_finitePhaseCorrection
        zCoefficient zCharge)
  have h1 : Integrable (fun phase ↦ secondMomentFirst (z phase) (w phase))
      (finitePhaseHaarLaw d) :=
    integrable_secondMomentFirst_finitePhaseCorrections
      zCoefficient zCharge wCoefficient wCharge
  have h2 : Integrable (fun phase ↦
      twoStepSecondCoefficient (z phase) (w phase) (u phase))
      (finitePhaseHaarLaw d) := by
    unfold twoStepSecondCoefficient
    exact (integrable_secondMomentSecond_finitePhaseCorrection
      wCoefficient wCharge).add
        (integrable_secondMomentFirst_finitePhaseCorrections
          zCoefficient zCharge uCoefficient uCharge)
  have h3 : Integrable (fun phase ↦
      twoStepThirdCoefficient (w phase) (u phase))
      (finitePhaseHaarLaw d) := by
    unfold twoStepThirdCoefficient
    exact integrable_secondMomentFirst_finitePhaseCorrections
      wCoefficient wCharge uCoefficient uCharge
  have h4 : Integrable (fun phase ↦ twoStepFourthCoefficient (u phase))
      (finitePhaseHaarLaw d) := by
    simpa only [twoStepFourthCoefficient, secondMomentSecond] using
      (integrable_secondMomentSecond_finitePhaseCorrection
        uCoefficient uCharge)
  calc
    (∫ phase : UnitAddTorus d,
      Complex.normSq
        (finiteCharacterFamilyTwoStepAmplitude epsilon
          zCoefficient zCharge wCoefficient wCharge
          uCoefficient uCharge phase)
      ∂finitePhaseHaarLaw d) =
        ∫ phase : UnitAddTorus d,
          secondMomentZeroth (z phase) +
            epsilon * secondMomentFirst (z phase) (w phase) +
            epsilon ^ 2 * twoStepSecondCoefficient
              (z phase) (w phase) (u phase) +
            epsilon ^ 3 * twoStepThirdCoefficient (w phase) (u phase) +
            epsilon ^ 4 * twoStepFourthCoefficient (u phase)
          ∂finitePhaseHaarLaw d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        exact normSq_twoStepPerturbedAmplitude
          (z phase) (w phase) (u phase) epsilon
    _ = (∫ phase, secondMomentZeroth (z phase) ∂finitePhaseHaarLaw d) +
          epsilon * (∫ phase,
            secondMomentFirst (z phase) (w phase) ∂finitePhaseHaarLaw d) +
          epsilon ^ 2 * (∫ phase,
            twoStepSecondCoefficient (z phase) (w phase) (u phase)
              ∂finitePhaseHaarLaw d) +
          epsilon ^ 3 * (∫ phase,
            twoStepThirdCoefficient (w phase) (u phase)
              ∂finitePhaseHaarLaw d) +
          epsilon ^ 4 * (∫ phase,
            twoStepFourthCoefficient (u phase) ∂finitePhaseHaarLaw d) := by
      simpa only [integral_const_mul] using
        integral_add_five (finitePhaseHaarLaw d) h0
          (h1.const_mul epsilon) (h2.const_mul (epsilon ^ 2))
          (h3.const_mul (epsilon ^ 3)) (h4.const_mul (epsilon ^ 4))
    _ = finiteCharacterFamilyTwoStepMomentPolynomial epsilon
        zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge := by
      unfold finiteCharacterFamilyTwoStepMomentPolynomial
        twoStepThirdCoefficient twoStepFourthCoefficient
      dsimp [z, w, u]
      rw [show (∫ phase : UnitAddTorus d,
            secondMomentZeroth
              (finitePhaseCorrection zCoefficient zCharge phase)
            ∂finitePhaseHaarLaw d) =
          sameChargeFamilySquare zCoefficient zCharge by
            simpa only [secondMomentZeroth, secondMomentSecond] using
              (integral_secondMomentSecond_finitePhaseCorrection
                zCoefficient zCharge),
        integral_secondMomentFirst_finitePhaseCorrections,
        integral_twoStepSecondCoefficient_finitePhaseCorrections,
        integral_secondMomentFirst_finitePhaseCorrections,
        integral_secondMomentSecond_finitePhaseCorrection]

end

end ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
