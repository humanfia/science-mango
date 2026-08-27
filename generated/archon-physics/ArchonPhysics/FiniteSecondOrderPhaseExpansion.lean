import ArchonPhysics.DuhamelTwoStepMomentAlgebra
import ArchonPhysics.FiniteDuhamelPhaseAverage

/-!
# Fixed finite-mode second-order phase average

This module combines the exact two-step Duhamel moment polynomial with the
finite Haar charge-balance rule for signed phase monomials.  For three
monomial amplitudes `z`, `w`, and `u`, it computes the full normalized Haar
average of

`|z + epsilon * w + epsilon^2 * u|^2`.

The coefficient of `epsilon^2` is kept intact: it is the sum of `|w|^2` and
the charge-selected interference `2 Re (z * conj u)`.  In particular, this
module does not call `|w|^2` by itself a collision kernel.  Everything here is
an exact identity on a fixed finite phase torus.  There is no thermodynamic
limit, kinetic limit, microscopic derivation of the supplied corrections, or
collision-kernel identification.
-/

namespace ArchonPhysics.FiniteSecondOrderPhaseExpansion

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.RandomPhaseMoments
open scoped ComplexConjugate

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The two-step perturbative amplitude with each supplied coefficient carrying
an explicit finite signed phase monomial. -/
def phaseTwoStepPerturbedAmplitude
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d))
    (phase : UnitAddTorus d) : Complex :=
  twoStepPerturbedAmplitude epsilon
    (weightedSignedMonomial zCoefficient zFactors phase)
    (weightedSignedMonomial wCoefficient wFactors phase)
    (weightedSignedMonomial uCoefficient uFactors phase)

/-- A finite two-step signed-monomial amplitude is continuous on its phase
torus; this supplies the measurability needed for transfer by `HasLaw`. -/
theorem phaseTwoStepPerturbedAmplitude_continuous
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d)) :
    Continuous (phaseTwoStepPerturbedAmplitude epsilon zCoefficient wCoefficient
      uCoefficient zFactors wFactors uFactors) := by
  unfold phaseTwoStepPerturbedAmplitude twoStepPerturbedAmplitude weightedSignedMonomial
  simp_rw [unitSignedMonomial_eq_mFourier]
  fun_prop
/-- The averaged interference between two monomial amplitudes.  Haar averaging
retains it exactly when their total integer charge vectors agree. -/
def chargeSelectedInterference
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d)) : Real :=
  if monomialCharge leftFactors = monomialCharge rightFactors then
    2 * (leftCoefficient * conj rightCoefficient).re
  else 0

/-- The complete averaged coefficient of `epsilon^2`.  Both the square of the
first correction and the initial/second-correction interference are present. -/
def finitePhaseSecondOrderCoefficient
    (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors uFactors : List (SignedMode d)) : Real :=
  Complex.normSq wCoefficient +
    chargeSelectedInterference zCoefficient uCoefficient zFactors uFactors

/-- The exact finite-Haar averaged polynomial associated with the supplied
two-step amplitude. -/
def finitePhaseTwoStepMomentPolynomial
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d)) : Real :=
  Complex.normSq zCoefficient +
    epsilon * chargeSelectedInterference
      zCoefficient wCoefficient zFactors wFactors +
    epsilon ^ 2 * finitePhaseSecondOrderCoefficient
      zCoefficient wCoefficient uCoefficient zFactors uFactors +
    epsilon ^ 3 * chargeSelectedInterference
      wCoefficient uCoefficient wFactors uFactors +
    epsilon ^ 4 * Complex.normSq uCoefficient

/-- A product of one monomial and the conjugate of another carries their
difference charge. -/
theorem weightedSignedMonomial_mul_conj_eq_differenceCharacter
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d))
    (phase : UnitAddTorus d) :
    weightedSignedMonomial leftCoefficient leftFactors phase *
        conj (weightedSignedMonomial rightCoefficient rightFactors phase) =
      (leftCoefficient * conj rightCoefficient) *
        mFourier (monomialCharge leftFactors - monomialCharge rightFactors) phase := by
  simp only [weightedSignedMonomial, unitSignedMonomial_eq_mFourier, map_mul]
  calc
    (leftCoefficient * mFourier (monomialCharge leftFactors) phase) *
        (conj rightCoefficient * conj (mFourier (monomialCharge rightFactors) phase)) =
      (leftCoefficient * conj rightCoefficient) *
        (mFourier (monomialCharge leftFactors) phase *
          conj (mFourier (monomialCharge rightFactors) phase)) := by ring
    _ = (leftCoefficient * conj rightCoefficient) *
        mFourier (monomialCharge leftFactors - monomialCharge rightFactors) phase := by
      rw [mFourier_mul_star_mFourier]


/-- The complex cross product of two weighted signed monomials is integrable. -/
theorem integrable_weightedSignedMonomial_mul_conj
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d)) :
    Integrable (fun phase : UnitAddTorus d =>
      weightedSignedMonomial leftCoefficient leftFactors phase *
        conj (weightedSignedMonomial rightCoefficient rightFactors phase))
      (finitePhaseHaarLaw d) := by
  refine ((integrable_mFourier_finitePhaseHaarLaw
    (monomialCharge leftFactors - monomialCharge rightFactors)).const_mul
      (leftCoefficient * conj rightCoefficient)).congr ?_
  exact Filter.Eventually.of_forall fun phase =>
    (weightedSignedMonomial_mul_conj_eq_differenceCharacter
      leftCoefficient rightCoefficient leftFactors rightFactors phase).symm

/-- Exact two-monomial Haar selector: precisely equal charges survive. -/
theorem integral_weightedSignedMonomial_mul_conj_eq_ite
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      weightedSignedMonomial leftCoefficient leftFactors phase *
        conj (weightedSignedMonomial rightCoefficient rightFactors phase)
      ∂finitePhaseHaarLaw d) =
      if monomialCharge leftFactors = monomialCharge rightFactors then
        leftCoefficient * conj rightCoefficient
      else 0 := by
  calc
    (∫ phase : UnitAddTorus d,
      weightedSignedMonomial leftCoefficient leftFactors phase *
        conj (weightedSignedMonomial rightCoefficient rightFactors phase)
      ∂finitePhaseHaarLaw d) =
        ∫ phase : UnitAddTorus d,
          (leftCoefficient * conj rightCoefficient) *
            mFourier
              (monomialCharge leftFactors - monomialCharge rightFactors) phase
          ∂finitePhaseHaarLaw d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase =>
        weightedSignedMonomial_mul_conj_eq_differenceCharacter
          leftCoefficient rightCoefficient leftFactors rightFactors phase
    _ = (leftCoefficient * conj rightCoefficient) *
        (if monomialCharge leftFactors - monomialCharge rightFactors = 0 then 1 else 0) := by
      rw [integral_const_mul, integral_mFourier_eq_ite]
    _ = if monomialCharge leftFactors = monomialCharge rightFactors then
        leftCoefficient * conj rightCoefficient else 0 := by
      simp only [sub_eq_zero]
      split_ifs <;> simp

/-- The real interference observable is integrable. -/
theorem integrable_secondMomentFirst_weightedSignedMonomial
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d)) :
    Integrable (fun phase : UnitAddTorus d =>
      secondMomentFirst
        (weightedSignedMonomial leftCoefficient leftFactors phase)
        (weightedSignedMonomial rightCoefficient rightFactors phase))
      (finitePhaseHaarLaw d) := by
  have hcross := integrable_weightedSignedMonomial_mul_conj
    leftCoefficient rightCoefficient leftFactors rightFactors
  change Integrable (fun phase => 2 * RCLike.re
    (weightedSignedMonomial leftCoefficient leftFactors phase *
      conj (weightedSignedMonomial rightCoefficient rightFactors phase)))
    (finitePhaseHaarLaw d)
  exact hcross.re.const_mul 2

/-- Haar averaging of a first-order interference is exactly the charge
selector encoded by `chargeSelectedInterference`. -/
theorem integral_secondMomentFirst_weightedSignedMonomial
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      secondMomentFirst
        (weightedSignedMonomial leftCoefficient leftFactors phase)
        (weightedSignedMonomial rightCoefficient rightFactors phase)
      ∂finitePhaseHaarLaw d) =
      chargeSelectedInterference
        leftCoefficient rightCoefficient leftFactors rightFactors := by
  have hcross := integrable_weightedSignedMonomial_mul_conj
    leftCoefficient rightCoefficient leftFactors rightFactors
  change (∫ phase : UnitAddTorus d, 2 * RCLike.re
      (weightedSignedMonomial leftCoefficient leftFactors phase *
        conj (weightedSignedMonomial rightCoefficient rightFactors phase))
      ∂finitePhaseHaarLaw d) = _
  rw [integral_const_mul, integral_re hcross,
    integral_weightedSignedMonomial_mul_conj_eq_ite]
  unfold chargeSelectedInterference
  split_ifs <;> simp

/-- The squared absolute value of one weighted signed monomial is integrable. -/
theorem integrable_secondMomentZeroth_weightedSignedMonomial
    (coefficient : Complex) (factors : List (SignedMode d)) :
    Integrable (fun phase : UnitAddTorus d =>
      secondMomentZeroth (weightedSignedMonomial coefficient factors phase))
      (finitePhaseHaarLaw d) := by
  have hcross := integrable_weightedSignedMonomial_mul_conj
    coefficient coefficient factors factors
  refine hcross.re.congr (Filter.Eventually.of_forall fun phase => ?_)
  change RCLike.re
      (weightedSignedMonomial coefficient factors phase *
        conj (weightedSignedMonomial coefficient factors phase)) =
    Complex.normSq (weightedSignedMonomial coefficient factors phase)
  rw [Complex.mul_conj]
  exact RCLike.ofReal_re _

/-- A monomial has constant squared magnitude after Haar averaging. -/
theorem integral_secondMomentZeroth_weightedSignedMonomial
    (coefficient : Complex) (factors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      secondMomentZeroth (weightedSignedMonomial coefficient factors phase)
      ∂finitePhaseHaarLaw d) = Complex.normSq coefficient := by
  have hcross := integrable_weightedSignedMonomial_mul_conj
    coefficient coefficient factors factors
  calc
    (∫ phase : UnitAddTorus d,
      secondMomentZeroth (weightedSignedMonomial coefficient factors phase)
      ∂finitePhaseHaarLaw d) =
        ∫ phase : UnitAddTorus d,
          (weightedSignedMonomial coefficient factors phase *
            conj (weightedSignedMonomial coefficient factors phase)).re
          ∂finitePhaseHaarLaw d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase => by
        change Complex.normSq (weightedSignedMonomial coefficient factors phase) =
          RCLike.re
            (weightedSignedMonomial coefficient factors phase *
              conj (weightedSignedMonomial coefficient factors phase))
        rw [Complex.mul_conj]
        exact (RCLike.ofReal_re _).symm
    _ = ((∫ phase : UnitAddTorus d,
          weightedSignedMonomial coefficient factors phase *
            conj (weightedSignedMonomial coefficient factors phase)
          ∂finitePhaseHaarLaw d)).re := integral_re hcross
    _ = Complex.normSq coefficient := by
      rw [integral_weightedSignedMonomial_mul_conj_eq_ite]
      simp [Complex.mul_conj]


/-- The square term used for a perturbative correction is integrable. -/
theorem integrable_secondMomentSecond_weightedSignedMonomial
    (coefficient : Complex) (factors : List (SignedMode d)) :
    Integrable (fun phase : UnitAddTorus d =>
      secondMomentSecond (weightedSignedMonomial coefficient factors phase))
      (finitePhaseHaarLaw d) := by
  simpa only [secondMomentSecond, secondMomentZeroth] using
    integrable_secondMomentZeroth_weightedSignedMonomial coefficient factors

/-- The averaged correction square is its deterministic squared magnitude. -/
theorem integral_secondMomentSecond_weightedSignedMonomial
    (coefficient : Complex) (factors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      secondMomentSecond (weightedSignedMonomial coefficient factors phase)
      ∂finitePhaseHaarLaw d) = Complex.normSq coefficient := by
  simpa only [secondMomentSecond, secondMomentZeroth] using
    integral_secondMomentZeroth_weightedSignedMonomial coefficient factors
/-- The averaged complete second-order coefficient contains both required
pieces, with the interference selected only by equality of total charges. -/
theorem integral_twoStepSecondCoefficient_weightedSignedMonomial
    (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      twoStepSecondCoefficient
        (weightedSignedMonomial zCoefficient zFactors phase)
        (weightedSignedMonomial wCoefficient wFactors phase)
        (weightedSignedMonomial uCoefficient uFactors phase)
      ∂finitePhaseHaarLaw d) =
      finitePhaseSecondOrderCoefficient
        zCoefficient wCoefficient uCoefficient zFactors uFactors := by
  unfold twoStepSecondCoefficient finitePhaseSecondOrderCoefficient
  rw [integral_add]
  · rw [integral_secondMomentSecond_weightedSignedMonomial,
      integral_secondMomentFirst_weightedSignedMonomial]
  · exact integrable_secondMomentSecond_weightedSignedMonomial
      wCoefficient wFactors
  · exact integrable_secondMomentFirst_weightedSignedMonomial
      zCoefficient uCoefficient zFactors uFactors

/-- Finite-term Bochner linearity used only to assemble the exact polynomial. -/
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

/-- Exact normalized finite-phase average of the full two-step squared
amplitude.  This is a fixed finite-dimensional identity, not a kinetic-limit
or collision-kernel theorem. -/
theorem integral_normSq_phaseTwoStepPerturbedAmplitude
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
        zCoefficient wCoefficient uCoefficient
        zFactors wFactors uFactors phase)
      ∂finitePhaseHaarLaw d) =
      finitePhaseTwoStepMomentPolynomial epsilon
        zCoefficient wCoefficient uCoefficient
        zFactors wFactors uFactors := by
  let z : UnitAddTorus d → Complex :=
    fun phase => weightedSignedMonomial zCoefficient zFactors phase
  let w : UnitAddTorus d → Complex :=
    fun phase => weightedSignedMonomial wCoefficient wFactors phase
  let u : UnitAddTorus d → Complex :=
    fun phase => weightedSignedMonomial uCoefficient uFactors phase
  have h0 : Integrable (fun phase => secondMomentZeroth (z phase))
      (finitePhaseHaarLaw d) :=
    integrable_secondMomentZeroth_weightedSignedMonomial zCoefficient zFactors
  have h1 : Integrable (fun phase => secondMomentFirst (z phase) (w phase))
      (finitePhaseHaarLaw d) :=
    integrable_secondMomentFirst_weightedSignedMonomial
      zCoefficient wCoefficient zFactors wFactors
  have h2 : Integrable (fun phase => twoStepSecondCoefficient
      (z phase) (w phase) (u phase)) (finitePhaseHaarLaw d) := by
    unfold twoStepSecondCoefficient
    exact (integrable_secondMomentZeroth_weightedSignedMonomial
      wCoefficient wFactors).add
        (integrable_secondMomentFirst_weightedSignedMonomial
          zCoefficient uCoefficient zFactors uFactors)
  have h3 : Integrable (fun phase => twoStepThirdCoefficient (w phase) (u phase))
      (finitePhaseHaarLaw d) := by
    exact integrable_secondMomentFirst_weightedSignedMonomial
      wCoefficient uCoefficient wFactors uFactors
  have h4 : Integrable (fun phase => twoStepFourthCoefficient (u phase))
      (finitePhaseHaarLaw d) := by
    exact integrable_secondMomentZeroth_weightedSignedMonomial
      uCoefficient uFactors
  calc
    (∫ phase : UnitAddTorus d,
      Complex.normSq (phaseTwoStepPerturbedAmplitude epsilon
        zCoefficient wCoefficient uCoefficient
        zFactors wFactors uFactors phase)
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
      exact Filter.Eventually.of_forall fun phase => by
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
    _ = finitePhaseTwoStepMomentPolynomial epsilon
        zCoefficient wCoefficient uCoefficient
        zFactors wFactors uFactors := by
      unfold finitePhaseTwoStepMomentPolynomial twoStepThirdCoefficient
        twoStepFourthCoefficient
      dsimp [z, w, u]
      rw [integral_secondMomentZeroth_weightedSignedMonomial,
        integral_secondMomentFirst_weightedSignedMonomial,
        integral_twoStepSecondCoefficient_weightedSignedMonomial,
        integral_secondMomentFirst_weightedSignedMonomial,
        integral_secondMomentSecond_weightedSignedMonomial]

/-- Direct transfer of the finite phase identity to an actual ensemble's
phase block.  All three complex coefficients remain deterministic; dependence
on masses would require a separate conditional-expectation argument. -/
theorem ensemble_integral_normSq_phaseTwoStepPerturbedAmplitude
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (epsilon : Real) (zCoefficient wCoefficient uCoefficient : Complex)
    (zFactors wFactors uFactors : List (SignedMode (Lattice.Site N))) :
    (∫ omega, Complex.normSq
      (phaseTwoStepPerturbedAmplitude epsilon
        zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
        (ensemble.restrictPhase omega)) ∂ensemble.probability) =
      finitePhaseTwoStepMomentPolynomial epsilon
        zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors := by
  calc
    (∫ omega, Complex.normSq
      (phaseTwoStepPerturbedAmplitude epsilon
        zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors
        (ensemble.restrictPhase omega)) ∂ensemble.probability) =
        ∫ phase, Complex.normSq
          (phaseTwoStepPerturbedAmplitude epsilon
            zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors phase)
          ∂finitePhaseHaarLaw (Lattice.Site N) := by
      simpa [Function.comp_def] using
        (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble
          (N := N)).integral_comp
            (Complex.continuous_normSq.comp
              (phaseTwoStepPerturbedAmplitude_continuous epsilon
                zCoefficient wCoefficient uCoefficient
                zFactors wFactors uFactors)).aestronglyMeasurable
    _ = _ := integral_normSq_phaseTwoStepPerturbedAmplitude
      epsilon zCoefficient wCoefficient uCoefficient zFactors wFactors uFactors

end

end ArchonPhysics.FiniteSecondOrderPhaseExpansion
