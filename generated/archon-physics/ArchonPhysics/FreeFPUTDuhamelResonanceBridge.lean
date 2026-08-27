import ArchonPhysics.FreeFPUTMismatchPhaseExpansion
import ArchonPhysics.FiniteHaarOscillatorySecondMoment
import ArchonPhysics.FiniteOscillatoryResonanceSplit

/-!
# Free FPUT Duhamel, Haar, and resonance bridge

The freely evaluated quadratic FPUT source has three exact finite-volume
descriptions.  Its first interaction-picture Picard correction is a finite
Haar-character sum with oscillatory mismatch coefficients; its Haar squared
norm is therefore the exact same-charge pair sum; and, after fixing the
initial phases, it is a finite oscillatory sum admitting an exact resonant /
nonresonant split and an inverse-mismatch estimate.

This module only connects those three already proved descriptions.  The
correction below is the first Picard term evaluated along the free harmonic
orbit.  It is not the Duhamel term of the true nonlinear trajectory, and no
random-phase propagation, thermodynamic limit, collision kernel, or
thermalization conclusion is asserted.
-/

namespace ArchonPhysics.FreeFPUTDuhamelResonanceBridge

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteOscillatoryResonanceSplit
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The quadratic interaction-picture first Picard correction evaluated on
the free harmonic orbit. -/
def freeQuadraticInteractionPictureCorrection
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  ∫ s in (0 : Real)..time,
    freeQuadraticPicardIntegrand
      (coupling * PhaseRenormalization.phaseFactor (frequency observed * s))
      m observed radius frequency s phase

/-- The deterministic coefficient of one signed quadratic free-Picard term. -/
def freeQuadraticDuhamelCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N) : Complex :=
  coupling * quadraticPhaseCoefficient m observed radius term

/-- At a fixed initial phase, absorb its character into the deterministic
coefficient of the corresponding finite oscillatory sum. -/
def phasedFreeQuadraticDuhamelCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (term : QuadraticPhaseTerm N) : Complex :=
  freeQuadraticDuhamelCoefficient coupling m observed radius term *
    mFourier (quadraticPhaseCharge term) phase

/-- The free quadratic interaction-picture correction is literally the
finite Haar oscillatory sum with the FPUT coefficient, charge, and exact
frequency mismatch. -/
theorem freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticInteractionPictureCorrection
        coupling m observed radius frequency time phase =
      finiteHaarOscillatorySum
        (freeQuadraticDuhamelCoefficient coupling m observed radius)
        quadraticPhaseCharge
        (quadraticPhaseMismatch frequency observed) time phase := by
  rw [freeQuadraticInteractionPictureCorrection,
    intervalIntegral_freeQuadraticPicardIntegrand_eq_mismatchSum]
  unfold finiteHaarOscillatorySum oscillatoryCoefficient
    finitePhaseCorrection freeQuadraticDuhamelCoefficient
  apply Finset.sum_congr rfl
  intro term hterm
  ring

/-- Exact Haar squared norm of the free first-Picard correction.  Every
ordered pair with equal phase charge survives, including distinct terms
having the same charge. -/
theorem integral_normSq_freeQuadraticInteractionPictureCorrection_eq_equalChargePairSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      (Complex.normSq
        (freeQuadraticInteractionPictureCorrection
          coupling m observed radius frequency time phase) : Complex)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = quadraticPhaseCharge right then
          oscillatoryCoefficient
              (freeQuadraticDuhamelCoefficient coupling m observed radius)
              (quadraticPhaseMismatch frequency observed) time left *
            starRingEnd Complex
              (oscillatoryCoefficient
                (freeQuadraticDuhamelCoefficient coupling m observed radius)
                (quadraticPhaseMismatch frequency observed) time right)
        else 0 := by
  simpa only
      [freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum]
    using
      (integral_normSq_finiteHaarOscillatorySum_eq_equalChargePairSum
        (freeQuadraticDuhamelCoefficient coupling m observed radius)
        (quadraticPhaseCharge :
          QuadraticPhaseTerm N → Lattice.Site N → Int)
        (quadraticPhaseMismatch frequency observed) time)

/-- For fixed initial phases, the same correction is exactly an
`oscillatorySum` over all signed quadratic terms. -/
theorem freeQuadraticInteractionPictureCorrection_eq_oscillatorySum_univ
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticInteractionPictureCorrection
        coupling m observed radius frequency time phase =
      oscillatorySum Finset.univ
        (phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase)
        (quadraticPhaseMismatch frequency observed) time := by
  rw [freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum]
  unfold finiteHaarOscillatorySum oscillatoryCoefficient
    finitePhaseCorrection oscillatorySum
    phasedFreeQuadraticDuhamelCoefficient
  apply Finset.sum_congr rfl
  intro term hterm
  ring

/-- Exact fixed-phase split: zero mismatch terms retain their secular time
factor, and all remaining terms form the nonresonant correction. -/
theorem freeQuadraticInteractionPictureCorrection_eq_resonantTime_add_nonresonant
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticInteractionPictureCorrection
        coupling m observed radius frequency time phase =
      (∑ term ∈ resonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
        phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase term) * time +
        nonresonantOscillatorySum Finset.univ
          (phasedFreeQuadraticDuhamelCoefficient
            coupling m observed radius phase)
          (quadraticPhaseMismatch frequency observed) time := by
  rw [freeQuadraticInteractionPictureCorrection_eq_oscillatorySum_univ]
  exact oscillatorySum_eq_resonant_time_add_nonresonant
    Finset.univ
    (phasedFreeQuadraticDuhamelCoefficient
      coupling m observed radius phase)
    (quadraticPhaseMismatch frequency observed) time

/-- The fixed-phase nonresonant sector has the finite inverse-mismatch bound,
uniformly in time.  No lattice-size-uniform lower bound on the mismatches is
claimed. -/
theorem norm_nonresonantFreeQuadraticInteractionPictureCorrection_le
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    ‖nonresonantOscillatorySum Finset.univ
        (phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase)
        (quadraticPhaseMismatch frequency observed) time‖ ≤
      2 * ∑ term ∈ nonresonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
        ‖phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase term‖ /
          |quadraticPhaseMismatch frequency observed term| := by
  exact norm_nonresonantOscillatorySum_le Finset.univ
    (phasedFreeQuadraticDuhamelCoefficient
      coupling m observed radius phase)
    (quadraticPhaseMismatch frequency observed) time

/-- Every multivariate phase character has pointwise unit norm. -/
theorem norm_mFourier_apply_eq_one
    {d : Type*} [Fintype d] (charge : d → Int)
    (phase : UnitAddTorus d) :
    ‖mFourier charge phase‖ = 1 := by
  unfold mFourier
  simp only [ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

/-- Phase-independent form of the inverse-mismatch estimate.  In particular,
the perturbative coupling is exposed as a single prefactor. -/
theorem norm_nonresonantFreeQuadraticInteractionPictureCorrection_le_coupling
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    ‖nonresonantOscillatorySum Finset.univ
        (phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase)
        (quadraticPhaseMismatch frequency observed) time‖ ≤
      2 * ‖coupling‖ *
        ∑ term ∈ nonresonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
          ‖quadraticPhaseCoefficient m observed radius term‖ /
            |quadraticPhaseMismatch frequency observed term| := by
  calc
    ‖nonresonantOscillatorySum Finset.univ
        (phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase)
        (quadraticPhaseMismatch frequency observed) time‖ ≤
      2 * ∑ term ∈ nonresonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
        ‖phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase term‖ /
          |quadraticPhaseMismatch frequency observed term| :=
      norm_nonresonantFreeQuadraticInteractionPictureCorrection_le
        coupling m observed radius frequency time phase
    _ = 2 * ‖coupling‖ *
        ∑ term ∈ nonresonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
          ‖quadraticPhaseCoefficient m observed radius term‖ /
            |quadraticPhaseMismatch frequency observed term| := by
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro term hterm
      rw [phasedFreeQuadraticDuhamelCoefficient,
        freeQuadraticDuhamelCoefficient, norm_mul, norm_mul,
        norm_mFourier_apply_eq_one]
      ring

end

end ArchonPhysics.FreeFPUTDuhamelResonanceBridge
