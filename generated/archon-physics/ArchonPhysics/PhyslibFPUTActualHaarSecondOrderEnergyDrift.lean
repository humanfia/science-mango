import ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition

/-!
# Exact `O(g^2)` Picard onset inside a genuine one-block Haar energy drift

This module combines the exact matched-charge expansion of the microscopic
post-second-Picard observable with finite `l1` coefficient bounds.  The Haar
average of the `A0`/`A1` interference is exactly zero, so the displayed
Picard contribution to the energy drift begins at order `g^2`.

The actual nonlinear orbit is kept separate.  Its post-second-Picard
correction is bounded by the already proved microscopic energy-window
envelope.  That coarse correction envelope is not proved to be `O(g^2)`.
Consequently the final theorem is a one-block Haar-initialized statement with
an exact `g^2` Picard onset plus a transparent correction; it does not assert
a restart theorem, a kinetic-time estimate, or propagation of Haar phases.
-/

namespace ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.RandomPhaseMoments
open scoped ComplexConjugate Interval

noncomputable section

/- Use exactly the normalized finite-dimensional Haar probability law used by
the phase-expansion modules. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

/-! ## Finite coefficient-mass bounds -/

/-- The complete matched-charge cross sum is bounded by the product of the
two finite coefficient `l1` masses.  No injectivity of charges is assumed. -/
theorem norm_equalChargeCrossPairSum_le_absMass_mul_absMass
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    ‖equalChargeCrossPairSum leftCoefficient leftCharge
        rightCoefficient rightCharge‖ ≤
      finiteCharacterCoefficientAbsMass leftCoefficient *
        finiteCharacterCoefficientAbsMass rightCoefficient := by
  classical
  unfold equalChargeCrossPairSum finiteCharacterCoefficientAbsMass
  calc
    ‖∑ left, ∑ right,
        if leftCharge left = rightCharge right then
          leftCoefficient left * starRingEnd Complex (rightCoefficient right)
        else 0‖ ≤
        ∑ left, ‖∑ right,
          if leftCharge left = rightCharge right then
            leftCoefficient left * starRingEnd Complex (rightCoefficient right)
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ left, ∑ right,
          ‖if leftCharge left = rightCharge right then
            leftCoefficient left * starRingEnd Complex (rightCoefficient right)
          else 0‖ := by
      apply Finset.sum_le_sum
      intro left hleft
      exact norm_sum_le _ _
    _ ≤ ∑ left, ∑ right,
          ‖leftCoefficient left‖ * ‖rightCoefficient right‖ := by
      apply Finset.sum_le_sum
      intro left hleft
      apply Finset.sum_le_sum
      intro right hright
      by_cases hcharge : leftCharge left = rightCharge right
      · simp [hcharge]
      · simp only [hcharge, if_false, norm_zero]
        positivity
    _ = (∑ left, ‖leftCoefficient left‖) *
          ∑ right, ‖rightCoefficient right‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro left hleft
      rw [Finset.mul_sum]

/-- The Haar square of a finite character family is bounded by the square of
its coefficient `l1` mass, including every charge collision. -/
theorem abs_sameChargeFamilySquare_le_absMass_sq
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → Complex) (charge : J → d → Int) :
    |sameChargeFamilySquare coefficient charge| ≤
      finiteCharacterCoefficientAbsMass coefficient ^ 2 := by
  unfold sameChargeFamilySquare
  calc
    |(equalChargeCrossPairSum coefficient charge coefficient charge).re| ≤
        ‖equalChargeCrossPairSum coefficient charge coefficient charge‖ :=
      Complex.abs_re_le_norm _
    _ ≤ finiteCharacterCoefficientAbsMass coefficient *
          finiteCharacterCoefficientAbsMass coefficient :=
      norm_equalChargeCrossPairSum_le_absMass_mul_absMass
        coefficient charge coefficient charge
    _ = finiteCharacterCoefficientAbsMass coefficient ^ 2 := by ring

/-- The real interference of two finite character families is bounded by
twice the product of their coefficient `l1` masses. -/
theorem abs_equalChargeFamilyInterference_le_two_mul_absMass
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    |equalChargeFamilyInterference leftCoefficient leftCharge
        rightCoefficient rightCharge| ≤
      2 * finiteCharacterCoefficientAbsMass leftCoefficient *
        finiteCharacterCoefficientAbsMass rightCoefficient := by
  unfold equalChargeFamilyInterference
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  calc
    2 * |(equalChargeCrossPairSum leftCoefficient leftCharge
        rightCoefficient rightCharge).re| ≤
      2 * ‖equalChargeCrossPairSum leftCoefficient leftCharge
        rightCoefficient rightCharge‖ := by
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ 2 * (finiteCharacterCoefficientAbsMass leftCoefficient *
          finiteCharacterCoefficientAbsMass rightCoefficient) := by
      exact mul_le_mul_of_nonneg_left
        (norm_equalChargeCrossPairSum_le_absMass_mul_absMass
          leftCoefficient leftCharge rightCoefficient rightCharge) (by norm_num)
    _ = _ := by ring

/-- Computable coefficient-mass bound for the complete order-two Haar
coefficient `|A1|^2 + 2 Re(A0 conj A2)`. -/
theorem abs_finiteCharacterFamilySecondOrderCoefficient_le
    {d J0 J1 J2 : Type*} [Fintype d]
    [Fintype J0] [Fintype J1] [Fintype J2]
    (zCoefficient : J0 → Complex) (zCharge : J0 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int) :
    |finiteCharacterFamilySecondOrderCoefficient
        zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge| ≤
      finiteCharacterCoefficientAbsMass wCoefficient ^ 2 +
        2 * finiteCharacterCoefficientAbsMass zCoefficient *
          finiteCharacterCoefficientAbsMass uCoefficient := by
  unfold finiteCharacterFamilySecondOrderCoefficient
  exact (abs_add_le _ _).trans (add_le_add
    (abs_sameChargeFamilySquare_le_absMass_sq wCoefficient wCharge)
    (abs_equalChargeFamilyInterference_le_two_mul_absMass
      zCoefficient zCharge uCoefficient uCharge))

/-! ## Physical coefficient masses and Picard drift -/

/-- Finite absolute mass of the physical free (`A0`) phase family. -/
def physlibA0CoefficientAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  finiteCharacterCoefficientAbsMass
    (freeInitialPhaseCoefficient radius (modeFrequency m) observed)

/-- Finite absolute mass of the physical first-Picard (`A1`) family. -/
def physlibA1CoefficientAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  finiteCharacterCoefficientAbsMass
    (physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed)

/-- Finite absolute mass of the complete physical second-Picard (`A2`)
family, retaining both the iterated-quadratic and direct-cubic branches. -/
def physlibA2CoefficientAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  finiteCharacterCoefficientAbsMass
    (completeSecondPicardCoefficient m kappa beta radius observed time)

/-- Explicit finite-sum coefficient at order `g^2`: `W^2 + 2 Z U`. -/
def physlibHaarEnergyDriftC2
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  physlibA1CoefficientAbsMass m kappa radius time observed ^ 2 +
    2 * physlibA0CoefficientAbsMass m radius observed *
      physlibA2CoefficientAbsMass m kappa beta radius time observed

/-- Explicit finite-sum coefficient at order `g^3`: `2 W U`. -/
def physlibHaarEnergyDriftC3
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  2 * physlibA1CoefficientAbsMass m kappa radius time observed *
    physlibA2CoefficientAbsMass m kappa beta radius time observed

/-- Explicit finite-sum coefficient at order `g^4`: `U^2`. -/
def physlibHaarEnergyDriftC4
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : Real :=
  physlibA2CoefficientAbsMass m kappa beta radius time observed ^ 2

theorem physlibHaarEnergyDriftC2_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    0 ≤ physlibHaarEnergyDriftC2 m kappa beta radius time observed := by
  unfold physlibHaarEnergyDriftC2 physlibA0CoefficientAbsMass
    physlibA1CoefficientAbsMass physlibA2CoefficientAbsMass
    finiteCharacterCoefficientAbsMass
  positivity

theorem physlibHaarEnergyDriftC3_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    0 ≤ physlibHaarEnergyDriftC3 m kappa beta radius time observed := by
  unfold physlibHaarEnergyDriftC3 physlibA1CoefficientAbsMass
    physlibA2CoefficientAbsMass finiteCharacterCoefficientAbsMass
  positivity

theorem physlibHaarEnergyDriftC4_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    0 ≤ physlibHaarEnergyDriftC4 m kappa beta radius time observed := by
  unfold physlibHaarEnergyDriftC4
  positivity

/-- The exact matched-charge two-step Haar moment differs from its `A0`
moment by order `g^2`.  The crucial point is that this conclusion uses the
proved parity cancellation of the full order-`g` family, not a triangle bound
on the amplitude. -/
theorem abs_physlibMatchedChargeTwoStepMoment_sub_A0_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    |physlibMatchedChargeTwoStepMoment
        m kappa beta g radius time observed -
      sameChargeFamilySquare
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)| ≤
      g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius time observed +
          |g| * physlibHaarEnergyDriftC3
            m kappa beta radius time observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius time observed) := by
  let zCoefficient :=
    freeInitialPhaseCoefficient radius (modeFrequency m) observed
  let wCoefficient :=
    physlibQuadraticFirstPicardCharacterCoefficient
      m kappa radius time observed
  let uCoefficient :=
    completeSecondPicardCoefficient m kappa beta radius observed time
  let S2 := finiteCharacterFamilySecondOrderCoefficient
    zCoefficient (freeInitialPhaseCharge observed)
    wCoefficient quadraticPhaseCharge
    uCoefficient completeSecondPicardCharge
  let S3 := equalChargeFamilyInterference
    wCoefficient quadraticPhaseCharge uCoefficient completeSecondPicardCharge
  let S4 := sameChargeFamilySquare uCoefficient completeSecondPicardCharge
  have hS2 : |S2| ≤
      finiteCharacterCoefficientAbsMass wCoefficient ^ 2 +
        2 * finiteCharacterCoefficientAbsMass zCoefficient *
          finiteCharacterCoefficientAbsMass uCoefficient := by
    exact abs_finiteCharacterFamilySecondOrderCoefficient_le
      zCoefficient (freeInitialPhaseCharge observed)
      wCoefficient quadraticPhaseCharge uCoefficient completeSecondPicardCharge
  have hS3 : |S3| ≤
      2 * finiteCharacterCoefficientAbsMass wCoefficient *
        finiteCharacterCoefficientAbsMass uCoefficient := by
    exact abs_equalChargeFamilyInterference_le_two_mul_absMass
      wCoefficient quadraticPhaseCharge uCoefficient completeSecondPicardCharge
  have hS4 : |S4| ≤
      finiteCharacterCoefficientAbsMass uCoefficient ^ 2 := by
    exact abs_sameChargeFamilySquare_le_absMass_sq
      uCoefficient completeSecondPicardCharge
  have hg2 : |g ^ 2| = g ^ 2 := abs_of_nonneg (sq_nonneg g)
  have hg3 : |g ^ 3| = g ^ 2 * |g| := by
    rw [abs_pow]
    rw [show |g| ^ 3 = |g| ^ 2 * |g| by ring, sq_abs]
  have hg4 : |g ^ 4| = g ^ 4 := abs_of_nonneg (by positivity)
  rw [physlibMatchedChargeTwoStepMoment_eq_without_firstOrder]
  change |sameChargeFamilySquare zCoefficient (freeInitialPhaseCharge observed) +
      g ^ 2 * S2 + g ^ 3 * S3 + g ^ 4 * S4 -
      sameChargeFamilySquare zCoefficient (freeInitialPhaseCharge observed)| ≤ _
  rw [show sameChargeFamilySquare zCoefficient (freeInitialPhaseCharge observed) +
      g ^ 2 * S2 + g ^ 3 * S3 + g ^ 4 * S4 -
      sameChargeFamilySquare zCoefficient (freeInitialPhaseCharge observed) =
      g ^ 2 * S2 + g ^ 3 * S3 + g ^ 4 * S4 by ring]
  calc
    |g ^ 2 * S2 + g ^ 3 * S3 + g ^ 4 * S4| ≤
        |g ^ 2 * S2| + |g ^ 3 * S3| + |g ^ 4 * S4| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = g ^ 2 * |S2| + (g ^ 2 * |g|) * |S3| + g ^ 4 * |S4| := by
      rw [abs_mul, abs_mul, abs_mul, hg2, hg3, hg4]
    _ ≤ g ^ 2 *
        (finiteCharacterCoefficientAbsMass wCoefficient ^ 2 +
          2 * finiteCharacterCoefficientAbsMass zCoefficient *
            finiteCharacterCoefficientAbsMass uCoefficient) +
        (g ^ 2 * |g|) *
          (2 * finiteCharacterCoefficientAbsMass wCoefficient *
            finiteCharacterCoefficientAbsMass uCoefficient) +
        g ^ 4 * finiteCharacterCoefficientAbsMass uCoefficient ^ 2 := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hS2 (sq_nonneg g))
          (mul_le_mul_of_nonneg_left hS3
            (mul_nonneg (sq_nonneg g) (abs_nonneg g))))
        (mul_le_mul_of_nonneg_left hS4 (by positivity))
    _ = g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius time observed +
          |g| * physlibHaarEnergyDriftC3
            m kappa beta radius time observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius time observed) := by
      dsimp only [zCoefficient, wCoefficient, uCoefficient]
      unfold physlibHaarEnergyDriftC2 physlibHaarEnergyDriftC3
        physlibHaarEnergyDriftC4 physlibA0CoefficientAbsMass
        physlibA1CoefficientAbsMass physlibA2CoefficientAbsMass
      ring

/-! ## The genuine initial Haar expectation -/

/-- The canonical Haar initial modal squared norm is exactly the complete
same-charge `A0` square. -/
theorem integral_canonicalFreeInitial_normSq_eq_sameChargeFamilySquare
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      Complex.normSq
        (canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      sameChargeFamilySquare
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed) := by
  calc
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
        secondMomentSecond
          (finitePhaseCorrection
            (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
            (freeInitialPhaseCharge observed) phase)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        dsimp only
        unfold secondMomentSecond
        rw [canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
          radius (modeFrequency m) phase observed homega]
    _ = _ := integral_secondMomentSecond_finitePhaseCorrection
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (freeInitialPhaseCharge observed)

/-- Under the canonical initial-amplitude identification, the actual
interaction-picture observable at time zero has the same `A0` Haar moment. -/
theorem integral_actualPhaseModalNormSq_zero_eq_sameChargeFamilySquare
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      actualPhaseModalNormSq m observed p q 0 phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      sameChargeFamilySquare
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed) := by
  calc
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
        Complex.normSq
          (canonicalFreeComplexInitialAmplitude
            radius (modeFrequency m) phase observed)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        dsimp only
        unfold actualPhaseModalNormSq
        rw [hinitial phase, mul_zero, normSq_phaseRenormalize]
    _ = _ := integral_canonicalFreeInitial_normSq_eq_sameChargeFamilySquare
      m radius observed homega

/-! ## Actual one-block energy drift -/

/-- The norm envelope for the literal post-second-Picard coefficient on the
microscopic energy window `[0,T]`. -/
def physlibAfterSecondPicardRemainderNormEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  afterSecondPicardWindowEnvelope m kappa beta g observed
    (actualModalEnergyL1Envelope N mUpper kappa beta H) radius T * T

/-- Explicit expectation-level envelope for the interference with the exact
post-second-Picard remainder plus its square. -/
def physlibHaarEnergyCorrectionEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  2 * finiteCharacterTwoStepAbsMass g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m kappa radius T observed)
      (completeSecondPicardCoefficient m kappa beta radius observed T) *
      physlibAfterSecondPicardRemainderNormEnvelope
        m mUpper kappa beta g H radius T observed +
    physlibAfterSecondPicardRemainderNormEnvelope
      m mUpper kappa beta g H radius T observed ^ 2

/-- Abstract bounded-correction endpoint.  It already compares the genuine
microscopic expectation at the end of one block with the genuine expectation
at time zero.  The first-order Picard contribution is absent exactly. -/
theorem abs_integral_actualPhaseModalNormSq_sub_initial_le_of_correction_bound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (time C : Real)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time))
    (hbound : ∀ phase,
      |actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius time phase| ≤ C) :
    |(∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q time phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) -
      ∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q 0 phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤
      g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius time observed +
          |g| * physlibHaarEnergyDriftC3
            m kappa beta radius time observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius time observed) + C := by
  rcases
      integral_actualPhaseModalNormSq_eq_matchedCharge_add_boundedCorrection
        m kappa beta g observed p q hp hq hHamilton radius homega hinitial
          time hmeasurable hbound with ⟨hactual, hcorrection⟩
  have hinitialMoment :=
    integral_actualPhaseModalNormSq_zero_eq_sameChargeFamilySquare
      m observed p q radius homega hinitial
  have hmatched := abs_physlibMatchedChargeTwoStepMoment_sub_A0_le
    m kappa beta g radius time observed
  rw [hactual, hinitialMoment]
  calc
    |physlibMatchedChargeTwoStepMoment
          m kappa beta g radius time observed +
        (∫ phase : UnitAddTorus (Lattice.Site N),
          actualPostSecondPicardEnergyCorrection
            m kappa beta g observed q radius time phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
        sameChargeFamilySquare
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (freeInitialPhaseCharge observed)| =
      |(physlibMatchedChargeTwoStepMoment
          m kappa beta g radius time observed -
        sameChargeFamilySquare
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (freeInitialPhaseCharge observed)) +
        ∫ phase : UnitAddTorus (Lattice.Site N),
          actualPostSecondPicardEnergyCorrection
            m kappa beta g observed q radius time phase
          ∂finitePhaseHaarLaw (Lattice.Site N)| := by ring_nf
    _ ≤ |physlibMatchedChargeTwoStepMoment
          m kappa beta g radius time observed -
        sameChargeFamilySquare
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (freeInitialPhaseCharge observed)| +
        |∫ phase : UnitAddTorus (Lattice.Site N),
          actualPostSecondPicardEnergyCorrection
            m kappa beta g observed q radius time phase
          ∂finitePhaseHaarLaw (Lattice.Site N)| := abs_add_le _ _
    _ ≤ g ^ 2 *
          (physlibHaarEnergyDriftC2 m kappa beta radius time observed +
            |g| * physlibHaarEnergyDriftC3
              m kappa beta radius time observed +
            g ^ 2 * physlibHaarEnergyDriftC4
              m kappa beta radius time observed) + C :=
      add_le_add hmatched hcorrection

/-- Main physical endpoint.  For a Haar-initialized family of genuine Physlib
Hamiltonian trajectories in one energy-controlled time block, the actual
modal squared-norm drift is bounded by a finite, computable `O(g^2)` Picard
polynomial plus the explicit nonlinear correction envelope.  The current
absolute-value energy envelope for that correction contains an `O(|g| T)`
contribution and is **not** proved to be `O(g^2)`; only the matched Haar/Picard
part has the rigorous `g^2` onset here.

This is deliberately a single-block theorem.  It does not prove that the
phase law is Haar again at time `T`, so it cannot be iterated to kinetic time
without an additional restart/coupling theorem. -/
theorem abs_integral_actualPhaseModalNormSq_sub_initial_le_energyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase, ∀ time ∈ Set.Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase, ∀ time ∈ Set.Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T)) :
    |(∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q T phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) -
      ∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q 0 phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤
      g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius T observed +
          |g| * physlibHaarEnergyDriftC3 m kappa beta radius T observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius T observed) +
        physlibHaarEnergyCorrectionEnvelope
          m mUpper kappa beta g H radius T observed := by
  apply abs_integral_actualPhaseModalNormSq_sub_initial_le_of_correction_bound
    m kappa beta g observed p q hp hq hHamilton radius homega hinitial T
      (physlibHaarEnergyCorrectionEnvelope
        m mUpper kappa beta g H radius T observed) hmeasurable
  intro phase
  apply abs_actualPostSecondPicardEnergyCorrection_le
    m kappa beta g observed q radius T phase homega
  exact norm_afterSecondPicardRemainderCoefficient_le_energyWindow
    m hmUpper0 hmassUpper hbeta observed (p phase) (q phase) radius phase
      homega hT (hgauge phase) (henergy phase)

end

end ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
