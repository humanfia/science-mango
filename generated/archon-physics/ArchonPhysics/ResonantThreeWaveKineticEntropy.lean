import ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

/-!
# Entropy production of the Radon--Nikodym three-wave operator

For a bounded measurable positive action with a uniform positive floor, its
inverse is an admissible bounded test. Pairing that test with the canonical
RN collision vector recovers the integral of the exact nonnegative three-wave
entropy production. This is the continuum algebraic H-theorem for the honest
pointwise operator; no continuum flow or entropy-dissipation coercivity is
assumed or asserted.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticEntropy

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Continuum logarithmic-entropy production: the weak collision slope tested
against inverse action. -/
def continuumLogEntropyProduction
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real) : Real :=
  weakCollisionSlope collision (fun mode => (action mode)⁻¹) action

/-- A uniformly positive bounded measurable action has a bounded measurable
inverse-action test. -/
theorem inverseAction_isBoundedMeasurable
    {action : Mode -> Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : forall mode, floor <= action mode) :
    IsBoundedMeasurable (fun mode => (action mode)⁻¹) := by
  constructor
  · exact haction.measurable.inv
  · refine ⟨floor⁻¹, ?_⟩
    intro mode
    have hactionPos : 0 < action mode :=
      hfloor.trans_le (hactionFloor mode)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hactionPos)]
    exact (inv_le_inv₀ hactionPos hfloor).2 (hactionFloor mode)

/-- The RN collision vector paired with inverse action is exactly the
continuum entropy-production functional. -/
theorem integral_inverseAction_mul_collisionVector_eq_entropyProduction
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : forall mode, floor <= action mode) :
    (∫ mode, (action mode)⁻¹ * collisionVector collision action mode
      ∂collisionReferenceMeasure collision) =
      continuumLogEntropyProduction collision action := by
  exact integral_test_mul_collisionVector_eq_weakCollisionSlope
    collision
      (inverseAction_isBoundedMeasurable haction floor hfloor hactionFloor)
      haction

/-- Positive action makes the continuum logarithmic-entropy production
nonnegative triad by triad. -/
theorem continuumLogEntropyProduction_nonneg
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} (haction : forall mode, 0 < action mode) :
    0 <= continuumLogEntropyProduction collision action := by
  unfold continuumLogEntropyProduction weakCollisionSlope
    triadWeakObservableIntegrand
  apply integral_nonneg_of_ae
  exact Filter.Eventually.of_forall fun triad => by
    change (0 : Real) <= collisionFlux
      (action (triad 0)) (action (triad 1)) (action (triad 2)) *
        ((action (triad 0))⁻¹ - (action (triad 1))⁻¹ - (action (triad 2))⁻¹)
    simpa only [entropyProduction, inverseActionMismatch, one_mul] using
      (entropyProduction_nonneg (by norm_num : (0 : Real) <= 1)
        (haction (triad 0)) (haction (triad 1)) (haction (triad 2)))

/-- The ordinary mode-space RN pairing is therefore nonnegative. -/
theorem integral_inverseAction_mul_collisionVector_nonneg
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : forall mode, floor <= action mode) :
    0 <= ∫ mode, (action mode)⁻¹ * collisionVector collision action mode
      ∂collisionReferenceMeasure collision := by
  rw [integral_inverseAction_mul_collisionVector_eq_entropyProduction
    collision haction floor hfloor hactionFloor]
  exact continuumLogEntropyProduction_nonneg collision fun mode =>
    hfloor.trans_le (hactionFloor mode)

/-- If frequency is bounded, the same RN operator has exactly zero frequency
moment, by the resonance support of the collision measure. -/
theorem integral_frequency_mul_collisionVector_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (hfrequency : IsBoundedMeasurable collision.frequency)
    {action : Mode -> Real} (haction : IsBoundedMeasurable action) :
    (∫ mode, collision.frequency mode * collisionVector collision action mode
      ∂collisionReferenceMeasure collision) = 0 := by
  rw [integral_test_mul_collisionVector_eq_weakCollisionSlope
    collision hfrequency haction]
  exact weakCollisionSlope_frequency_eq_zero collision action

end

end ArchonPhysics.ResonantThreeWaveKineticEntropy
