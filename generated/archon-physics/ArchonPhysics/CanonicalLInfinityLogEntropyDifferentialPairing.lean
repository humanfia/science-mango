import ArchonPhysics.ResonantThreeWaveKineticLInfinityCollisionInvariant
import ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity

/-!
# Canonical logarithmic-entropy differential as an L1--L-infinity pairing

Every bounded measurable test defines an `L1` class for the finite canonical
collision reference measure, hence a continuous linear functional on
canonical `L-infinity`.  Specializing the test to the inverse of the
positive-floor representative gives the linear pairing that will serve as
the differential of logarithmic entropy.

For an action satisfying the supplied essential lower bound, applying this
functional to the genuine quotient collision map is exactly the canonical
logarithmic entropy production.  No time derivative or chain rule is assumed
or proved in this module.
-/

namespace ArchonPhysics.CanonicalLInfinityLogEntropyDifferentialPairing

open Filter MeasureTheory
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A bounded measurable scalar test belongs to `L1` because the canonical
collision reference measure is finite. -/
theorem boundedMeasurableTest_memLp_one
    (collision : ResonantThreeWaveMeasure Mode)
    {test : Mode → Real} (htest : IsBoundedMeasurable test) :
    MemLp test 1 (collisionReferenceMeasure collision) := by
  rw [memLp_one_iff_integrable]
  obtain ⟨bound, hbound⟩ := htest.exists_norm_bound
  exact Integrable.of_bound htest.measurable.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hbound)

/-- The `L1` class of an arbitrary bounded measurable test. -/
def boundedMeasurableTestToL1
    (collision : ResonantThreeWaveMeasure Mode)
    (test : Mode → Real) (htest : IsBoundedMeasurable test) :
    Lp Real 1 (collisionReferenceMeasure collision) :=
  (boundedMeasurableTest_memLp_one collision htest).toLp test

/-- Genuine `L1`--`L-infinity` pairing induced by a bounded measurable test. -/
def boundedTestPairingCLM
    (collision : ResonantThreeWaveMeasure Mode)
    (test : Mode → Real) (htest : IsBoundedMeasurable test) :
    CanonicalLInfinity collision →L[Real] Real :=
  (ContinuousLinearMap.mul Real Real).lpPairing
    (collisionReferenceMeasure collision) 1 ∞
    (boundedMeasurableTestToL1 collision test htest)

/-- The abstract quotient pairing is the ordinary integral of the supplied
test against the `L-infinity` class. -/
theorem boundedTestPairingCLM_apply
    (collision : ResonantThreeWaveMeasure Mode)
    (test : Mode → Real) (htest : IsBoundedMeasurable test)
    (direction : CanonicalLInfinity collision) :
    boundedTestPairingCLM collision test htest direction =
      ∫ mode, test mode * direction mode
        ∂collisionReferenceMeasure collision := by
  rw [boundedTestPairingCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards
    [MemLp.coeFn_toLp (boundedMeasurableTest_memLp_one collision htest)]
      with mode hmode
  simp only [ContinuousLinearMap.mul_apply']
  simpa only [boundedMeasurableTestToL1] using
    congrArg (fun value : Real ↦ value * direction mode) hmode

/-- The inverse positive-floor representative used as the logarithmic
entropy differential test. -/
def inversePositiveFloorRepresentative
    (collision : ResonantThreeWaveMeasure Mode) (floor : Real)
    (action : CanonicalLInfinity collision) : Mode → Real :=
  fun mode ↦
    (positiveFloorRepresentative collision floor action mode)⁻¹

/-- A strictly positive floor makes the inverse representative bounded and
measurable, with no extra analytic hypothesis. -/
theorem inversePositiveFloorRepresentative_isBoundedMeasurable
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision) :
    IsBoundedMeasurable
      (inversePositiveFloorRepresentative collision floor action) := by
  exact inverseAction_isBoundedMeasurable
    (positiveFloorRepresentative_isBoundedMeasurable
      collision hfloor.le action)
    floor hfloor
    (floor_le_positiveFloorRepresentative collision floor action)

/-- Continuous linear logarithmic-entropy differential at one positive-floor
canonical action. -/
def canonicalLogEntropyDifferential
    (collision : ResonantThreeWaveMeasure Mode)
    (floor : Real) (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision) :
    CanonicalLInfinity collision →L[Real] Real :=
  boundedTestPairingCLM collision
    (inversePositiveFloorRepresentative collision floor action)
    (inversePositiveFloorRepresentative_isBoundedMeasurable
      collision hfloor action)

/-- Evaluation of the canonical logarithmic-entropy differential is exactly
the inverse-action integral pairing. -/
theorem canonicalLogEntropyDifferential_apply
    (collision : ResonantThreeWaveMeasure Mode)
    (floor : Real) (hfloor : 0 < floor)
    (action direction : CanonicalLInfinity collision) :
    canonicalLogEntropyDifferential collision floor hfloor action direction =
      ∫ mode,
        (positiveFloorRepresentative collision floor action mode)⁻¹ *
          direction mode
        ∂collisionReferenceMeasure collision := by
  exact boundedTestPairingCLM_apply collision
    (inversePositiveFloorRepresentative collision floor action)
    (inversePositiveFloorRepresentative_isBoundedMeasurable
      collision hfloor action) direction

/-- Under the essential action floor, the quotient collision map is
represented by the RN collision vector of the same positive-floor
representative used in the entropy differential. -/
theorem collisionMap_ae_eq_collisionVector_positiveFloorRepresentative
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision)
    (hactionFloor : AELowerBound collision floor action) :
    collisionMap collision action =ᵐ[collisionReferenceMeasure collision]
      collisionVector collision
        (positiveFloorRepresentative collision floor action) := by
  let representative := positiveFloorRepresentative collision floor action
  have hrepresentativeMeasurable : Measurable representative :=
    measurable_positiveFloorRepresentative collision floor action
  have hrepresentativeBound : ∀ mode,
      ‖representative mode‖ ≤ max floor ‖action‖ :=
    norm_positiveFloorRepresentative_le collision hfloor.le action
  have hmap := collisionMap_eq_toLp_of_ae_eq collision action
    hrepresentativeMeasurable hrepresentativeBound
    (positiveFloorRepresentative_ae_eq collision action hactionFloor)
  rw [hmap]
  exact MemLp.coeFn_toLp
    (collisionVector_memLp_top_of_bound collision
      hrepresentativeMeasurable hrepresentativeBound)

/-- Fundamental exact pairing identity: the canonical log-entropy
differential applied to the genuine quotient collision map is the canonical
log-entropy production. -/
theorem canonicalLogEntropyDifferential_collisionMap_eq_production
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision)
    (hactionFloor : AELowerBound collision floor action) :
    canonicalLogEntropyDifferential collision floor hfloor action
        (collisionMap collision action) =
      canonicalLogEntropyProduction collision floor action := by
  rw [canonicalLogEntropyDifferential_apply]
  let representative := positiveFloorRepresentative collision floor action
  have hmap :=
    collisionMap_ae_eq_collisionVector_positiveFloorRepresentative
      collision hfloor action hactionFloor
  calc
    (∫ mode, (representative mode)⁻¹ * collisionMap collision action mode
        ∂collisionReferenceMeasure collision) =
        ∫ mode, (representative mode)⁻¹ *
          collisionVector collision representative mode
          ∂collisionReferenceMeasure collision := by
      apply integral_congr_ae
      filter_upwards [hmap] with mode hmode
      rw [hmode]
    _ = continuumLogEntropyProduction collision representative :=
      integral_inverseAction_mul_collisionVector_eq_entropyProduction
        collision
        (positiveFloorRepresentative_isBoundedMeasurable
          collision hfloor.le action)
        floor hfloor
        (floor_le_positiveFloorRepresentative collision floor action)
    _ = canonicalLogEntropyProduction collision floor action := rfl

/-- Coupling-scaled corollary, still purely a linear-pairing identity rather
than a time-derivative statement. -/
theorem canonicalLogEntropyDifferential_rnCollisionVectorField_eq
    (collision : ResonantThreeWaveMeasure Mode)
    (g : Real) {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision)
    (hactionFloor : AELowerBound collision floor action) :
    canonicalLogEntropyDifferential collision floor hfloor action
        (rnCollisionVectorField collision g action) =
      g ^ 2 * canonicalLogEntropyProduction collision floor action := by
  rw [rnCollisionVectorField, map_smul,
    canonicalLogEntropyDifferential_collisionMap_eq_production
      collision hfloor action hactionFloor]
  rfl

end

end ArchonPhysics.CanonicalLInfinityLogEntropyDifferentialPairing
