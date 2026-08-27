import ArchonPhysics.ResonantThreeWaveKineticEntropy
import ArchonPhysics.ResonantThreeWaveKineticLInfinityNonnegativeLocalFlow
import Mathlib.MeasureTheory.Function.Holder

/-!
# Bounded collision invariants on canonical L-infinity

A bounded measurable mode test which is additive on collision triads defines
a continuous linear functional on canonical `L-infinity`.  This file builds
that functional from the genuine `L1`--`L∞` pairing and proves that it
annihilates the genuine, unclipped RN collision field.  Consequently it is
constant along every integral curve.

This is not a smoothing or continuation hypothesis.  The only structural
input is the pointwise collision-invariant identity on the supplied triad
measure.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityCollisionInvariant

open MeasureTheory Set
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A bounded measurable additive test on the actual collision triads. -/
structure BoundedCollisionInvariant
    (collision : ResonantThreeWaveMeasure Mode) (test : Mode → Real) : Prop where
  boundedMeasurable : IsBoundedMeasurable test
  balance_ae :
    ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 → Mode)),
      test (triad 0) = test (triad 1) + test (triad 2)

/-- An additive bounded test has zero weak collision slope for every action. -/
theorem BoundedCollisionInvariant.weakCollisionSlope_eq_zero
    {collision : ResonantThreeWaveMeasure Mode} {test : Mode → Real}
    (hinvariant : BoundedCollisionInvariant collision test)
    (action : Mode → Real) :
    weakCollisionSlope collision test action = 0 := by
  unfold weakCollisionSlope
  apply integral_eq_zero_of_ae
  filter_upwards [hinvariant.balance_ae] with triad hbalance
  have hzero : triadWeakObservableIntegrand test action triad = (0 : Real) := by
    unfold triadWeakObservableIntegrand
    rw [hbalance]
    ring
  simpa only [Pi.zero_apply] using hzero

/-- A bounded invariant belongs to `L1` for the finite canonical reference
measure. -/
theorem BoundedCollisionInvariant.memLp_one
    {collision : ResonantThreeWaveMeasure Mode} {test : Mode → Real}
    (hinvariant : BoundedCollisionInvariant collision test) :
    MemLp test 1 (collisionReferenceMeasure collision) := by
  rw [memLp_one_iff_integrable]
  obtain ⟨bound, hbound⟩ :=
    hinvariant.boundedMeasurable.exists_norm_bound
  exact Integrable.of_bound
    hinvariant.boundedMeasurable.measurable.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hbound)

/-- The `L1` class of a bounded collision invariant. -/
def BoundedCollisionInvariant.toL1
    {collision : ResonantThreeWaveMeasure Mode} {test : Mode → Real}
    (hinvariant : BoundedCollisionInvariant collision test) :
    Lp Real 1 (collisionReferenceMeasure collision) :=
  hinvariant.memLp_one.toLp test

/-- Continuous moment functional induced by a bounded collision invariant. -/
def momentCLM
    (collision : ResonantThreeWaveMeasure Mode) (test : Mode → Real)
    (hinvariant : BoundedCollisionInvariant collision test) :
    CanonicalLInfinity collision →L[Real] Real :=
  (ContinuousLinearMap.mul Real Real).lpPairing
    (collisionReferenceMeasure collision) 1 ∞ hinvariant.toL1

/-- The quotient-level moment is the ordinary integral of the chosen bounded
representative against the `L∞` class. -/
theorem momentCLM_apply
    (collision : ResonantThreeWaveMeasure Mode) (test : Mode → Real)
    (hinvariant : BoundedCollisionInvariant collision test)
    (action : CanonicalLInfinity collision) :
    momentCLM collision test hinvariant action =
      ∫ mode, test mode * action mode ∂collisionReferenceMeasure collision := by
  rw [momentCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hinvariant.memLp_one] with mode hmode
  simp only [ContinuousLinearMap.mul_apply']
  simpa only [BoundedCollisionInvariant.toL1] using
    congrArg (fun value : Real ↦ value * action mode) hmode

/-- The genuine unclipped RN collision map is annihilated by every bounded
collision invariant. -/
theorem momentCLM_collisionMap_eq_zero
    (collision : ResonantThreeWaveMeasure Mode) (test : Mode → Real)
    (hinvariant : BoundedCollisionInvariant collision test)
    (action : CanonicalLInfinity collision) :
    momentCLM collision test hinvariant (collisionMap collision action) = 0 := by
  rw [momentCLM_apply]
  calc
    (∫ mode, test mode * collisionMap collision action mode
        ∂collisionReferenceMeasure collision) =
        ∫ mode, test mode * collisionVector collision
            (linfinityRepresentative collision action) mode
          ∂collisionReferenceMeasure collision := by
      apply integral_congr_ae
      filter_upwards [coeFn_collisionMap_ae_eq collision action] with mode hmode
      rw [hmode]
    _ = weakCollisionSlope collision test
        (linfinityRepresentative collision action) := by
      apply integral_test_mul_collisionVector_eq_weakCollisionSlope
      · exact hinvariant.boundedMeasurable
      · exact ⟨measurable_linfinityRepresentative collision action,
          ⟨‖action‖, norm_linfinityRepresentative_le collision action⟩⟩
    _ = 0 := hinvariant.weakCollisionSlope_eq_zero _

/-- The coupling-scaled genuine RN vector field has zero invariant moment. -/
theorem momentCLM_rnCollisionVectorField_eq_zero
    (collision : ResonantThreeWaveMeasure Mode) (test : Mode → Real)
    (hinvariant : BoundedCollisionInvariant collision test)
    (g : Real) (action : CanonicalLInfinity collision) :
    momentCLM collision test hinvariant
      (rnCollisionVectorField collision g action) = 0 := by
  rw [rnCollisionVectorField, map_smul,
    momentCLM_collisionMap_eq_zero, smul_zero]

/-- The invariant moment has derivative zero along an unclipped integral
curve, on the same time set as the curve. -/
theorem hasDerivWithinAt_momentCLM_eq_zero
    (collision : ResonantThreeWaveMeasure Mode) (test : Mode → Real)
    (hinvariant : BoundedCollisionInvariant collision test)
    (g : Real) {curve : Real → CanonicalLInfinity collision}
    {s : Set Real} {t : Real}
    (hcurve : IsIntegralCurveOn curve
      (fun _ ↦ rnCollisionVectorField collision g) s)
    (ht : t ∈ s) :
    HasDerivWithinAt
      (fun u ↦ momentCLM collision test hinvariant (curve u)) 0 s t := by
  have hcomp :=
    (momentCLM collision test hinvariant).hasFDerivAt.comp_hasFDerivWithinAt
      t (hcurve t ht).hasFDerivWithinAt
  have hzero := momentCLM_rnCollisionVectorField_eq_zero
    collision test hinvariant g (curve t)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, hzero] using
      hcomp.hasDerivWithinAt

/-- A bounded collision-invariant moment is exactly constant on every convex
time domain of an unclipped integral curve. -/
theorem momentCLM_eq_of_mem
    (collision : ResonantThreeWaveMeasure Mode) (test : Mode → Real)
    (hinvariant : BoundedCollisionInvariant collision test)
    (g : Real) {curve : Real → CanonicalLInfinity collision}
    {s : Set Real} (hs : Convex Real s)
    (hcurve : IsIntegralCurveOn curve
      (fun _ ↦ rnCollisionVectorField collision g) s)
    {t₁ t₂ : Real} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) :
    momentCLM collision test hinvariant (curve t₁) =
      momentCLM collision test hinvariant (curve t₂) := by
  let moment : Real → Real :=
    fun t ↦ momentCLM collision test hinvariant (curve t)
  have hnorm : ‖moment t₂ - moment t₁‖ ≤ (0 : Real) := by
    simpa using
      (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := moment) (f' := fun _ ↦ 0) (C := 0)
        (fun t ht ↦ hasDerivWithinAt_momentCLM_eq_zero
          collision test hinvariant g hcurve ht)
        (fun _ _ ↦ by simp) hs ht₁ ht₂)
  have heq : moment t₂ = moment t₁ := by
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  exact heq.symm

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityCollisionInvariant
