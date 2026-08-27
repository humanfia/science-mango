import ArchonPhysics.ResonantThreeWaveKineticL1Stability

/-!
# Continuum L1 continuity of the resonant three-wave collision operator

This module completes the variation argument behind the pointwise flux bounds
in `ResonantThreeWaveKineticL1Stability`.  The canonical Radon--Nikodym
collision vector is only an `L1` function, so all conclusions remain in the
honest `L1` topology of the three-leg reference measure.

Two quantitative estimates are obtained for bounded measurable actions in a
common radius-`R` ball:

* an intrinsic `L1 -> L1` estimate with constant `6 * R`;
* the uniform-distance corollary with explicit collision-mass constant
  `18 * R * epsilon * collisionMass`.

No essential-boundedness claim about the RN derivative is made.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticL1Continuity

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticL1Stability
open scoped MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Transporting one common signed flux through the parent and two child
legs enlarges its total variation by at most a factor of three. -/
theorem signedCollisionDifferenceMeasure_variation_le
    (collision : ResonantThreeWaveMeasure Mode)
    (action₁ action₂ : Mode -> Real) :
    (signedCollisionDifferenceMeasure collision action₁ action₂).variation
        Set.univ <=
      3 *
        (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation
          Set.univ := by
  let flux := fluxDifferenceSignedTriadMeasure collision action₁ action₂
  let leg₀ := legFluxDifferenceSignedMeasure collision action₁ action₂ 0
  let leg₁ := legFluxDifferenceSignedMeasure collision action₁ action₂ 1
  let leg₂ := legFluxDifferenceSignedMeasure collision action₁ action₂ 2
  have hleg (leg : Fin 3) :
      (legFluxDifferenceSignedMeasure collision action₁ action₂ leg).variation
          Set.univ <= flux.variation Set.univ := by
    calc
      _ <= (flux.variation.map (triadLeg leg)) Set.univ :=
        VectorMeasure.variation_map_le Set.univ
      _ = flux.variation Set.univ := by
        rw [Measure.map_apply (measurable_triadLeg leg) MeasurableSet.univ]
        simp
  have h₀₁ : (leg₀ - leg₁).variation <= leg₀.variation + leg₁.variation :=
    VectorMeasure.variation_sub_le
  have h₀₁₂ : ((leg₀ - leg₁) - leg₂).variation <=
      (leg₀ - leg₁).variation + leg₂.variation :=
    VectorMeasure.variation_sub_le
  have htotal : ((leg₀ - leg₁) - leg₂).variation <=
      (leg₀.variation + leg₁.variation) + leg₂.variation :=
    h₀₁₂.trans (add_le_add h₀₁ le_rfl)
  change ((leg₀ - leg₁) - leg₂).variation Set.univ <= _
  calc
    _ <= ((leg₀.variation + leg₁.variation) + leg₂.variation) Set.univ :=
      htotal Set.univ
    _ = leg₀.variation Set.univ + leg₁.variation Set.univ +
        leg₂.variation Set.univ := by
      rw [Measure.add_apply, Measure.add_apply]
    _ <= flux.variation Set.univ + flux.variation Set.univ +
        flux.variation Set.univ := by
      dsimp only [leg₀, leg₁, leg₂]
      gcongr <;> apply hleg
    _ = 3 * flux.variation Set.univ := by ring

/-- The common-density collision difference is absolutely continuous with
respect to the same canonical three-leg reference measure. -/
theorem signedCollisionDifferenceMeasure_absolutelyContinuous
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    signedCollisionDifferenceMeasure collision action₁ action₂ ≪ᵥ
      (collisionReferenceMeasure collision).toENNRealVectorMeasure := by
  rw [signedCollisionDifferenceMeasure_eq_sub collision haction₁ haction₂]
  exact (signedCollisionMeasure_absolutelyContinuous collision action₁).sub
    (signedCollisionMeasure_absolutelyContinuous collision action₂)

/-- Subtracting collision vectors agrees almost everywhere with taking the
RN derivative of the common-density signed collision difference. -/
theorem collisionVector_sub_ae_eq_rnDeriv_difference
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    (fun mode => collisionVector collision action₁ mode -
      collisionVector collision action₂ mode) =ᵐ[
        collisionReferenceMeasure collision]
      (signedCollisionDifferenceMeasure collision action₁ action₂).rnDeriv
        (collisionReferenceMeasure collision) := by
  rw [signedCollisionDifferenceMeasure_eq_sub collision haction₁ haction₂]
  filter_upwards [SignedMeasure.rnDeriv_sub
    (signedCollisionMeasure collision action₁)
    (signedCollisionMeasure collision action₂)
    (collisionReferenceMeasure collision)] with mode hmode
  simpa only [collisionVector, Pi.sub_apply] using hmode.symm

/-- For an integrable scalar density, the total variation of its signed
density measure on the whole space is exactly its ordinary `L1` norm. -/
theorem variation_withDensity_real_univ_eq_integral_norm
    (reference : Measure Mode) {density : Mode -> Real}
    (hdensity : Integrable density reference) :
    (reference.withDensityᵥ density).variation.real Set.univ =
      ∫ mode, ‖density mode‖ ∂reference := by
  rw [Measure.variation_withDensityᵥ hdensity]
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using
    (integral_norm_eq_lintegral_enorm hdensity.aestronglyMeasurable).symm

/-- Exact identification of the `L1` distance between two collision vectors
with the variation of their signed collision-measure difference. -/
theorem integral_norm_collisionVector_sub_eq_variation_real
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    (∫ mode, ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖
      ∂collisionReferenceMeasure collision) =
      (signedCollisionDifferenceMeasure collision action₁ action₂).variation.real
        Set.univ := by
  let reference := collisionReferenceMeasure collision
  let difference := signedCollisionDifferenceMeasure collision action₁ action₂
  have hae := collisionVector_sub_ae_eq_rnDeriv_difference
    collision haction₁ haction₂
  have hrn : Integrable (difference.rnDeriv reference) reference :=
    SignedMeasure.integrable_rnDeriv difference reference
  calc
    _ = ∫ mode, ‖difference.rnDeriv reference mode‖ ∂reference := by
      apply integral_congr_ae
      filter_upwards [hae] with mode hmode
      rw [hmode]
    _ = (reference.withDensityᵥ (difference.rnDeriv reference)).variation.real
        Set.univ :=
      (variation_withDensity_real_univ_eq_integral_norm reference hrn).symm
    _ = difference.variation.real Set.univ := by
      rw [SignedMeasure.withDensityᵥ_rnDeriv_eq difference reference
        (signedCollisionDifferenceMeasure_absolutelyContinuous
          collision haction₁ haction₂)]

/-- Total variation of the common triad flux-difference density is exactly
the triad-space `L1` norm of that density. -/
theorem fluxDifference_variation_real_eq_integral_norm
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation.real
        Set.univ =
      ∫ (triad : Fin 3 -> Mode),
        ‖triadFlux action₁ triad - triadFlux action₂ triad‖
        ∂collision.collisionMeasure := by
  have hint := integrable_triadFlux_sub collision haction₁ haction₂
  rw [fluxDifferenceSignedTriadMeasure,
    Measure.variation_withDensityᵥ hint]
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ, Pi.sub_apply] using
    (integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable).symm

/-- Pointwise action distance used by the intrinsic `L1` estimate. -/
def actionDistance (action₁ action₂ : Mode -> Real) (mode : Mode) : Real :=
  norm (action₁ mode - action₂ mode)

theorem measurable_actionDistance {action₁ action₂ : Mode -> Real}
    (haction₁ : Measurable action₁) (haction₂ : Measurable action₂) :
    Measurable (actionDistance action₁ action₂) := by
  exact (haction₁.sub haction₂).norm

omit [MeasurableSpace Mode] in
/-- Two actions in a common radius ball differ pointwise by at most twice
that radius. -/
theorem actionDistance_le_two_mul_radius
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (mode : Mode) :
    actionDistance action₁ action₂ mode <= 2 * radius := by
  calc
    _ <= norm (action₁ mode) + norm (action₂ mode) := norm_sub_le _ _
    _ <= radius + radius := add_le_add (haction₁ mode) (haction₂ mode)
    _ = 2 * radius := by ring

/-- Bounded measurable actions have finite `L1` distance in the finite
canonical reference measure. -/
theorem integrable_actionDistance_reference
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius) :
    Integrable (actionDistance action₁ action₂)
      (collisionReferenceMeasure collision) := by
  apply Integrable.of_bound
    (measurable_actionDistance haction₁_measurable
      haction₂_measurable).aestronglyMeasurable
    (2 * radius)
  exact Filter.Eventually.of_forall (fun mode => by
    simpa only [actionDistance, norm_norm] using
      actionDistance_le_two_mul_radius haction₁ haction₂ mode)

/-- The action distance pulled back along one triad leg is integrable against
the finite collision measure. -/
theorem integrable_actionDistance_triadLeg
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (leg : Fin 3) :
    Integrable (fun triad : Fin 3 -> Mode =>
      actionDistance action₁ action₂ (triad leg))
      collision.collisionMeasure := by
  apply Integrable.of_bound
    ((measurable_actionDistance haction₁_measurable haction₂_measurable).comp
      (measurable_triadLeg leg)).aestronglyMeasurable
    (2 * radius)
  exact Filter.Eventually.of_forall (fun triad : Fin 3 -> Mode => by
    simpa only [Function.comp_apply, triadLeg, actionDistance, norm_norm] using
      actionDistance_le_two_mul_radius haction₁ haction₂ (triad leg))

/-- Integrating the three pulled-back leg distances is exactly integration
against the sum of the three leg marginals. -/
theorem integral_actionDistance_reference_eq_triadLegSum
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius) :
    (∫ mode, actionDistance action₁ action₂ mode
      ∂collisionReferenceMeasure collision) =
      ∫ (triad : Fin 3 -> Mode),
        actionDistance action₁ action₂ (triad 0) +
          actionDistance action₁ action₂ (triad 1) +
          actionDistance action₁ action₂ (triad 2)
        ∂collision.collisionMeasure := by
  let distance := actionDistance action₁ action₂
  have hdistance_measurable : Measurable distance :=
    measurable_actionDistance haction₁_measurable haction₂_measurable
  have hreference : Integrable distance (collisionReferenceMeasure collision) :=
    integrable_actionDistance_reference collision haction₁_measurable
      haction₂_measurable haction₁ haction₂
  have hleg (leg : Fin 3) : Integrable distance (legMarginal collision leg) :=
    hreference.mono_measure (legMarginal_le_collisionReferenceMeasure collision leg)
  have hcomp (leg : Fin 3) : Integrable
      (fun triad : Fin 3 -> Mode => distance (triad leg))
      collision.collisionMeasure := by
    simpa only [distance] using integrable_actionDistance_triadLeg
      collision haction₁_measurable haction₂_measurable haction₁ haction₂ leg
  have hmap (leg : Fin 3) :
      (∫ mode, distance mode ∂legMarginal collision leg) =
        ∫ (triad : Fin 3 -> Mode), distance (triad leg)
          ∂collision.collisionMeasure := by
    unfold legMarginal
    exact integral_map (measurable_triadLeg leg).aemeasurable
      hdistance_measurable.aestronglyMeasurable
  change (∫ mode, distance mode ∂collisionReferenceMeasure collision) =
    ∫ (triad : Fin 3 -> Mode),
      distance (triad 0) + distance (triad 1) + distance (triad 2)
      ∂collision.collisionMeasure
  rw [collisionReferenceMeasure,
    integral_add_measure ((hleg 0).add_measure (hleg 1)) (hleg 2),
    integral_add_measure (hleg 0) (hleg 1), hmap 0, hmap 1, hmap 2]
  have hadd₀₁ :
      (∫ (triad : Fin 3 -> Mode), distance (triad 0) + distance (triad 1)
        ∂collision.collisionMeasure) =
        (∫ (triad : Fin 3 -> Mode), distance (triad 0)
          ∂collision.collisionMeasure) +
          ∫ (triad : Fin 3 -> Mode), distance (triad 1)
            ∂collision.collisionMeasure := by
    simpa only [Pi.add_apply] using integral_add (hcomp 0) (hcomp 1)
  have hadd₀₁₂ :
      (∫ (triad : Fin 3 -> Mode),
          (distance (triad 0) + distance (triad 1)) + distance (triad 2)
        ∂collision.collisionMeasure) =
        (∫ (triad : Fin 3 -> Mode), distance (triad 0) + distance (triad 1)
          ∂collision.collisionMeasure) +
          ∫ (triad : Fin 3 -> Mode), distance (triad 2)
            ∂collision.collisionMeasure := by
    simpa only [Pi.add_apply] using
      integral_add ((hcomp 0).add (hcomp 1)) (hcomp 2)
  calc
    _ = (∫ (triad : Fin 3 -> Mode),
          distance (triad 0) + distance (triad 1)
          ∂collision.collisionMeasure) +
        ∫ (triad : Fin 3 -> Mode), distance (triad 2)
          ∂collision.collisionMeasure := by
      rw [hadd₀₁]
    _ = _ := hadd₀₁₂.symm

end

end ArchonPhysics.ResonantThreeWaveKineticL1Continuity
