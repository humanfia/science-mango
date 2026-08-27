import ArchonPhysics.ResonantThreeWaveKineticL1Continuity

/-!
# Quantitative L1 Lipschitz bounds for the RN three-wave collision vector

For two bounded measurable actions in a common radius-`R` ball, this module
proves the intrinsic continuum estimate

`integral |C(a) - C(b)| dnu <= 6 * R * integral |a - b| dnu`.

Here `nu` is the canonical sum of the three collision-leg marginals.  A
second theorem derives the uniform-distance estimate

`integral |C(a) - C(b)| dnu <= 18 * R * epsilon * mu(univ)`.

These are `L1` conclusions.  The RN collision vector is never asserted to be
essentially bounded.  The intrinsic estimate also proves representative
independence on the bounded measurable class, which is the quotient-level
input needed by a future continuum `L1` ODE construction.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticL1Lipschitz

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticL1Stability
open ArchonPhysics.ResonantThreeWaveKineticL1Continuity
open scoped MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The real total variation of the three-leg net difference is at most
three times the real total variation of its common triad flux density. -/
theorem signedCollisionDifference_variation_real_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    (signedCollisionDifferenceMeasure collision action₁ action₂).variation.real
        Set.univ <=
      3 *
        (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation.real
          Set.univ := by
  let _ : IsFiniteMeasure
      (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation := by
    have hflux := integrable_triadFlux_sub collision haction₁ haction₂
    rw [fluxDifferenceSignedTriadMeasure,
      Measure.variation_withDensityᵥ hflux]
    exact isFiniteMeasure_withDensity
      (hasFiniteIntegral_iff_enorm.mp hflux.2).ne
  rw [measureReal_def, measureReal_def]
  calc
    _ <= (3 *
        (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation
          Set.univ).toReal := by
      apply ENNReal.toReal_mono
      · finiteness
      · exact signedCollisionDifferenceMeasure_variation_le
          collision action₁ action₂
    _ = 3 *
        ((fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation
          Set.univ).toReal := by
      norm_num

/-- The triad-space flux `L1` difference is controlled by twice the common
action radius times the action `L1` distance in the canonical reference. -/
theorem integral_norm_triadFlux_sub_le_actionL1
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (hradius : 0 <= radius)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius) :
    (∫ (triad : Fin 3 -> Mode),
        ‖triadFlux action₁ triad - triadFlux action₂ triad‖
        ∂collision.collisionMeasure) <=
      2 * radius *
        ∫ mode, actionDistance action₁ action₂ mode
          ∂collisionReferenceMeasure collision := by
  have hbounded₁ : IsBoundedMeasurable action₁ :=
    ⟨haction₁_measurable, ⟨radius, haction₁⟩⟩
  have hbounded₂ : IsBoundedMeasurable action₂ :=
    ⟨haction₂_measurable, ⟨radius, haction₂⟩⟩
  have hflux : Integrable
      (fun triad : Fin 3 -> Mode =>
        triadFlux action₁ triad - triadFlux action₂ triad)
      collision.collisionMeasure := by
    change Integrable (triadFlux action₁ - triadFlux action₂)
      collision.collisionMeasure
    exact integrable_triadFlux_sub collision hbounded₁ hbounded₂
  have hleg (leg : Fin 3) := integrable_actionDistance_triadLeg
    collision haction₁_measurable haction₂_measurable haction₁ haction₂ leg
  have hsum : Integrable
      (fun triad : Fin 3 -> Mode =>
        actionDistance action₁ action₂ (triad 0) +
          actionDistance action₁ action₂ (triad 1) +
          actionDistance action₁ action₂ (triad 2))
      collision.collisionMeasure :=
    ((hleg 0).add (hleg 1)).add (hleg 2)
  calc
    _ <= ∫ (triad : Fin 3 -> Mode),
        2 * radius *
          (actionDistance action₁ action₂ (triad 0) +
            actionDistance action₁ action₂ (triad 1) +
            actionDistance action₁ action₂ (triad 2))
        ∂collision.collisionMeasure := by
      apply integral_mono hflux.norm (hsum.const_mul (2 * radius))
      intro triad
      simpa only [actionDistance] using
        norm_triadFlux_sub_le_sum hradius haction₁ haction₂ triad
    _ = 2 * radius *
        ∫ (triad : Fin 3 -> Mode),
          actionDistance action₁ action₂ (triad 0) +
            actionDistance action₁ action₂ (triad 1) +
            actionDistance action₁ action₂ (triad 2)
          ∂collision.collisionMeasure := by
      rw [integral_const_mul]
    _ = _ := by
      rw [← integral_actionDistance_reference_eq_triadLegSum
        collision haction₁_measurable haction₂_measurable haction₁ haction₂]

/-- Intrinsic continuum `L1 -> L1` Lipschitz estimate for the canonical RN
collision vector on a common pointwise radius ball. -/
theorem integral_norm_collisionVector_sub_le_actionL1
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (hradius : 0 <= radius)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius) :
    (∫ mode, ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖
      ∂collisionReferenceMeasure collision) <=
      6 * radius *
        ∫ mode, actionDistance action₁ action₂ mode
          ∂collisionReferenceMeasure collision := by
  have hbounded₁ : IsBoundedMeasurable action₁ :=
    ⟨haction₁_measurable, ⟨radius, haction₁⟩⟩
  have hbounded₂ : IsBoundedMeasurable action₂ :=
    ⟨haction₂_measurable, ⟨radius, haction₂⟩⟩
  calc
    _ = (signedCollisionDifferenceMeasure collision action₁ action₂).variation.real
        Set.univ := integral_norm_collisionVector_sub_eq_variation_real
          collision hbounded₁ hbounded₂
    _ <= 3 *
        (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation.real
          Set.univ :=
      signedCollisionDifference_variation_real_le collision hbounded₁ hbounded₂
    _ = 3 *
        ∫ (triad : Fin 3 -> Mode),
          ‖triadFlux action₁ triad - triadFlux action₂ triad‖
          ∂collision.collisionMeasure := by
      rw [fluxDifference_variation_real_eq_integral_norm
        collision hbounded₁ hbounded₂]
    _ <= 3 * (2 * radius *
        ∫ mode, actionDistance action₁ action₂ mode
          ∂collisionReferenceMeasure collision) := by
      gcongr
      exact integral_norm_triadFlux_sub_le_actionL1 collision hradius
        haction₁_measurable haction₂_measurable haction₁ haction₂
    _ = _ := by ring

/-- Under a uniform action distance `epsilon`, the triad flux `L1` distance
is bounded by its pointwise constant times the finite collision mass. -/
theorem integral_norm_triadFlux_sub_le_uniform_mass
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon) :
    (∫ (triad : Fin 3 -> Mode),
        ‖triadFlux action₁ triad - triadFlux action₂ triad‖
        ∂collision.collisionMeasure) <=
      6 * radius * epsilon *
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)).real Set.univ := by
  have hbounded₁ : IsBoundedMeasurable action₁ :=
    ⟨haction₁_measurable, ⟨radius, haction₁⟩⟩
  have hbounded₂ : IsBoundedMeasurable action₂ :=
    ⟨haction₂_measurable, ⟨radius, haction₂⟩⟩
  have hflux : Integrable
      (fun triad : Fin 3 -> Mode =>
        triadFlux action₁ triad - triadFlux action₂ triad)
      collision.collisionMeasure := by
    change Integrable (triadFlux action₁ - triadFlux action₂)
      collision.collisionMeasure
    exact integrable_triadFlux_sub collision hbounded₁ hbounded₂
  calc
    _ <= ∫ _ : Fin 3 -> Mode, 6 * radius * epsilon
        ∂collision.collisionMeasure := by
      apply integral_mono hflux.norm (integrable_const _)
      intro triad
      exact norm_triadFlux_sub_le_uniform hradius hepsilon
        haction₁ haction₂ hdistance triad
    _ = _ := by
      rw [integral_const]
      simp only [smul_eq_mul]
      ring

/-- Uniform-distance corollary with explicit common action radius and total
collision-measure mass. -/
theorem integral_norm_collisionVector_sub_le_uniform_mass
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon) :
    (∫ mode, ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖
      ∂collisionReferenceMeasure collision) <=
      18 * radius * epsilon *
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)).real Set.univ := by
  have hbounded₁ : IsBoundedMeasurable action₁ :=
    ⟨haction₁_measurable, ⟨radius, haction₁⟩⟩
  have hbounded₂ : IsBoundedMeasurable action₂ :=
    ⟨haction₂_measurable, ⟨radius, haction₂⟩⟩
  calc
    _ = (signedCollisionDifferenceMeasure collision action₁ action₂).variation.real
        Set.univ := integral_norm_collisionVector_sub_eq_variation_real
          collision hbounded₁ hbounded₂
    _ <= 3 *
        (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation.real
          Set.univ :=
      signedCollisionDifference_variation_real_le collision hbounded₁ hbounded₂
    _ = 3 *
        ∫ (triad : Fin 3 -> Mode),
          ‖triadFlux action₁ triad - triadFlux action₂ triad‖
          ∂collision.collisionMeasure := by
      rw [fluxDifference_variation_real_eq_integral_norm
        collision hbounded₁ hbounded₂]
    _ <= 3 * (6 * radius * epsilon *
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)).real Set.univ) := by
      gcongr
      exact integral_norm_triadFlux_sub_le_uniform_mass collision hradius hepsilon
        haction₁_measurable haction₂_measurable haction₁ haction₂ hdistance
    _ = _ := by ring

/-- On the common bounded measurable class, the RN collision vector depends
only on the action equivalence class in `L1` of the canonical reference
measure.  This is the faithful quotient-level interface; it does not assert
that the output lies in `L-infinity`. -/
theorem collisionVector_ae_eq_of_action_ae_eq
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (hradius : 0 <= radius)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hae : action₁ =ᵐ[collisionReferenceMeasure collision] action₂) :
    collisionVector collision action₁ =ᵐ[collisionReferenceMeasure collision]
      collisionVector collision action₂ := by
  let reference := collisionReferenceMeasure collision
  have hactionDistanceZero :
      (∫ mode, actionDistance action₁ action₂ mode ∂reference) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with mode hmode
    simp only [actionDistance, hmode, sub_self, norm_zero, Pi.zero_apply]
  have hupper := integral_norm_collisionVector_sub_le_actionL1 collision hradius
    haction₁_measurable haction₂_measurable haction₁ haction₂
  rw [hactionDistanceZero, mul_zero] at hupper
  have hnonneg : 0 <=
      ∫ mode, ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖ ∂reference :=
    integral_nonneg fun _ => norm_nonneg _
  have hzero :
      (∫ mode, ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖ ∂reference) = 0 :=
    le_antisymm hupper hnonneg
  have hcollisionSub : Integrable
      (fun mode => collisionVector collision action₁ mode -
        collisionVector collision action₂ mode) reference := by
    change Integrable
      (collisionVector collision action₁ - collisionVector collision action₂)
      reference
    exact (integrable_collisionVector collision action₁).sub
      (integrable_collisionVector collision action₂)
  have hnormZero :
      (fun mode => ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖) =ᵐ[reference] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun _ => norm_nonneg _) hcollisionSub.norm).mp hzero
  filter_upwards [hnormZero] with mode hmode
  have hsubzero : collisionVector collision action₁ mode -
      collisionVector collision action₂ mode = 0 := by
    apply norm_eq_zero.mp
    simpa only [Pi.zero_apply] using hmode
  exact sub_eq_zero.mp hsubzero

end

end ArchonPhysics.ResonantThreeWaveKineticL1Lipschitz
