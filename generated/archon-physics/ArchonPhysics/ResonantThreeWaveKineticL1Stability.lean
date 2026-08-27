import ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

/-!
# Quantitative L1 stability of the resonant three-wave collision operator

The Radon--Nikodym collision vector is only known to be integrable with
respect to the canonical three-leg reference measure.  This file therefore
states stability in the honest `L1` norm.  A common pointwise action bound
`R` and a uniform action distance `epsilon` give the explicit estimate

`integral ‖C(a) - C(b)‖ dnu <= 18 * R * epsilon * mu(univ)`.

The factor `6` is the Lipschitz constant of the quadratic three-wave flux on
the radius-`R` ball; the remaining factor `3` comes from transporting the
same signed flux through the three collision legs.  No `L-infinity` bound on
the Radon--Nikodym derivative is claimed.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticL1Stability

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThreeWaveCollisionAlgebra
open scoped MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

omit [MeasurableSpace Mode] in
/-- A product is Lipschitz on a common norm-bounded interval. -/
theorem norm_mul_sub_mul_le_of_norm_le
    {a b c d radius : Real}
    (_hradius : 0 <= radius)
    (ha : norm a <= radius) (hd : norm d <= radius) :
    norm (a * b - c * d) <=
      radius * (norm (a - c) + norm (b - d)) := by
  calc
    norm (a * b - c * d) =
        norm (a * (b - d) + (a - c) * d) := congrArg norm (by ring)
    _ <= norm (a * (b - d)) + norm ((a - c) * d) := norm_add_le _ _
    _ = norm a * norm (b - d) + norm (a - c) * norm d := by
      rw [norm_mul, norm_mul]
    _ <= radius * norm (b - d) + norm (a - c) * radius := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
    _ = radius * (norm (a - c) + norm (b - d)) := by ring

omit [MeasurableSpace Mode] in
/-- Pointwise flux difference bound retaining the three individual leg
distances. -/
theorem norm_triadFlux_sub_le_sum
    {action₁ action₂ : Mode -> Real} {radius : Real}
    (hradius : 0 <= radius)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (triad : Fin 3 -> Mode) :
    norm (triadFlux action₁ triad - triadFlux action₂ triad) <=
      2 * radius *
        (norm (action₁ (triad 0) - action₂ (triad 0)) +
          norm (action₁ (triad 1) - action₂ (triad 1)) +
          norm (action₁ (triad 2) - action₂ (triad 2))) := by
  have hmul (i j : Fin 3) :
      norm
          (action₁ (triad i) * action₁ (triad j) -
            action₂ (triad i) * action₂ (triad j)) <=
        radius *
          (norm (action₁ (triad i) - action₂ (triad i)) +
            norm (action₁ (triad j) - action₂ (triad j))) := by
    exact norm_mul_sub_mul_le_of_norm_le hradius
      (haction₁ (triad i)) (haction₂ (triad j))
  unfold triadFlux collisionFlux
  calc
    norm
        ((action₁ (triad 1) * action₁ (triad 2) -
            action₁ (triad 0) * action₁ (triad 1) -
            action₁ (triad 0) * action₁ (triad 2)) -
          (action₂ (triad 1) * action₂ (triad 2) -
            action₂ (triad 0) * action₂ (triad 1) -
            action₂ (triad 0) * action₂ (triad 2))) =
        norm
          ((action₁ (triad 1) * action₁ (triad 2) -
              action₂ (triad 1) * action₂ (triad 2)) -
            (action₁ (triad 0) * action₁ (triad 1) -
              action₂ (triad 0) * action₂ (triad 1)) -
            (action₁ (triad 0) * action₁ (triad 2) -
              action₂ (triad 0) * action₂ (triad 2))) := by
      ring
    _ <=
        norm
            (action₁ (triad 1) * action₁ (triad 2) -
              action₂ (triad 1) * action₂ (triad 2)) +
          norm
            (action₁ (triad 0) * action₁ (triad 1) -
              action₂ (triad 0) * action₂ (triad 1)) +
          norm
            (action₁ (triad 0) * action₁ (triad 2) -
              action₂ (triad 0) * action₂ (triad 2)) := by
      calc
        _ <= norm
              ((action₁ (triad 1) * action₁ (triad 2) -
                  action₂ (triad 1) * action₂ (triad 2)) -
                (action₁ (triad 0) * action₁ (triad 1) -
                  action₂ (triad 0) * action₂ (triad 1))) +
              norm
                (action₁ (triad 0) * action₁ (triad 2) -
                  action₂ (triad 0) * action₂ (triad 2)) := norm_sub_le _ _
        _ <= _ := by gcongr; exact norm_sub_le _ _
    _ <=
        radius *
            (norm (action₁ (triad 1) - action₂ (triad 1)) +
              norm (action₁ (triad 2) - action₂ (triad 2))) +
          radius *
            (norm (action₁ (triad 0) - action₂ (triad 0)) +
              norm (action₁ (triad 1) - action₂ (triad 1))) +
          radius *
            (norm (action₁ (triad 0) - action₂ (triad 0)) +
              norm (action₁ (triad 2) - action₂ (triad 2))) := by
      gcongr
      · exact hmul 1 2
      · exact hmul 0 1
      · exact hmul 0 2
    _ = 2 * radius *
        (norm (action₁ (triad 0) - action₂ (triad 0)) +
          norm (action₁ (triad 1) - action₂ (triad 1)) +
          norm (action₁ (triad 2) - action₂ (triad 2))) := by ring

omit [MeasurableSpace Mode] in
/-- Uniform version of the pointwise flux Lipschitz estimate. -/
theorem norm_triadFlux_sub_le_uniform
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (_hepsilon : 0 <= epsilon)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode, norm (action₁ mode - action₂ mode) <= epsilon)
    (triad : Fin 3 -> Mode) :
    norm (triadFlux action₁ triad - triadFlux action₂ triad) <=
      6 * radius * epsilon := by
  calc
    norm (triadFlux action₁ triad - triadFlux action₂ triad) <=
        2 * radius *
          (norm (action₁ (triad 0) - action₂ (triad 0)) +
            norm (action₁ (triad 1) - action₂ (triad 1)) +
            norm (action₁ (triad 2) - action₂ (triad 2))) :=
      norm_triadFlux_sub_le_sum hradius haction₁ haction₂ triad
    _ <= 2 * radius * (epsilon + epsilon + epsilon) := by
      gcongr <;> apply hdistance
    _ = 6 * radius * epsilon := by ring

/-- The triad flux difference is integrable for bounded measurable actions. -/
theorem integrable_triadFlux_sub
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    Integrable (triadFlux action₁ - triadFlux action₂)
      collision.collisionMeasure :=
  (integrable_triadFlux collision haction₁).sub
    (integrable_triadFlux collision haction₂)

/-- Signed triad measure carrying the difference of two collision fluxes. -/
def fluxDifferenceSignedTriadMeasure
    (collision : ResonantThreeWaveMeasure Mode)
    (action₁ action₂ : Mode -> Real) : SignedMeasure (Fin 3 -> Mode) :=
  (collision.collisionMeasure : Measure (Fin 3 -> Mode)).withDensityᵥ
    (triadFlux action₁ - triadFlux action₂)

/-- Transport the flux difference through one collision leg. -/
def legFluxDifferenceSignedMeasure
    (collision : ResonantThreeWaveMeasure Mode)
    (action₁ action₂ : Mode -> Real) (leg : Fin 3) : SignedMeasure Mode :=
  (fluxDifferenceSignedTriadMeasure collision action₁ action₂).map
    (triadLeg leg)

/-- Net mode-space difference measure built from one common triad density. -/
def signedCollisionDifferenceMeasure
    (collision : ResonantThreeWaveMeasure Mode)
    (action₁ action₂ : Mode -> Real) : SignedMeasure Mode :=
  legFluxDifferenceSignedMeasure collision action₁ action₂ 0 -
    legFluxDifferenceSignedMeasure collision action₁ action₂ 1 -
    legFluxDifferenceSignedMeasure collision action₁ action₂ 2

/-- The common-density triad difference is the difference of the two flux
measures. -/
theorem fluxDifferenceSignedTriadMeasure_eq_sub
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    fluxDifferenceSignedTriadMeasure collision action₁ action₂ =
      fluxSignedTriadMeasure collision action₁ -
        fluxSignedTriadMeasure collision action₂ := by
  unfold fluxDifferenceSignedTriadMeasure fluxSignedTriadMeasure
  exact withDensityᵥ_sub
    (integrable_triadFlux collision haction₁)
    (integrable_triadFlux collision haction₂)

/-- Mapping the common-density difference through a leg commutes with
subtraction. -/
theorem legFluxDifferenceSignedMeasure_eq_sub
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) (leg : Fin 3) :
    legFluxDifferenceSignedMeasure collision action₁ action₂ leg =
      legFluxSignedMeasure collision action₁ leg -
        legFluxSignedMeasure collision action₂ leg := by
  unfold legFluxDifferenceSignedMeasure legFluxSignedMeasure
  rw [fluxDifferenceSignedTriadMeasure_eq_sub collision haction₁ haction₂]
  exact (VectorMeasure.mapGm (M := Real) (triadLeg leg)).map_sub _ _

/-- The net common-density construction is exactly the difference of the two
nonlinear signed collision measures. -/
theorem signedCollisionDifferenceMeasure_eq_sub
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    signedCollisionDifferenceMeasure collision action₁ action₂ =
      signedCollisionMeasure collision action₁ -
        signedCollisionMeasure collision action₂ := by
  unfold signedCollisionDifferenceMeasure signedCollisionMeasure
  rw [legFluxDifferenceSignedMeasure_eq_sub collision haction₁ haction₂ 0,
    legFluxDifferenceSignedMeasure_eq_sub collision haction₁ haction₂ 1,
    legFluxDifferenceSignedMeasure_eq_sub collision haction₁ haction₂ 2]
  abel

end

end ArchonPhysics.ResonantThreeWaveKineticL1Stability
