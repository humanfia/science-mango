import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0715

open Dimension

/-!
# Error in a flat-Earth launch-speed estimate

A small satellite moves straight upward from the surface of the Earth.  The
primary figure labels the initial state by `y₁ = 0 km`, `v₁` and the later
state by `y₂ = 400 km`, `v₂ = 500 m/s`.  The question compares the launch
speed inferred from inverse-square Newtonian gravity with the speed inferred
from a constant-`g` flat-Earth approximation.

Lengths, mass, acceleration, speeds, and energies below are unit-independent
dimensionful quantities.  Real scalars occur only at named-unit readout
boundaries, in the bitmap transcription, and in the dimensionless percentage
answer choices.

The source records choice C (`2.5%`).  With the conventional mean Earth radius
and standard surface gravity used below, however, the displayed boundary data
give an error close to `2.99%` when the exact speed is the denominator.  Thus D
(`2.7%`) is the closest displayed choice.  The recorded choice is retained only
as dataset metadata, while the theorem states the physically supported result.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in kilometres. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read a speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read an energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Physical states and primary-figure vocabulary -/

/-- The two labelled states in the launch diagram. -/
inductive LaunchInstant where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- The two gravitational models whose launch-speed predictions are compared. -/
inductive GravityModel where
  | sphericalEarth
  | flatEarth
  deriving DecidableEq, Fintype, Repr

/-- The kind of launched object described by the problem. -/
inductive LaunchedObjectKind where
  | smallSatellite
  | other
  deriving DecidableEq, Repr

/-- The central body pictured below the launch path. -/
inductive CentralBody where
  | earth
  | other
  deriving DecidableEq, Repr

/-- The path used by the inventor to launch the satellite. -/
inductive LaunchPath where
  | straightUpFromSurface
  | other
  deriving DecidableEq, Repr

/-- Directions available along the vertical launch axis. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Coordinate-axis symbols that may be printed in the figure. -/
inductive AxisSymbol where
  | y
  | other
  deriving DecidableEq, Repr

/-- Velocity labels attached to the two satellite markers. -/
inductive VelocitySymbol where
  | v1
  | v2
  deriving DecidableEq, Repr

/-- Altitude-coordinate labels attached to the two satellite markers. -/
inductive AltitudeSymbol where
  | y1
  | y2
  deriving DecidableEq, Repr

/-- The Earth-radius symbol printed inside the central body. -/
inductive RadiusSymbol where
  | Re
  | other
  deriving DecidableEq, Repr

/-!
Literal evidence visible in `715.png`.  The scalar fields are printed readouts
and are kept separate from the physical dimensionful quantities.
-/
structure EarthLaunchFigure where
  verticalAxisSymbol : AxisSymbol
  axisOriginLabelKilometers : ℝ
  altitudeSymbol : LaunchInstant → AltitudeSymbol
  altitudeLabelKilometers : LaunchInstant → ℝ
  velocitySymbol : LaunchInstant → VelocitySymbol
  velocityValueMetersPerSecond : LaunchInstant → Option ℝ
  upwardArrowShown : LaunchInstant → Bool
  satelliteMarkerShown : LaunchInstant → Bool
  beforeTextShown : Bool
  afterTextShown : Bool
  earthShown : Bool
  earthTextLabel : CentralBody
  earthRadiusArrowShown : Bool
  earthRadiusSymbol : RadiusSymbol

/-!
Independent physical quantities for the true spherical model and the
flat-Earth approximation.  In particular, both initial speeds are independent
fields; neither is defined from an answer choice or predicted formula.
-/
structure VerticalSatelliteLaunchSetup where
  objectKind : LaunchedObjectKind
  centralBody : CentralBody
  launchPath : LaunchPath
  satelliteMass : MassQuantity
  earthRadius : LengthQuantity
  surfaceGravity : AccelerationQuantity
  altitudeAt : LaunchInstant → LengthQuantity
  directionAt : LaunchInstant → VerticalDirection
  speedAt : GravityModel → LaunchInstant → DimSpeed
  kineticEnergyAt : GravityModel → LaunchInstant → DimEnergy
  gravitationalPotentialEnergyAt : GravityModel → LaunchInstant → DimEnergy
  figure : EarthLaunchFigure

/-! ## Scenario, source readouts, and figure evidence -/

/-- Qualitative facts stated in the problem prose. -/
structure MatchesStraightUpSatelliteScenario
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  objectIsSmallSatellite : setup.objectKind = .smallSatellite
  centralBodyIsEarth : setup.centralBody = .earth
  pathIsStraightUpFromSurface : setup.launchPath = .straightUpFromSurface
  motionIsUpward : ∀ instant, setup.directionAt instant = .upward

/-- The numerical state data printed in the primary image. -/
structure MatchesDisplayedLaunchReadouts
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  beforeAltitudeIsZeroKilometers :
    lengthInKilometers (setup.altitudeAt .before) = 0
  afterAltitudeIsFourHundredKilometers :
    lengthInKilometers (setup.altitudeAt .after) = 400
  sphericalAfterSpeedIsFiveHundredMetersPerSecond :
    speedInMetersPerSecond
      (setup.speedAt .sphericalEarth .after) = 500

/-!
Raster-visible geometry and labels.  The before-state velocity has the symbol
`v₁` but no numerical value, whereas the after-state label is `v₂ = 500 m/s`.
-/
structure MatchesPrimaryEarthLaunchFigure
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  axisIsY : setup.figure.verticalAxisSymbol = .y
  axisOriginIsZero : setup.figure.axisOriginLabelKilometers = 0
  beforeAltitudeSymbolIsY1 :
    setup.figure.altitudeSymbol .before = .y1
  afterAltitudeSymbolIsY2 :
    setup.figure.altitudeSymbol .after = .y2
  beforeAltitudeLabelIsZero :
    setup.figure.altitudeLabelKilometers .before = 0
  afterAltitudeLabelIsFourHundred :
    setup.figure.altitudeLabelKilometers .after = 400
  beforeAltitudeLabelDescribesState :
    setup.figure.altitudeLabelKilometers .before =
      lengthInKilometers (setup.altitudeAt .before)
  afterAltitudeLabelDescribesState :
    setup.figure.altitudeLabelKilometers .after =
      lengthInKilometers (setup.altitudeAt .after)
  beforeVelocitySymbolIsV1 :
    setup.figure.velocitySymbol .before = .v1
  afterVelocitySymbolIsV2 :
    setup.figure.velocitySymbol .after = .v2
  beforeVelocityHasNoNumericReadout :
    setup.figure.velocityValueMetersPerSecond .before = none
  afterVelocityReadoutIsFiveHundred :
    setup.figure.velocityValueMetersPerSecond .after = some 500
  afterVelocityReadoutDescribesState :
    setup.figure.velocityValueMetersPerSecond .after =
      some (speedInMetersPerSecond
        (setup.speedAt .sphericalEarth .after))
  upwardArrowsAreShown :
    ∀ instant, setup.figure.upwardArrowShown instant = true
  satelliteMarkersAreShown :
    ∀ instant, setup.figure.satelliteMarkerShown instant = true
  beforeTextIsShown : setup.figure.beforeTextShown = true
  afterTextIsShown : setup.figure.afterTextShown = true
  earthIsShown : setup.figure.earthShown = true
  earthTextSaysEarth : setup.figure.earthTextLabel = .earth
  earthRadiusArrowIsShown : setup.figure.earthRadiusArrowShown = true
  earthRadiusSymbolIsRe : setup.figure.earthRadiusSymbol = .Re

/-!
Standard numerical data needed because the raster labels `Rₑ` but does not
print its value.  The mean Earth radius and conventional standard gravity are
kept separate from facts directly read from the source.
-/
structure UsesStandardEarthCalibration
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  meanEarthRadiusKilometers :
    lengthInKilometers setup.earthRadius = 6371
  standardSurfaceGravity :
    accelerationInMetersPerSecondSquared setup.surfaceGravity = 9.80665

/-!
The flat model answers the same boundary-value question as the spherical
model: it uses the same final altitude and final speed.  Altitudes are already
shared fields, so only the independently stored final speeds must be related.
-/
structure UsesSameBoundaryDataForFlatApproximation
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  sameFinalSpeed :
    speedInMetersPerSecond (setup.speedAt .flatEarth .after) =
      speedInMetersPerSecond (setup.speedAt .sphericalEarth .after)

/-- Positivity and nondegeneracy conditions for the physical comparison. -/
structure HasPhysicalVerticalLaunchParameters
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  positiveSatelliteMass : 0 < massInKilograms setup.satelliteMass
  positiveEarthRadius : 0 < lengthInMeters setup.earthRadius
  positiveSurfaceGravity :
    0 < accelerationInMetersPerSecondSquared setup.surfaceGravity
  nonnegativeAltitudes :
    ∀ instant, 0 ≤ lengthInMeters (setup.altitudeAt instant)
  afterIsAboveBefore :
    lengthInMeters (setup.altitudeAt .before) <
      lengthInMeters (setup.altitudeAt .after)
  positiveSphericalInitialSpeed :
    0 < speedInMetersPerSecond
      (setup.speedAt .sphericalEarth .before)

/-! ## Governing energy laws -/

/-- Translational kinetic energy `K = (1/2) m v²` in either model. -/
structure SatisfiesSatelliteKineticEnergyLaw
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  energyFormula : ∀ model instant,
    energyInJoules (setup.kineticEnergyAt model instant) =
      (1 / 2 : ℝ) * massInKilograms setup.satelliteMass *
        speedInMetersPerSecond (setup.speedAt model instant) ^ 2

/-!
The inverse-square Newtonian potential, normalized to zero at infinity and
written using surface gravity `g₀ = GM / Rₑ²`:

`U(y) = -m g₀ Rₑ² / (Rₑ + y)`.
-/
structure SatisfiesSphericalEarthPotentialLaw
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  energyFormula : ∀ instant,
    energyInJoules
        (setup.gravitationalPotentialEnergyAt .sphericalEarth instant) =
      -(massInKilograms setup.satelliteMass *
          accelerationInMetersPerSecondSquared setup.surfaceGravity *
          lengthInMeters setup.earthRadius ^ 2) /
        (lengthInMeters setup.earthRadius +
          lengthInMeters (setup.altitudeAt instant))

/-!
The flat-Earth approximation uses a uniform downward acceleration and the
near-surface potential `U_flat(y) = m g₀ y`.
-/
structure SatisfiesFlatEarthPotentialLaw
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  energyFormula : ∀ instant,
    energyInJoules
        (setup.gravitationalPotentialEnergyAt .flatEarth instant) =
      massInKilograms setup.satelliteMass *
        accelerationInMetersPerSecondSquared setup.surfaceGravity *
        lengthInMeters (setup.altitudeAt instant)

/-- Total mechanical energy in one model at one labelled instant. -/
def totalMechanicalEnergyInJoules
    (setup : VerticalSatelliteLaunchSetup)
    (model : GravityModel) (instant : LaunchInstant) : ℝ :=
  energyInJoules (setup.kineticEnergyAt model instant) +
    energyInJoules
      (setup.gravitationalPotentialEnergyAt model instant)

/-- Each conservative model equates the before and after mechanical energies. -/
structure SatisfiesMechanicalEnergyConservation
    (setup : VerticalSatelliteLaunchSetup) : Prop where
  conserved : ∀ model,
    totalMechanicalEnergyInJoules setup model .before =
      totalMechanicalEnergyInJoules setup model .after

/-! ## Derived model predictions and percentage error -/

/-- Launch-speed readout predicted by the spherical inverse-square model. -/
def sphericalPredictedInitialSpeedInMetersPerSecond
    (setup : VerticalSatelliteLaunchSetup) : ℝ :=
  Real.sqrt
    (speedInMetersPerSecond (setup.speedAt .sphericalEarth .after) ^ 2 +
      2 * accelerationInMetersPerSecondSquared setup.surfaceGravity *
        lengthInMeters setup.earthRadius ^ 2 *
        (1 /
            (lengthInMeters setup.earthRadius +
              lengthInMeters (setup.altitudeAt .before)) -
          1 /
            (lengthInMeters setup.earthRadius +
              lengthInMeters (setup.altitudeAt .after))))

/-- Launch-speed readout predicted by the constant-`g` flat-Earth model. -/
def flatPredictedInitialSpeedInMetersPerSecond
    (setup : VerticalSatelliteLaunchSetup) : ℝ :=
  Real.sqrt
    (speedInMetersPerSecond (setup.speedAt .flatEarth .after) ^ 2 +
      2 * accelerationInMetersPerSecondSquared setup.surfaceGravity *
        (lengthInMeters (setup.altitudeAt .after) -
          lengthInMeters (setup.altitudeAt .before)))

/-!
Standard absolute percentage error of the approximate launch speed, using the
spherical-model launch speed as the exact reference value.
-/
def flatEarthPercentageError
    (setup : VerticalSatelliteLaunchSetup) : ℝ :=
  100 *
    |speedInMetersPerSecond (setup.speedAt .flatEarth .before) -
      speedInMetersPerSecond (setup.speedAt .sphericalEarth .before)| /
    |speedInMetersPerSecond (setup.speedAt .sphericalEarth .before)|

/-- The four percentage labels displayed by the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Percentage printed next to an answer label. -/
def AnswerChoice.percentage : AnswerChoice → ℝ
  | .A => 21 / 10
  | .B => 23 / 10
  | .C => 25 / 10
  | .D => 27 / 10

/-- Dataset answer label retained as metadata, never used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice is at least as close as every option to the model error. -/
def IsClosestPercentageChoice
    (errorPercentage : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |errorPercentage - choice.percentage| ≤
      |errorPercentage - other.percentage|

/-!
Energy conservation and the two potential laws give the respective spherical
and flat-Earth launch-speed formulas.  This is a symbolic derived conclusion;
it contains no answer-choice percentage.
-/
lemma initialSpeeds_eq_modelPredictions
    (setup : VerticalSatelliteLaunchSetup)
    (hPhysical : HasPhysicalVerticalLaunchParameters setup)
    (hKinetic : SatisfiesSatelliteKineticEnergyLaw setup)
    (hSpherical : SatisfiesSphericalEarthPotentialLaw setup)
    (hFlat : SatisfiesFlatEarthPotentialLaw setup)
    (hConservation : SatisfiesMechanicalEnergyConservation setup) :
    speedInMetersPerSecond (setup.speedAt .sphericalEarth .before) =
        sphericalPredictedInitialSpeedInMetersPerSecond setup ∧
      speedInMetersPerSecond (setup.speedAt .flatEarth .before) =
        flatPredictedInitialSpeedInMetersPerSecond setup := by
  constructor
  · have hsConservation :=
      hConservation.conserved GravityModel.sphericalEarth
    unfold totalMechanicalEnergyInJoules at hsConservation
    rw [hKinetic.energyFormula .sphericalEarth .before,
      hKinetic.energyFormula .sphericalEarth .after,
      hSpherical.energyFormula .before,
      hSpherical.energyFormula .after] at hsConservation
    have hsSquared :
        speedInMetersPerSecond
              (setup.speedAt .sphericalEarth .before) ^ 2 =
          speedInMetersPerSecond
                (setup.speedAt .sphericalEarth .after) ^ 2 +
            2 * accelerationInMetersPerSecondSquared setup.surfaceGravity *
              lengthInMeters setup.earthRadius ^ 2 *
                (1 /
                    (lengthInMeters setup.earthRadius +
                      lengthInMeters (setup.altitudeAt .before)) -
                  1 /
                    (lengthInMeters setup.earthRadius +
                      lengthInMeters (setup.altitudeAt .after))) := by
      have hm : massInKilograms setup.satelliteMass ≠ 0 :=
        ne_of_gt hPhysical.positiveSatelliteMass
      apply mul_left_cancel₀ hm
      linear_combination 2 * hsConservation
    unfold sphericalPredictedInitialSpeedInMetersPerSecond
    rw [← hsSquared, Real.sqrt_sq_eq_abs,
      abs_of_pos hPhysical.positiveSphericalInitialSpeed]
  · have hfConservation :=
      hConservation.conserved GravityModel.flatEarth
    unfold totalMechanicalEnergyInJoules at hfConservation
    rw [hKinetic.energyFormula .flatEarth .before,
      hKinetic.energyFormula .flatEarth .after,
      hFlat.energyFormula .before,
      hFlat.energyFormula .after] at hfConservation
    have hfSquared :
        speedInMetersPerSecond (setup.speedAt .flatEarth .before) ^ 2 =
          speedInMetersPerSecond (setup.speedAt .flatEarth .after) ^ 2 +
            2 * accelerationInMetersPerSecondSquared setup.surfaceGravity *
              (lengthInMeters (setup.altitudeAt .after) -
                lengthInMeters (setup.altitudeAt .before)) := by
      have hm : massInKilograms setup.satelliteMass ≠ 0 :=
        ne_of_gt hPhysical.positiveSatelliteMass
      apply mul_left_cancel₀ hm
      linear_combination 2 * hfConservation
    have hvNonnegative :
        0 ≤ speedInMetersPerSecond
          (setup.speedAt .flatEarth .before) := by
      unfold speedInMetersPerSecond
      exact NNReal.coe_nonneg _
    unfold flatPredictedInitialSpeedInMetersPerSecond
    rw [← hfSquared, Real.sqrt_sq_eq_abs, abs_of_nonneg hvNonnegative]

/-!
The conventional calibration and displayed boundary data give an absolute
percentage error strictly between `2.99%` and `3%`; consequently D (`2.7%`) is
the closest displayed choice.  The two launch-speed equalities expose the
physical calculation used before making that comparison.  The inconsistent
recorded choice C remains only in `recordedDatasetAnswer`, never in a premise
or in the physically supported conclusion.

Blueprint: `thm:physics:phyx_mini_0715:target`.
-/
theorem flatEarthApproximationErrorIsApproximatelyThreePercentAndChoiceD
    (setup : VerticalSatelliteLaunchSetup)
    (hScenario : MatchesStraightUpSatelliteScenario setup)
    (hReadouts : MatchesDisplayedLaunchReadouts setup)
    (hFigure : MatchesPrimaryEarthLaunchFigure setup)
    (hEarth : UsesStandardEarthCalibration setup)
    (hBoundary : UsesSameBoundaryDataForFlatApproximation setup)
    (hPhysical : HasPhysicalVerticalLaunchParameters setup)
    (hKinetic : SatisfiesSatelliteKineticEnergyLaw setup)
    (hSpherical : SatisfiesSphericalEarthPotentialLaw setup)
    (hFlat : SatisfiesFlatEarthPotentialLaw setup)
    (hConservation : SatisfiesMechanicalEnergyConservation setup) :
    speedInMetersPerSecond (setup.speedAt .sphericalEarth .before) =
        sphericalPredictedInitialSpeedInMetersPerSecond setup ∧
      speedInMetersPerSecond (setup.speedAt .flatEarth .before) =
        flatPredictedInitialSpeedInMetersPerSecond setup ∧
      299 / 100 < flatEarthPercentageError setup ∧
      flatEarthPercentageError setup < 3 ∧
      IsClosestPercentageChoice (flatEarthPercentageError setup) .D := by
  have lengthInKilometers_eq_lengthInMeters_div_thousand
      (length : LengthQuantity) :
      lengthInKilometers length = lengthInMeters length / 1000 := by
    unfold lengthInKilometers lengthInMeters
    have hscale := length.property
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.kilometers} : UnitChoices)
    change
      length ({UnitChoices.SI with
          length := LengthUnit.kilometers} : UnitChoices) =
        UnitChoices.dimScale
            ({UnitChoices.SI with
              length := LengthUnit.meters} : UnitChoices)
            ({UnitChoices.SI with
              length := LengthUnit.kilometers} : UnitChoices) L𝓭 •
          length ({UnitChoices.SI with
            length := LengthUnit.meters} : UnitChoices) at hscale
    have hdim :
        UnitChoices.dimScale
            ({UnitChoices.SI with
              length := LengthUnit.meters} : UnitChoices)
            ({UnitChoices.SI with
              length := LengthUnit.kilometers} : UnitChoices) L𝓭 =
          (1000 : NNReal)⁻¹ := by
      ext
      norm_num [UnitChoices.dimScale, LengthUnit.kilometers,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
        Dimension.L𝓭]
      rfl
    change
      (((length ({UnitChoices.SI with
        length := LengthUnit.kilometers} : UnitChoices)).val : NNReal) : ℝ) =
        (((length ({UnitChoices.SI with
          length := LengthUnit.meters} : UnitChoices)).val : NNReal) : ℝ) /
          1000
    rw [hscale, hdim]
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul,
      NNReal.coe_inv]
    norm_num
    ring
  have hRadius : lengthInMeters setup.earthRadius = 6371000 := by
    have h := hEarth.meanEarthRadiusKilometers
    rw [lengthInKilometers_eq_lengthInMeters_div_thousand] at h
    linarith
  have hBefore :
      lengthInMeters (setup.altitudeAt .before) = 0 := by
    have h := hReadouts.beforeAltitudeIsZeroKilometers
    rw [lengthInKilometers_eq_lengthInMeters_div_thousand] at h
    linarith
  have hAfter :
      lengthInMeters (setup.altitudeAt .after) = 400000 := by
    have h := hReadouts.afterAltitudeIsFourHundredKilometers
    rw [lengthInKilometers_eq_lengthInMeters_div_thousand] at h
    linarith
  have hGravity :
      accelerationInMetersPerSecondSquared setup.surfaceGravity =
        9.80665 :=
    hEarth.standardSurfaceGravity
  have hSphericalAfter :
      speedInMetersPerSecond
          (setup.speedAt .sphericalEarth .after) = 500 :=
    hReadouts.sphericalAfterSpeedIsFiveHundredMetersPerSecond
  have hFlatAfter :
      speedInMetersPerSecond
          (setup.speedAt .flatEarth .after) = 500 := by
    rw [hBoundary.sameFinalSpeed, hSphericalAfter]
  have hPredictions :=
    initialSpeeds_eq_modelPredictions setup hPhysical hKinetic
      hSpherical hFlat hConservation
  have hSphericalSquared :
      speedInMetersPerSecond
          (setup.speedAt .sphericalEarth .before) ^ 2 =
        51675283720 / 6771 := by
    rw [hPredictions.1]
    unfold sphericalPredictedInitialSpeedInMetersPerSecond
    rw [hSphericalAfter, hGravity, hRadius, hBefore, hAfter]
    rw [Real.sq_sqrt]
    · norm_num
    · norm_num
  have hFlatSquared :
      speedInMetersPerSecond
          (setup.speedAt .flatEarth .before) ^ 2 = 8095320 := by
    rw [hPredictions.2]
    unfold flatPredictedInitialSpeedInMetersPerSecond
    rw [hFlatAfter, hGravity, hBefore, hAfter]
    rw [Real.sq_sqrt]
    · norm_num
    · norm_num
  have hFlatNonnegative :
      0 ≤ speedInMetersPerSecond
        (setup.speedAt .flatEarth .before) := by
    unfold speedInMetersPerSecond
    exact NNReal.coe_nonneg _
  have hSphericalPositive :=
    hPhysical.positiveSphericalInitialSpeed
  have hLowerSquare :
      (10299 / 10000 : ℝ) ^ 2 * (51675283720 / 6771) <
        8095320 := by
    norm_num
  have hUpperSquare :
      (8095320 : ℝ) <
        (103 / 100 : ℝ) ^ 2 * (51675283720 / 6771) := by
    norm_num
  have hScaledLower :
      (10299 / 10000 : ℝ) *
          speedInMetersPerSecond
            (setup.speedAt .sphericalEarth .before) <
        speedInMetersPerSecond
          (setup.speedAt .flatEarth .before) := by
    nlinarith [hSphericalSquared, hFlatSquared]
  have hScaledUpper :
      speedInMetersPerSecond
          (setup.speedAt .flatEarth .before) <
        (103 / 100 : ℝ) *
          speedInMetersPerSecond
            (setup.speedAt .sphericalEarth .before) := by
    nlinarith [hSphericalSquared, hFlatSquared]
  have hFlatGreater :
      speedInMetersPerSecond
          (setup.speedAt .sphericalEarth .before) <
        speedInMetersPerSecond
          (setup.speedAt .flatEarth .before) := by
    nlinarith
  have hErrorLower :
      299 / 100 < flatEarthPercentageError setup := by
    unfold flatEarthPercentageError
    rw [abs_of_pos (sub_pos.mpr hFlatGreater),
      abs_of_pos hSphericalPositive]
    rw [lt_div_iff₀ hSphericalPositive]
    nlinarith [hScaledLower]
  have hErrorUpper :
      flatEarthPercentageError setup < 3 := by
    unfold flatEarthPercentageError
    rw [abs_of_pos (sub_pos.mpr hFlatGreater),
      abs_of_pos hSphericalPositive]
    rw [div_lt_iff₀ hSphericalPositive]
    nlinarith [hScaledUpper]
  refine
    ⟨hPredictions.1, hPredictions.2, hErrorLower, hErrorUpper, ?_⟩
  intro other
  have hOtherAtMostD :
      other.percentage ≤ AnswerChoice.D.percentage := by
    cases other <;> norm_num [AnswerChoice.percentage]
  have hErrorAboveD :
      AnswerChoice.D.percentage < flatEarthPercentageError setup := by
    norm_num [AnswerChoice.percentage]
    linarith
  rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hErrorAboveD)),
    abs_of_nonneg
      (sub_nonneg.mpr
        (hOtherAtMostD.trans (le_of_lt hErrorAboveD)))]
  linarith

end PhyXMiniProblems.ProblemPhyXMini0715
