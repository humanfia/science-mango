import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Temperature of water in a spring-loaded piston cylinder

This file formalizes problem `phyx_mini_0446`.  A closed amount of water is
initially a saturated liquid-vapor mixture at `105 °C`, quality `0.85`, and
volume `1 L`.  Heating first raises a vertical piston until it touches a
linear spring at `1.5 L`; further heating compresses the spring.  The piston
diameter is `150 mm`, the spring stiffness is `100 N/mm`, and the requested
state is the one at `200 kPa`.

Physical length, area, volume, mass, pressure, temperature, force, spring
stiffness, and specific volume retain their dimensions through Physlib.  Real
numbers occur only as explicitly named unit readouts, vapor quality, and the
numbers printed in the problem or in rounded reference-table rows.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose data and the topology
  visible in image `446.png`;
* `MatchesRoundedReferenceWaterData` records saturation data at `105 °C` and
  two adjacent superheated-water table rows at `200 kPa`;
* `HasPhysicalParameters` selects the positive physical branch;
* `SatisfiesClosedWaterThermodynamics` states the target phase regime,
  saturation, mixture, closed-mass, and equilibrium property-table laws;
* `SatisfiesSpringLoadedPistonMechanics` states the circular-piston geometry,
  Hooke law, piston displacement law, and quasistatic pressure increment;
* `SatisfiesLocalSuperheatedTableInterpolation` states an order law and linear
  interpolation between the two reference table rows; and
* `final_temperature_matches_recorded_answer_D` concludes, rather than
  assumes, that the final temperature is within the stated table precision of
  `641 °C` and uniquely selects answer D.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0446

open Dimension

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A physical length or signed piston displacement. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical area, grounded in Physlib's nonnegative `DimArea`. -/
abbrev AreaQuantity : Type := DimArea

/-- A physical volume with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical pressure, grounded in Physlib's `DimPressure`. -/
abbrev PressureQuantity : Type := DimPressure

/-- An absolute thermodynamic temperature with temperature dimension. -/
abbrev TemperatureQuantity : Type := Dimensionful (WithDim Θ𝓭 ℝ)

/-- A physical force with dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A linear spring stiffness, force per length, with dimension `M T⁻²`. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A thermodynamic specific volume with dimension `L³ M⁻¹`. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹) ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Millimetre readout used for the piston diameter. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  1000 * lengthInMeters length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Litre readout used for the two stated volumes. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Kilogram readout of the closed amount of water. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used in the problem statement. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Kelvin readout of an absolute thermodynamic temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  (temperature UnitChoices.SI).val

/-- Celsius readout obtained from the kelvin readout by the affine offset. -/
def temperatureInDegreesCelsius (temperature : TemperatureQuantity) : ℝ :=
  temperatureInKelvins temperature - 27315 / 100

/-- Newton readout of the downward force exerted by the spring. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- Newton-per-metre readout of the spring stiffness. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  (stiffness UnitChoices.SI).val

/-- Newton-per-millimetre readout used by the source. -/
def springStiffnessInNewtonsPerMillimeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  springStiffnessInNewtonsPerMeter stiffness / 1000

/-- Cubic-metre-per-kilogram readout of a specific volume. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  (specificVolume UnitChoices.SI).val

/-! ## Apparatus, thermodynamic states, and primary-figure vocabulary -/

/-- The three process states needed by the problem. -/
inductive ProcessState where
  | initial
  | firstSpringContact
  | targetPressure
  deriving DecidableEq, Fintype, Repr

/-- The working substance named by the prose and printed in the figure. -/
inductive WorkingSubstance where
  | waterH2O
  deriving DecidableEq, Repr

/-- Thermodynamic regions relevant to the water process. -/
inductive WaterRegion where
  | saturatedMixture
  | superheatedVapor
  deriving DecidableEq, Repr

/-- Orientation of the piston-cylinder apparatus. -/
inductive CylinderOrientation where
  | vertical
  deriving DecidableEq, Repr

/-- Kinematic constraint on the piston. -/
inductive PistonMobility where
  | verticalTranslation
  deriving DecidableEq, Repr

/-- Constitutive idealization explicitly stated for the spring. -/
inductive SpringModel where
  | linearHookean
  deriving DecidableEq, Repr

/-- Components and graphical elements visible in image `446.png`. -/
inductive FigureComponent where
  | cylinder
  | topSupport
  | coilSpring
  | piston
  | waterRegion
  | dashedWaterBoundary
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative transcription of the primary raster.  The image supplies topology
and the `H₂O` label but no numerical dimension or thermodynamic readout.
-/
structure SpringLoadedPistonFigure where
  componentShown : FigureComponent → Bool
  h2oLabelShown : Bool
  springIsAbovePiston : Bool
  pistonIsAboveWater : Bool
  springIsBelowTopSupport : Bool
  dashedBoundarySurroundsWater : Bool

/-!
An external equilibrium-water property table.  Physlib has no saturated-water
or superheated-steam table API, so the four functions retain the physical
input and output roles without replacing them by scalar aliases.
-/
structure EquilibriumWaterPropertyTable where
  saturationPressureAt : TemperatureQuantity → PressureQuantity
  saturatedLiquidSpecificVolumeAt :
    TemperatureQuantity → SpecificVolumeQuantity
  saturatedVaporSpecificVolumeAt :
    TemperatureQuantity → SpecificVolumeQuantity
  superheatedSpecificVolumeAt :
    PressureQuantity → TemperatureQuantity → SpecificVolumeQuantity

/-!
Independent quantities for the closed water system, piston, and spring.  In
particular, `waterTemperature .targetPressure` is an independent physical
field and is not defined from an answer choice or from `641`.
-/
structure SpringLoadedWaterCylinder where
  substance : WorkingSubstance
  orientation : CylinderOrientation
  pistonMobility : PistonMobility
  springModel : SpringModel
  pistonDiameter : LengthQuantity
  pistonArea : AreaQuantity
  springStiffness : SpringStiffnessQuantity
  waterMass : MassQuantity
  waterPressure : ProcessState → PressureQuantity
  waterVolume : ProcessState → VolumeQuantity
  waterTemperature : ProcessState → TemperatureQuantity
  waterSpecificVolume : ProcessState → SpecificVolumeQuantity
  waterRegion : ProcessState → WaterRegion
  initialVaporQuality : ℝ
  springEngaged : ProcessState → Bool
  springCompression : ProcessState → LengthQuantity
  springForceMagnitude : ProcessState → ForceQuantity
  waterTable : EquilibriumWaterPropertyTable
  tableTemperatureAtSixHundredCelsius : TemperatureQuantity
  tableTemperatureAtSevenHundredCelsius : TemperatureQuantity
  figure : SpringLoadedPistonFigure

/-! ## Source data, reference readouts, and governing laws -/

/-!
The prose data and qualitative facts visible in image `446.png`.  The final
temperature and every displayed temperature choice are deliberately absent.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : SpringLoadedWaterCylinder) : Prop where
  containsWater : setup.substance = .waterH2O
  cylinderIsVertical : setup.orientation = .vertical
  pistonMovesVertically : setup.pistonMobility = .verticalTranslation
  springIsLinear : setup.springModel = .linearHookean
  initialTemperatureIsOneHundredFiveCelsius :
    temperatureInDegreesCelsius (setup.waterTemperature .initial) = 105
  initialQualityIsEightyFivePercent :
    setup.initialVaporQuality = 85 / 100
  initialVolumeIsOneLiter :
    volumeInLiters (setup.waterVolume .initial) = 1
  springContactVolumeIsOnePointFiveLiters :
    volumeInLiters (setup.waterVolume .firstSpringContact) = 3 / 2
  pistonDiameterIsOneHundredFiftyMillimeters :
    lengthInMillimeters setup.pistonDiameter = 150
  springStiffnessIsOneHundredNewtonsPerMillimeter :
    springStiffnessInNewtonsPerMillimeter setup.springStiffness = 100
  targetPressureIsTwoHundredKilopascals :
    pressureInKilopascals (setup.waterPressure .targetPressure) = 200
  initialWaterIsSaturatedMixture :
    setup.waterRegion .initial = .saturatedMixture
  springNotYetEngagedInitially : setup.springEngaged .initial = false
  springEngagedAtFirstContact :
    setup.springEngaged .firstSpringContact = true
  springEngagedAtTarget : setup.springEngaged .targetPressure = true
  everyComponentIsShown :
    ∀ component, setup.figure.componentShown component = true
  waterLabelIsShown : setup.figure.h2oLabelShown = true
  springDrawnAbovePiston : setup.figure.springIsAbovePiston = true
  pistonDrawnAboveWater : setup.figure.pistonIsAboveWater = true
  springDrawnBelowSupport : setup.figure.springIsBelowTopSupport = true
  dashedBoundaryDrawnAroundWater :
    setup.figure.dashedBoundarySurroundsWater = true

/-!
Rounded equilibrium-water data used by the standard table/interpolation
solution route.  These are independent table rows at `105 °C`, `600 °C`, and
`700 °C`; no field gives the unknown final temperature or the value `641`.
-/
structure MatchesRoundedReferenceWaterData
    (setup : SpringLoadedWaterCylinder) : Prop where
  saturationPressureAtOneHundredFiveCelsiusKilopascals :
    pressureInKilopascals
        (setup.waterTable.saturationPressureAt
          (setup.waterTemperature .initial)) =
      1209 / 10
  saturatedLiquidSpecificVolumeAtOneHundredFiveCelsius :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.saturatedLiquidSpecificVolumeAt
          (setup.waterTemperature .initial)) =
      1047 / 1000000
  saturatedVaporSpecificVolumeAtOneHundredFiveCelsius :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.saturatedVaporSpecificVolumeAt
          (setup.waterTemperature .initial)) =
      1418 / 1000
  lowerTableTemperatureIsSixHundredCelsius :
    temperatureInDegreesCelsius
        setup.tableTemperatureAtSixHundredCelsius = 600
  upperTableTemperatureIsSevenHundredCelsius :
    temperatureInDegreesCelsius
        setup.tableTemperatureAtSevenHundredCelsius = 700
  lowerSuperheatedRowSpecificVolume :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.superheatedSpecificVolumeAt
          (setup.waterPressure .targetPressure)
          setup.tableTemperatureAtSixHundredCelsius) =
      2012 / 1000
  upperSuperheatedRowSpecificVolume :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.superheatedSpecificVolumeAt
          (setup.waterPressure .targetPressure)
          setup.tableTemperatureAtSevenHundredCelsius) =
      2242 / 1000

/-- Positivity and phase-fraction conditions selecting the physical branch. -/
structure HasPhysicalParameters
    (setup : SpringLoadedWaterCylinder) : Prop where
  diameterPositive : 0 < lengthInMeters setup.pistonDiameter
  areaPositive : 0 < areaInSquareMeters setup.pistonArea
  stiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness
  massPositive : 0 < massInKilograms setup.waterMass
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.waterPressure state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.waterVolume state)
  absoluteTemperaturePositive :
    ∀ state, 0 < temperatureInKelvins (setup.waterTemperature state)
  specificVolumePositive :
    ∀ state,
      0 < specificVolumeInCubicMetersPerKilogram
        (setup.waterSpecificVolume state)
  qualityInUnitInterval :
    0 ≤ setup.initialVaporQuality ∧ setup.initialVaporQuality ≤ 1
  engagedCompressionNonnegative :
    ∀ state,
      setup.springEngaged state = true →
        0 ≤ lengthInMeters (setup.springCompression state)
  engagedSpringForceNonnegative :
    ∀ state,
      setup.springEngaged state = true →
        0 ≤ forceInNewtons (setup.springForceMagnitude state)

/-!
Closed-system equilibrium thermodynamics.  The initial saturated-mixture law
uses quality `x` in `v = v_f + x (v_g - v_f)`.  Every state obeys `V = m v`,
and the final superheated state is related to the external water table.  These
laws constrain but do not assign the final temperature.
-/
structure SatisfiesClosedWaterThermodynamics
    (setup : SpringLoadedWaterCylinder) : Prop where
  targetWaterIsSuperheatedVapor :
    setup.waterRegion .targetPressure = .superheatedVapor
  initialSaturationEquilibrium :
    setup.waterPressure .initial =
      setup.waterTable.saturationPressureAt
        (setup.waterTemperature .initial)
  initialQualityMixtureLaw :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterSpecificVolume .initial) =
      specificVolumeInCubicMetersPerKilogram
          (setup.waterTable.saturatedLiquidSpecificVolumeAt
            (setup.waterTemperature .initial)) +
        setup.initialVaporQuality *
          (specificVolumeInCubicMetersPerKilogram
              (setup.waterTable.saturatedVaporSpecificVolumeAt
                (setup.waterTemperature .initial)) -
            specificVolumeInCubicMetersPerKilogram
              (setup.waterTable.saturatedLiquidSpecificVolumeAt
                (setup.waterTemperature .initial)))
  closedMassVolumeLaw :
    ∀ state,
      volumeInCubicMeters (setup.waterVolume state) =
        massInKilograms setup.waterMass *
          specificVolumeInCubicMetersPerKilogram
            (setup.waterSpecificVolume state)
  targetSuperheatedPropertyLaw :
    setup.waterSpecificVolume .targetPressure =
      setup.waterTable.superheatedSpecificVolumeAt
        (setup.waterPressure .targetPressure)
        (setup.waterTemperature .targetPressure)

/-!
Quasistatic spring-loaded piston mechanics in coherent SI readouts.

Before spring contact the piston load is unchanged, so the initial and contact
pressures agree.  Once engaged, piston travel changes the cylinder volume by
`A Δz`, the spring obeys `F = k Δz`, and subtracting the force balance at
first contact gives `(P - P_contact) A = F`.  None of these laws mentions a
temperature answer.
-/
structure SatisfiesSpringLoadedPistonMechanics
    (setup : SpringLoadedWaterCylinder) : Prop where
  circularPistonArea :
    areaInSquareMeters setup.pistonArea =
      Real.pi * (lengthInMeters setup.pistonDiameter / 2) ^ 2
  constantPressureUntilSpringContact :
    setup.waterPressure .firstSpringContact = setup.waterPressure .initial
  zeroCompressionAtFirstContact :
    lengthInMeters (setup.springCompression .firstSpringContact) = 0
  engagedPistonDisplacementLaw :
    ∀ state,
      setup.springEngaged state = true →
        volumeInCubicMeters (setup.waterVolume state) -
            volumeInCubicMeters
              (setup.waterVolume .firstSpringContact) =
          areaInSquareMeters setup.pistonArea *
            lengthInMeters (setup.springCompression state)
  hookeLaw :
    ∀ state,
      setup.springEngaged state = true →
        forceInNewtons (setup.springForceMagnitude state) =
          springStiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters (setup.springCompression state)
  quasistaticPressureIncrement :
    ∀ state,
      setup.springEngaged state = true →
        (pressureInPascals (setup.waterPressure state) -
            pressureInPascals
              (setup.waterPressure .firstSpringContact)) *
            areaInSquareMeters setup.pistonArea =
          forceInNewtons (setup.springForceMagnitude state)

/-!
Local constitutive model for the `200 kPa` superheated-water table.  Specific
volume is strictly increasing with temperature, and values between the
`600 °C` and `700 °C` rows are obtained by linear interpolation.  This is a
general table law on the bracket, not the requested `641 °C` lookup.
-/
structure SatisfiesLocalSuperheatedTableInterpolation
    (setup : SpringLoadedWaterCylinder) : Prop where
  specificVolumeStrictlyIncreasesWithTemperature :
    ∀ temperature₁ temperature₂,
      temperatureInDegreesCelsius temperature₁ <
          temperatureInDegreesCelsius temperature₂ →
        specificVolumeInCubicMetersPerKilogram
            (setup.waterTable.superheatedSpecificVolumeAt
              (setup.waterPressure .targetPressure) temperature₁) <
          specificVolumeInCubicMetersPerKilogram
            (setup.waterTable.superheatedSpecificVolumeAt
              (setup.waterPressure .targetPressure) temperature₂)
  linearInterpolationBetweenReferenceRows :
    ∀ temperature,
      600 ≤ temperatureInDegreesCelsius temperature →
      temperatureInDegreesCelsius temperature ≤ 700 →
      specificVolumeInCubicMetersPerKilogram
          (setup.waterTable.superheatedSpecificVolumeAt
            (setup.waterPressure .targetPressure) temperature) =
        specificVolumeInCubicMetersPerKilogram
            (setup.waterTable.superheatedSpecificVolumeAt
              (setup.waterPressure .targetPressure)
              setup.tableTemperatureAtSixHundredCelsius) +
          ((temperatureInDegreesCelsius temperature - 600) / 100) *
            (specificVolumeInCubicMetersPerKilogram
                (setup.waterTable.superheatedSpecificVolumeAt
                  (setup.waterPressure .targetPressure)
                  setup.tableTemperatureAtSevenHundredCelsius) -
              specificVolumeInCubicMetersPerKilogram
                (setup.waterTable.superheatedSpecificVolumeAt
                  (setup.waterPressure .targetPressure)
                  setup.tableTemperatureAtSixHundredCelsius))

/-! ## Derived table bracket and displayed-answer target -/

/-!
The mechanics and initial mixture data put the final specific volume between
the two adjacent `200 kPa` superheated-water table rows.  This is an
intermediate conclusion, not an assumption of the main theorem.
-/
lemma targetSpecificVolume_lies_between_referenceRows
    (setup : SpringLoadedWaterCylinder)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_reference : MatchesRoundedReferenceWaterData setup)
    (_physical : HasPhysicalParameters setup)
    (_thermodynamics : SatisfiesClosedWaterThermodynamics setup)
    (_mechanics : SatisfiesSpringLoadedPistonMechanics setup) :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.superheatedSpecificVolumeAt
          (setup.waterPressure .targetPressure)
          setup.tableTemperatureAtSixHundredCelsius) <
      specificVolumeInCubicMetersPerKilogram
        (setup.waterSpecificVolume .targetPressure) ∧
    specificVolumeInCubicMetersPerKilogram
        (setup.waterSpecificVolume .targetPressure) <
      specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.superheatedSpecificVolumeAt
          (setup.waterPressure .targetPressure)
          setup.tableTemperatureAtSevenHundredCelsius) := by
  have hInitialVolume :
      volumeInCubicMeters (setup.waterVolume .initial) = 1 / 1000 := by
    have h := _data.initialVolumeIsOneLiter
    unfold volumeInLiters at h
    linarith
  have hContactVolume :
      volumeInCubicMeters (setup.waterVolume .firstSpringContact) =
        3 / 2000 := by
    have h := _data.springContactVolumeIsOnePointFiveLiters
    unfold volumeInLiters at h
    linarith
  have hTargetPressure :
      pressureInPascals (setup.waterPressure .targetPressure) = 200000 := by
    have h := _data.targetPressureIsTwoHundredKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hSaturationPressure :
      pressureInPascals
          (setup.waterTable.saturationPressureAt
            (setup.waterTemperature .initial)) = 120900 := by
    have h :=
      _reference.saturationPressureAtOneHundredFiveCelsiusKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hInitialPressure :
      pressureInPascals (setup.waterPressure .initial) = 120900 := by
    rw [_thermodynamics.initialSaturationEquilibrium]
    exact hSaturationPressure
  have hContactPressure :
      pressureInPascals (setup.waterPressure .firstSpringContact) =
        120900 := by
    rw [_mechanics.constantPressureUntilSpringContact]
    exact hInitialPressure
  have hSpringStiffness :
      springStiffnessInNewtonsPerMeter setup.springStiffness = 100000 := by
    have h := _data.springStiffnessIsOneHundredNewtonsPerMillimeter
    unfold springStiffnessInNewtonsPerMillimeter at h
    linarith
  have hDiameter : lengthInMeters setup.pistonDiameter = 3 / 20 := by
    have h := _data.pistonDiameterIsOneHundredFiftyMillimeters
    unfold lengthInMillimeters at h
    linarith
  have hInitialSpecificVolume :
      specificVolumeInCubicMetersPerKilogram
          (setup.waterSpecificVolume .initial) =
        24109141 / 20000000 := by
    have h := _thermodynamics.initialQualityMixtureLaw
    rw [_reference.saturatedLiquidSpecificVolumeAtOneHundredFiveCelsius,
      _reference.saturatedVaporSpecificVolumeAtOneHundredFiveCelsius,
      _data.initialQualityIsEightyFivePercent] at h
    norm_num at h ⊢
    linarith
  have hInitialMassVolume :=
    _thermodynamics.closedMassVolumeLaw .initial
  have hWaterMass : massInKilograms setup.waterMass = 20000 / 24109141 := by
    rw [hInitialVolume, hInitialSpecificVolume] at hInitialMassVolume
    norm_num at hInitialMassVolume ⊢
    linarith
  have hArea := _mechanics.circularPistonArea
  have hPistonArea :
      areaInSquareMeters setup.pistonArea = 9 * Real.pi / 1600 := by
    rw [hDiameter] at hArea
    nlinarith [hArea]
  have hDisplacement :=
    _mechanics.engagedPistonDisplacementLaw .targetPressure
      _data.springEngagedAtTarget
  have hHooke :=
    _mechanics.hookeLaw .targetPressure _data.springEngagedAtTarget
  have hPressureIncrement :=
    _mechanics.quasistaticPressureIncrement .targetPressure
      _data.springEngagedAtTarget
  rw [hSpringStiffness] at hHooke
  rw [hTargetPressure, hContactPressure] at hPressureIncrement
  have hCompression :
      lengthInMeters (setup.springCompression .targetPressure) =
        (791 / 1000) * areaInSquareMeters setup.pistonArea := by
    nlinarith [hHooke, hPressureIncrement]
  rw [hContactVolume, hCompression, hPistonArea] at hDisplacement
  have hTargetMassVolume :=
    _thermodynamics.closedMassVolumeLaw .targetPressure
  rw [hWaterMass] at hTargetMassVolume
  have hPiBounds : (3 : ℝ) < Real.pi ∧ Real.pi < (3.2 : ℝ) := by
    have hr2Sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hr2Nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hr2Lower : (1.4142 : ℝ) < Real.sqrt 2 := by
      nlinarith only [hr2Sq, hr2Nonnegative]
    have hr2Upper : Real.sqrt 2 < (1.4143 : ℝ) := by
      nlinarith only [hr2Sq, hr2Nonnegative]
    have hr3Argument : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
    have hr3Sq :
        (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
      Real.sq_sqrt hr3Argument
    have hr3Nonnegative : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
      Real.sqrt_nonneg _
    have hr3Lower : (1.8477 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
      nlinarith only [hr2Lower, hr3Sq, hr3Nonnegative]
    have hr3Upper : Real.sqrt (2 + Real.sqrt 2) < (1.8478 : ℝ) := by
      nlinarith only [hr2Upper, hr3Sq, hr3Nonnegative]
    have hsArgument :
        0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt 2) := by
      linarith only [hr3Upper]
    have hsSq :
        (Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
          2 - Real.sqrt (2 + Real.sqrt 2) :=
      Real.sq_sqrt hsArgument
    have hsNonnegative :
        0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
      Real.sqrt_nonneg _
    have hsLower :
        (0.3901 : ℝ) <
          Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
      nlinarith only [hr3Upper, hsSq, hsNonnegative]
    have hsUpper :
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
          (0.3903 : ℝ) := by
      nlinarith only [hr3Lower, hsSq, hsNonnegative]
    have hSinLower : (0.19505 : ℝ) < Real.sin (Real.pi / 16) := by
      rw [Real.sin_pi_div_sixteen]
      linarith
    have hSinUpper : Real.sin (Real.pi / 16) < (0.19515 : ℝ) := by
      rw [Real.sin_pi_div_sixteen]
      linarith
    have hPiDivSixteenNonnegative : 0 ≤ Real.pi / 16 := by positivity
    have hPiDivSixteenLeQuarter : Real.pi / 16 ≤ (1 / 4 : ℝ) := by
      nlinarith only [Real.pi_le_four]
    have hPiDivSixteenAbs : |Real.pi / 16| ≤ 1 := by
      rw [abs_of_nonneg hPiDivSixteenNonnegative]
      linarith
    have hSinApproximation := Real.sin_bound hPiDivSixteenAbs
    have hSinApproximationLower := (abs_le.mp hSinApproximation).1
    have hSinApproximationUpper := (abs_le.mp hSinApproximation).2
    rw [abs_of_nonneg hPiDivSixteenNonnegative] at hSinApproximationLower hSinApproximationUpper
    have hPiLower : (3 : ℝ) < Real.pi := by
      by_contra h
      have hPiLe : Real.pi ≤ (3 : ℝ) := le_of_not_gt h
      have hxLe : Real.pi / 16 ≤ (3 : ℝ) / 16 := by
        linarith only [hPiLe]
      have hxFourthLe :
          (Real.pi / 16) ^ 4 ≤ ((3 : ℝ) / 16) ^ 4 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative hxLe 4
      have hxCubeNonnegative : 0 ≤ (Real.pi / 16) ^ 3 :=
        pow_nonneg hPiDivSixteenNonnegative 3
      nlinarith only [hSinLower, hSinApproximationUpper,
        hPiDivSixteenNonnegative, hxLe, hxCubeNonnegative, hxFourthLe]
    have hPiUpper : Real.pi < (3.2 : ℝ) := by
      by_contra h
      have hPiGe : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
      have hxLower : (1 : ℝ) / 5 ≤ Real.pi / 16 := by
        linarith only [hPiGe]
      have hxCubeUpper :
          (Real.pi / 16) ^ 3 ≤ ((1 : ℝ) / 4) ^ 3 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative
          hPiDivSixteenLeQuarter 3
      have hxFourthUpper :
          (Real.pi / 16) ^ 4 ≤ ((1 : ℝ) / 4) ^ 4 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative
          hPiDivSixteenLeQuarter 4
      nlinarith only [hSinUpper, hSinApproximationLower, hxLower,
        hxCubeUpper, hxFourthUpper]
    exact ⟨hPiLower, hPiUpper⟩
  have hPiSqLower : (3 : ℝ) ^ 2 < Real.pi ^ 2 := by
    have hProduct :
        0 < (Real.pi - 3) * (Real.pi + 3) :=
      mul_pos (sub_pos.mpr hPiBounds.1) (by nlinarith [Real.pi_pos])
    nlinarith
  have hPiSqUpper : Real.pi ^ 2 < (3.2 : ℝ) ^ 2 := by
    have hProduct :
        0 < ((3.2 : ℝ) - Real.pi) * ((3.2 : ℝ) + Real.pi) :=
      mul_pos (sub_pos.mpr hPiBounds.2) (by nlinarith [Real.pi_pos])
    nlinarith
  rw [_reference.lowerSuperheatedRowSpecificVolume,
    _reference.upperSuperheatedRowSpecificVolume]
  constructor
  · norm_num at hDisplacement hTargetMassVolume ⊢
    nlinarith only [hDisplacement, hTargetMassVolume, hPiSqLower]
  · norm_num at hDisplacement hTargetMassVolume ⊢
    nlinarith only [hDisplacement, hTargetMassVolume, hPiSqUpper]

/-!
Strict temperature dependence of the table turns the derived specific-volume
bracket into the interpolation temperature bracket.
-/
lemma targetTemperature_lies_between_referenceRows
    (setup : SpringLoadedWaterCylinder)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_reference : MatchesRoundedReferenceWaterData setup)
    (_physical : HasPhysicalParameters setup)
    (_thermodynamics : SatisfiesClosedWaterThermodynamics setup)
    (_mechanics : SatisfiesSpringLoadedPistonMechanics setup)
    (_interpolation : SatisfiesLocalSuperheatedTableInterpolation setup) :
    600 <
        temperatureInDegreesCelsius
          (setup.waterTemperature .targetPressure) ∧
      temperatureInDegreesCelsius
          (setup.waterTemperature .targetPressure) < 700 := by
  have hSpecific :=
    targetSpecificVolume_lies_between_referenceRows setup _data _reference
      _physical _thermodynamics _mechanics
  rw [_thermodynamics.targetSuperheatedPropertyLaw] at hSpecific
  constructor
  · by_contra hNot
    have hAtMost :
        temperatureInDegreesCelsius
            (setup.waterTemperature .targetPressure) ≤ 600 :=
      le_of_not_gt hNot
    rcases lt_or_eq_of_le hAtMost with hBelow | hEqual
    · have hTemperatureOrder :
          temperatureInDegreesCelsius
              (setup.waterTemperature .targetPressure) <
            temperatureInDegreesCelsius
              setup.tableTemperatureAtSixHundredCelsius := by
        rw [_reference.lowerTableTemperatureIsSixHundredCelsius]
        exact hBelow
      have hVolumeOrder :=
        _interpolation.specificVolumeStrictlyIncreasesWithTemperature
          (setup.waterTemperature .targetPressure)
          setup.tableTemperatureAtSixHundredCelsius hTemperatureOrder
      linarith [hSpecific.1, hVolumeOrder]
    · have hInterpolated :=
        _interpolation.linearInterpolationBetweenReferenceRows
          (setup.waterTemperature .targetPressure)
          (by linarith) (by linarith)
      nlinarith [hSpecific.1, hInterpolated]
  · by_contra hNot
    have hAtLeast :
        700 ≤
          temperatureInDegreesCelsius
            (setup.waterTemperature .targetPressure) :=
      le_of_not_gt hNot
    rcases lt_or_eq_of_le hAtLeast with hAbove | hEqual
    · have hTemperatureOrder :
          temperatureInDegreesCelsius
              setup.tableTemperatureAtSevenHundredCelsius <
            temperatureInDegreesCelsius
              (setup.waterTemperature .targetPressure) := by
        rw [_reference.upperTableTemperatureIsSevenHundredCelsius]
        exact hAbove
      have hVolumeOrder :=
        _interpolation.specificVolumeStrictlyIncreasesWithTemperature
          setup.tableTemperatureAtSevenHundredCelsius
          (setup.waterTemperature .targetPressure) hTemperatureOrder
      linarith [hSpecific.2, hVolumeOrder]
    · have hInterpolated :=
        _interpolation.linearInterpolationBetweenReferenceRows
          (setup.waterTemperature .targetPressure)
          (by linarith) (by linarith)
      nlinarith [hSpecific.2, hInterpolated]

/-- Labels printed beside the four candidate cylinder temperatures. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Celsius value printed beside each answer label. -/
def displayedTemperatureInDegreesCelsius : AnswerChoice → ℝ
  | .A => 407 / 2
  | .B => 265
  | .C => 600
  | .D => 641

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A displayed answer matches the physical result when it is within `2 °C`.
This tolerance covers rounding and linear interpolation of the rounded steam-
table rows while remaining far smaller than the separation between choices.
-/
def TemperatureMatchesDisplayedChoice
    (setup : SpringLoadedWaterCylinder) (choice : AnswerChoice) : Prop :=
  abs
      (temperatureInDegreesCelsius
          (setup.waterTemperature .targetPressure) -
        displayedTemperatureInDegreesCelsius choice) <
    2

/-!
At the `200 kPa` state, the spring displacement fixes the final volume; the
initial quality fixes the closed water mass; and interpolation in the
superheated-water table gives approximately `641 °C`.  Thus D is the unique
displayed choice within `2 °C`.

Blueprint label: `thm:physics:phyx_mini_0446:target`.
-/
theorem final_temperature_matches_recorded_answer_D
    (setup : SpringLoadedWaterCylinder)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_reference : MatchesRoundedReferenceWaterData setup)
    (_physical : HasPhysicalParameters setup)
    (_thermodynamics : SatisfiesClosedWaterThermodynamics setup)
    (_mechanics : SatisfiesSpringLoadedPistonMechanics setup)
    (_interpolation : SatisfiesLocalSuperheatedTableInterpolation setup) :
    TemperatureMatchesDisplayedChoice setup .D ∧
      ∀ choice : AnswerChoice,
        TemperatureMatchesDisplayedChoice setup choice → choice = .D := by
  have hTemperatureBracket :=
    targetTemperature_lies_between_referenceRows setup _data _reference
      _physical _thermodynamics _mechanics _interpolation
  have hInterpolation :=
    _interpolation.linearInterpolationBetweenReferenceRows
      (setup.waterTemperature .targetPressure)
      hTemperatureBracket.1.le hTemperatureBracket.2.le
  rw [← _thermodynamics.targetSuperheatedPropertyLaw,
    _reference.lowerSuperheatedRowSpecificVolume,
    _reference.upperSuperheatedRowSpecificVolume] at hInterpolation
  have hInitialVolume :
      volumeInCubicMeters (setup.waterVolume .initial) = 1 / 1000 := by
    have h := _data.initialVolumeIsOneLiter
    unfold volumeInLiters at h
    linarith
  have hContactVolume :
      volumeInCubicMeters (setup.waterVolume .firstSpringContact) =
        3 / 2000 := by
    have h := _data.springContactVolumeIsOnePointFiveLiters
    unfold volumeInLiters at h
    linarith
  have hTargetPressure :
      pressureInPascals (setup.waterPressure .targetPressure) = 200000 := by
    have h := _data.targetPressureIsTwoHundredKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hSaturationPressure :
      pressureInPascals
          (setup.waterTable.saturationPressureAt
            (setup.waterTemperature .initial)) = 120900 := by
    have h :=
      _reference.saturationPressureAtOneHundredFiveCelsiusKilopascals
    unfold pressureInKilopascals at h
    linarith
  have hInitialPressure :
      pressureInPascals (setup.waterPressure .initial) = 120900 := by
    rw [_thermodynamics.initialSaturationEquilibrium]
    exact hSaturationPressure
  have hContactPressure :
      pressureInPascals (setup.waterPressure .firstSpringContact) =
        120900 := by
    rw [_mechanics.constantPressureUntilSpringContact]
    exact hInitialPressure
  have hSpringStiffness :
      springStiffnessInNewtonsPerMeter setup.springStiffness = 100000 := by
    have h := _data.springStiffnessIsOneHundredNewtonsPerMillimeter
    unfold springStiffnessInNewtonsPerMillimeter at h
    linarith
  have hDiameter : lengthInMeters setup.pistonDiameter = 3 / 20 := by
    have h := _data.pistonDiameterIsOneHundredFiftyMillimeters
    unfold lengthInMillimeters at h
    linarith
  have hInitialSpecificVolume :
      specificVolumeInCubicMetersPerKilogram
          (setup.waterSpecificVolume .initial) =
        24109141 / 20000000 := by
    have h := _thermodynamics.initialQualityMixtureLaw
    rw [_reference.saturatedLiquidSpecificVolumeAtOneHundredFiveCelsius,
      _reference.saturatedVaporSpecificVolumeAtOneHundredFiveCelsius,
      _data.initialQualityIsEightyFivePercent] at h
    norm_num at h ⊢
    linarith
  have hInitialMassVolume :=
    _thermodynamics.closedMassVolumeLaw .initial
  have hWaterMass : massInKilograms setup.waterMass = 20000 / 24109141 := by
    rw [hInitialVolume, hInitialSpecificVolume] at hInitialMassVolume
    norm_num at hInitialMassVolume ⊢
    linarith
  have hArea := _mechanics.circularPistonArea
  have hPistonArea :
      areaInSquareMeters setup.pistonArea = 9 * Real.pi / 1600 := by
    rw [hDiameter] at hArea
    nlinarith [hArea]
  have hDisplacement :=
    _mechanics.engagedPistonDisplacementLaw .targetPressure
      _data.springEngagedAtTarget
  have hHooke :=
    _mechanics.hookeLaw .targetPressure _data.springEngagedAtTarget
  have hPressureIncrement :=
    _mechanics.quasistaticPressureIncrement .targetPressure
      _data.springEngagedAtTarget
  rw [hSpringStiffness] at hHooke
  rw [hTargetPressure, hContactPressure] at hPressureIncrement
  have hCompression :
      lengthInMeters (setup.springCompression .targetPressure) =
        (791 / 1000) * areaInSquareMeters setup.pistonArea := by
    nlinarith [hHooke, hPressureIncrement]
  rw [hContactVolume, hCompression, hPistonArea] at hDisplacement
  have hTargetMassVolume :=
    _thermodynamics.closedMassVolumeLaw .targetPressure
  rw [hWaterMass] at hTargetMassVolume
  have hPiBounds : (3.135 : ℝ) < Real.pi ∧ Real.pi < (3.148 : ℝ) := by
    have hr2Sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hr2Nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hr2Lower : (1.4142 : ℝ) < Real.sqrt 2 := by
      nlinarith only [hr2Sq, hr2Nonnegative]
    have hr2Upper : Real.sqrt 2 < (1.4143 : ℝ) := by
      nlinarith only [hr2Sq, hr2Nonnegative]
    have hr3Argument : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
    have hr3Sq :
        (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
      Real.sq_sqrt hr3Argument
    have hr3Nonnegative : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
      Real.sqrt_nonneg _
    have hr3Lower : (1.8477 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
      nlinarith only [hr2Lower, hr3Sq, hr3Nonnegative]
    have hr3Upper : Real.sqrt (2 + Real.sqrt 2) < (1.8478 : ℝ) := by
      nlinarith only [hr2Upper, hr3Sq, hr3Nonnegative]
    have hsArgument :
        0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt 2) := by
      linarith only [hr3Upper]
    have hsSq :
        (Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
          2 - Real.sqrt (2 + Real.sqrt 2) :=
      Real.sq_sqrt hsArgument
    have hsNonnegative :
        0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
      Real.sqrt_nonneg _
    have hsLower :
        (0.3901 : ℝ) <
          Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
      nlinarith only [hr3Upper, hsSq, hsNonnegative]
    have hsUpper :
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
          (0.3903 : ℝ) := by
      nlinarith only [hr3Lower, hsSq, hsNonnegative]
    have hSinLower : (0.19505 : ℝ) < Real.sin (Real.pi / 16) := by
      rw [Real.sin_pi_div_sixteen]
      linarith
    have hSinUpper : Real.sin (Real.pi / 16) < (0.19515 : ℝ) := by
      rw [Real.sin_pi_div_sixteen]
      linarith
    have hPiDivSixteenNonnegative : 0 ≤ Real.pi / 16 := by positivity
    have hPiDivSixteenLeQuarter : Real.pi / 16 ≤ (1 / 4 : ℝ) := by
      nlinarith only [Real.pi_le_four]
    have hPiDivSixteenAbs : |Real.pi / 16| ≤ 1 := by
      rw [abs_of_nonneg hPiDivSixteenNonnegative]
      linarith
    have hSinApproximation := Real.sin_bound hPiDivSixteenAbs
    have hSinApproximationLower := (abs_le.mp hSinApproximation).1
    have hSinApproximationUpper := (abs_le.mp hSinApproximation).2
    rw [abs_of_nonneg hPiDivSixteenNonnegative] at hSinApproximationLower hSinApproximationUpper
    have hPiGtThree : (3 : ℝ) < Real.pi := by
      by_contra h
      have hPiLe : Real.pi ≤ (3 : ℝ) := le_of_not_gt h
      have hxLe : Real.pi / 16 ≤ (3 : ℝ) / 16 := by
        linarith only [hPiLe]
      have hxFourthLe :
          (Real.pi / 16) ^ 4 ≤ ((3 : ℝ) / 16) ^ 4 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative hxLe 4
      have hxCubeNonnegative : 0 ≤ (Real.pi / 16) ^ 3 :=
        pow_nonneg hPiDivSixteenNonnegative 3
      nlinarith only [hSinLower, hSinApproximationUpper,
        hPiDivSixteenNonnegative, hxLe, hxCubeNonnegative, hxFourthLe]
    have hPiLower : (3.135 : ℝ) < Real.pi := by
      by_contra h
      have hPiLe : Real.pi ≤ (3.135 : ℝ) := le_of_not_gt h
      have hxLower : (3 : ℝ) / 16 ≤ Real.pi / 16 := by
        linarith only [hPiGtThree]
      have hxUpper : Real.pi / 16 ≤ (49 : ℝ) / 250 := by
        linarith only [hPiLe]
      have hxCubeLower :
          ((3 : ℝ) / 16) ^ 3 ≤ (Real.pi / 16) ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hxLower 3
      have hxFourthUpper :
          (Real.pi / 16) ^ 4 ≤ ((49 : ℝ) / 250) ^ 4 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative hxUpper 4
      nlinarith only [hSinLower, hSinApproximationUpper, hPiLe,
        hxCubeLower, hxFourthUpper]
    have hPiLtCoarse : Real.pi < (3.2 : ℝ) := by
      by_contra h
      have hPiGe : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
      have hxLower : (1 : ℝ) / 5 ≤ Real.pi / 16 := by
        linarith only [hPiGe]
      have hxCubeUpper :
          (Real.pi / 16) ^ 3 ≤ ((1 : ℝ) / 4) ^ 3 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative
          hPiDivSixteenLeQuarter 3
      have hxFourthUpper :
          (Real.pi / 16) ^ 4 ≤ ((1 : ℝ) / 4) ^ 4 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative
          hPiDivSixteenLeQuarter 4
      nlinarith only [hSinUpper, hSinApproximationLower, hxLower,
        hxCubeUpper, hxFourthUpper]
    have hPiUpper : Real.pi < (3.148 : ℝ) := by
      by_contra h
      have hPiGe : (3.148 : ℝ) ≤ Real.pi := le_of_not_gt h
      have hxLower : (787 : ℝ) / 4000 ≤ Real.pi / 16 := by
        linarith only [hPiGe]
      have hxUpper : Real.pi / 16 ≤ (1 : ℝ) / 5 := by
        linarith only [hPiLtCoarse]
      have hxCubeUpper :
          (Real.pi / 16) ^ 3 ≤ ((1 : ℝ) / 5) ^ 3 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative hxUpper 3
      have hxFourthUpper :
          (Real.pi / 16) ^ 4 ≤ ((1 : ℝ) / 5) ^ 4 :=
        pow_le_pow_left₀ hPiDivSixteenNonnegative hxUpper 4
      nlinarith only [hSinUpper, hSinApproximationLower, hxLower,
        hxCubeUpper, hxFourthUpper]
    exact ⟨hPiLower, hPiUpper⟩
  have hPiSqLower : (3.135 : ℝ) ^ 2 < Real.pi ^ 2 := by
    have hProduct :
        0 < (Real.pi - (3.135 : ℝ)) * (Real.pi + (3.135 : ℝ)) :=
      mul_pos (sub_pos.mpr hPiBounds.1) (by nlinarith [Real.pi_pos])
    nlinarith
  have hPiSqUpper : Real.pi ^ 2 < (3.148 : ℝ) ^ 2 := by
    have hProduct :
        0 < ((3.148 : ℝ) - Real.pi) * ((3.148 : ℝ) + Real.pi) :=
      mul_pos (sub_pos.mpr hPiBounds.2) (by nlinarith [Real.pi_pos])
    nlinarith
  norm_num at hDisplacement hTargetMassVolume hInterpolation
  have hTargetTemperatureLower :
      639 <
        temperatureInDegreesCelsius
          (setup.waterTemperature .targetPressure) := by
    nlinarith only [hDisplacement, hTargetMassVolume, hInterpolation,
      hPiSqLower]
  have hTargetTemperatureUpper :
      temperatureInDegreesCelsius
          (setup.waterTemperature .targetPressure) < 643 := by
    nlinarith only [hDisplacement, hTargetMassVolume, hInterpolation,
      hPiSqUpper]
  constructor
  · unfold TemperatureMatchesDisplayedChoice
    simp only [displayedTemperatureInDegreesCelsius]
    rw [abs_lt]
    constructor <;> linarith
  · intro choice hChoice
    fin_cases choice
    · unfold TemperatureMatchesDisplayedChoice at hChoice
      norm_num [displayedTemperatureInDegreesCelsius, abs_lt] at hChoice
      exfalso
      linarith
    · unfold TemperatureMatchesDisplayedChoice at hChoice
      norm_num [displayedTemperatureInDegreesCelsius, abs_lt] at hChoice
      exfalso
      linarith
    · unfold TemperatureMatchesDisplayedChoice at hChoice
      norm_num [displayedTemperatureInDegreesCelsius, abs_lt] at hChoice
      exfalso
      linarith
    · rfl

end PhyXMiniProblems.ProblemPhyXMini0446
