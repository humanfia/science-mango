import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0375

open Dimension

/-!
# Heating an ideal gas in a spring-loaded piston

The supplied raster shows gas in a horizontal cylinder, a movable piston, and
a coiled spring between the piston and a fixed wall. The printed labels are
`A = 10 cm²` for the piston area and `1500 N/m` for the spring constant. The
cylinder contains `0.0040 mol` of gas. The spring is unstrained at `20 °C`, and
the gas is then heated quasistatically to `100 °C`.

Physlib dimensionful quantities are used for area, length, volume, pressure,
force, spring constant, and absolute temperature. Real numbers occur only as
unit readouts, calibrated amount-of-substance data, or displayed answer values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative spring constant, with dimension force per length. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude along the horizontal piston axis. -/
abbrev ForceQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read the figure's piston-area label in square centimetres. -/
def areaInSquareCentimeters (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with
    length := LengthUnit.centimeters}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with
    length := LengthUnit.centimeters}).val : ℝ)

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a spring constant in newtons per metre. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-!
Physlib's `Temperature` is an absolute nonnegative temperature whose stored
magnitude uses a zero-preserving unit. Recording the storage unit explicitly
allows a coherent kelvin readout.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-!
The affine Celsius readout is kept separate from the absolute temperature.
The exact rational `5463 / 20` is `273.15` kelvin.
-/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - 5463 / 20

/-!
Physlib currently has no amount-of-substance base dimension. This abstract
carrier and its mole readout preserve the role of gas amount without
identifying the physical quantity itself with a real number.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-! ## Physical states and figure-derived geometry -/

/-- The two equilibrium states named in the problem. -/
inductive ThermalState where
  | initialAtTwentyCelsius
  | heatedAtHundredCelsius
  deriving DecidableEq, Fintype, Repr

/-- Objects visible in the supplied raster. -/
inductive FigureObject where
  | cylinder
  | gasRegion
  | movablePiston
  | coiledSpring
  | fixedRightWall
  deriving DecidableEq, Fintype, Repr

/-- Text labels printed in the supplied raster. -/
inductive FigureTextLabel where
  | pistonAreaTenSquareCentimeters
  | springConstantFifteenHundredNewtonsPerMeter
  deriving DecidableEq, Fintype, Repr

/-- Distinguished endpoints of the spring shown in the raster. -/
inductive SpringEndpoint where
  | pistonRightFace
  | fixedRightWall
  deriving DecidableEq, Repr

/-- Orientation of the piston axis in the supplied drawing. -/
inductive PistonAxisOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Constitutive model used for the spring. -/
inductive SpringModel where
  | idealHookean
  | other
  deriving DecidableEq, Repr

/-!
Qualitative geometry and labels transcribed from the primary raster. The image
supplies no numerical compression readout.
-/
structure SuppliedSpringPistonFigure where
  showsObject : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  springEndpoints : SpringEndpoint × SpringEndpoint
  pistonAxisOrientation : PistonAxisOrientation
  gasIsLeftOfPiston : Bool
  springIsRightOfPiston : Bool

/-!
The physical apparatus and its endpoint observables. In particular, the
heated-state spring compression is an independent physical field rather than
a definition made from an answer choice.
-/
structure SpringPistonSetup (amountScale : AmountOfSubstanceScale) where
  figure : SuppliedSpringPistonFigure
  pistonArea : DimArea
  gasAmount : amountScale.Quantity
  universalGasConstantJoulesPerMoleKelvin : ℝ
  gasPressure : ThermalState → DimPressure
  externalPressure : DimPressure
  gasVolume : ThermalState → VolumeQuantity
  gasTemperature : ThermalState → Temperature
  temperatureStorageUnit : TemperatureUnit
  springConstant : SpringConstantQuantity
  springCompression : ThermalState → LengthQuantity
  springRestoringForce : ThermalState → ForceQuantity
  springModel : SpringModel
  gasSampleIsClosed : Bool
  pistonIsMovable : Bool
  pistonIsFrictionless : Bool
  endpointStatesAreStatic : Bool

/-- Kelvin readout of the gas temperature in a named equilibrium state. -/
def gasTemperatureInKelvin
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) (state : ThermalState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit (setup.gasTemperature state)

/-- Celsius readout of the gas temperature in a named equilibrium state. -/
def gasTemperatureInDegreesCelsius
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) (state : ThermalState) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    (setup.gasTemperature state)

/-- Centimetre readout of the spring compression after heating. -/
def heatedSpringCompressionInCentimeters
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) : ℝ :=
  lengthInCentimeters
    (setup.springCompression .heatedAtHundredCelsius)

/-! ## Assumptions supplied by the scenario, data, and governing laws -/

/-- Qualitative properties stated or implied by the physical scenario. -/
structure MatchesSpringPistonScenario
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) : Prop where
  closedGasSample : setup.gasSampleIsClosed = true
  movablePiston : setup.pistonIsMovable = true
  frictionlessPiston : setup.pistonIsFrictionless = true
  staticEndpointStates : setup.endpointStatesAreStatic = true
  hookeanSpring : setup.springModel = .idealHookean

/-!
Primary-image evidence: all drawn components and both printed labels are
present, the spring runs from the piston to the fixed right wall, and the
piston axis is horizontal with the gas on its left and spring on its right.
-/
structure MatchesSuppliedSpringPistonFigure
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) : Prop where
  everyObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyPrintedLabelShown :
    ∀ label : FigureTextLabel, setup.figure.showsTextLabel label = true
  springAttachmentGeometry :
    setup.figure.springEndpoints =
      (.pistonRightFace, .fixedRightWall)
  horizontalPistonAxis :
    setup.figure.pistonAxisOrientation = .horizontal
  gasOnLeft : setup.figure.gasIsLeftOfPiston = true
  springOnRight : setup.figure.springIsRightOfPiston = true

/-!
Numerical readouts printed in the problem, together with the standard
atmosphere and SI gas-constant calibrations required by the textbook model.
The heated compression and all answer-choice relations are absent.
-/
structure MatchesProblemReadouts
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) : Prop where
  pistonAreaSquareCentimeters :
    areaInSquareCentimeters setup.pistonArea = 10
  gasAmountMoles : amountScale.inMoles setup.gasAmount = 4 / 1000
  springConstantNewtonsPerMeter :
    springConstantInNewtonsPerMeter setup.springConstant = 1500
  initialTemperatureCelsius :
    gasTemperatureInDegreesCelsius setup .initialAtTwentyCelsius = 20
  heatedTemperatureCelsius :
    gasTemperatureInDegreesCelsius setup .heatedAtHundredCelsius = 100
  springInitiallyUnstrained :
    lengthInMeters
      (setup.springCompression .initialAtTwentyCelsius) = 0
  externalPressureIsStandardAtmosphere :
    setup.externalPressure = DimPressure.standardAtmosphere
  universalGasConstantSI :
    setup.universalGasConstantJoulesPerMoleKelvin = 4157 / 500

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalSpringPistonParameters
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) : Prop where
  pistonAreaPositive : 0 < areaInSquareMeters setup.pistonArea
  gasAmountPositive : 0 < amountScale.inMoles setup.gasAmount
  gasConstantPositive :
    0 < setup.universalGasConstantJoulesPerMoleKelvin
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant
  externalPressurePositive :
    0 < pressureInPascals setup.externalPressure
  gasPressurePositive :
    ∀ state, 0 < pressureInPascals (setup.gasPressure state)
  gasVolumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.gasVolume state)
  absoluteTemperaturePositive :
    ∀ state, 0 < gasTemperatureInKelvin setup state

/-!
The ideal-gas equation `PV = nRT` at each static endpoint, expressed in
coherent SI readouts. It is a governing state law and contains no solved
compression value.
-/
structure SatisfiesEndpointIdealGasLaw
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) : Prop where
  idealGasEquation : ∀ state : ThermalState,
    pressureInPascals (setup.gasPressure state) *
        volumeInCubicMeters (setup.gasVolume state) =
      amountScale.inMoles setup.gasAmount *
        setup.universalGasConstantJoulesPerMoleKelvin *
          gasTemperatureInKelvin setup state

/-!
Mechanical and geometric laws of the spring-loaded piston:

* Hooke's law makes the spring-force magnitude `kx`.
* Static force balance equates the gas force on the piston with the sum of
  atmospheric and spring forces.
* Piston sweep increases gas volume by piston area times displacement; because
  the spring is fixed to the right wall, this displacement is also its
  compression relative to the initially unstrained state.

These are general apparatus laws, not a numerical answer for the compression.
-/
structure SatisfiesSpringPistonMechanicalLaws
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) : Prop where
  hookesLaw : ∀ state : ThermalState,
    forceInNewtons (setup.springRestoringForce state) =
      springConstantInNewtonsPerMeter setup.springConstant *
        lengthInMeters (setup.springCompression state)
  staticPistonForceBalance : ∀ state : ThermalState,
    pressureInPascals (setup.gasPressure state) *
        areaInSquareMeters setup.pistonArea =
      pressureInPascals setup.externalPressure *
          areaInSquareMeters setup.pistonArea +
        forceInNewtons (setup.springRestoringForce state)
  pistonSweptVolumeLaw : ∀ state : ThermalState,
    volumeInCubicMeters (setup.gasVolume state) =
      volumeInCubicMeters
          (setup.gasVolume .initialAtTwentyCelsius) +
        areaInSquareMeters setup.pistonArea *
          (lengthInMeters (setup.springCompression state) -
            lengthInMeters
              (setup.springCompression .initialAtTwentyCelsius))

/-! ## Displayed answers and current target -/

/-- Labels of the four compression choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Centimetre value printed beside each answer label. -/
def displayedCompressionInCentimeters : AnswerChoice → ℝ
  | .A => 1
  | .B => 2
  | .C => 5
  | .D => 6 / 5

/-- Distance between the calculated compression and a displayed choice. -/
def distanceFromDisplayedCompression
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) (choice : AnswerChoice) : ℝ :=
  |heatedSpringCompressionInCentimeters setup -
    displayedCompressionInCentimeters choice|

/-!
A choice is the unique nearest displayed compression. This expresses the
rounding inherent in the multiple-choice answer without asserting that the
solution of the calibrated physical equations is exactly an integral number
of centimetres.
-/
def IsUniqueClosestDisplayedCompression
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    other ≠ choice →
      distanceFromDisplayedCompression setup choice <
        distanceFromDisplayedCompression setup other

/-!
Blueprint label: `thm:physics:phyx_mini_0375:target`.

With the supplied data, ideal-gas law, Hooke's law, piston force balance, and
swept-volume geometry, the heated-state compression is uniquely closest to
the displayed `1 cm` value, answer choice A.
-/
theorem springCompression_after_heating
    {amountScale : AmountOfSubstanceScale}
    (setup : SpringPistonSetup amountScale)
    (hScenario : MatchesSpringPistonScenario setup)
    (hFigure : MatchesSuppliedSpringPistonFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalSpringPistonParameters setup)
    (hIdealGas : SatisfiesEndpointIdealGasLaw setup)
    (hMechanics : SatisfiesSpringPistonMechanicalLaws setup) :
    IsUniqueClosestDisplayedCompression setup .A := by
  have hAreaScale :
      UnitChoices.dimScale UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters}
        (L𝓭 * L𝓭) = 10000 := by
    rw [map_mul]
    apply NNReal.eq
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters]
    change (100 : ℝ) * 100 = 10000
    norm_num
  have hAreaConversion :
      areaInSquareCentimeters setup.pistonArea =
        10000 * areaInSquareMeters setup.pistonArea := by
    have h := congrArg (fun z => ((z.val : NNReal) : ℝ))
      (setup.pistonArea.property UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    change _ = ((UnitChoices.dimScale UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}
      (L𝓭 * L𝓭) : NNReal) : ℝ) * _ at h
    rw [hAreaScale] at h
    norm_num [areaInSquareCentimeters, areaInSquareMeters] at h ⊢
    exact h
  have hLengthConversion (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun z => ((z.val : NNReal) : ℝ))
      (length.property UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters,
      lengthInCentimeters, lengthInMeters] at h ⊢
    exact h
  have hArea : areaInSquareMeters setup.pistonArea = 1 / 1000 := by
    nlinarith [hReadouts.pistonAreaSquareCentimeters, hAreaConversion]
  have hExternalPressure :
      pressureInPascals setup.externalPressure = 101325 := by
    rw [hReadouts.externalPressureIsStandardAtmosphere]
    simp [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have hInitialTemperature :
      gasTemperatureInKelvin setup .initialAtTwentyCelsius = 5863 / 20 := by
    have h := hReadouts.initialTemperatureCelsius
    change gasTemperatureInKelvin setup .initialAtTwentyCelsius -
      5463 / 20 = 20 at h
    linarith
  have hHeatedTemperature :
      gasTemperatureInKelvin setup .heatedAtHundredCelsius = 7463 / 20 := by
    have h := hReadouts.heatedTemperatureCelsius
    change gasTemperatureInKelvin setup .heatedAtHundredCelsius -
      5463 / 20 = 100 at h
    linarith
  let x : ℝ :=
    lengthInMeters (setup.springCompression .heatedAtHundredCelsius)
  have hxNonnegative : 0 ≤ x := by
    dsimp [x, lengthInMeters]
    exact NNReal.coe_nonneg _
  have hInitialSpringForce :
      forceInNewtons
          (setup.springRestoringForce .initialAtTwentyCelsius) = 0 := by
    have h := hMechanics.hookesLaw .initialAtTwentyCelsius
    rw [hReadouts.springConstantNewtonsPerMeter,
      hReadouts.springInitiallyUnstrained] at h
    norm_num at h ⊢
    exact h
  have hInitialPressure :
      pressureInPascals
          (setup.gasPressure .initialAtTwentyCelsius) = 101325 := by
    have h := hMechanics.staticPistonForceBalance
      .initialAtTwentyCelsius
    rw [hArea, hExternalPressure, hInitialSpringForce] at h
    norm_num at h
    linarith
  have hInitialVolume :
      volumeInCubicMeters
          (setup.gasVolume .initialAtTwentyCelsius) =
        24372491 / 253312500000 := by
    have h := hIdealGas.idealGasEquation .initialAtTwentyCelsius
    rw [hInitialPressure, hReadouts.gasAmountMoles,
      hReadouts.universalGasConstantSI, hInitialTemperature] at h
    norm_num at h
    linarith
  have hHeatedSpringForce :
      forceInNewtons
          (setup.springRestoringForce .heatedAtHundredCelsius) =
        1500 * x := by
    have h := hMechanics.hookesLaw .heatedAtHundredCelsius
    rw [hReadouts.springConstantNewtonsPerMeter] at h
    simpa [x] using h
  have hHeatedPressure :
      pressureInPascals
          (setup.gasPressure .heatedAtHundredCelsius) =
        101325 + 1500000 * x := by
    have h := hMechanics.staticPistonForceBalance
      .heatedAtHundredCelsius
    rw [hArea, hExternalPressure, hHeatedSpringForce] at h
    norm_num at h
    linarith
  have hHeatedVolume :
      volumeInCubicMeters
          (setup.gasVolume .heatedAtHundredCelsius) =
        24372491 / 253312500000 + x / 1000 := by
    have h := hMechanics.pistonSweptVolumeLaw
      .heatedAtHundredCelsius
    rw [hInitialVolume, hArea,
      hReadouts.springInitiallyUnstrained] at h
    norm_num at h
    simpa [x, div_eq_mul_inv, mul_comm] using h
  have hCompressionEquation :
      1500 * x ^ 2 + (331870003 / 1351000) * x -
        8314 / 3125 = 0 := by
    have h := hIdealGas.idealGasEquation .heatedAtHundredCelsius
    rw [hHeatedPressure, hHeatedVolume, hReadouts.gasAmountMoles,
      hReadouts.universalGasConstantSI, hHeatedTemperature] at h
    norm_num at h
    nlinarith
  have hxLower : 1 / 100 < x := by
    nlinarith [hCompressionEquation, sq_nonneg (x - 1 / 100)]
  have hxUpper : x < 11 / 1000 := by
    nlinarith [hCompressionEquation, sq_nonneg (x - 11 / 1000)]
  have hCompressionConversion :
      heatedSpringCompressionInCentimeters setup = 100 * x := by
    simpa [heatedSpringCompressionInCentimeters, x] using
      hLengthConversion
        (setup.springCompression .heatedAtHundredCelsius)
  have hCompressionLower :
      1 < heatedSpringCompressionInCentimeters setup := by
    nlinarith
  have hCompressionUpper :
      heatedSpringCompressionInCentimeters setup < 11 / 10 := by
    nlinarith
  unfold IsUniqueClosestDisplayedCompression
  intro other hOther
  cases other with
  | A =>
      exact (hOther rfl).elim
  | B =>
      unfold distanceFromDisplayedCompression
      simp only [displayedCompressionInCentimeters]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
  | C =>
      unfold distanceFromDisplayedCompression
      simp only [displayedCompressionInCentimeters]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
  | D =>
      unfold distanceFromDisplayedCompression
      simp only [displayedCompressionInCentimeters]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0375
