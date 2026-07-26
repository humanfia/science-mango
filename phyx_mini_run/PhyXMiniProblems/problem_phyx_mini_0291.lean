import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0291

open Dimension

/-!
# Period of a transverse wave on a string

A sinusoidal transverse wave travels in the negative `x` direction on a
uniform string. At `t = 0`, the supplied displacement-versus-position graph
shows successive crests separated by `40 cm`. The vertical scale is
`y_s = 4.0 cm`; reading the primary raster's grid places the crests at
`5 cm` and the trough at `-5 cm`. The string tension is `3.6 N`, and its
linear mass density is `25 g/m`.

Physical quantities are represented by Physlib's unit-independent
`Dimensionful` type. Real numbers occur only as readouts in explicitly chosen
units, graph coordinates, and displayed answer values.
-/

/-! ## Dimensionful physical quantities and their readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional position or transverse displacement. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Mass per unit length of the uniform string. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A tensile force, with dimension `mass * length / time^2`. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- The nonnegative magnitude of the transverse-wave propagation velocity. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed position or displacement in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read linear mass density in selected mass-per-length units. -/
def linearMassDensityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : LinearMassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read tension in the coherent force unit induced by the base units. -/
def tensionReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (tension : TensionQuantity) : ℝ :=
  ((tension {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read wave speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimeter readout used by both axes of the supplied graph. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Linear-density readout in grams per meter, as printed in the problem. -/
def linearMassDensityInGramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  linearMassDensityReadout MassUnit.grams LengthUnit.meters density

/-- SI linear-density readout in kilograms per meter. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  linearMassDensityReadout MassUnit.kilograms LengthUnit.meters density

/-- SI tension readout in newtons. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  tensionReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds tension

/-- SI speed readout in meters per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Scenario and primary-figure data -/

/-- The material object supporting the wave. -/
inductive WaveMediumKind where
  | uniformString
  deriving DecidableEq, Repr

/-- The stated waveform and polarization. -/
inductive WaveMotionKind where
  | sinusoidalTransverse
  deriving DecidableEq, Repr

/-- Direction of travel along the horizontal coordinate axis. -/
inductive PropagationDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Symbols printed beside the two axes in the primary raster. -/
inductive GraphAxisSymbol where
  | x
  | y
  deriving DecidableEq, Repr

/-- Text labels visible in the supplied graph. -/
inductive FigureLabel where
  | horizontalAxisX
  | verticalAxisY
  | positiveScaleYs
  | negativeScaleYs
  | originZero
  | positionTwenty
  | positionForty
  deriving DecidableEq, Repr

/-- Grid-readable points spanning one complete spatial cycle at `t = 0`. -/
inductive GraphPointLabel where
  | leftCrest
  | descendingZero
  | trough
  | ascendingZero
  | rightCrest
  deriving DecidableEq, Repr

/-- Qualitative shape of the displacement-versus-position trace. -/
inductive DisplacementCurveShape where
  | sinusoidal
  | other
  deriving DecidableEq, Repr

/-!
Idealized `(x,y)` coordinates read from the primary grid, in centimeters.
The two crests are `40 cm` apart. Since `y_s = 4 cm` marks the horizontal
grid line one division below the crest, the plotted amplitude is `5 cm`.
-/
def displayedGraphCoordinate : GraphPointLabel → ℝ × ℝ
  | .leftCrest => (5, 5)
  | .descendingZero => (15, 0)
  | .trough => (25, -5)
  | .ascendingZero => (35, 0)
  | .rightCrest => (45, 5)

/-- Dimensionful axes, marked grid points, and metadata of the primary graph. -/
structure StringWaveFigure where
  horizontalAxisSymbol : GraphAxisSymbol
  verticalAxisSymbol : GraphAxisSymbol
  horizontalAxisUnit : LengthUnit
  verticalAxisUnit : LengthUnit
  labelShown : FigureLabel → Bool
  snapshotTime : TimeQuantity
  verticalScaleYs : LengthQuantity
  markedPosition : GraphPointLabel → SignedLengthQuantity
  markedDisplacement : GraphPointLabel → SignedLengthQuantity
  successiveCrestPair : GraphPointLabel × GraphPointLabel
  horizontalAxisMinimumCentimeters : ℝ
  horizontalAxisMaximumCentimeters : ℝ
  verticalAxisMinimumCentimeters : ℝ
  verticalAxisMaximumCentimeters : ℝ
  curveShape : DisplacementCurveShape

/-!
The independent physical observables of the traveling wave. In particular,
the requested period is not defined from an answer choice or target value.
-/
structure TravelingStringWaveSetup where
  mediumKind : WaveMediumKind
  motionKind : WaveMotionKind
  propagationDirection : PropagationDirection
  stringTension : TensionQuantity
  stringLinearMassDensity : LinearMassDensityQuantity
  displacementAt : SignedLengthQuantity → TimeQuantity → SignedLengthQuantity
  amplitude : LengthQuantity
  wavelength : LengthQuantity
  propagationSpeed : SpeedQuantity
  period : TimeQuantity
  figure : StringWaveFigure

/-- Categorical facts stated in the physical scenario. -/
structure MatchesTravelingWaveScenario
    (setup : TravelingStringWaveSetup) : Prop where
  mediumIsUniformString : setup.mediumKind = .uniformString
  waveIsSinusoidalTransverse : setup.motionKind = .sinusoidalTransverse
  travelsInNegativeXDirection : setup.propagationDirection = .negativeX

/-!
Numerical readouts supplied by the prose. No period, speed, or wavelength
value is present here.
-/
structure MatchesProblemReadouts (setup : TravelingStringWaveSetup) : Prop where
  tensionIsThreePointSixNewtons :
    tensionInNewtons setup.stringTension = 18 / 5
  linearDensityIsTwentyFiveGramsPerMeter :
    linearMassDensityInGramsPerMeter setup.stringLinearMassDensity = 25
  verticalScaleIsFourCentimeters :
    lengthInCentimeters setup.figure.verticalScaleYs = 4

/-!
Primary-image evidence. The wavelength relation is a geometric readout from
the distinguished pair of successive crests, not a premise about the period.
-/
structure MatchesSuppliedFigure (setup : TravelingStringWaveSetup) : Prop where
  horizontalAxisIsPosition : setup.figure.horizontalAxisSymbol = .x
  verticalAxisIsDisplacement : setup.figure.verticalAxisSymbol = .y
  horizontalAxisUsesCentimeters :
    setup.figure.horizontalAxisUnit = LengthUnit.centimeters
  verticalAxisUsesCentimeters :
    setup.figure.verticalAxisUnit = LengthUnit.centimeters
  allPrintedLabelsShown : ∀ label : FigureLabel,
    setup.figure.labelShown label = true
  snapshotIsAtTimeZero : timeInSeconds setup.figure.snapshotTime = 0
  horizontalAxisMinimum : setup.figure.horizontalAxisMinimumCentimeters = 0
  horizontalAxisMaximum : setup.figure.horizontalAxisMaximumCentimeters = 50
  verticalAxisMinimum : setup.figure.verticalAxisMinimumCentimeters = -5
  verticalAxisMaximum : setup.figure.verticalAxisMaximumCentimeters = 5
  curveIsSinusoidal : setup.figure.curveShape = .sinusoidal
  markedCoordinates :
    ∀ point : GraphPointLabel,
      (signedLengthReadout setup.figure.horizontalAxisUnit
          (setup.figure.markedPosition point),
        signedLengthReadout setup.figure.verticalAxisUnit
          (setup.figure.markedDisplacement point)) =
        displayedGraphCoordinate point
  curvePassesThroughMarkedPoints :
    ∀ point : GraphPointLabel,
      setup.displacementAt (setup.figure.markedPosition point)
          setup.figure.snapshotTime =
        setup.figure.markedDisplacement point
  amplitudeFromGrid : lengthInCentimeters setup.amplitude = 5
  displayedCrestsAreSuccessive :
    setup.figure.successiveCrestPair = (.leftCrest, .rightCrest)
  wavelengthFromSuccessiveCrests :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.wavelength =
        signedLengthReadout unit
            (setup.figure.markedPosition .rightCrest) -
          signedLengthReadout unit
            (setup.figure.markedPosition .leftCrest)

/-- Positivity and nondegeneracy of the physical wave parameters. -/
structure HasPhysicalStringWaveParameters
    (setup : TravelingStringWaveSetup) : Prop where
  tensionPositive : 0 < tensionInNewtons setup.stringTension
  densityPositive :
    0 < linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity
  amplitudePositive : 0 < lengthInMeters setup.amplitude
  scalePositive : 0 < lengthInMeters setup.figure.verticalScaleYs
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  propagationSpeedPositive :
    0 < speedInMetersPerSecond setup.propagationSpeed
  periodPositive : 0 < timeInSeconds setup.period

/-!
The two governing laws used by the textbook solution, in arbitrary coherent
units: `T = μ v²` and `λ = v P`. These general relations do not assign any
numerical period or answer label.
-/
structure SatisfiesUniformStringWaveLaws
    (setup : TravelingStringWaveSetup) : Prop where
  tensionEqualsLinearDensityTimesSpeedSquared :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      tensionReadout massUnit lengthUnit timeUnit setup.stringTension =
        linearMassDensityReadout massUnit lengthUnit
            setup.stringLinearMassDensity *
          speedReadout lengthUnit timeUnit setup.propagationSpeed ^ 2
  wavelengthEqualsSpeedTimesPeriod :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      lengthReadout lengthUnit setup.wavelength =
        speedReadout lengthUnit timeUnit setup.propagationSpeed *
          timeReadout timeUnit setup.period

/-! ## Derived quantities and formalization target -/

/-- Successive crests at `5 cm` and `45 cm` give wavelength `2/5 m`. -/
lemma wavelengthInMeters_eq_two_fifths
    (setup : TravelingStringWaveSetup)
    (_figure : MatchesSuppliedFigure setup) :
    lengthInMeters setup.wavelength = 2 / 5 := by
  have hleft := _figure.markedCoordinates .leftCrest
  have hright := _figure.markedCoordinates .rightCrest
  rw [_figure.horizontalAxisUsesCentimeters] at hleft hright
  have hleftcm : signedLengthReadout LengthUnit.centimeters
      (setup.figure.markedPosition .leftCrest) = 5 := by
    simpa [displayedGraphCoordinate] using congrArg Prod.fst hleft
  have hrightcm : signedLengthReadout LengthUnit.centimeters
      (setup.figure.markedPosition .rightCrest) = 45 := by
    simpa [displayedGraphCoordinate] using congrArg Prod.fst hright
  have hcm : lengthInCentimeters setup.wavelength = 40 := by
    rw [lengthInCentimeters,
      _figure.wavelengthFromSuccessiveCrests LengthUnit.centimeters,
      hrightcm, hleftcm]
    norm_num
  have hConversion (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value : WithDim L𝓭 NNReal => (value.val : ℝ))
      (length.2
        ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
        ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices))
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at h ⊢
    exact h
  nlinarith [hcm, hConversion setup.wavelength]

/-- The string-wave law and prose readouts give propagation speed `12 m/s`. -/
lemma propagationSpeedInMetersPerSecond_eq_twelve
    (setup : TravelingStringWaveSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_physical : HasPhysicalStringWaveParameters setup)
    (_laws : SatisfiesUniformStringWaveLaws setup) :
    speedInMetersPerSecond setup.propagationSpeed = 12 := by
  have hDensityConversion (density : LinearMassDensityQuantity) :
      linearMassDensityInGramsPerMeter density =
        1000 * linearMassDensityInKilogramsPerMeter density := by
    have h := congrArg (fun value : WithDim (M𝓭 * L𝓭⁻¹) NNReal =>
        (value.val : ℝ))
      (density.2 UnitChoices.SI
        ({UnitChoices.SI with mass := MassUnit.grams} : UnitChoices))
    norm_num [linearMassDensityInGramsPerMeter,
      linearMassDensityInKilogramsPerMeter, linearMassDensityReadout,
      UnitChoices.dimScale, M𝓭, L𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, LengthUnit.meters,
      NNReal.smul_def] at h ⊢
    exact h
  have hdensity := hDensityConversion setup.stringLinearMassDensity
  rw [_readouts.linearDensityIsTwentyFiveGramsPerMeter] at hdensity
  have hlaw := _laws.tensionEqualsLinearDensityTimesSpeedSquared
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change tensionInNewtons setup.stringTension =
    linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity *
      speedInMetersPerSecond setup.propagationSpeed ^ 2 at hlaw
  rw [_readouts.tensionIsThreePointSixNewtons] at hlaw
  nlinarith [_physical.propagationSpeedPositive]

/-- Combining `λ = 2/5 m`, `v = 12 m/s`, and `λ = v P` gives `P = 1/30 s`. -/
lemma wavePeriodInSeconds_eq_one_thirtieth
    (setup : TravelingStringWaveSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedFigure setup)
    (_physical : HasPhysicalStringWaveParameters setup)
    (_laws : SatisfiesUniformStringWaveLaws setup) :
    timeInSeconds setup.period = 1 / 30 := by
  have hwavelength := wavelengthInMeters_eq_two_fifths setup _figure
  have hspeed := propagationSpeedInMetersPerSecond_eq_twelve
    setup _readouts _physical _laws
  have hlaw := _laws.wavelengthEqualsSpeedTimesPeriod
    LengthUnit.meters TimeUnit.seconds
  change lengthInMeters setup.wavelength =
    speedInMetersPerSecond setup.propagationSpeed *
      timeInSeconds setup.period at hlaw
  rw [hwavelength, hspeed] at hlaw
  nlinarith

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed period values, in seconds. -/
def displayedPeriodInSeconds : AnswerChoice → ℝ
  | .A => 19 / 1000
  | .B => 28 / 1000
  | .C => 45 / 1000
  | .D => 33 / 1000

/-- The answer label recorded by the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed answer is at least as close as every other displayed value. -/
def IsNearestDisplayedPeriod
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |timeInSeconds period - displayedPeriodInSeconds choice| ≤
      |timeInSeconds period - displayedPeriodInSeconds other|

/-!
The ideal physical model gives the exact period `1/30 s`, approximately
`0.033 s`. Among the four displayed values, choice D is uniquely nearest.

This formalizes blueprint label `thm:physics:phyx_mini_0291:target`.
Neither the exact period, `0.033 s`, nor answer D occurs in any scenario,
readout, figure, positivity, or governing-law premise.
-/
theorem problem_phyx_mini_0291
    (setup : TravelingStringWaveSetup)
    (_scenario : MatchesTravelingWaveScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedFigure setup)
    (_physical : HasPhysicalStringWaveParameters setup)
    (_laws : SatisfiesUniformStringWaveLaws setup) :
    timeInSeconds setup.period = 1 / 30 ∧
      IsNearestDisplayedPeriod setup.period .D ∧
      ∀ choice : AnswerChoice,
        IsNearestDisplayedPeriod setup.period choice ↔ choice = .D := by
  have hperiod := wavePeriodInSeconds_eq_one_thirtieth
    setup _readouts _figure _physical _laws
  refine ⟨hperiod, ?_, ?_⟩
  · intro other
    rw [hperiod]
    cases other <;> norm_num [displayedPeriodInSeconds]
  · intro choice
    constructor
    · intro hnearest
      cases choice with
      | A =>
          have h := hnearest .D
          rw [hperiod] at h
          norm_num [displayedPeriodInSeconds] at h
      | B =>
          have h := hnearest .D
          rw [hperiod] at h
          norm_num [displayedPeriodInSeconds] at h
      | C =>
          have h := hnearest .D
          rw [hperiod] at h
          norm_num [displayedPeriodInSeconds] at h
      | D => rfl
    · intro hchoice
      subst choice
      intro other
      rw [hperiod]
      cases other <;> norm_num [displayedPeriodInSeconds]

end PhyXMiniProblems.ProblemPhyXMini0291
