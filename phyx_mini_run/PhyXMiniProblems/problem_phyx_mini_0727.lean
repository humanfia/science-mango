import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/-!
# PhyX mini problem 0727: the Earth--Sun distance in light-years

The physical distances, duration, and speed below use Physlib's dimensionful
quantity API.  Real numbers occur only as explicitly named numerical readouts
in selected units, as dimensionless answer values, or as error tolerances for
the rounded data printed in the problem.

The auxiliary image is retained as an isosceles parsec diagram: its short base
is labelled `1 AU`, its two long sides are labelled `1 pc`, and its apex angle
is labelled exactly one arcsecond.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0727

open Dimension

/-- A physical length, independent of the units used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical duration, independent of the units used to read it. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical speed with Physlib's length-per-time dimension.  This is the
actual codomain used by `DimSpeed.speedOfLight` in the pinned Physlib version. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A unit system whose selected length unit is `unit` and whose other units
are SI units. -/
noncomputable def unitsWithLength (unit : LengthUnit) : UnitChoices :=
  { UnitChoices.SI with length := unit }

/-- A unit system whose selected time unit is `unit` and whose other units are
SI units. -/
noncomputable def unitsWithTime (unit : TimeUnit) : UnitChoices :=
  { UnitChoices.SI with time := unit }

/-- A unit system for speed readouts in `lengthUnit / timeUnit`. -/
noncomputable def unitsForSpeed
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : UnitChoices :=
  { UnitChoices.SI with length := lengthUnit, time := timeUnit }

/-- The real numerical readout of a physical length in the selected unit. -/
def lengthReadout (unit : LengthUnit) (quantity : LengthQuantity) : ℝ :=
  ((quantity (unitsWithLength unit)).val : ℝ)

/-- The real numerical readout of a physical duration in the selected unit. -/
def timeReadout (unit : TimeUnit) (quantity : TimeQuantity) : ℝ :=
  ((quantity (unitsWithTime unit)).val : ℝ)

/-- The real numerical readout of a physical speed in the selected quotient
of a length unit by a time unit. -/
def speedReadout
    (lengthUnit : LengthUnit)
    (timeUnit : TimeUnit)
    (quantity : SpeedQuantity) : ℝ :=
  ((quantity (unitsForSpeed lengthUnit timeUnit)).val : ℝ)

/-- A Julian year, the `365.25`-day duration used in the standard definition
of a light-year. -/
noncomputable def julianYears : TimeUnit :=
  TimeUnit.scale 365.25 TimeUnit.days

/-- One arcsecond as a physical angle: `π / (180 * 60 * 60)` radians. -/
noncomputable def oneArcsecond : Real.Angle :=
  (((Real.pi / (180 * 60 * 60)) : ℝ) : Real.Angle)

/-- `actual` lies within the stated absolute tolerance of a rounded reported
readout. -/
def Approximately (actual reported absoluteTolerance : ℝ) : Prop :=
  0 ≤ absoluteTolerance ∧ |actual - reported| ≤ absoluteTolerance

/-- The three length labels and the angle label visible in the supplied
parsec diagram. -/
structure ParsecFigure where
  /-- The short, nearly vertical segment labelled `1 AU`. -/
  base : LengthQuantity
  /-- The upper long side labelled `1 pc`. -/
  upperSide : LengthQuantity
  /-- The lower long side labelled `1 pc`. -/
  lowerSide : LengthQuantity
  /-- The angle between the two long sides, labelled exactly one second. -/
  apexAngle : Real.Angle

/-- The physical quantities named in the text, together with a minimal
interface for the angular subtense used to define a parsec. -/
structure AstronomicalDistanceSetup where
  earthSunDistance : LengthQuantity
  oneAstronomicalUnit : LengthQuantity
  oneParsec : LengthQuantity
  oneLightYear : LengthQuantity
  vacuumLightSpeed : SpeedQuantity
  oneYear : TimeQuantity
  /-- Angular size of the first length when viewed from the second distance. -/
  angularSubtense : LengthQuantity → LengthQuantity → Real.Angle
  parsecFigure : ParsecFigure

/-- Constant-speed travel obeys `distance = speed * duration`.  The equality
is required in every common unit system, so it relates physical quantities
rather than one privileged scalar representation. -/
def SatisfiesConstantSpeedTravelLaw
    (distance : LengthQuantity)
    (speed : SpeedQuantity)
    (duration : TimeQuantity) : Prop :=
  ∀ units : UnitChoices,
    ((distance units).val : ℝ) =
      ((speed units).val : ℝ) * ((duration units).val : ℝ)

/-- Governing astronomical definitions used in the problem.  These fields
state that the AU is the Earth--Sun distance, that a light-year obeys the
vacuum-light travel law for one year, and that a parsec gives a one-arcsecond
subtense to one AU.  They do not state the requested light-year conversion. -/
structure SatisfiesAstronomicalDefinitions
    (setup : AstronomicalDistanceSetup) : Prop where
  astronomicalUnitIsEarthSunDistance :
    setup.oneAstronomicalUnit = setup.earthSunDistance
  lightYearTravelLaw :
    SatisfiesConstantSpeedTravelLaw
      setup.oneLightYear setup.vacuumLightSpeed setup.oneYear
  parsecAngularDefinition :
    setup.angularSubtense setup.oneAstronomicalUnit setup.oneParsec =
      oneArcsecond

/-- Numerical unit calibrations and rounded readouts stated in the problem.
The tolerances make the word “about” and the rounded speed `186000 mi/s`
explicit, while the named unit quantities themselves use Physlib's standard
AU, parsec, light-year, mile, second, and speed-of-light definitions. -/
structure MatchesReportedAstronomicalData
    (setup : AstronomicalDistanceSetup) : Prop where
  oneAstronomicalUnitReadout :
    lengthReadout LengthUnit.astronomicalUnits
      setup.oneAstronomicalUnit = 1
  oneParsecReadout :
    lengthReadout LengthUnit.parsecs setup.oneParsec = 1
  oneLightYearReadout :
    lengthReadout LengthUnit.lightYears setup.oneLightYear = 1
  oneJulianYearReadout :
    timeReadout julianYears setup.oneYear = 1
  vacuumLightSpeedIsStandard :
    setup.vacuumLightSpeed = DimSpeed.speedOfLight
  earthSunMilesReported :
    Approximately
      (lengthReadout LengthUnit.miles setup.earthSunDistance)
      (92.9 * 10 ^ 6)
      (0.1 * 10 ^ 6)
  lightSpeedMilesPerSecondReported :
    Approximately
      (speedReadout LengthUnit.miles TimeUnit.seconds
        setup.vacuumLightSpeed)
      186000
      500

/-- Primary-image readouts.  The supplied diagram has a `1 AU` base, two
`1 pc` sides, and a one-arcsecond apex angle. -/
structure MatchesParsecFigure (setup : AstronomicalDistanceSetup) : Prop where
  baseLabel :
    setup.parsecFigure.base = setup.oneAstronomicalUnit
  upperSideLabel :
    setup.parsecFigure.upperSide = setup.oneParsec
  lowerSideLabel :
    setup.parsecFigure.lowerSide = setup.oneParsec
  apexAngleLabel :
    setup.parsecFigure.apexAngle = oneArcsecond

/-- The four displayed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless number of light-years printed beside each answer. -/
def AnswerChoice.valueInLightYears : AnswerChoice → ℝ
  | .A => 1.26 / 10 ^ 5
  | .B => 1.42 / 10 ^ 5
  | .C => 1.57 / 10 ^ 5
  | .D => 1.74 / 10 ^ 5

/-- Dataset metadata: the recorded answer label is C.  This is not a premise
of the conversion theorem. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A choice is uniquely closest to the physical distance's light-year
readout among the four printed alternatives. -/
def IsNearestAnswerChoice
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |lengthReadout LengthUnit.lightYears distance -
          choice.valueInLightYears| <
        |lengthReadout LengthUnit.lightYears distance -
          otherChoice.valueInLightYears|

/--
**Physics formalization target
(`thm:physics:phyx_mini_0727:target`).**

The Earth--Sun distance is one AU, so its exact light-year readout is the
ratio of Physlib's AU and light-year scales.  That value is within
`0.02 × 10⁻⁵ ly` of the displayed `1.57 × 10⁻⁵ ly` and is uniquely closest
to answer C.
-/
theorem earthSunDistanceInLightYears
    (setup : AstronomicalDistanceSetup)
    (_definitions : SatisfiesAstronomicalDefinitions setup)
    (_reportedData : MatchesReportedAstronomicalData setup)
    (_figure : MatchesParsecFigure setup) :
    lengthReadout LengthUnit.lightYears setup.earthSunDistance =
        LengthUnit.astronomicalUnits.val / LengthUnit.lightYears.val ∧
      Approximately
        (lengthReadout LengthUnit.lightYears setup.earthSunDistance)
        AnswerChoice.C.valueInLightYears
        (0.02 / 10 ^ 5) ∧
      IsNearestAnswerChoice setup.earthSunDistance .C := by
  have hAU :
      lengthReadout LengthUnit.astronomicalUnits setup.earthSunDistance = 1 := by
    rw [← _definitions.astronomicalUnitIsEarthSunDistance]
    exact _reportedData.oneAstronomicalUnitReadout
  have hscale := congrArg WithDim.val (setup.earthSunDistance.property
    (unitsWithLength LengthUnit.astronomicalUnits)
    (unitsWithLength LengthUnit.lightYears))
  have hscale' :
      lengthReadout LengthUnit.lightYears setup.earthSunDistance =
        ((LengthUnit.astronomicalUnits / LengthUnit.lightYears : NNReal) : ℝ) *
          lengthReadout LengthUnit.astronomicalUnits
            setup.earthSunDistance := by
    simpa [lengthReadout, UnitChoices.dimScale, unitsWithLength,
      WithDim.dim_apply, NNReal.smul_def] using hscale
  have hconversion :
      lengthReadout LengthUnit.lightYears setup.earthSunDistance =
        LengthUnit.astronomicalUnits.val / LengthUnit.lightYears.val := by
    calc
      lengthReadout LengthUnit.lightYears setup.earthSunDistance =
          ((LengthUnit.astronomicalUnits /
            LengthUnit.lightYears : NNReal) : ℝ) := by
        simpa [hAU] using hscale'
      _ = LengthUnit.astronomicalUnits.val /
          LengthUnit.lightYears.val := rfl
  refine ⟨hconversion, ?_, ?_⟩
  · rw [hconversion]
    norm_num [Approximately, AnswerChoice.valueInLightYears,
      LengthUnit.astronomicalUnits, LengthUnit.lightYears,
      LengthUnit.scale, LengthUnit.meters]
  · intro otherChoice hne
    rw [hconversion]
    cases otherChoice with
    | A =>
        norm_num [AnswerChoice.valueInLightYears,
          LengthUnit.astronomicalUnits, LengthUnit.lightYears,
          LengthUnit.scale, LengthUnit.meters]
    | B =>
        norm_num [AnswerChoice.valueInLightYears,
          LengthUnit.astronomicalUnits, LengthUnit.lightYears,
          LengthUnit.scale, LengthUnit.meters]
    | C => exact (hne rfl).elim
    | D =>
        norm_num [AnswerChoice.valueInLightYears,
          LengthUnit.astronomicalUnits, LengthUnit.lightYears,
          LengthUnit.scale, LengthUnit.meters]

end PhyXMiniProblems.ProblemPhyXMini0727
