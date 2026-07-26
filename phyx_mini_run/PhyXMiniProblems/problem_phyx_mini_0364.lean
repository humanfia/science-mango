import Mathlib.Analysis.Real.Sqrt
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0364

open Dimension

/-!
# Trapped-air length in a slowly immersed closed-top pipe

A straight `3.0 m` pipe is open at its lower end and closed at its upper end.
It is pushed vertically and slowly into water until its closed upper end is
level with the outside water surface. Water entering the lower end compresses
the fixed amount of trapped air. The final air--water interface is therefore
as far below the outside surface as the trapped-air column is long.

The textbook model combines constant-area pipe geometry, isothermal
pressure--volume conservation, and the hydrostatic pressure increase
`rho * g * depth`. Physical lengths, areas, volumes, pressures, mass density,
and acceleration are represented by unit-independent Physlib quantities.
Real numbers occur only as coherent unit readouts and displayed answer values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- The physical dimension of volume, `L^3`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of mass density, `M L^-3`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical volume in the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read pressure in the coherent unit induced by selected base units. -/
def pressureReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (pressure : DimPressure) : ℝ :=
  (pressure {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Read mass density in a selected mass unit per selected length unit cubed. -/
def densityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : MassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read acceleration in selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Square-meter readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Cubic-meter readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  pressureReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds pressure

/-- Kilogram-per-cubic-meter readout of a mass density. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  densityReadout MassUnit.kilograms LengthUnit.meters density

/-- Meter-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Physical states, apparatus roles, and figure labels -/

/-- The two physical states pictured in the supplied before/after figure. -/
inductive PipeState where
  | beforeImmersion
  | afterCompression
  deriving DecidableEq, Fintype, Repr

/-- The liquid surrounding and entering the pipe. -/
inductive PipeLiquid where
  | water
  | other
  deriving DecidableEq, Repr

/-- The gas occupying the pipe. -/
inductive PipeGas where
  | air
  | other
  deriving DecidableEq, Repr

/-- How the pipe is moved from the before state to the after state. -/
inductive ImmersionProtocol where
  | slowlyStraightDown
  | other
  deriving DecidableEq, Repr

/-- Thermal model for the slowly compressed trapped air. -/
inductive CompressionProtocol where
  | quasistaticIsothermal
  | other
  deriving DecidableEq, Repr

/-- Literal labels visible in the supplied bitmap. -/
inductive FigureTextLabel where
  | before
  | after
  | threePointZeroMeters
  | capitalL
  deriving DecidableEq, Fintype, Repr

/-- The two dimensionful length marks drawn in the figure. -/
inductive FigureLengthMark where
  | overallPipeLength
  | finalAirLengthL
  deriving DecidableEq, Fintype, Repr

/-- Physical roles of the length marks in the supplied figure. -/
inductive FigureLengthRole where
  | fullPipeLength
  | trappedAirColumnLength
  deriving DecidableEq, Repr

/-!
Dimensionful and qualitative data represented by the primary image. The
`L` arrow has no numerical value stored here; it is an independently modeled
physical length that the theorem must determine.
-/
structure ClosedTopPipeFigure where
  labelShown : FigureTextLabel → Bool
  markedLength : FigureLengthMark → LengthQuantity
  markedLengthRole : FigureLengthMark → FigureLengthRole
  beforePipeAboveWater : Bool
  afterPipeSubmergedInWater : Bool
  afterOutsideWaterSurfaceShown : Bool
  afterInternalAirWaterInterfaceShown : Bool
  lengthArrowsVertical : Bool

/-!
Independent physical quantities in the immersion experiment. In particular,
the final trapped-air length and pressure are fields rather than definitions
made from the recorded answer or from the desired closed form.
-/
structure ClosedTopPipeSetup where
  figure : ClosedTopPipeFigure
  liquid : PipeLiquid
  trappedGas : PipeGas
  immersionProtocol : ImmersionProtocol
  compressionProtocol : CompressionProtocol
  pipeLength : LengthQuantity
  constantInternalCrossSectionalArea : AreaQuantity
  trappedAirLength : PipeState → LengthQuantity
  trappedAirVolume : PipeState → VolumeQuantity
  trappedAirAbsolutePressure : PipeState → DimPressure
  finalInterfaceDepthBelowOutsideSurface : LengthQuantity
  atmosphericPressure : DimPressure
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  pipeStraight : Bool
  pipeVertical : Bool
  topEndClosed : Bool
  bottomEndOpen : Bool
  finalTopEndLevelWithOutsideSurface : Bool
  trappedAirAmountFixed : Bool

/-! ## Figure/data readouts and physical assumptions -/

/-!
Evidence read from the primary bitmap. It records both named panels, the
`3.0 m` mark, the role of `L`, and the visible water/air geometry. It does not
assign a numerical value to `L`.
-/
structure MatchesPrimaryFigure (setup : ClosedTopPipeSetup) : Prop where
  everyTextLabelShown : ∀ label, setup.figure.labelShown label = true
  overallMarkIsPipeLength :
    setup.figure.markedLength .overallPipeLength = setup.pipeLength
  overallMarkIsThreeMeters :
    lengthInMeters (setup.figure.markedLength .overallPipeLength) = 3
  overallMarkRole :
    setup.figure.markedLengthRole .overallPipeLength = .fullPipeLength
  finalLMarkIsTrappedAirLength :
    setup.figure.markedLength .finalAirLengthL =
      setup.trappedAirLength .afterCompression
  finalLMarkRole :
    setup.figure.markedLengthRole .finalAirLengthL = .trappedAirColumnLength
  beforePipeIsAboveWater : setup.figure.beforePipeAboveWater = true
  afterPipeIsSubmerged : setup.figure.afterPipeSubmergedInWater = true
  outsideSurfaceVisible : setup.figure.afterOutsideWaterSurfaceShown = true
  internalInterfaceVisible :
    setup.figure.afterInternalAirWaterInterfaceShown = true
  arrowsAreVertical : setup.figure.lengthArrowsVertical = true

/-!
Qualitative prose and the vertical geometry of the experiment. The initial
air fills the pipe. In the final state the closed top is at the outside water
surface, so the depth of the internal interface equals the final air-column
length. These relations do not specify that length numerically.
-/
structure MatchesClosedTopPipeScenario (setup : ClosedTopPipeSetup) : Prop where
  liquidIsWater : setup.liquid = .water
  trappedGasIsAir : setup.trappedGas = .air
  pipeIsStraight : setup.pipeStraight = true
  pipeIsVertical : setup.pipeVertical = true
  closedAtTop : setup.topEndClosed = true
  openAtBottom : setup.bottomEndOpen = true
  movedSlowlyStraightDown : setup.immersionProtocol = .slowlyStraightDown
  usesIsothermalCompressionModel :
    setup.compressionProtocol = .quasistaticIsothermal
  finalTopAtOutsideSurface :
    setup.finalTopEndLevelWithOutsideSurface = true
  fixedAmountOfTrappedAir : setup.trappedAirAmountFixed = true
  initialAirFillsPipe :
    setup.trappedAirLength .beforeImmersion = setup.pipeLength
  finalInterfaceDepthEqualsAirLength :
    setup.finalInterfaceDepthBelowOutsideSurface =
      setup.trappedAirLength .afterCompression

/-!
Standard textbook calibrations implicit in the multiple-choice numerical
answer: atmospheric pressure is approximated by `1.00 * 10^5 Pa`, water by
`1000 kg/m^3`, and gravity by `9.8 m/s^2`. None mentions the requested
trapped-air length.
-/
structure UsesStandardAtmosphereWaterAndGravity
    (setup : ClosedTopPipeSetup) : Prop where
  atmosphericPressurePascals :
    pressureInPascals setup.atmosphericPressure = 100000
  waterDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.waterMassDensity = 1000
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-!
Positivity and geometric ordering for the two physical states. The final air
column is shorter than the initially full pipe, selecting compression without
assigning the final length any answer-choice value.
-/
structure HasPhysicalPipeParameters (setup : ClosedTopPipeSetup) : Prop where
  pipeLengthPositive : 0 < lengthInMeters setup.pipeLength
  crossSectionalAreaPositive :
    0 < areaInSquareMeters setup.constantInternalCrossSectionalArea
  trappedAirLengthsPositive :
    ∀ state, 0 < lengthInMeters (setup.trappedAirLength state)
  finalAirColumnIsCompressed :
    lengthInMeters (setup.trappedAirLength .afterCompression) <
      lengthInMeters (setup.trappedAirLength .beforeImmersion)
  interfaceDepthPositive :
    0 < lengthInMeters setup.finalInterfaceDepthBelowOutsideSurface
  trappedAirVolumesPositive :
    ∀ state, 0 < volumeInCubicMeters (setup.trappedAirVolume state)
  trappedAirPressuresPositive :
    ∀ state, 0 < pressureInPascals
      (setup.trappedAirAbsolutePressure state)
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericPressure
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.waterMassDensity
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-!
The governing relations for the experiment:

* constant cross section gives `V = A * length` in each state;
* before immersion the freely connected air is at atmospheric pressure;
* the slowly compressed fixed gas obeys Boyle's law `P_i V_i = P_f V_f`;
* at the final internal interface, hydrostatics gives
  `P_f = P_atm + rho * g * depth`.

The equations are stated in every coherent selection of base units. They do
not give the final length a numerical value and do not mention an answer
choice.
-/
structure SatisfiesClosedTopPipeLaws (setup : ClosedTopPipeSetup) : Prop where
  constantCrossSectionAirVolume :
    ∀ (state : PipeState) (lengthUnit : LengthUnit),
      volumeReadout lengthUnit (setup.trappedAirVolume state) =
        areaReadout lengthUnit setup.constantInternalCrossSectionalArea *
          lengthReadout lengthUnit (setup.trappedAirLength state)
  initialAirPressureIsAtmospheric :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      pressureReadout massUnit lengthUnit timeUnit
          (setup.trappedAirAbsolutePressure .beforeImmersion) =
        pressureReadout massUnit lengthUnit timeUnit setup.atmosphericPressure
  isothermalPressureVolumeProduct :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      pressureReadout massUnit lengthUnit timeUnit
            (setup.trappedAirAbsolutePressure .beforeImmersion) *
          volumeReadout lengthUnit
            (setup.trappedAirVolume .beforeImmersion) =
        pressureReadout massUnit lengthUnit timeUnit
            (setup.trappedAirAbsolutePressure .afterCompression) *
          volumeReadout lengthUnit
            (setup.trappedAirVolume .afterCompression)
  finalHydrostaticPressure :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      pressureReadout massUnit lengthUnit timeUnit
          (setup.trappedAirAbsolutePressure .afterCompression) =
        pressureReadout massUnit lengthUnit timeUnit setup.atmosphericPressure +
          densityReadout massUnit lengthUnit setup.waterMassDensity *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit
              setup.finalInterfaceDepthBelowOutsideSurface

/-! ## Displayed answer choices and target conclusions -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Trapped-air length in meters printed beside each answer label. -/
def displayedLengthInMeters : AnswerChoice → ℝ
  | .A => 12 / 5
  | .B => 11 / 5
  | .C => 2
  | .D => 21 / 10

/-- Dataset answer metadata, deliberately not used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- A physical length rounds to a displayed value to the nearest tenth meter. -/
def RoundsToNearestTenthMeter
    (length : LengthQuantity) (displayedMeters : ℝ) : Prop :=
  |lengthInMeters length - displayedMeters| < 1 / 20

/-- A displayed choice agrees with the final trapped-air length. -/
def MatchesDisplayedTrappedAirLength
    (setup : ClosedTopPipeSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenthMeter
    (setup.trappedAirLength .afterCompression)
    (displayedLengthInMeters choice)

/-- Exactly one displayed choice agrees with the modeled final air length. -/
def IsUniqueMatchingDisplayedLength
    (setup : ClosedTopPipeSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedTrappedAirLength setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedTrappedAirLength setup other → other = choice

/-!
Eliminating the two air volumes and the final pressure from pipe geometry,
Boyle's law, hydrostatics, and the final surface geometry gives

`49 * L^2 + 500 * L - 1500 = 0`

for the final trapped-air length `L` in meters. This is a derived relation,
not a premise or definition of the final state.
-/
lemma finalAirLength_satisfies_quadratic
    (setup : ClosedTopPipeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hScenario : MatchesClosedTopPipeScenario setup)
    (hCalibration : UsesStandardAtmosphereWaterAndGravity setup)
    (hPhysical : HasPhysicalPipeParameters setup)
    (hLaws : SatisfiesClosedTopPipeLaws setup) :
    49 * lengthInMeters (setup.trappedAirLength .afterCompression) ^ 2 +
        500 * lengthInMeters (setup.trappedAirLength .afterCompression) -
        1500 = 0 := by
  have hInitialLength :
      lengthInMeters (setup.trappedAirLength .beforeImmersion) = 3 := by
    rw [hScenario.initialAirFillsPipe,
      ← hFigure.overallMarkIsPipeLength]
    exact hFigure.overallMarkIsThreeMeters
  have hFinalDepth :
      lengthInMeters setup.finalInterfaceDepthBelowOutsideSurface =
        lengthInMeters (setup.trappedAirLength .afterCompression) :=
    congrArg lengthInMeters hScenario.finalInterfaceDepthEqualsAirLength
  have hInitialVolume :
      volumeInCubicMeters (setup.trappedAirVolume .beforeImmersion) =
        areaInSquareMeters setup.constantInternalCrossSectionalArea *
          lengthInMeters (setup.trappedAirLength .beforeImmersion) := by
    simpa [volumeInCubicMeters, areaInSquareMeters, lengthInMeters] using
      hLaws.constantCrossSectionAirVolume
        PipeState.beforeImmersion LengthUnit.meters
  have hFinalVolume :
      volumeInCubicMeters (setup.trappedAirVolume .afterCompression) =
        areaInSquareMeters setup.constantInternalCrossSectionalArea *
          lengthInMeters (setup.trappedAirLength .afterCompression) := by
    simpa [volumeInCubicMeters, areaInSquareMeters, lengthInMeters] using
      hLaws.constantCrossSectionAirVolume
        PipeState.afterCompression LengthUnit.meters
  have hInitialPressure :
      pressureInPascals
          (setup.trappedAirAbsolutePressure .beforeImmersion) =
        pressureInPascals setup.atmosphericPressure := by
    simpa [pressureInPascals] using
      hLaws.initialAirPressureIsAtmospheric
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hPressureVolume :
      pressureInPascals
            (setup.trappedAirAbsolutePressure .beforeImmersion) *
          volumeInCubicMeters
            (setup.trappedAirVolume .beforeImmersion) =
        pressureInPascals
            (setup.trappedAirAbsolutePressure .afterCompression) *
          volumeInCubicMeters
            (setup.trappedAirVolume .afterCompression) := by
    simpa [pressureInPascals, volumeInCubicMeters] using
      hLaws.isothermalPressureVolumeProduct
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hFinalPressure :
      pressureInPascals
          (setup.trappedAirAbsolutePressure .afterCompression) =
        pressureInPascals setup.atmosphericPressure +
          densityInKilogramsPerCubicMeter setup.waterMassDensity *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.finalInterfaceDepthBelowOutsideSurface := by
    simpa [pressureInPascals, densityInKilogramsPerCubicMeter,
      accelerationInMetersPerSecondSquared, lengthInMeters] using
      hLaws.finalHydrostaticPressure
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  rw [hInitialPressure, hInitialVolume, hFinalPressure, hFinalVolume,
    hCalibration.atmosphericPressurePascals,
    hCalibration.waterDensityKilogramsPerCubicMeter,
    hCalibration.gravitationalAccelerationMetersPerSecondSquared,
    hFinalDepth, hInitialLength] at hPressureVolume
  have hFactored :
      areaInSquareMeters setup.constantInternalCrossSectionalArea *
          (49 *
              lengthInMeters
                  (setup.trappedAirLength .afterCompression) ^ 2 +
            500 *
              lengthInMeters
                (setup.trappedAirLength .afterCompression) -
            1500) = 0 := by
    nlinarith [hPressureVolume]
  rcases mul_eq_zero.mp hFactored with hAreaZero | hQuadratic
  · exact (ne_of_gt hPhysical.crossSectionalAreaPositive hAreaZero).elim
  · exact hQuadratic

/-!
The positive physical root is
`(20 * sqrt 340 - 250) / 49`, approximately `2.424 m`. It rounds to
`2.4 m`, and among the displayed values this uniquely selects answer A.

This formalizes `thm:physics:phyx_mini_0364:target`.
-/
theorem problem_phyx_mini_0364
    (setup : ClosedTopPipeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hScenario : MatchesClosedTopPipeScenario setup)
    (hCalibration : UsesStandardAtmosphereWaterAndGravity setup)
    (hPhysical : HasPhysicalPipeParameters setup)
    (hLaws : SatisfiesClosedTopPipeLaws setup) :
    lengthInMeters (setup.trappedAirLength .afterCompression) =
        (20 * Real.sqrt 340 - 250) / 49 ∧
      RoundsToNearestTenthMeter
        (setup.trappedAirLength .afterCompression)
        (displayedLengthInMeters .A) ∧
      IsUniqueMatchingDisplayedLength setup .A := by
  have hQuadratic :=
    finalAirLength_satisfies_quadratic
      setup hFigure hScenario hCalibration hPhysical hLaws
  have hLengthPositive :
      0 < lengthInMeters
        (setup.trappedAirLength .afterCompression) :=
    hPhysical.trappedAirLengthsPositive PipeState.afterCompression
  have hSqrtNonnegative : 0 ≤ Real.sqrt 340 := Real.sqrt_nonneg 340
  have hSqrtSquared : (Real.sqrt 340) ^ 2 = 340 :=
    Real.sq_sqrt (by norm_num)
  have hCompletedSquare :
      (49 *
          lengthInMeters
            (setup.trappedAirLength .afterCompression) +
        250) ^ 2 =
        (20 * Real.sqrt 340) ^ 2 := by
    nlinarith [hQuadratic, hSqrtSquared]
  have hPositiveSquareRoot :
      49 *
          lengthInMeters
            (setup.trappedAirLength .afterCompression) +
        250 =
        20 * Real.sqrt 340 := by
    nlinarith [hCompletedSquare]
  have hRoot :
      lengthInMeters
          (setup.trappedAirLength .afterCompression) =
        (20 * Real.sqrt 340 - 250) / 49 := by
    nlinarith [hPositiveSquareRoot]
  have hSqrtLower : 183 / 10 < Real.sqrt 340 := by
    nlinarith [hSqrtSquared]
  have hSqrtUpper : Real.sqrt 340 < 37 / 2 := by
    nlinarith [hSqrtSquared]
  have hRounds :
      RoundsToNearestTenthMeter
        (setup.trappedAirLength .afterCompression)
        (displayedLengthInMeters .A) := by
    change
      |lengthInMeters
          (setup.trappedAirLength .afterCompression) - 12 / 5| <
        1 / 20
    rw [hRoot, abs_lt]
    constructor <;> nlinarith [hSqrtLower, hSqrtUpper]
  refine ⟨hRoot, hRounds, hRounds, ?_⟩
  intro other hOther
  fin_cases other
  · rfl
  · have hOtherUpper :
        lengthInMeters
              (setup.trappedAirLength .afterCompression) -
            11 / 5 <
          1 / 20 := by
      apply (abs_lt.mp ?_).2
      exact hOther
    rw [hRoot] at hOtherUpper
    exfalso
    nlinarith [hSqrtLower]
  · have hOtherUpper :
        lengthInMeters
              (setup.trappedAirLength .afterCompression) -
            2 <
          1 / 20 := by
      apply (abs_lt.mp ?_).2
      exact hOther
    rw [hRoot] at hOtherUpper
    exfalso
    nlinarith [hSqrtLower]
  · have hOtherUpper :
        lengthInMeters
              (setup.trappedAirLength .afterCompression) -
            21 / 10 <
          1 / 20 := by
      apply (abs_lt.mp ?_).2
      exact hOther
    rw [hRoot] at hOtherUpper
    exfalso
    nlinarith [hSqrtLower]

end PhyXMiniProblems.ProblemPhyXMini0364
