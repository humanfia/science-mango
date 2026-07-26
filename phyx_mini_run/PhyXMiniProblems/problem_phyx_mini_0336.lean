import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

/-!
# Maximum amount of air in a lung from a gauge-pressure–volume diagram

The primary figure is a four-vertex cycle in a `p`–`V` plane.  Its horizontal
axis is volume in litres and its vertical axis is **gauge** pressure in
millimetres of mercury.  The first two directed edges are inhalation and the
last two directed edges are exhalation.

Pressures, volumes, temperatures, and the molar gas constant below retain
their physical roles.  Physlib has no amount-of-substance component in its
current dimension type, so the gas amount is an explicitly named scalar
readout in moles.  Other real numbers occur only as named unit readouts or
displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0336

open Dimension

/-! ## Dimensionful physical quantities and named readouts -/

/-- A physical gas volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure, used both for gauge and absolute pressure. -/
abbrev PressureQuantity : Type := DimPressure

/--
The molar gas constant, with energy-per-temperature dimension.  The omitted
inverse-mole dimension is paired with the explicitly molar scalar readout in
`amountOfAirInMolesAt`, since Physlib currently has no amount-of-substance
base dimension.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Litre readout used on the horizontal axis of the primary figure. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/--
Millimetre-of-mercury readout, obtained by comparing with Physlib's physical
quantity `DimPressure.millimeterOfMercury`.
-/
def pressureInMillimetersOfMercury (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.millimeterOfMercury

/-- Kelvin readout of Physlib's absolute-temperature object. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/--
Readout of the molar gas constant in litre-millimetres of mercury per
mole-kelvin.  The factor `1000` converts cubic metres to litres.
-/
def molarGasConstantInLiterMillimetersOfMercuryPerMoleKelvin
    (gasConstant : MolarGasConstantQuantity) : ℝ :=
  1000 * (gasConstant UnitChoices.SI).val /
    pressureInPascals DimPressure.millimeterOfMercury

/-! ## Figure labels, states, and process directions -/

/-- The four black vertices in cyclic order in the primary `p`–`V` plot. -/
inductive BreathCycleState where
  | lowerLeft
  | upperLeft
  | upperRight
  | lowerRight
  deriving DecidableEq, Repr

/--
A point on one of the four directed straight edges.  `edgeFraction = 0` is
the named starting vertex and `edgeFraction = 1` is the next vertex.
-/
structure BreathCyclePosition where
  edgeStart : BreathCycleState
  edgeFraction : ℝ
  edgeFraction_mem : edgeFraction ∈ Set.Icc (0 : ℝ) 1

/-- The canonical cycle position at a named vertex. -/
def vertexPosition (state : BreathCycleState) : BreathCyclePosition :=
  ⟨state, 0, by constructor <;> norm_num⟩

/-- A cycle position with an explicitly supplied edge fraction. -/
def positionOnEdge
    (edgeStart : BreathCycleState) (edgeFraction : ℝ)
    (hFraction : edgeFraction ∈ Set.Icc (0 : ℝ) 1) :
    BreathCyclePosition :=
  ⟨edgeStart, edgeFraction, hFraction⟩

/-- Quantities named on the two axes of the primary figure. -/
inductive FigureAxisLabel where
  | volumeV
  | pressureP
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal axis. -/
inductive VolumeDisplayUnit where
  | liters
  deriving DecidableEq, Repr

/-- Unit printed on the vertical axis. -/
inductive PressureDisplayUnit where
  | millimetersOfMercury
  deriving DecidableEq, Repr

/-- Whether the pressure plotted vertically is absolute or gauge pressure. -/
inductive PlottedPressureKind where
  | gauge
  | absolute
  deriving DecidableEq, Repr

/-- Breathing phase named beside an outgoing directed edge. -/
inductive BreathingPhase where
  | inhaling
  | exhaling
  deriving DecidableEq, Repr

/-- Material model used for the air in the lung. -/
inductive GasModel where
  | ideal
  deriving DecidableEq, Repr

/--
The labelled graph and its physical coordinates.  The four vertices and the
edge directions are independent fields here; their observed values belong to
`MatchesPrimaryLungFigure`, not to this structure's definitions.
-/
structure LungPressureVolumeFigure where
  horizontalAxisLabel : FigureAxisLabel
  verticalAxisLabel : FigureAxisLabel
  horizontalAxisUnit : VolumeDisplayUnit
  verticalAxisUnit : PressureDisplayUnit
  plottedPressureKind : PlottedPressureKind
  volumeAt : BreathCyclePosition → VolumeQuantity
  gaugePressureAt : BreathCyclePosition → PressureQuantity
  nextState : BreathCycleState → BreathCycleState
  phaseAlongOutgoingEdge : BreathCycleState → BreathingPhase

/-! ## Lung setup and assumptions -/

/--
The thermodynamic quantities throughout one deep breath.

`absolutePressureAt` is distinct from the plotted gauge pressure so that their
physical relation is an explicit governing law.  Likewise, neither the amount
at the upper-right state nor any maximum amount is prescribed by this setup.
-/
structure LungBreathSetup where
  gasModel : GasModel
  figure : LungPressureVolumeFigure
  ambientPressure : PressureQuantity
  absolutePressureAt : BreathCyclePosition → PressureQuantity
  airTemperatureAt : BreathCyclePosition → Temperature
  /-- Celsius readout stated in the problem, indexed to expose constancy. -/
  airTemperatureCelsiusAt : BreathCyclePosition → ℝ
  /-- Amount-of-substance readout in moles throughout the plotted cycle. -/
  amountOfAirInMolesAt : BreathCyclePosition → ℝ
  molarGasConstant : MolarGasConstantQuantity

/--
Qualitative labels, directed edges, and numerical coordinates read from the
primary image.  The auxiliary caption is not used where it conflicts with the
grid: the four visible points are `(0.1, 1)`, `(0.4, 9)`, `(1.4, 11)`, and
`(1.0, 2)` in litres and millimetres of mercury.
-/
structure MatchesPrimaryLungFigure (setup : LungBreathSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisLabel = .volumeV
  verticalAxisIsPressure :
    setup.figure.verticalAxisLabel = .pressureP
  horizontalAxisUsesLiters :
    setup.figure.horizontalAxisUnit = .liters
  verticalAxisUsesMillimetersOfMercury :
    setup.figure.verticalAxisUnit = .millimetersOfMercury
  verticalAxisShowsGaugePressure :
    setup.figure.plottedPressureKind = .gauge
  lowerLeftVolume :
    volumeInLiters
        (setup.figure.volumeAt (vertexPosition .lowerLeft)) = 1 / 10
  lowerLeftGaugePressure :
    pressureInMillimetersOfMercury
        (setup.figure.gaugePressureAt (vertexPosition .lowerLeft)) = 1
  upperLeftVolume :
    volumeInLiters
        (setup.figure.volumeAt (vertexPosition .upperLeft)) = 2 / 5
  upperLeftGaugePressure :
    pressureInMillimetersOfMercury
        (setup.figure.gaugePressureAt (vertexPosition .upperLeft)) = 9
  upperRightVolume :
    volumeInLiters
        (setup.figure.volumeAt (vertexPosition .upperRight)) = 7 / 5
  upperRightGaugePressure :
    pressureInMillimetersOfMercury
        (setup.figure.gaugePressureAt (vertexPosition .upperRight)) = 11
  lowerRightVolume :
    volumeInLiters
        (setup.figure.volumeAt (vertexPosition .lowerRight)) = 1
  lowerRightGaugePressure :
    pressureInMillimetersOfMercury
        (setup.figure.gaugePressureAt (vertexPosition .lowerRight)) = 2
  lowerLeftNext : setup.figure.nextState .lowerLeft = .upperLeft
  upperLeftNext : setup.figure.nextState .upperLeft = .upperRight
  upperRightNext : setup.figure.nextState .upperRight = .lowerRight
  lowerRightNext : setup.figure.nextState .lowerRight = .lowerLeft
  lowerLeftEdgeIsInhaling :
    setup.figure.phaseAlongOutgoingEdge .lowerLeft = .inhaling
  upperLeftEdgeIsInhaling :
    setup.figure.phaseAlongOutgoingEdge .upperLeft = .inhaling
  upperRightEdgeIsExhaling :
    setup.figure.phaseAlongOutgoingEdge .upperRight = .exhaling
  lowerRightEdgeIsExhaling :
    setup.figure.phaseAlongOutgoingEdge .lowerRight = .exhaling
  volumeIsPiecewiseLinear :
    ∀ (edgeStart : BreathCycleState) (edgeFraction : ℝ)
        (hFraction : edgeFraction ∈ Set.Icc (0 : ℝ) 1),
      volumeInLiters
          (setup.figure.volumeAt
            (positionOnEdge edgeStart edgeFraction hFraction)) =
        (1 - edgeFraction) *
            volumeInLiters
              (setup.figure.volumeAt (vertexPosition edgeStart)) +
          edgeFraction *
            volumeInLiters
              (setup.figure.volumeAt
                (vertexPosition (setup.figure.nextState edgeStart)))
  gaugePressureIsPiecewiseLinear :
    ∀ (edgeStart : BreathCycleState) (edgeFraction : ℝ)
        (hFraction : edgeFraction ∈ Set.Icc (0 : ℝ) 1),
      pressureInMillimetersOfMercury
          (setup.figure.gaugePressureAt
            (positionOnEdge edgeStart edgeFraction hFraction)) =
        (1 - edgeFraction) *
            pressureInMillimetersOfMercury
              (setup.figure.gaugePressureAt (vertexPosition edgeStart)) +
          edgeFraction *
            pressureInMillimetersOfMercury
              (setup.figure.gaugePressureAt
                (vertexPosition (setup.figure.nextState edgeStart)))

/-- Numerical and qualitative data stated outside the plotted cycle. -/
structure MatchesProblemData (setup : LungBreathSetup) : Prop where
  airIsIdeal : setup.gasModel = .ideal
  ambientPressureIs760MillimetersOfMercury :
    pressureInMillimetersOfMercury setup.ambientPressure = 760
  temperatureRemains20Celsius :
    ∀ position, setup.airTemperatureCelsiusAt position = 20
  molarGasConstantReadout :
    molarGasConstantInLiterMillimetersOfMercuryPerMoleKelvin
        setup.molarGasConstant = 624 / 10

/-- Positivity conditions selecting the physical branch of the gas model. -/
structure HasPhysicalLungParameters (setup : LungBreathSetup) : Prop where
  volumePositive :
    ∀ position, 0 < volumeInLiters (setup.figure.volumeAt position)
  ambientPressurePositive :
    0 < pressureInMillimetersOfMercury setup.ambientPressure
  absolutePressurePositive :
    ∀ position,
      0 < pressureInMillimetersOfMercury (setup.absolutePressureAt position)
  temperaturePositive :
    ∀ position, 0 < temperatureInKelvins (setup.airTemperatureAt position)
  gasAmountNonnegative :
    ∀ position, 0 ≤ setup.amountOfAirInMolesAt position
  molarGasConstantPositive :
    0 < molarGasConstantInLiterMillimetersOfMercuryPerMoleKelvin
      setup.molarGasConstant

/--
The governing pressure-conversion, temperature-conversion, and ideal-gas laws.

The ideal-gas equation is stated in the compatible units displayed by the
problem: millimetres of mercury, litres, moles, and kelvins.  It applies to
every plotted state.  In particular, it does not state which state maximizes
the amount of air or prescribe the numerical answer.
-/
structure SatisfiesLungIdealGasLaws (setup : LungBreathSetup) : Prop where
  gaugePressureToAbsolutePressure :
    ∀ position,
      pressureInMillimetersOfMercury (setup.absolutePressureAt position) =
        pressureInMillimetersOfMercury setup.ambientPressure +
          pressureInMillimetersOfMercury
            (setup.figure.gaugePressureAt position)
  CelsiusToKelvin :
    ∀ position,
      temperatureInKelvins (setup.airTemperatureAt position) =
        setup.airTemperatureCelsiusAt position + 27315 / 100
  idealGasLaw :
    ∀ position,
      pressureInMillimetersOfMercury (setup.absolutePressureAt position) *
          volumeInLiters (setup.figure.volumeAt position) =
        setup.amountOfAirInMolesAt position *
          molarGasConstantInLiterMillimetersOfMercuryPerMoleKelvin
            setup.molarGasConstant *
          temperatureInKelvins (setup.airTemperatureAt position)

/-! ## Displayed choices and requested conclusion -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Mole readout printed beside each answer label. -/
def answerAmountInMoles : AnswerChoice → ℝ
  | .A => 69 / 1000
  | .B => 59 / 1000
  | .C => 459 / 1000
  | .D => 55 / 1000

/-- The answer label recorded by the dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/--
The upper-right vertex contains at least as many moles as every other plotted
state, and its amount rounds to `0.059 mol`, recorded answer B.  The strict
half-thousandth bound formalizes rounding to the displayed three decimals.

Blueprint label: `thm:physics:phyx_mini_0336:target`.
-/
theorem maximum_amount_of_air_is_answer_B
    (setup : LungBreathSetup)
    (_figure : MatchesPrimaryLungFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalLungParameters setup)
    (_laws : SatisfiesLungIdealGasLaws setup) :
    (∀ position,
      setup.amountOfAirInMolesAt position ≤
        setup.amountOfAirInMolesAt (vertexPosition .upperRight)) ∧
      |setup.amountOfAirInMolesAt (vertexPosition .upperRight) -
          answerAmountInMoles recordedAnswerChoice| < 1 / 2000 := by
  have hUpperRightTemperature :
      temperatureInKelvins
          (setup.airTemperatureAt (vertexPosition .upperRight)) =
        5863 / 20 := by
    rw [_laws.CelsiusToKelvin, _data.temperatureRemains20Celsius]
    norm_num
  have hUpperRightGasLaw :=
    _laws.idealGasLaw (vertexPosition .upperRight)
  rw [_laws.gaugePressureToAbsolutePressure,
      _data.ambientPressureIs760MillimetersOfMercury,
      _figure.upperRightGaugePressure, _figure.upperRightVolume,
      _data.molarGasConstantReadout, hUpperRightTemperature] at hUpperRightGasLaw
  constructor
  · rintro ⟨edgeStart, edgeFraction, hFraction⟩
    have hFractionProduct :
        0 ≤ edgeFraction * (1 - edgeFraction) :=
      mul_nonneg hFraction.1 (sub_nonneg.mpr hFraction.2)
    cases edgeStart with
    | lowerLeft =>
        have hVolume :=
          _figure.volumeIsPiecewiseLinear
            .lowerLeft edgeFraction hFraction
        have hGaugePressure :=
          _figure.gaugePressureIsPiecewiseLinear
            .lowerLeft edgeFraction hFraction
        rw [_figure.lowerLeftVolume, _figure.lowerLeftNext,
            _figure.upperLeftVolume] at hVolume
        rw [_figure.lowerLeftGaugePressure, _figure.lowerLeftNext,
            _figure.upperLeftGaugePressure] at hGaugePressure
        simp only [positionOnEdge] at hVolume hGaugePressure
        have hTemperature :
            temperatureInKelvins
                (setup.airTemperatureAt
                  ⟨.lowerLeft, edgeFraction, hFraction⟩) =
              5863 / 20 := by
          rw [_laws.CelsiusToKelvin,
              _data.temperatureRemains20Celsius]
          norm_num
        have hGasLaw :=
          _laws.idealGasLaw
            ⟨.lowerLeft, edgeFraction, hFraction⟩
        rw [_laws.gaugePressureToAbsolutePressure,
            _data.ambientPressureIs760MillimetersOfMercury,
            hGaugePressure, hVolume,
            _data.molarGasConstantReadout, hTemperature] at hGasLaw
        nlinarith
    | upperLeft =>
        have hVolume :=
          _figure.volumeIsPiecewiseLinear
            .upperLeft edgeFraction hFraction
        have hGaugePressure :=
          _figure.gaugePressureIsPiecewiseLinear
            .upperLeft edgeFraction hFraction
        rw [_figure.upperLeftVolume, _figure.upperLeftNext,
            _figure.upperRightVolume] at hVolume
        rw [_figure.upperLeftGaugePressure, _figure.upperLeftNext,
            _figure.upperRightGaugePressure] at hGaugePressure
        simp only [positionOnEdge] at hVolume hGaugePressure
        have hTemperature :
            temperatureInKelvins
                (setup.airTemperatureAt
                  ⟨.upperLeft, edgeFraction, hFraction⟩) =
              5863 / 20 := by
          rw [_laws.CelsiusToKelvin,
              _data.temperatureRemains20Celsius]
          norm_num
        have hGasLaw :=
          _laws.idealGasLaw
            ⟨.upperLeft, edgeFraction, hFraction⟩
        rw [_laws.gaugePressureToAbsolutePressure,
            _data.ambientPressureIs760MillimetersOfMercury,
            hGaugePressure, hVolume,
            _data.molarGasConstantReadout, hTemperature] at hGasLaw
        nlinarith
    | upperRight =>
        have hVolume :=
          _figure.volumeIsPiecewiseLinear
            .upperRight edgeFraction hFraction
        have hGaugePressure :=
          _figure.gaugePressureIsPiecewiseLinear
            .upperRight edgeFraction hFraction
        rw [_figure.upperRightVolume, _figure.upperRightNext,
            _figure.lowerRightVolume] at hVolume
        rw [_figure.upperRightGaugePressure, _figure.upperRightNext,
            _figure.lowerRightGaugePressure] at hGaugePressure
        simp only [positionOnEdge] at hVolume hGaugePressure
        have hTemperature :
            temperatureInKelvins
                (setup.airTemperatureAt
                  ⟨.upperRight, edgeFraction, hFraction⟩) =
              5863 / 20 := by
          rw [_laws.CelsiusToKelvin,
              _data.temperatureRemains20Celsius]
          norm_num
        have hGasLaw :=
          _laws.idealGasLaw
            ⟨.upperRight, edgeFraction, hFraction⟩
        rw [_laws.gaugePressureToAbsolutePressure,
            _data.ambientPressureIs760MillimetersOfMercury,
            hGaugePressure, hVolume,
            _data.molarGasConstantReadout, hTemperature] at hGasLaw
        nlinarith
    | lowerRight =>
        have hVolume :=
          _figure.volumeIsPiecewiseLinear
            .lowerRight edgeFraction hFraction
        have hGaugePressure :=
          _figure.gaugePressureIsPiecewiseLinear
            .lowerRight edgeFraction hFraction
        rw [_figure.lowerRightVolume, _figure.lowerRightNext,
            _figure.lowerLeftVolume] at hVolume
        rw [_figure.lowerRightGaugePressure, _figure.lowerRightNext,
            _figure.lowerLeftGaugePressure] at hGaugePressure
        simp only [positionOnEdge] at hVolume hGaugePressure
        have hTemperature :
            temperatureInKelvins
                (setup.airTemperatureAt
                  ⟨.lowerRight, edgeFraction, hFraction⟩) =
              5863 / 20 := by
          rw [_laws.CelsiusToKelvin,
              _data.temperatureRemains20Celsius]
          norm_num
        have hGasLaw :=
          _laws.idealGasLaw
            ⟨.lowerRight, edgeFraction, hFraction⟩
        rw [_laws.gaugePressureToAbsolutePressure,
            _data.ambientPressureIs760MillimetersOfMercury,
            hGaugePressure, hVolume,
            _data.molarGasConstantReadout, hTemperature] at hGasLaw
        nlinarith
  · rw [abs_lt]
    constructor <;>
      norm_num [answerAmountInMoles, recordedAnswerChoice] at * <;>
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0336
