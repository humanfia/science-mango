import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0405

open Dimension

/-!
# Specific latent heat of vaporization from a heating curve

A `500 g` sample is heated steadily.  The primary temperature-versus-supplied-
heat image shows its vaporization plateau at `40 °C`, from `120 kJ` to
`180 kJ`.  Consequently the phase change absorbs `60 kJ`; the specific latent
heat is obtained from the governing relation `Q_vap = m L_v`.

The primary raster is used instead of the auxiliary caption where they
disagree.  In particular, the first plateau is at `-20 °C` from `20 kJ` to
`40 kJ`, and the vaporization plateau is at `40 °C` from `120 kJ` to `180 kJ`.

Mass, energy, absolute temperature, and specific latent heat retain their
physical dimensions.  Real numbers occur only in explicitly named unit
readouts, graph coordinates, and displayed answer values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/--
Specific latent heat, equivalently energy per unit mass, with dimension
`L² T⁻²`.  Its coherent SI readout is in joules per kilogram.
-/
abbrev SpecificLatentHeatQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical mass in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a signed physical energy in kilojoules, the graph's horizontal unit. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Read a specific latent heat in joules per kilogram. -/
def specificLatentHeatInJoulesPerKilogram
    (latentHeat : SpecificLatentHeatQuantity) : ℝ :=
  ((latentHeat UnitChoices.SI).val : ℝ)

/-- Celsius readout of Physlib's nonnegative absolute temperature. -/
def temperatureInDegreesCelsius (temperature : Temperature) : ℝ :=
  temperature.toReal - 27315 / 100

/-! ## Experiment, graph labels, and curve geometry -/

/-- The physical quantity printed on each graph axis. -/
inductive AxisQuantity where
  | suppliedHeatQ
  | temperatureT
  deriving DecidableEq, Repr

/-- The units explicitly printed beside the graph axes. -/
inductive AxisUnit where
  | kilojoules
  | degreesCelsius
  deriving DecidableEq, Repr

/-- The way heat is delivered according to the problem statement. -/
inductive HeatSupplyMode where
  | steady
  deriving DecidableEq, Repr

/-- The phase changes represented by the two horizontal portions. -/
inductive PhaseChangeKind where
  | fusion
  | vaporization
  deriving DecidableEq, Repr

/-- Visual shape of a segment in the temperature-versus-heat graph. -/
inductive CurveSegmentShape where
  | risingLine
  | horizontalLine
  deriving DecidableEq, Repr

/-- Named vertices and the rightmost visible point of the plotted polyline. -/
inductive CurvePointLabel where
  | initial
  | fusionStart
  | fusionEnd
  | vaporizationStart
  | vaporizationEnd
  | rightmostVisible
  deriving DecidableEq, Repr

/-- The five successive portions of the heating curve. -/
inductive CurveSegment where
  | solidWarming
  | fusionPlateau
  | liquidWarming
  | vaporizationPlateau
  | vaporWarming
  deriving DecidableEq, Repr

/-- Initial vertex of each successive curve segment. -/
def segmentStartLabel : CurveSegment → CurvePointLabel
  | .solidWarming => .initial
  | .fusionPlateau => .fusionStart
  | .liquidWarming => .fusionEnd
  | .vaporizationPlateau => .vaporizationStart
  | .vaporWarming => .vaporizationEnd

/-- Final vertex of each successive curve segment. -/
def segmentFinishLabel : CurveSegment → CurvePointLabel
  | .solidWarming => .fusionStart
  | .fusionPlateau => .fusionEnd
  | .liquidWarming => .vaporizationStart
  | .vaporizationPlateau => .vaporizationEnd
  | .vaporWarming => .rightmostVisible

/-- A dimensionful point on the supplied heating curve. -/
structure HeatingCurvePoint where
  suppliedHeat : DimEnergy
  absoluteTemperature : Temperature

/-!
The heated sample and its plotted curve.  The latent heat is an independent
dimensionful field; it is not defined as the requested numerical answer.
-/
structure HeatingCurveExperiment where
  sampleMass : MassQuantity
  specificLatentHeatOfVaporization : SpecificLatentHeatQuantity
  point : CurvePointLabel → HeatingCurvePoint
  segmentShape : CurveSegment → CurveSegmentShape
  phaseChangeOn : CurveSegment → Option PhaseChangeKind
  heatSupplyMode : HeatSupplyMode
  horizontalAxis : AxisQuantity
  verticalAxis : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisUnit : AxisUnit

/-! ## Problem data, primary-image readouts, and governing law -/

/-!
The stated sample mass and a transcription of the primary raster.  The point
values are read in the units printed on the axes.  No numerical value of the
specific latent heat requested in the question occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : HeatingCurveExperiment) : Prop where
  heat_is_supplied_steadily : setup.heatSupplyMode = .steady
  horizontal_axis_is_heat_Q : setup.horizontalAxis = .suppliedHeatQ
  vertical_axis_is_temperature_T : setup.verticalAxis = .temperatureT
  horizontal_axis_unit_is_kilojoules :
    setup.horizontalAxisUnit = .kilojoules
  vertical_axis_unit_is_degrees_Celsius :
    setup.verticalAxisUnit = .degreesCelsius
  sample_mass_is_500_grams : massInGrams setup.sampleMass = 500
  solid_warming_is_rising :
    setup.segmentShape .solidWarming = .risingLine
  fusion_segment_is_horizontal :
    setup.segmentShape .fusionPlateau = .horizontalLine
  liquid_warming_is_rising :
    setup.segmentShape .liquidWarming = .risingLine
  vaporization_segment_is_horizontal :
    setup.segmentShape .vaporizationPlateau = .horizontalLine
  vapor_warming_is_rising :
    setup.segmentShape .vaporWarming = .risingLine
  fusion_plateau_represents_fusion :
    setup.phaseChangeOn .fusionPlateau = some .fusion
  vaporization_plateau_represents_vaporization :
    setup.phaseChangeOn .vaporizationPlateau = some .vaporization
  solid_warming_has_no_phase_change :
    setup.phaseChangeOn .solidWarming = none
  liquid_warming_has_no_phase_change :
    setup.phaseChangeOn .liquidWarming = none
  vapor_warming_has_no_phase_change :
    setup.phaseChangeOn .vaporWarming = none
  initial_heat_kilojoules :
    energyInKilojoules (setup.point .initial).suppliedHeat = 0
  initial_temperature_Celsius :
    temperatureInDegreesCelsius
        (setup.point .initial).absoluteTemperature = -40
  fusion_start_heat_kilojoules :
    energyInKilojoules (setup.point .fusionStart).suppliedHeat = 20
  fusion_start_temperature_Celsius :
    temperatureInDegreesCelsius
        (setup.point .fusionStart).absoluteTemperature = -20
  fusion_end_heat_kilojoules :
    energyInKilojoules (setup.point .fusionEnd).suppliedHeat = 40
  fusion_end_temperature_Celsius :
    temperatureInDegreesCelsius
        (setup.point .fusionEnd).absoluteTemperature = -20
  vaporization_start_heat_kilojoules :
    energyInKilojoules
        (setup.point .vaporizationStart).suppliedHeat = 120
  vaporization_start_temperature_Celsius :
    temperatureInDegreesCelsius
        (setup.point .vaporizationStart).absoluteTemperature = 40
  vaporization_end_heat_kilojoules :
    energyInKilojoules
        (setup.point .vaporizationEnd).suppliedHeat = 180
  vaporization_end_temperature_Celsius :
    temperatureInDegreesCelsius
        (setup.point .vaporizationEnd).absoluteTemperature = 40
  rightmost_heat_kilojoules :
    energyInKilojoules (setup.point .rightmostVisible).suppliedHeat = 200
  rightmost_temperature_above_60_Celsius :
    60 < temperatureInDegreesCelsius
      (setup.point .rightmostVisible).absoluteTemperature

/-- Heat absorbed during the constant-temperature vaporization segment. -/
def vaporizationHeatAbsorbedInJoules
    (setup : HeatingCurveExperiment) : ℝ :=
  energyInJoules (setup.point .vaporizationEnd).suppliedHeat -
    energyInJoules (setup.point .vaporizationStart).suppliedHeat

/-!
The governing phase-change energy balance `Q_vap = m L_v`, expressed in
coherent SI readouts.  It is a general physical law and contains no numerical
value for the current question's requested latent heat.
-/
structure SatisfiesSpecificLatentHeatOfVaporizationLaw
    (setup : HeatingCurveExperiment) : Prop where
  vaporization_energy_balance :
    vaporizationHeatAbsorbedInJoules setup =
      massInKilograms setup.sampleMass *
        specificLatentHeatInJoulesPerKilogram
          setup.specificLatentHeatOfVaporization

/-!
The stated `500 g` sample has mass `0.5 kg`.  This is a derived conversion,
not a premise field.
-/
lemma sampleMassInKilograms_eq_oneHalf
    (setup : HeatingCurveExperiment)
    (_data : MatchesProblemAndPrimaryFigure setup) :
    massInKilograms setup.sampleMass = 1 / 2 := by
  have h := _data.sample_mass_is_500_grams
  unfold massInGrams at h
  norm_num at h ⊢
  linarith

/-!
The primary figure's `120 kJ` to `180 kJ` plateau absorbs `60000 J`.  This
intermediate graph calculation remains on the conclusion side.
-/
lemma vaporizationHeatAbsorbedInJoules_eq_sixtyThousand
    (setup : HeatingCurveExperiment)
    (_data : MatchesProblemAndPrimaryFigure setup) :
    vaporizationHeatAbsorbedInJoules setup = 60000 := by
  simp only [vaporizationHeatAbsorbedInJoules]
  have hStart := _data.vaporization_start_heat_kilojoules
  have hEnd := _data.vaporization_end_heat_kilojoules
  unfold energyInKilojoules at hStart hEnd
  linarith

/-! ## Displayed answers and final target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Specific latent heat in `J/kg` displayed beside each answer label. -/
def displayedSpecificLatentHeatInJoulesPerKilogram : AnswerChoice → ℝ
  | .A => 12000
  | .B => 60000
  | .C => 120000
  | .D => 240000

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A displayed choice agrees with the experiment's derived latent heat. -/
def MatchesDisplayedAnswer
    (setup : HeatingCurveExperiment) (choice : AnswerChoice) : Prop :=
  specificLatentHeatInJoulesPerKilogram
      setup.specificLatentHeatOfVaporization =
    displayedSpecificLatentHeatInJoulesPerKilogram choice

/-!
The vaporization plateau absorbs `180 - 120 = 60 kJ`; dividing by
`500 g = 0.5 kg` gives `1.2 × 10⁵ J/kg`, displayed as choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0405:target`.
-/
theorem problem_phyx_mini_0405
    (setup : HeatingCurveExperiment)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_latentHeatLaw :
      SatisfiesSpecificLatentHeatOfVaporizationLaw setup) :
    specificLatentHeatInJoulesPerKilogram
          setup.specificLatentHeatOfVaporization = 120000 ∧
      MatchesDisplayedAnswer setup .C := by
  have hMass := sampleMassInKilograms_eq_oneHalf setup _data
  have hEnergy :=
    vaporizationHeatAbsorbedInJoules_eq_sixtyThousand setup _data
  have hBalance := _latentHeatLaw.vaporization_energy_balance
  rw [hEnergy, hMass] at hBalance
  have hLatent :
      specificLatentHeatInJoulesPerKilogram
          setup.specificLatentHeatOfVaporization = 120000 := by
    norm_num at hBalance ⊢
    linarith
  exact ⟨hLatent, by
    simpa [MatchesDisplayedAnswer,
      displayedSpecificLatentHeatInJoulesPerKilogram] using hLatent⟩

end PhyXMiniProblems.ProblemPhyXMini0405
