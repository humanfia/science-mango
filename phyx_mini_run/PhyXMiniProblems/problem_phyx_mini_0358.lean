import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0358

open Dimension

/-!
# Work done along a two-leg quasi-static pressure-volume path

One mole of an ideal diatomic gas follows the straight-line path `A → B → C`
shown in the primary pressure-volume diagram.  Direct inspection of that image
gives the exact plotted coordinates

* `A = (1, 6)`,
* `B = (2, 8)`, and
* `C = (3, 4)`.

The horizontal plot unit is `10³ cm³ = 10⁻³ m³`, and the vertical plot unit is
`10⁶ dyn cm⁻² = 10⁵ Pa`.  Thus one plot-area unit is `100 J`.

Pressure, volume, temperature, molar internal energy, the gas constant, and
work retain physical dimensions.  Real numbers are used only for explicitly
named unit readouts, diagram coordinates, mole readouts, and displayed answer
values.
-/

/-! ## Dimensionful quantities and named readouts -/

/-- A signed physical gas volume, with dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- An absolute-temperature quantity, with Physlib's temperature dimension. -/
abbrev AbsoluteTemperature : Type :=
  Dimensionful (WithDim Θ𝓭 ℝ)

/--
The molar gas constant, represented with energy-per-temperature dimension.
Physlib's current `Dimension` has no amount-of-substance component, so the
inverse-mole role is recorded by the name and paired with a scalar mole
readout below.
-/
abbrev MolarGasConstant : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/--
Molar internal energy.  Its omitted inverse-mole component is handled in the
same way as for `MolarGasConstant`; the underlying energy dimension is the
grounded Physlib type `DimEnergy`.
-/
abbrev MolarInternalEnergy : Type := DimEnergy

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/--
Read a volume in the horizontal-axis unit `10³ cm³`, equivalently litres.
-/
def volumeInDiagramUnits (volume : GasVolume) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read a pressure in SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/--
Read a pressure in the vertical-axis unit `10⁶ dyn cm⁻²`, which is exactly one
bar or `10⁵ Pa`.
-/
def pressureInDiagramUnits (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.bar UnitChoices.SI).val

/-- Kelvin readout of a dimensionful absolute temperature. -/
def temperatureInKelvins (temperature : AbsoluteTemperature) : ℝ :=
  (temperature UnitChoices.SI).val

/-- SI readout of the molar gas constant in joules per mole-kelvin. -/
def molarGasConstantInJoulesPerMoleKelvin
    (gasConstant : MolarGasConstant) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-- Joule-per-mole readout of a molar internal energy. -/
def molarInternalEnergyInJoulesPerMole
    (energy : MolarInternalEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Joule readout of a signed physical work quantity. -/
def workInJoules (work : DimEnergy) : ℝ :=
  (work UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Printed axis scales and their SI calibration -/

/-- Number of dynes per square centimetre represented by one vertical unit. -/
def pressureAxisScaleDynesPerSquareCentimeter : ℝ := 10 ^ 6

/-- Number of cubic centimetres represented by one horizontal unit. -/
def volumeAxisScaleCubicCentimeters : ℝ := 10 ^ 3

/-- SI pressure represented by one vertical plot unit. -/
def pressureDiagramUnitInPascals : ℝ := 10 ^ 5

/-- SI volume represented by one horizontal plot unit. -/
def volumeDiagramUnitInCubicMeters : ℝ := 1 / 1000

/-- Energy represented by one unit of area in the supplied `pV` diagram. -/
def joulesPerDiagramAreaUnit : ℝ :=
  pressureDiagramUnitInPascals * volumeDiagramUnitInCubicMeters

/-! ## Gas model, process, and figure labels -/

/-- Material model specified in the prose. -/
inductive GasModel where
  | idealDiatomic
  deriving DecidableEq, Repr

/-- The three state labels printed in the diagram. -/
inductive PVDiagramState where
  | A
  | B
  | C
  deriving DecidableEq, Repr

/-- The two directed legs of the route `A → B → C`. -/
inductive ProcessLeg where
  | aToB
  | bToC
  deriving DecidableEq, Repr

/-- Thermodynamic regime stated for both legs. -/
inductive ProcessRegime where
  | quasiStatic
  deriving DecidableEq, Repr

/-- Geometric shape of a leg in the pressure-volume plane. -/
inductive PathShape where
  | straightLine
  deriving DecidableEq, Repr

/-- Literal variable labels appearing on the axes. -/
inductive AxisLabel where
  | pressureP
  | volumeV
  deriving DecidableEq, Repr

/-- Literal scale labels printed beside the two axes. -/
inductive AxisScaleLabel where
  | pressureTenToSixDynesPerSquareCentimeter
  | volumeTenToThreeCubicCentimeters
  deriving DecidableEq, Repr

/--
The one-mole gas sample and its piecewise-straight process.

The leg works are independent dimensionful fields.  In particular, neither
they nor their sum is assigned any requested numerical value here.
-/
structure DiatomicGasPVProcess where
  gasModel : GasModel
  amountOfGasMoles : ℝ
  molarGasConstant : MolarGasConstant
  absoluteTemperatureAt : PVDiagramState → AbsoluteTemperature
  molarInternalEnergyAt : PVDiagramState → MolarInternalEnergy
  molarInternalEnergyFromTemperature :
    AbsoluteTemperature → MolarInternalEnergy
  volumeAt : PVDiagramState → GasVolume
  pressureAt : PVDiagramState → DimPressure
  workByGas : ProcessLeg → DimEnergy
  pathStart : ProcessLeg → PVDiagramState
  pathFinish : ProcessLeg → PVDiagramState
  pathRegime : ProcessLeg → ProcessRegime
  pathShape : ProcessLeg → PathShape
  stateLabelVisible : PVDiagramState → Bool
  axisLabelVisible : AxisLabel → Bool
  axisScaleLabelVisible : AxisScaleLabel → Bool
  gridVisible : Bool

/-! ## Scenario data and governing laws -/

/--
Problem-text data and exact transcription of the primary raster.  The
auxiliary caption's approximate `(1,4)`, `(2,7)`, `(3,5)` transcription is not
used because the problem designates the image as primary evidence.
-/
structure MatchesProblemAndPrimaryFigure
    (process : DiatomicGasPVProcess) : Prop where
  gas_is_ideal_diatomic : process.gasModel = .idealDiatomic
  amount_is_one_mole : process.amountOfGasMoles = 1
  volume_at_A : volumeInDiagramUnits (process.volumeAt .A) = 1
  pressure_at_A : pressureInDiagramUnits (process.pressureAt .A) = 6
  volume_at_B : volumeInDiagramUnits (process.volumeAt .B) = 2
  pressure_at_B : pressureInDiagramUnits (process.pressureAt .B) = 8
  volume_at_C : volumeInDiagramUnits (process.volumeAt .C) = 3
  pressure_at_C : pressureInDiagramUnits (process.pressureAt .C) = 4
  ab_starts_at_A : process.pathStart .aToB = .A
  ab_finishes_at_B : process.pathFinish .aToB = .B
  bc_starts_at_B : process.pathStart .bToC = .B
  bc_finishes_at_C : process.pathFinish .bToC = .C
  ab_is_quasi_static : process.pathRegime .aToB = .quasiStatic
  bc_is_quasi_static : process.pathRegime .bToC = .quasiStatic
  ab_is_straight : process.pathShape .aToB = .straightLine
  bc_is_straight : process.pathShape .bToC = .straightLine
  label_A_visible : process.stateLabelVisible .A = true
  label_B_visible : process.stateLabelVisible .B = true
  label_C_visible : process.stateLabelVisible .C = true
  pressure_axis_label_visible : process.axisLabelVisible .pressureP = true
  volume_axis_label_visible : process.axisLabelVisible .volumeV = true
  pressure_scale_label_visible :
    process.axisScaleLabelVisible
      .pressureTenToSixDynesPerSquareCentimeter = true
  volume_scale_label_visible :
    process.axisScaleLabelVisible .volumeTenToThreeCubicCentimeters = true
  background_grid_visible : process.gridVisible = true

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalGasParameters
    (process : DiatomicGasPVProcess) : Prop where
  amount_positive : 0 < process.amountOfGasMoles
  gas_constant_positive :
    0 < molarGasConstantInJoulesPerMoleKelvin process.molarGasConstant
  temperature_positive :
    ∀ state, 0 < temperatureInKelvins (process.absoluteTemperatureAt state)
  volume_positive :
    ∀ state, 0 < volumeInCubicMeters (process.volumeAt state)
  pressure_positive :
    ∀ state, 0 < pressureInPascals (process.pressureAt state)

/--
The caloric equation of state stated in the problem: the molar internal energy
is a function only of absolute temperature and obeys
`Uₘ(T) = (5/2) R T`.  This law makes no assertion about work.
-/
structure SatisfiesDiatomicIdealGasCaloricLaw
    (process : DiatomicGasPVProcess) : Prop where
  internal_energy_depends_only_on_temperature :
    ∀ state,
      process.molarInternalEnergyAt state =
        process.molarInternalEnergyFromTemperature
          (process.absoluteTemperatureAt state)
  diatomic_internal_energy_formula :
    ∀ temperature,
      molarInternalEnergyInJoulesPerMole
          (process.molarInternalEnergyFromTemperature temperature) =
        (5 / 2 : ℝ) *
          molarGasConstantInJoulesPerMoleKelvin process.molarGasConstant *
            temperatureInKelvins temperature

/--
Boundary-work law for a quasi-static straight segment in a `pV` diagram.
Linear pressure variation makes the integral `∫ p dV` equal average pressure
times volume change.  The final factor converts diagram-area units to joules.
This general law contains none of the requested segment or total work values.
-/
structure SatisfiesQuasiStaticStraightPathWorkLaw
    (process : DiatomicGasPVProcess) : Prop where
  work_for_quasi_static_straight_leg :
    ∀ leg,
      process.pathRegime leg = .quasiStatic →
      process.pathShape leg = .straightLine →
        workInJoules (process.workByGas leg) =
          ((pressureInDiagramUnits
                (process.pressureAt (process.pathStart leg)) +
              pressureInDiagramUnits
                (process.pressureAt (process.pathFinish leg))) / 2) *
            (volumeInDiagramUnits
                (process.volumeAt (process.pathFinish leg)) -
              volumeInDiagramUnits
                (process.volumeAt (process.pathStart leg))) *
              joulesPerDiagramAreaUnit

/-- Total work by the gas along the concatenated route `A → B → C`. -/
def totalWorkByGasInJoules (process : DiatomicGasPVProcess) : ℝ :=
  workInJoules (process.workByGas .aToB) +
    workInJoules (process.workByGas .bToC)

/-! ## Displayed choices and requested conclusion -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Work readout in joules printed beside each answer label. -/
def displayedWorkInJoules : AnswerChoice → ℝ
  | .A => 1300
  | .B => 1895
  | .C => 1550
  | .D => 1600

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
The two straight legs contribute `700 J` and `600 J`, respectively.  Both
equalities are conclusions derived from the general boundary-work law and the
primary-image readouts; neither occurs in a premise structure.
-/
lemma workAlongStraightProcessLegs
    (process : DiatomicGasPVProcess)
    (_figure : MatchesProblemAndPrimaryFigure process)
    (_workLaw : SatisfiesQuasiStaticStraightPathWorkLaw process) :
    workInJoules (process.workByGas .aToB) = 700 ∧
      workInJoules (process.workByGas .bToC) = 600 := by
  constructor
  · calc
      workInJoules (process.workByGas .aToB) =
          ((pressureInDiagramUnits
                (process.pressureAt (process.pathStart .aToB)) +
              pressureInDiagramUnits
                (process.pressureAt (process.pathFinish .aToB))) / 2) *
            (volumeInDiagramUnits
                (process.volumeAt (process.pathFinish .aToB)) -
              volumeInDiagramUnits
                (process.volumeAt (process.pathStart .aToB))) *
              joulesPerDiagramAreaUnit :=
        _workLaw.work_for_quasi_static_straight_leg .aToB
          _figure.ab_is_quasi_static _figure.ab_is_straight
      _ = 700 := by
        rw [_figure.ab_starts_at_A, _figure.ab_finishes_at_B,
          _figure.pressure_at_A, _figure.pressure_at_B,
          _figure.volume_at_A, _figure.volume_at_B]
        norm_num [joulesPerDiagramAreaUnit, pressureDiagramUnitInPascals,
          volumeDiagramUnitInCubicMeters]
  · calc
      workInJoules (process.workByGas .bToC) =
          ((pressureInDiagramUnits
                (process.pressureAt (process.pathStart .bToC)) +
              pressureInDiagramUnits
                (process.pressureAt (process.pathFinish .bToC))) / 2) *
            (volumeInDiagramUnits
                (process.volumeAt (process.pathFinish .bToC)) -
              volumeInDiagramUnits
                (process.volumeAt (process.pathStart .bToC))) *
              joulesPerDiagramAreaUnit :=
        _workLaw.work_for_quasi_static_straight_leg .bToC
          _figure.bc_is_quasi_static _figure.bc_is_straight
      _ = 600 := by
        rw [_figure.bc_starts_at_B, _figure.bc_finishes_at_C,
          _figure.pressure_at_B, _figure.pressure_at_C,
          _figure.volume_at_B, _figure.volume_at_C]
        norm_num [joulesPerDiagramAreaUnit, pressureDiagramUnitInPascals,
          volumeDiagramUnitInCubicMeters]

/--
The work done by the gas along `A → B → C` is `1300 J`, which is displayed
answer A.

Blueprint label: `thm:physics:phyx_mini_0358:target`.
-/
theorem workDoneByGasAlongABC_eq_1300_joules
    (process : DiatomicGasPVProcess)
    (_data : MatchesProblemAndPrimaryFigure process)
    (_physical : HasPhysicalGasParameters process)
    (_caloricLaw : SatisfiesDiatomicIdealGasCaloricLaw process)
    (_workLaw : SatisfiesQuasiStaticStraightPathWorkLaw process) :
    totalWorkByGasInJoules process = 1300 := by
  obtain ⟨workAB, workBC⟩ :=
    workAlongStraightProcessLegs process _data _workLaw
  rw [totalWorkByGasInJoules, workAB, workBC]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0358
