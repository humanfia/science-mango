import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0376

open Dimension

/-!
# Final pressure in two connected, non-isothermal gas containers

Rigid containers `A` and `B` hold portions of the same ideal gas.  Container
`B` has four times the volume of `A`.  Initially the valve between them is
closed: `A` is at `300 K` and `1.0 * 10^5 Pa`, while `B` is at `400 K` and
`5.0 * 10^5 Pa`.  After the valve opens, separate heaters retain those two
temperatures while gas is redistributed until both pressures agree.

Pressure, volume, absolute temperature, and the molar gas constant retain
their physical roles.  Real numbers below are explicitly named SI readouts,
mole readouts, schematic figure data, or displayed answer values.

The dataset records `5.0 * 10^5 Pa` as the requested answer.  A direct check
of the stated data under ideal-gas conservation instead gives a common final
pressure of `4.0 * 10^5 Pa`, which is absent from the displayed choices.  The
recorded answer is preserved below only as source metadata; the theorem states
the physically supported result, as required by the retry protocol.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A physical gas volume, carrying the length-cubed dimension. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/--
The molar gas constant with its energy-per-temperature dimension.

Physlib's current `Dimension` has no amount-of-substance coordinate, so the
inverse-mole role is recorded by this name and is paired with explicit mole
readouts in the ideal-gas law below.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Read a physical gas volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read Physlib's absolute-temperature value on the calibrated kelvin scale. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Read the molar gas constant in joules per mole-kelvin. -/
def molarGasConstantInSI (gasConstant : MolarGasConstantQuantity) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-! ## Containers, stages, gas portions, and figure vocabulary -/

/-- The container labels printed in the primary figure. -/
inductive ContainerLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The two thermodynamic stages relevant to the question. -/
inductive ProcessStage where
  | beforeValveOpens
  | afterPressureEquilibrates
  deriving DecidableEq, Repr

/-- Horizontal positions of the two containers in the primary figure. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Shape used to draw each gas vessel. -/
inductive ContainerShape where
  | rectangular
  | other
  deriving DecidableEq, Repr

/-- Position of the valve at a modeled stage. -/
inductive ValvePosition where
  | closed
  | open
  deriving DecidableEq, Repr

/-- The thin connecting tube and its negligible-volume idealization. -/
inductive ConnectionModel where
  | thinTubeWithNegligibleVolume
  | other
  deriving DecidableEq, Repr

/-- Operating mode of a heater attached to a container. -/
inductive HeaterMode where
  | maintainsTemperature
  | inactive
  deriving DecidableEq, Repr

/-- The ideal-gas model named by the problem. -/
inductive GasModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/--
An abstract gas species.  The problem does not identify the chemical species;
it only states that both vessels contain the same one.
-/
inductive GasSpecies where
  | unspecified
  | other
  deriving DecidableEq, Repr

/--
A physical portion of gas, with a species and an explicit amount readout in
moles.  This is not a scalar alias: it retains which gas the amount describes.
-/
structure GasPortion where
  species : GasSpecies
  amountInMoles : ℝ

/-- Figure-only labels and geometry read directly from the supplied image. -/
structure TwoContainerValveFigure where
  sideOf : ContainerLabel → FigureSide
  containerLabelVisible : ContainerLabel → Bool
  temperatureLabelKelvins : ContainerLabel → ℝ
  valveLabelVisible : Bool
  connectingTubeVisible : Bool

/-!
The two rigid containers, their thermodynamic data before and after opening,
and the physical equipment connecting them.  The common final pressure is not
stored as a separate scalar and is not assigned a numerical value here.
-/
structure ConnectedGasContainers where
  gasModel : GasModel
  commonGasSpecies : GasSpecies
  containerShape : ContainerLabel → ContainerShape
  containerVolume : ContainerLabel → GasVolume
  pressureAt : ProcessStage → ContainerLabel → DimPressure
  temperatureAt : ProcessStage → ContainerLabel → Temperature
  gasPortionAt : ProcessStage → ContainerLabel → GasPortion
  molarGasConstant : MolarGasConstantQuantity
  valvePositionAt : ProcessStage → ValvePosition
  connectionModel : ConnectionModel
  connectingTubeVolume : GasVolume
  heaterMode : ContainerLabel → HeaterMode
  temperatureReadoutUnit : TemperatureUnit
  figure : TwoContainerValveFigure

/-! ## Source data, operating conditions, and governing laws -/

/--
Primary-image readouts.  The image shows `A` on the left, `B` on the right,
the labels `300 K` and `400 K`, a connecting tube, and a labeled valve.  It
does not display either pressure or the volume ratio.
-/
structure MatchesPrimaryFigure (setup : ConnectedGasContainers) : Prop where
  containerAIsLeft : setup.figure.sideOf .A = .left
  containerBIsRight : setup.figure.sideOf .B = .right
  containerALabelVisible : setup.figure.containerLabelVisible .A = true
  containerBLabelVisible : setup.figure.containerLabelVisible .B = true
  containersAreRectangular :
    ∀ container, setup.containerShape container = .rectangular
  containerATemperatureLabel :
    setup.figure.temperatureLabelKelvins .A = 300
  containerBTemperatureLabel :
    setup.figure.temperatureLabelKelvins .B = 400
  temperatureLabelsMatchInitialGas :
    ∀ container,
      setup.figure.temperatureLabelKelvins container =
        temperatureInKelvins
          (setup.temperatureAt .beforeValveOpens container)
  valveLabelIsVisible : setup.figure.valveLabelVisible = true
  connectingTubeIsVisible : setup.figure.connectingTubeVisible = true

/--
Data stated in the prose.  These fields specify the initial condition and the
equipment, but do not state a numerical final pressure.
-/
structure MatchesProblemStatement (setup : ConnectedGasContainers) : Prop where
  gasIsIdeal : setup.gasModel = .ideal
  bothContainersHoldSameGas :
    ∀ stage container,
      (setup.gasPortionAt stage container).species = setup.commonGasSpecies
  containerBHasFourTimesVolumeA :
    volumeInCubicMeters (setup.containerVolume .B) =
      4 * volumeInCubicMeters (setup.containerVolume .A)
  initialPressureA :
    pressureInPascals (setup.pressureAt .beforeValveOpens .A) = 100000
  initialPressureB :
    pressureInPascals (setup.pressureAt .beforeValveOpens .B) = 500000
  initialValveIsClosed :
    setup.valvePositionAt .beforeValveOpens = .closed
  finalValveIsOpen :
    setup.valvePositionAt .afterPressureEquilibrates = .open
  usesThinNegligibleVolumeTube :
    setup.connectionModel = .thinTubeWithNegligibleVolume
  connectingTubeVolumeIsNegligible :
    volumeInCubicMeters setup.connectingTubeVolume = 0
  heatersOperate :
    ∀ container, setup.heaterMode container = .maintainsTemperature
  temperaturesAreReadInKelvins :
    setup.temperatureReadoutUnit = .kelvin

/-- The quantitative effect of the two operating heaters. -/
structure HeatersMaintainTemperatures
    (setup : ConnectedGasContainers) : Prop where
  fixedContainerTemperature :
    ∀ container,
      temperatureInKelvins
          (setup.temperatureAt .afterPressureEquilibrates container) =
        temperatureInKelvins
          (setup.temperatureAt .beforeValveOpens container)

/-- Positivity conditions selecting physical pressures, volumes, and amounts. -/
structure HasPhysicalParameters (setup : ConnectedGasContainers) : Prop where
  containerVolumePositive :
    ∀ container, 0 < volumeInCubicMeters (setup.containerVolume container)
  pressurePositive :
    ∀ stage container, 0 < pressureInPascals (setup.pressureAt stage container)
  absoluteTemperaturePositive :
    ∀ stage container,
      0 < temperatureInKelvins (setup.temperatureAt stage container)
  gasAmountPositive :
    ∀ stage container, 0 < (setup.gasPortionAt stage container).amountInMoles
  molarGasConstantPositive :
    0 < molarGasConstantInSI setup.molarGasConstant

/-!
Macroscopic ideal-gas and closed-system conservation laws.  Because the tube
has negligible volume, all gas amount is accounted for by the two container
portions.  Neither law supplies a numerical final pressure.
-/
structure ObeysIdealGasAndAmountConservation
    (setup : ConnectedGasContainers) : Prop where
  idealGasLaw :
    ∀ stage container,
      pressureInPascals (setup.pressureAt stage container) *
          volumeInCubicMeters (setup.containerVolume container) =
        (setup.gasPortionAt stage container).amountInMoles *
          molarGasConstantInSI setup.molarGasConstant *
            temperatureInKelvins (setup.temperatureAt stage container)
  totalGasAmountConserved :
    (setup.gasPortionAt .beforeValveOpens .A).amountInMoles +
        (setup.gasPortionAt .beforeValveOpens .B).amountInMoles =
      (setup.gasPortionAt .afterPressureEquilibrates .A).amountInMoles +
        (setup.gasPortionAt .afterPressureEquilibrates .B).amountInMoles

/-- Opening the valve allows flow until the two final pressures are equal. -/
structure ReachesPressureEquilibrium
    (setup : ConnectedGasContainers) : Prop where
  finalPressuresEqual :
    pressureInPascals (setup.pressureAt .afterPressureEquilibrates .A) =
      pressureInPascals (setup.pressureAt .afterPressureEquilibrates .B)

/-! ## Displayed choices and requested conclusion -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Pascal value printed beside each answer label in the source. -/
def answerPressureInPascals : AnswerChoice → ℝ
  | .A => 500000
  | .B => 550000
  | .C => 540000
  | .D => 590000

/-- Answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
The physically supported common final pressure.  After cancelling the
positive common gas constant and the volume of `A`, the faithfully modeled
conservation law reads

`100000 / 300 + 4 * 500000 / 400 = p_f / 300 + 4 * p_f / 400`,

whose solution is `p_f = 400000`.  This value is absent from the displayed
choices and disagrees with recorded answer A (`500000 Pa`).

Blueprint label: `thm:physics:phyx_mini_0376:target`.
-/
theorem finalPressureInPascals_eq_fourHundredThousand
    (setup : ConnectedGasContainers)
    (_figure : MatchesPrimaryFigure setup)
    (_problem : MatchesProblemStatement setup)
    (_heaters : HeatersMaintainTemperatures setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : ObeysIdealGasAndAmountConservation setup)
    (_equilibrium : ReachesPressureEquilibrium setup) :
    ∀ container,
      pressureInPascals
          (setup.pressureAt .afterPressureEquilibrates container) = 400000 := by
  have hTemperatureBeforeA :
      temperatureInKelvins
          (setup.temperatureAt .beforeValveOpens .A) = 300 := by
    calc
      temperatureInKelvins
          (setup.temperatureAt .beforeValveOpens .A) =
          setup.figure.temperatureLabelKelvins .A :=
        (_figure.temperatureLabelsMatchInitialGas .A).symm
      _ = 300 := _figure.containerATemperatureLabel
  have hTemperatureBeforeB :
      temperatureInKelvins
          (setup.temperatureAt .beforeValveOpens .B) = 400 := by
    calc
      temperatureInKelvins
          (setup.temperatureAt .beforeValveOpens .B) =
          setup.figure.temperatureLabelKelvins .B :=
        (_figure.temperatureLabelsMatchInitialGas .B).symm
      _ = 400 := _figure.containerBTemperatureLabel
  have hTemperatureAfterA :
      temperatureInKelvins
          (setup.temperatureAt .afterPressureEquilibrates .A) = 300 := by
    calc
      temperatureInKelvins
          (setup.temperatureAt .afterPressureEquilibrates .A) =
          temperatureInKelvins
            (setup.temperatureAt .beforeValveOpens .A) :=
        _heaters.fixedContainerTemperature .A
      _ = 300 := hTemperatureBeforeA
  have hTemperatureAfterB :
      temperatureInKelvins
          (setup.temperatureAt .afterPressureEquilibrates .B) = 400 := by
    calc
      temperatureInKelvins
          (setup.temperatureAt .afterPressureEquilibrates .B) =
          temperatureInKelvins
            (setup.temperatureAt .beforeValveOpens .B) :=
        _heaters.fixedContainerTemperature .B
      _ = 400 := hTemperatureBeforeB
  have hInitialA := _laws.idealGasLaw .beforeValveOpens .A
  rw [_problem.initialPressureA, hTemperatureBeforeA] at hInitialA
  have hInitialB := _laws.idealGasLaw .beforeValveOpens .B
  rw [_problem.initialPressureB, _problem.containerBHasFourTimesVolumeA,
    hTemperatureBeforeB] at hInitialB
  have hFinalA := _laws.idealGasLaw .afterPressureEquilibrates .A
  rw [hTemperatureAfterA] at hFinalA
  have hFinalB := _laws.idealGasLaw .afterPressureEquilibrates .B
  rw [_problem.containerBHasFourTimesVolumeA, hTemperatureAfterB] at hFinalB
  have hAmountConservation :=
    congrArg
      (fun amount : ℝ =>
        amount * molarGasConstantInSI setup.molarGasConstant)
      _laws.totalGasAmountConserved
  have hFinalPressureA :
      pressureInPascals
          (setup.pressureAt .afterPressureEquilibrates .A) = 400000 := by
    nlinarith
      [hInitialA, hInitialB, hFinalA, hFinalB, hAmountConservation,
        _problem.containerBHasFourTimesVolumeA,
        _physical.containerVolumePositive .A,
        _physical.molarGasConstantPositive,
        _equilibrium.finalPressuresEqual]
  have hFinalPressureB :
      pressureInPascals
          (setup.pressureAt .afterPressureEquilibrates .B) = 400000 := by
    rw [← _equilibrium.finalPressuresEqual]
    exact hFinalPressureA
  intro container
  cases container with
  | A => exact hFinalPressureA
  | B => exact hFinalPressureB

end PhyXMiniProblems.ProblemPhyXMini0376
