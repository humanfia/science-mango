import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0428

open Dimension

/-!
# Efficiency of a monatomic-gas heat-engine cycle

The primary image shows the directed pressure--volume cycle

`1 → 2 → 3 → 1`.

States `1` and `2` lie at the pressure labelled `p_max`; state `1` has
volume `100 cm³`, while states `2` and `3` have volume `600 cm³`.  State `3`
has pressure `100 kPa`, and the image attaches the temperature `600 K` to
state `2`.  The first leg is isobaric, the second is isochoric, and the curved
return leg is adiabatic.

Pressure, volume, heat, work, and internal-energy change are represented by
dimensionful quantities.  Real numbers are used only for calibrated unit
readouts, mole and gas-constant readouts, dimensionless ratios, and displayed
answer values.  Heat is positive into the gas and work is positive when done
by the gas.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A physical gas volume carrying the dimension length cubed. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Coherent-SI pressure readout, in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure readout in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Coherent-SI volume readout, in cubic metres. -/
def volumeInCubicMetres (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/-- Volume readout in the cubic centimetres printed on the horizontal axis. -/
def volumeInCubicCentimetres (volume : GasVolume) : ℝ :=
  volumeInCubicMetres volume * 1000000

/-- Coherent-SI signed-energy readout, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Absolute-temperature readout in kelvins.

The `Temperature` values in this setup are calibrated in the kelvin unit, as
fixed by the `600 K` label in the supplied figure.
-/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Gas, cycle, and figure vocabulary -/

/-- The working-substance model stated in the problem. -/
inductive GasModel where
  | monatomicIdealGas
  deriving DecidableEq, Repr

/-- The thermodynamic role of the cyclic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- Labels of the three black equilibrium states in the diagram. -/
inductive StateLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- Directed legs indicated by the arrowheads in the diagram. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic constraint written or geometrically displayed on a leg. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  | adiabatic
  deriving DecidableEq, Repr

/-- Geometric appearance of a leg in the primary raster. -/
inductive PathGeometry where
  | horizontalSegment
  | verticalSegment
  | curvedSegment
  deriving DecidableEq, Repr

/-- Quantity assigned to one of the two diagram axes. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit printed next to a diagram axis. -/
inductive AxisUnit where
  | cubicCentimetre
  | kilopascal
  deriving DecidableEq, Repr

/-- Text or numerical annotations visibly present in the source image. -/
inductive DiagramLabel where
  | stateOne
  | stateTwo
  | stateThree
  | pressureMaximum
  | pressure100
  | volume0
  | volume200
  | volume400
  | volume600
  | temperature600Kelvin
  | adiabatic
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint prescribed by the displayed arrow direction. -/
def expectedLegStart : CycleLeg → StateLabel
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final endpoint prescribed by the displayed arrow direction. -/
def expectedLegFinish : CycleLeg → StateLabel
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Process classification read from the horizontal, vertical, and labelled
curved paths. -/
def expectedProcessKind : CycleLeg → ProcessKind
  | .oneToTwo => .isobaric
  | .twoToThree => .isochoric
  | .threeToOne => .adiabatic

/-- Geometry of each path in the pressure--volume plane. -/
def expectedPathGeometry : CycleLeg → PathGeometry
  | .oneToTwo => .horizontalSegment
  | .twoToThree => .verticalSegment
  | .threeToOne => .curvedSegment

/-- Pressure, volume, and absolute temperature at an equilibrium state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : GasVolume
  temperature : Temperature

/-- Diagram-level data independent of the thermodynamic laws. -/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisUnit : AxisUnit
  labelVisible : DiagramLabel → Bool
  stateVisible : StateLabel → Bool
  legVisible : CycleLeg → Bool
  legStart : CycleLeg → StateLabel
  legFinish : CycleLeg → StateLabel
  processKind : CycleLeg → ProcessKind
  pathGeometry : CycleLeg → PathGeometry

/-!
The physical gas sample, its state variables, and the signed energy transfers
on the three legs.  Neither thermal efficiency nor any answer choice is a
field of this structure.
-/
structure MonatomicIdealGasHeatEngineCycle where
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  sameClosedGasSample : Bool
  quasistaticEquilibriumPath : Bool
  amountOfGasMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  heatCapacityRatio : ℝ
  maximumPressure : DimPressure
  stateAt : StateLabel → ThermodynamicState
  workDoneByGas : CycleLeg → DimEnergy
  heatTransferredIntoGas : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  diagram : PressureVolumeDiagram

/-! ## Assumptions: scenario, figure readouts, and governing laws -/

/-- Prose-level model assumptions: a closed monatomic ideal-gas heat engine.
The value `5/3` is the heat-capacity ratio of a monatomic ideal gas. -/
structure MatchesProblemStatement
    (cycle : MonatomicIdealGasHeatEngineCycle) : Prop where
  gasIsMonatomicIdeal : cycle.gasModel = .monatomicIdealGas
  deviceIsHeatEngine : cycle.deviceRole = .heatEngine
  sameClosedSample : cycle.sameClosedGasSample = true
  pathIsQuasistatic : cycle.quasistaticEquilibriumPath = true
  monatomicHeatCapacityRatio : cycle.heatCapacityRatio = (5 / 3 : ℝ)

/-!
Primary-image evidence: axes and units, visible labels, directed path types,
the three volume coordinates, the `100 kPa` pressure at state `3`, the common
pressure `p_max` at states `1` and `2`, and the `600 K` readout at state `2`.
No heat, work, or efficiency conclusion occurs here.
-/
structure MatchesSuppliedPressureVolumeDiagram
    (cycle : MonatomicIdealGasHeatEngineCycle) : Prop where
  horizontalAxisIsVolume :
    cycle.diagram.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    cycle.diagram.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimetres :
    cycle.diagram.horizontalAxisUnit = .cubicCentimetre
  verticalAxisUsesKilopascals :
    cycle.diagram.verticalAxisUnit = .kilopascal
  everyPrintedLabelVisible :
    ∀ label : DiagramLabel, cycle.diagram.labelVisible label = true
  everyStateVisible :
    ∀ state : StateLabel, cycle.diagram.stateVisible state = true
  everyDirectedLegVisible :
    ∀ leg : CycleLeg, cycle.diagram.legVisible leg = true
  arrowDirectionsAgree :
    ∀ leg : CycleLeg,
      cycle.diagram.legStart leg = expectedLegStart leg ∧
        cycle.diagram.legFinish leg = expectedLegFinish leg
  processKindsAgree :
    ∀ leg : CycleLeg,
      cycle.diagram.processKind leg = expectedProcessKind leg
  pathGeometriesAgree :
    ∀ leg : CycleLeg,
      cycle.diagram.pathGeometry leg = expectedPathGeometry leg
  stateOneVolumeCubicCentimetres :
    volumeInCubicCentimetres (cycle.stateAt .one).volume = 100
  stateTwoVolumeCubicCentimetres :
    volumeInCubicCentimetres (cycle.stateAt .two).volume = 600
  stateThreeVolumeCubicCentimetres :
    volumeInCubicCentimetres (cycle.stateAt .three).volume = 600
  stateOneAtMaximumPressure :
    (cycle.stateAt .one).pressure = cycle.maximumPressure
  stateTwoAtMaximumPressure :
    (cycle.stateAt .two).pressure = cycle.maximumPressure
  maximumPressureDominatesStates :
    ∀ state : StateLabel,
      pressureInPascals (cycle.stateAt state).pressure ≤
        pressureInPascals cycle.maximumPressure
  stateThreePressureKilopascals :
    pressureInKilopascals (cycle.stateAt .three).pressure = 100
  stateTwoTemperatureKelvins :
    temperatureInKelvins (cycle.stateAt .two).temperature = 600

/-- Positivity and nondegeneracy conditions selecting physical state readouts. -/
structure HasPhysicalThermodynamicParameters
    (cycle : MonatomicIdealGasHeatEngineCycle) : Prop where
  amountPositive : 0 < cycle.amountOfGasMoles
  gasConstantPositive : 0 < cycle.molarGasConstantJoulesPerMoleKelvin
  heatCapacityRatioGreaterThanOne : 1 < cycle.heatCapacityRatio
  maximumPressurePositive : 0 < pressureInPascals cycle.maximumPressure
  pressurePositive :
    ∀ state : StateLabel,
      0 < pressureInPascals (cycle.stateAt state).pressure
  volumePositive :
    ∀ state : StateLabel,
      0 < volumeInCubicMetres (cycle.stateAt state).volume
  temperaturePositive :
    ∀ state : StateLabel,
      0 < temperatureInKelvins (cycle.stateAt state).temperature

/-!
Macroscopic thermodynamic laws used to analyze the cycle:

* `pV = nRT` at each equilibrium state;
* `ΔU = (3/2)nRΔT` for a monatomic ideal gas;
* `Q_into = ΔU + W_by` on every leg;
* the usual quasistatic boundary-work laws on isobaric and isochoric legs;
* `p_f/p_i = (V_i/V_f)^γ` and zero heat on an adiabatic leg.

The laws are uniform in the leg and contain no numerical efficiency or answer
choice.
-/
structure ObeysMonatomicIdealGasCycleLaws
    (cycle : MonatomicIdealGasHeatEngineCycle) : Prop where
  idealGasLaw : ∀ state : StateLabel,
    pressureInPascals (cycle.stateAt state).pressure *
        volumeInCubicMetres (cycle.stateAt state).volume =
      cycle.amountOfGasMoles *
        cycle.molarGasConstantJoulesPerMoleKelvin *
        temperatureInKelvins (cycle.stateAt state).temperature
  monatomicInternalEnergyLaw : ∀ leg : CycleLeg,
    energyInJoules (cycle.internalEnergyChange leg) =
      (3 / 2 : ℝ) * cycle.amountOfGasMoles *
        cycle.molarGasConstantJoulesPerMoleKelvin *
        (temperatureInKelvins
              (cycle.stateAt (cycle.diagram.legFinish leg)).temperature -
          temperatureInKelvins
              (cycle.stateAt (cycle.diagram.legStart leg)).temperature)
  firstLaw : ∀ leg : CycleLeg,
    energyInJoules (cycle.heatTransferredIntoGas leg) =
      energyInJoules (cycle.internalEnergyChange leg) +
        energyInJoules (cycle.workDoneByGas leg)
  isobaricBoundaryWorkLaw : ∀ leg : CycleLeg,
    cycle.diagram.processKind leg = .isobaric →
      pressureInPascals
          (cycle.stateAt (cycle.diagram.legFinish leg)).pressure =
        pressureInPascals
          (cycle.stateAt (cycle.diagram.legStart leg)).pressure ∧
      energyInJoules (cycle.workDoneByGas leg) =
        pressureInPascals
            (cycle.stateAt (cycle.diagram.legStart leg)).pressure *
          (volumeInCubicMetres
                (cycle.stateAt (cycle.diagram.legFinish leg)).volume -
            volumeInCubicMetres
                (cycle.stateAt (cycle.diagram.legStart leg)).volume)
  isochoricBoundaryWorkLaw : ∀ leg : CycleLeg,
    cycle.diagram.processKind leg = .isochoric →
      volumeInCubicMetres
          (cycle.stateAt (cycle.diagram.legFinish leg)).volume =
        volumeInCubicMetres
          (cycle.stateAt (cycle.diagram.legStart leg)).volume ∧
      energyInJoules (cycle.workDoneByGas leg) = 0
  adiabaticPressureVolumeLaw : ∀ leg : CycleLeg,
    cycle.diagram.processKind leg = .adiabatic →
      pressureInPascals
            (cycle.stateAt (cycle.diagram.legFinish leg)).pressure /
          pressureInPascals
            (cycle.stateAt (cycle.diagram.legStart leg)).pressure =
        Real.rpow
          (volumeInCubicMetres
                (cycle.stateAt (cycle.diagram.legStart leg)).volume /
            volumeInCubicMetres
                (cycle.stateAt (cycle.diagram.legFinish leg)).volume)
          cycle.heatCapacityRatio
  adiabaticNoHeat : ∀ leg : CycleLeg,
    cycle.diagram.processKind leg = .adiabatic →
      energyInJoules (cycle.heatTransferredIntoGas leg) = 0

/-! ## Heat accounting, efficiency, and displayed answers -/

/-- Net work done by the gas in one traversal of the closed cycle. -/
def netWorkDoneByGasInJoules
    (cycle : MonatomicIdealGasHeatEngineCycle) : ℝ :=
  energyInJoules (cycle.workDoneByGas .oneToTwo) +
    energyInJoules (cycle.workDoneByGas .twoToThree) +
    energyInJoules (cycle.workDoneByGas .threeToOne)

/-- Total heat absorbed by the gas, the sum of positive signed leg heats. -/
def totalHeatInputInJoules
    (cycle : MonatomicIdealGasHeatEngineCycle) : ℝ :=
  max (energyInJoules (cycle.heatTransferredIntoGas .oneToTwo)) 0 +
    max (energyInJoules (cycle.heatTransferredIntoGas .twoToThree)) 0 +
    max (energyInJoules (cycle.heatTransferredIntoGas .threeToOne)) 0

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency
    (cycle : MonatomicIdealGasHeatEngineCycle) : ℝ :=
  netWorkDoneByGasInJoules cycle / totalHeatInputInJoules cycle

/-- Labels of the four choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless decimal value printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 2 / 5
  | .B => 16 / 25
  | .C => 79 / 250
  | .D => 8 / 25

/-- Answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A dimensionless value rounds to a specified two-decimal display. -/
def RoundsToTwoDecimalPlaces (value displayed : ℝ) : Prop :=
  displayed - (1 / 200 : ℝ) ≤ value ∧
    value < displayed + (1 / 200 : ℝ)

/-- Exact dimensionless efficiency predicted by the figure and laws. -/
def exactEfficiencyFromFigure : ℝ :=
  ((7 : ℝ) + 3 / Real.rpow 6 (2 / 3 : ℝ)) / 25

/-!
The figure and governing laws first determine `T₁ = 100 K` and
`T₃ = 100 / 6^(2/3) K`.  The first two leg heats and the total work then
follow from the monatomic internal-energy law and the first law.  These are
derived conclusions, not fields of a scenario, figure, or law structure.
-/
lemma derivedTemperatureHeatAndWorkReadouts
    (cycle : MonatomicIdealGasHeatEngineCycle)
    (_problem : MatchesProblemStatement cycle)
    (_figure : MatchesSuppliedPressureVolumeDiagram cycle)
    (_physical : HasPhysicalThermodynamicParameters cycle)
    (_laws : ObeysMonatomicIdealGasCycleLaws cycle) :
    temperatureInKelvins (cycle.stateAt .one).temperature = 100 ∧
      temperatureInKelvins (cycle.stateAt .three).temperature =
        100 / Real.rpow 6 (2 / 3 : ℝ) ∧
      energyInJoules (cycle.heatTransferredIntoGas .oneToTwo) =
        1250 * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin ∧
      energyInJoules (cycle.heatTransferredIntoGas .twoToThree) =
        (3 / 2 : ℝ) * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          (100 / Real.rpow 6 (2 / 3 : ℝ) - 600) ∧
      energyInJoules (cycle.heatTransferredIntoGas .threeToOne) = 0 ∧
      netWorkDoneByGasInJoules cycle =
        cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          (350 + 150 / Real.rpow 6 (2 / 3 : ℝ)) := by
  have hStart₁₂ :
      cycle.diagram.legStart .oneToTwo = .one := by
    simpa [expectedLegStart] using
      (_figure.arrowDirectionsAgree .oneToTwo).1
  have hFinish₁₂ :
      cycle.diagram.legFinish .oneToTwo = .two := by
    simpa [expectedLegFinish] using
      (_figure.arrowDirectionsAgree .oneToTwo).2
  have hStart₂₃ :
      cycle.diagram.legStart .twoToThree = .two := by
    simpa [expectedLegStart] using
      (_figure.arrowDirectionsAgree .twoToThree).1
  have hFinish₂₃ :
      cycle.diagram.legFinish .twoToThree = .three := by
    simpa [expectedLegFinish] using
      (_figure.arrowDirectionsAgree .twoToThree).2
  have hStart₃₁ :
      cycle.diagram.legStart .threeToOne = .three := by
    simpa [expectedLegStart] using
      (_figure.arrowDirectionsAgree .threeToOne).1
  have hFinish₃₁ :
      cycle.diagram.legFinish .threeToOne = .one := by
    simpa [expectedLegFinish] using
      (_figure.arrowDirectionsAgree .threeToOne).2
  have hKind₁₂ :
      cycle.diagram.processKind .oneToTwo = .isobaric := by
    simpa [expectedProcessKind] using
      _figure.processKindsAgree .oneToTwo
  have hKind₂₃ :
      cycle.diagram.processKind .twoToThree = .isochoric := by
    simpa [expectedProcessKind] using
      _figure.processKindsAgree .twoToThree
  have hKind₃₁ :
      cycle.diagram.processKind .threeToOne = .adiabatic := by
    simpa [expectedProcessKind] using
      _figure.processKindsAgree .threeToOne

  have hV₁ :
      volumeInCubicMetres (cycle.stateAt .one).volume =
        (1 / 10000 : ℝ) := by
    have h := _figure.stateOneVolumeCubicCentimetres
    simp only [volumeInCubicCentimetres] at h
    norm_num at h ⊢
    linarith
  have hV₂ :
      volumeInCubicMetres (cycle.stateAt .two).volume =
        (3 / 5000 : ℝ) := by
    have h := _figure.stateTwoVolumeCubicCentimetres
    simp only [volumeInCubicCentimetres] at h
    norm_num at h ⊢
    linarith
  have hV₃ :
      volumeInCubicMetres (cycle.stateAt .three).volume =
        (3 / 5000 : ℝ) := by
    have h := _figure.stateThreeVolumeCubicCentimetres
    simp only [volumeInCubicCentimetres] at h
    norm_num at h ⊢
    linarith
  have hP₃ :
      pressureInPascals (cycle.stateAt .three).pressure = 100000 := by
    have h := _figure.stateThreePressureKilopascals
    simp only [pressureInKilopascals] at h
    linarith
  have hP₁₂ :
      pressureInPascals (cycle.stateAt .one).pressure =
        pressureInPascals (cycle.stateAt .two).pressure := by
    rw [_figure.stateOneAtMaximumPressure,
      _figure.stateTwoAtMaximumPressure]
  have hT₂ :
      temperatureInKelvins (cycle.stateAt .two).temperature = 600 :=
    _figure.stateTwoTemperatureKelvins
  have hNRPos :
      0 <
        cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin :=
    mul_pos _physical.amountPositive _physical.gasConstantPositive

  have hIdeal₁ := _laws.idealGasLaw .one
  have hIdeal₂ := _laws.idealGasLaw .two
  have hIdeal₃ := _laws.idealGasLaw .three
  have hT₁ :
      temperatureInKelvins (cycle.stateAt .one).temperature = 100 := by
    rw [hV₁] at hIdeal₁
    rw [hV₂, hT₂] at hIdeal₂
    nlinarith

  have hAdiabatic :=
    _laws.adiabaticPressureVolumeLaw .threeToOne hKind₃₁
  simp only [hFinish₃₁, hStart₃₁] at hAdiabatic
  rw [hV₃, hV₁, _problem.monatomicHeatCapacityRatio] at hAdiabatic
  norm_num at hAdiabatic
  have hRpowSplit :
      Real.rpow 6 (5 / 3 : ℝ) =
        6 * Real.rpow 6 (2 / 3 : ℝ) := by
    have h := Real.rpow_add (x := (6 : ℝ))
      (by norm_num : (0 : ℝ) < 6) (1 : ℝ) (2 / 3 : ℝ)
    norm_num at h ⊢
    exact h
  change
    pressureInPascals (cycle.stateAt .one).pressure /
        pressureInPascals (cycle.stateAt .three).pressure =
      Real.rpow 6 (5 / 3 : ℝ) at hAdiabatic
  rw [hRpowSplit] at hAdiabatic
  have hRpowPos :
      0 < Real.rpow 6 (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hNRRpow :
      cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin =
        (3 / 5 : ℝ) * Real.rpow 6 (2 / 3 : ℝ) := by
    rw [hV₂, hT₂] at hIdeal₂
    rw [hP₃] at hAdiabatic
    nlinarith [hP₁₂]
  have hT₃ :
      temperatureInKelvins (cycle.stateAt .three).temperature =
        100 / Real.rpow 6 (2 / 3 : ℝ) := by
    rw [hP₃, hV₃] at hIdeal₃
    apply (eq_div_iff hRpowPos.ne').2
    nlinarith [hNRRpow]

  have hWork₁₂ :
      energyInJoules (cycle.workDoneByGas .oneToTwo) =
        500 * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin := by
    have h :=
      (_laws.isobaricBoundaryWorkLaw .oneToTwo hKind₁₂).2
    simp only [hFinish₁₂, hStart₁₂] at h
    rw [hV₁, hV₂] at h
    rw [hV₂, hT₂] at hIdeal₂
    nlinarith [hP₁₂]
  have hInternal₁₂ :
      energyInJoules (cycle.internalEnergyChange .oneToTwo) =
        750 * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin := by
    have h := _laws.monatomicInternalEnergyLaw .oneToTwo
    simp only [hFinish₁₂, hStart₁₂] at h
    rw [hT₁, hT₂] at h
    norm_num at h ⊢
    ring_nf at h ⊢
    exact h
  have hHeat₁₂ :
      energyInJoules (cycle.heatTransferredIntoGas .oneToTwo) =
        1250 * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin := by
    rw [_laws.firstLaw .oneToTwo, hInternal₁₂, hWork₁₂]
    ring

  have hWork₂₃ :
      energyInJoules (cycle.workDoneByGas .twoToThree) = 0 :=
    (_laws.isochoricBoundaryWorkLaw .twoToThree hKind₂₃).2
  have hInternal₂₃ :
      energyInJoules (cycle.internalEnergyChange .twoToThree) =
        (3 / 2 : ℝ) * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          (100 / Real.rpow 6 (2 / 3 : ℝ) - 600) := by
    have h := _laws.monatomicInternalEnergyLaw .twoToThree
    simp only [hFinish₂₃, hStart₂₃] at h
    rw [hT₂, hT₃] at h
    exact h
  have hHeat₂₃ :
      energyInJoules (cycle.heatTransferredIntoGas .twoToThree) =
        (3 / 2 : ℝ) * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          (100 / Real.rpow 6 (2 / 3 : ℝ) - 600) := by
    rw [_laws.firstLaw .twoToThree, hInternal₂₃, hWork₂₃, add_zero]

  have hHeat₃₁ :
      energyInJoules (cycle.heatTransferredIntoGas .threeToOne) = 0 :=
    _laws.adiabaticNoHeat .threeToOne hKind₃₁
  have hInternal₃₁ :
      energyInJoules (cycle.internalEnergyChange .threeToOne) =
        (3 / 2 : ℝ) * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          (100 - 100 / Real.rpow 6 (2 / 3 : ℝ)) := by
    have h := _laws.monatomicInternalEnergyLaw .threeToOne
    simp only [hFinish₃₁, hStart₃₁] at h
    rw [hT₁, hT₃] at h
    exact h
  have hWork₃₁ :
      energyInJoules (cycle.workDoneByGas .threeToOne) =
        (3 / 2 : ℝ) * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          (100 / Real.rpow 6 (2 / 3 : ℝ) - 100) := by
    have h := _laws.firstLaw .threeToOne
    rw [hHeat₃₁, hInternal₃₁] at h
    linarith
  have hNetWork :
      netWorkDoneByGasInJoules cycle =
        cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin *
          (350 + 150 / Real.rpow 6 (2 / 3 : ℝ)) := by
    rw [netWorkDoneByGasInJoules, hWork₁₂, hWork₂₃, hWork₃₁]
    ring

  exact ⟨hT₁, hT₃, hHeat₁₂, hHeat₂₃, hHeat₃₁, hNetWork⟩

/-!
The exact efficiency is

`(7 + 3 / 6^(2/3)) / 25 ≈ 0.31634`.

Consequently it rounds to `0.32` at two decimal places, matching recorded
answer D.  The use of a rounding predicate avoids falsely equating the exact
irrational expression with the displayed decimal.

This formalizes `thm:physics:phyx_mini_0428:target`.
-/
theorem problem_phyx_mini_0428
    (cycle : MonatomicIdealGasHeatEngineCycle)
    (_problem : MatchesProblemStatement cycle)
    (_figure : MatchesSuppliedPressureVolumeDiagram cycle)
    (_physical : HasPhysicalThermodynamicParameters cycle)
    (_laws : ObeysMonatomicIdealGasCycleLaws cycle) :
    thermalEfficiency cycle = exactEfficiencyFromFigure ∧
      RoundsToTwoDecimalPlaces
        (thermalEfficiency cycle)
        (displayedEfficiency recordedAnswerChoice) := by
  rcases derivedTemperatureHeatAndWorkReadouts
      cycle _problem _figure _physical _laws with
    ⟨_, _, hHeat₁₂, hHeat₂₃, hHeat₃₁, hNetWork⟩
  have hNRPos :
      0 <
        cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin :=
    mul_pos _physical.amountPositive _physical.gasConstantPositive
  have hRpowPos :
      0 < Real.rpow 6 (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hRpowCube :
      (Real.rpow 6 (2 / 3 : ℝ)) ^ 3 = 36 := by
    have h := Real.rpow_mul_natCast (x := (6 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 6) (2 / 3 : ℝ) 3
    norm_num at h ⊢
    exact h.symm
  have hRpowLower :
      (8 / 3 : ℝ) < Real.rpow 6 (2 / 3 : ℝ) := by
    by_contra h
    have hCubeLe :
        (Real.rpow 6 (2 / 3 : ℝ)) ^ 3 ≤ (8 / 3 : ℝ) ^ 3 :=
      (Odd.strictMono_pow (by decide : Odd 3)).monotone
        (le_of_not_gt h)
    rw [hRpowCube] at hCubeLe
    norm_num at hCubeLe
  have hRpowUpper :
      Real.rpow 6 (2 / 3 : ℝ) ≤ (24 / 7 : ℝ) := by
    by_contra h
    have hCubeLt :
        (24 / 7 : ℝ) ^ 3 <
          (Real.rpow 6 (2 / 3 : ℝ)) ^ 3 :=
      (Odd.strictMono_pow (by decide : Odd 3))
        (lt_of_not_ge h)
    rw [hRpowCube] at hCubeLt
    norm_num at hCubeLt

  have hTemperatureTermNeg :
      100 / Real.rpow 6 (2 / 3 : ℝ) - 600 < 0 := by
    rw [sub_neg, div_lt_iff₀ hRpowPos]
    nlinarith [hRpowLower]
  have hHeat₁₂Pos :
      0 < energyInJoules
        (cycle.heatTransferredIntoGas .oneToTwo) := by
    rw [hHeat₁₂]
    nlinarith [hNRPos]
  have hHeat₂₃Nonpos :
      energyInJoules
          (cycle.heatTransferredIntoGas .twoToThree) ≤ 0 := by
    rw [hHeat₂₃]
    exact (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg
        (mul_nonneg (by norm_num) _physical.amountPositive.le)
        _physical.gasConstantPositive.le)
      hTemperatureTermNeg.le)
  have hTotalHeat :
      totalHeatInputInJoules cycle =
        1250 * cycle.amountOfGasMoles *
          cycle.molarGasConstantJoulesPerMoleKelvin := by
    rw [totalHeatInputInJoules, max_eq_left hHeat₁₂Pos.le,
      max_eq_right hHeat₂₃Nonpos, hHeat₃₁]
    norm_num
    exact hHeat₁₂
  have hEfficiency :
      thermalEfficiency cycle = exactEfficiencyFromFigure := by
    rw [thermalEfficiency, hNetWork, hTotalHeat,
      exactEfficiencyFromFigure]
    field_simp [_physical.amountPositive.ne',
      _physical.gasConstantPositive.ne', hRpowPos.ne']
    ring

  refine ⟨hEfficiency, ?_⟩
  rw [hEfficiency]
  change
    (8 / 25 : ℝ) - 1 / 200 ≤
        ((7 : ℝ) + 3 / Real.rpow 6 (2 / 3 : ℝ)) / 25 ∧
      ((7 : ℝ) + 3 / Real.rpow 6 (2 / 3 : ℝ)) / 25 <
        (8 / 25 : ℝ) + 1 / 200
  have hReciprocalLower :
      (7 / 8 : ℝ) ≤ 3 / Real.rpow 6 (2 / 3 : ℝ) := by
    rw [le_div_iff₀ hRpowPos]
    nlinarith [hRpowUpper]
  have hReciprocalUpper :
      3 / Real.rpow 6 (2 / 3 : ℝ) < (9 / 8 : ℝ) := by
    rw [div_lt_iff₀ hRpowPos]
    nlinarith [hRpowLower]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0428
