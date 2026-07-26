import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0473

open Dimension

/-!
# Gasoline burned during one heat-engine cycle

A truck engine receives `10000 J` of heat and produces `2000 J` of mechanical
work in one cycle.  The heat comes from gasoline whose heat of combustion is
`5.0 * 10^4 J/g`.  The supplied diagram also shows an unknown rejected heat
`Q_C` flowing from a hot reservoir labelled `T_H` toward a cold reservoir
labelled `T_C`.

Energy, fuel mass, heat of combustion, and reservoir temperature remain
physical quantities.  Real numbers occur only as readouts in the named units
printed in the exercise and figure.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- Nonnegative gasoline mass with physical dimension `M`. -/
abbrev FuelMassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/--
Heat released per unit fuel mass.  Its dimension is energy divided by mass,
namely `L² T⁻²`; its SI readout is in joules per kilogram.
-/
abbrev SpecificCombustionEnergyQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a dimensionful energy magnitude in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a physical fuel mass in grams. -/
def fuelMassInGrams (mass : FuelMassQuantity) : ℝ :=
  (((mass {UnitChoices.SI with mass := MassUnit.grams}).val : NNReal) : ℝ)

/--
Read a specific combustion energy in joules per gram.  A coherent-SI readout
of this dimension is in joules per kilogram, and `1 J/g = 1000 J/kg`.
-/
def combustionEnergyInJoulesPerGram
    (energyPerMass : SpecificCombustionEnergyQuantity) : ℝ :=
  (((energyPerMass UnitChoices.SI).val : NNReal) : ℝ) / 1000

/-! ## Cycle observables and primary-figure vocabulary -/

/-- Arrow orientations appearing in the heat-engine diagram. -/
inductive FigureArrowDirection where
  | downward
  | rightward
  deriving DecidableEq, Repr

/-- The two literal reservoir-temperature labels in the diagram. -/
inductive FigureTemperatureLabel where
  | T_H
  | T_C
  deriving DecidableEq, Fintype, Repr

/-- The three literal energy-flow labels in the diagram. -/
inductive FigureEnergyLabel where
  | Q_H
  | W
  | Q_C
  deriving DecidableEq, Fintype, Repr

/-!
Data transcribed from primary image `473.png`.  The two numeric fields are
display readouts, while the cold-side heat is explicitly marked unknown.
-/
structure SuppliedHeatEngineFigure where
  temperatureLabelShown : FigureTemperatureLabel → Bool
  energyLabelShown : FigureEnergyLabel → Bool
  heatInputArrowDirection : FigureArrowDirection
  workOutputArrowDirection : FigureArrowDirection
  rejectedHeatArrowDirection : FigureArrowDirection
  displayedHeatInputJoules : ℝ
  displayedWorkOutputJoules : ℝ
  rejectedHeatMarkedUnknown : Bool

/-!
Independent physical observables for one truck-engine cycle.  In particular,
the gasoline mass is not defined from an answer choice, and the rejected heat
is retained even though the question asks only for fuel consumption.
-/
structure GasolineTruckEngineCycle where
  hotReservoirTemperature : Temperature
  coldReservoirTemperature : Temperature
  heatInputFromHotReservoir : DimEnergy
  mechanicalWorkOutput : DimEnergy
  rejectedHeatToColdReservoir : DimEnergy
  gasolineBurned : FuelMassQuantity
  heatOfCombustion : SpecificCombustionEnergyQuantity
  figure : SuppliedHeatEngineFigure

/-! ## Figure/data readouts and governing laws -/

/-!
The numerical problem statement and qualitative primary-image transcription.
No field specifies the gasoline mass or any answer-choice value.
-/
structure MatchesProblemStatementAndPrimaryFigure
    (cycle : GasolineTruckEngineCycle) : Prop where
  heatInputAgreesWithFigure :
    energyInJoules cycle.heatInputFromHotReservoir =
      cycle.figure.displayedHeatInputJoules
  workOutputAgreesWithFigure :
    energyInJoules cycle.mechanicalWorkOutput =
      cycle.figure.displayedWorkOutputJoules
  displayedHeatInput : cycle.figure.displayedHeatInputJoules = 10000
  displayedWorkOutput : cycle.figure.displayedWorkOutputJoules = 2000
  statedHeatOfCombustion :
    combustionEnergyInJoulesPerGram cycle.heatOfCombustion = 5 * 10 ^ 4
  everyTemperatureLabelShown :
    ∀ label, cycle.figure.temperatureLabelShown label = true
  everyEnergyLabelShown :
    ∀ label, cycle.figure.energyLabelShown label = true
  heatInputArrowPointsDown :
    cycle.figure.heatInputArrowDirection = .downward
  workOutputArrowPointsRight :
    cycle.figure.workOutputArrowDirection = .rightward
  rejectedHeatArrowPointsDown :
    cycle.figure.rejectedHeatArrowDirection = .downward
  coldSideHeatIsUnknownInFigure :
    cycle.figure.rejectedHeatMarkedUnknown = true

/-!
The first law for a cyclic heat engine and the fuel-combustion energy law.
These are general relations among independent observables, not numerical
assertions of the requested fuel mass.
-/
structure ObeysGasolineHeatEngineCycleLaws
    (cycle : GasolineTruckEngineCycle) : Prop where
  heatInputNonnegative :
    0 ≤ energyInJoules cycle.heatInputFromHotReservoir
  workOutputNonnegative :
    0 ≤ energyInJoules cycle.mechanicalWorkOutput
  rejectedHeatNonnegative :
    0 ≤ energyInJoules cycle.rejectedHeatToColdReservoir
  hotReservoirIsHotter :
    cycle.coldReservoirTemperature.val < cycle.hotReservoirTemperature.val
  firstLawForOneCycle :
    energyInJoules cycle.heatInputFromHotReservoir =
      energyInJoules cycle.mechanicalWorkOutput +
        energyInJoules cycle.rejectedHeatToColdReservoir
  heatInputSuppliedByCombustion :
    energyInJoules cycle.heatInputFromHotReservoir =
      fuelMassInGrams cycle.gasolineBurned *
        combustionEnergyInJoulesPerGram cycle.heatOfCombustion

/-!
The heat-input and heat-of-combustion readouts imply that one cycle burns
`0.20 g` of gasoline.  The `2000 J` work and the unknown `Q_C` remain in the
faithful heat-engine model through the figure data and first-law premise.
-/
theorem gasoline_burned_per_cycle_eq_point_two_grams
    (cycle : GasolineTruckEngineCycle)
    (hData : MatchesProblemStatementAndPrimaryFigure cycle)
    (hLaws : ObeysGasolineHeatEngineCycleLaws cycle) :
    fuelMassInGrams cycle.gasolineBurned = 0.20 := by
  have hHeatInput :
      energyInJoules cycle.heatInputFromHotReservoir = 10000 :=
    hData.heatInputAgreesWithFigure.trans hData.displayedHeatInput
  have hCombustion := hLaws.heatInputSuppliedByCombustion
  rw [hHeatInput, hData.statedHeatOfCombustion] at hCombustion
  norm_num at hCombustion ⊢
  linarith

end PhyXMiniProblems.ProblemPhyXMini0473
