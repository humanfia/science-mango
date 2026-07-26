import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0349

open Dimension

/-!
# Thermal efficiency of a rectangular ideal-gas cycle

The supplied pressure-volume diagram has vertices

* `1 = (V₀, p₀)`,
* `2 = (V₀, 2 p₀)`,
* `3 = (2 V₀, 2 p₀)`, and
* `4 = (2 V₀, p₀)`,

and arrows `1 -> 2 -> 3 -> 4 -> 1`.  Thus the two vertical legs are
isochoric and the two horizontal legs are isobaric.  Pressure, volume,
internal energy, work, and heat are retained as unit-independent physical
quantities.  Real numbers occur only as explicitly named unit readouts,
amounts measured in moles, and dimensionless efficiencies.
-/

/-! ## Dimensionful thermodynamic quantities and readouts -/

/-- A nonnegative physical volume, carrying dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical pressure in the units selected by `units`. -/
def pressureReadout (units : UnitChoices) (pressure : DimPressure) : ℝ :=
  (pressure units).val

/-- Read a physical volume in the cubic length unit selected by `units`. -/
def volumeReadout (units : UnitChoices) (volume : GasVolume) : ℝ :=
  ((volume units).val : ℝ)

/-- Read a physical energy in the units selected by `units`. -/
def energyReadout (units : UnitChoices) (energy : DimEnergy) : ℝ :=
  (energy units).val

/-- Kelvin readout of a `Temperature`; the ambient temperature units for this
engine model are fixed to kelvin so that they match the stated SI molar gas
constant. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Pascal readout of a pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  pressureReadout UnitChoices.SI pressure

/-- Cubic-meter readout of a volume. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  volumeReadout UnitChoices.SI volume

/-- Joule readout of an internal energy, heat, or work quantity. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  energyReadout UnitChoices.SI energy

/-! ## Figure labels and the physical engine -/

/-- The four numbered equilibrium states shown in the diagram. -/
inductive CycleVertex where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- The four directed arrows shown in the diagram. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial vertex of each directed diagram leg. -/
def CycleLeg.initialVertex : CycleLeg → CycleVertex
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final vertex of each directed diagram leg. -/
def CycleLeg.finalVertex : CycleLeg → CycleVertex
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- Constant coordinate of a vertical or horizontal leg in the `p-V` plane. -/
inductive ProcessConstraint where
  | constantVolume
  | constantPressure
  deriving DecidableEq, Repr

/-- The process type read from the orientation of each depicted leg. -/
def CycleLeg.depictedConstraint : CycleLeg → ProcessConstraint
  | .oneToTwo => .constantVolume
  | .twoToThree => .constantPressure
  | .threeToFour => .constantVolume
  | .fourToOne => .constantPressure

/-- The molecular model stated in the problem.  The diatomic case has five
active translational and rotational quadratic degrees of freedom. -/
inductive MolecularModel where
  | diatomicIdealGas
  deriving DecidableEq, Repr

/-- Thermodynamic observables at one numbered equilibrium state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : GasVolume
  temperature : Temperature
  internalEnergy : DimEnergy

/-- All independent quantities and observables of the depicted engine cycle.

`molarGasConstantJoulePerMoleKelvin` is explicitly an SI scalar readout because
Physlib's dimension system does not include amount of substance as a base
dimension.  The signed `workByGas` and `heatIntoGas` use the convention that
work done by the gas and heat entering the gas are positive. -/
structure RectangularDiatomicEngine where
  molecularModel : MolecularModel
  amountOfGasMoles : ℝ
  molarGasConstantJoulePerMoleKelvin : ℝ
  basePressure : DimPressure
  baseVolume : GasVolume
  state : CycleVertex → ThermodynamicState
  workByGas : CycleLeg → DimEnergy
  heatIntoGas : CycleLeg → DimEnergy
  netWorkByGas : DimEnergy
  absorbedHeat : DimEnergy
  thermalEfficiency : ℝ

/-!
The gas description and coordinate information taken from the problem text
and primary image.  Equalities involving a factor of two are required in
every choice of units, so they express a physical ratio rather than merely an
SI calibration.  No heat, work, efficiency, or answer choice occurs here.
-/
structure MatchesProblemStatementAndFigure
    (engine : RectangularDiatomicEngine) : Prop where
  gasIsDiatomicIdeal :
    engine.molecularModel = .diatomicIdealGas
  pointOnePressure :
    (engine.state .one).pressure = engine.basePressure
  pointOneVolume :
    (engine.state .one).volume = engine.baseVolume
  pointTwoVolume :
    (engine.state .two).volume = engine.baseVolume
  pointTwoPressure : ∀ units : UnitChoices,
    pressureReadout units (engine.state .two).pressure =
      2 * pressureReadout units engine.basePressure
  pointThreePressure : ∀ units : UnitChoices,
    pressureReadout units (engine.state .three).pressure =
      2 * pressureReadout units engine.basePressure
  pointThreeVolume : ∀ units : UnitChoices,
    volumeReadout units (engine.state .three).volume =
      2 * volumeReadout units engine.baseVolume
  pointFourPressure :
    (engine.state .four).pressure = engine.basePressure
  pointFourVolume : ∀ units : UnitChoices,
    volumeReadout units (engine.state .four).volume =
      2 * volumeReadout units engine.baseVolume

/-- Positivity and nondegeneracy conditions for a functioning heat engine. -/
structure HasPhysicalEngineParameters
    (engine : RectangularDiatomicEngine) : Prop where
  amountOfGasPositive : 0 < engine.amountOfGasMoles
  molarGasConstantPositive :
    0 < engine.molarGasConstantJoulePerMoleKelvin
  basePressurePositive :
    0 < pressureInPascals engine.basePressure
  baseVolumePositive :
    0 < volumeInCubicMeters engine.baseVolume
  stateTemperaturesPositive : ∀ vertex,
    0 < temperatureInKelvins (engine.state vertex).temperature
  absorbedHeatPositive :
    0 < energyInJoules engine.absorbedHeat

/-!
## Governing laws

The first field is `p V = n R T`.  For a diatomic ideal gas with five active
quadratic degrees of freedom, the second is `U = (5/2) n R T`.  Boundary work
is zero on an isochore and `p (V_f - V_i)` on an isobar.  The first-law sign
convention is `Q = ΔU + W_by`.  The remaining fields give the generic cycle
totals and the definition `eta = W_net / Q_in`, where `Q_in` is the sum of
the positive parts of the four signed heats.

These laws apply to arbitrary rectangular-cycle data and contain neither the
derived value `2/19` nor any displayed answer choice.
-/
structure SatisfiesDiatomicIdealGasCycleLaws
    (engine : RectangularDiatomicEngine) : Prop where
  idealGasEquation : ∀ vertex,
    pressureInPascals (engine.state vertex).pressure *
        volumeInCubicMeters (engine.state vertex).volume =
      engine.amountOfGasMoles *
        engine.molarGasConstantJoulePerMoleKelvin *
        temperatureInKelvins (engine.state vertex).temperature
  diatomicInternalEnergy : ∀ vertex,
    energyInJoules (engine.state vertex).internalEnergy =
      (5 / 2 : ℝ) * engine.amountOfGasMoles *
        engine.molarGasConstantJoulePerMoleKelvin *
        temperatureInKelvins (engine.state vertex).temperature
  isochoricBoundaryWork : ∀ leg,
    leg.depictedConstraint = .constantVolume →
      energyInJoules (engine.workByGas leg) = 0
  isobaricBoundaryWork : ∀ leg,
    leg.depictedConstraint = .constantPressure →
      energyInJoules (engine.workByGas leg) =
        pressureInPascals
            (engine.state leg.initialVertex).pressure *
          (volumeInCubicMeters
              (engine.state leg.finalVertex).volume -
            volumeInCubicMeters
              (engine.state leg.initialVertex).volume)
  firstLaw : ∀ leg,
    energyInJoules (engine.heatIntoGas leg) =
      energyInJoules
          (engine.state leg.finalVertex).internalEnergy -
        energyInJoules
          (engine.state leg.initialVertex).internalEnergy +
        energyInJoules (engine.workByGas leg)
  netWorkIsSumOfLegWork :
    energyInJoules engine.netWorkByGas =
      energyInJoules (engine.workByGas .oneToTwo) +
      energyInJoules (engine.workByGas .twoToThree) +
      energyInJoules (engine.workByGas .threeToFour) +
      energyInJoules (engine.workByGas .fourToOne)
  absorbedHeatIsPositivePartOfLegHeat :
    energyInJoules engine.absorbedHeat =
      max (energyInJoules (engine.heatIntoGas .oneToTwo)) 0 +
      max (energyInJoules (engine.heatIntoGas .twoToThree)) 0 +
      max (energyInJoules (engine.heatIntoGas .threeToFour)) 0 +
      max (energyInJoules (engine.heatIntoGas .fourToOne)) 0
  efficiencyIsNetWorkOverAbsorbedHeat :
    energyInJoules engine.absorbedHeat ≠ 0 →
      engine.thermalEfficiency =
        energyInJoules engine.netWorkByGas /
          energyInJoules engine.absorbedHeat

/-! ## Derived cycle energetics -/

/-- The signed work and heat on each arrow, expressed in terms of the common
energy scale `p₀ V₀`.  These are consequences of the figure coordinates and
governing laws, not input data. -/
lemma leg_work_and_heat_readouts
    (engine : RectangularDiatomicEngine)
    (hFigure : MatchesProblemStatementAndFigure engine)
    (hLaws : SatisfiesDiatomicIdealGasCycleLaws engine) :
    energyInJoules (engine.workByGas .oneToTwo) = 0 ∧
    energyInJoules (engine.heatIntoGas .oneToTwo) =
      (5 / 2 : ℝ) * pressureInPascals engine.basePressure *
        volumeInCubicMeters engine.baseVolume ∧
    energyInJoules (engine.workByGas .twoToThree) =
      2 * pressureInPascals engine.basePressure *
        volumeInCubicMeters engine.baseVolume ∧
    energyInJoules (engine.heatIntoGas .twoToThree) =
      7 * pressureInPascals engine.basePressure *
        volumeInCubicMeters engine.baseVolume ∧
    energyInJoules (engine.workByGas .threeToFour) = 0 ∧
    energyInJoules (engine.heatIntoGas .threeToFour) =
      -5 * pressureInPascals engine.basePressure *
        volumeInCubicMeters engine.baseVolume ∧
    energyInJoules (engine.workByGas .fourToOne) =
      -1 * pressureInPascals engine.basePressure *
        volumeInCubicMeters engine.baseVolume ∧
    energyInJoules (engine.heatIntoGas .fourToOne) =
      -(7 / 2 : ℝ) * pressureInPascals engine.basePressure *
        volumeInCubicMeters engine.baseVolume := by
  have hP1 :
      pressureInPascals (engine.state .one).pressure =
        pressureInPascals engine.basePressure :=
    congrArg pressureInPascals hFigure.pointOnePressure
  have hV1 :
      volumeInCubicMeters (engine.state .one).volume =
        volumeInCubicMeters engine.baseVolume :=
    congrArg volumeInCubicMeters hFigure.pointOneVolume
  have hP2 :
      pressureInPascals (engine.state .two).pressure =
        2 * pressureInPascals engine.basePressure := by
    simpa [pressureInPascals] using
      hFigure.pointTwoPressure UnitChoices.SI
  have hV2 :
      volumeInCubicMeters (engine.state .two).volume =
        volumeInCubicMeters engine.baseVolume :=
    congrArg volumeInCubicMeters hFigure.pointTwoVolume
  have hP3 :
      pressureInPascals (engine.state .three).pressure =
        2 * pressureInPascals engine.basePressure := by
    simpa [pressureInPascals] using
      hFigure.pointThreePressure UnitChoices.SI
  have hV3 :
      volumeInCubicMeters (engine.state .three).volume =
        2 * volumeInCubicMeters engine.baseVolume := by
    simpa [volumeInCubicMeters] using
      hFigure.pointThreeVolume UnitChoices.SI
  have hP4 :
      pressureInPascals (engine.state .four).pressure =
        pressureInPascals engine.basePressure :=
    congrArg pressureInPascals hFigure.pointFourPressure
  have hV4 :
      volumeInCubicMeters (engine.state .four).volume =
        2 * volumeInCubicMeters engine.baseVolume := by
    simpa [volumeInCubicMeters] using
      hFigure.pointFourVolume UnitChoices.SI
  have hIG1 := hLaws.idealGasEquation .one
  rw [hP1, hV1] at hIG1
  have hIG2 := hLaws.idealGasEquation .two
  rw [hP2, hV2] at hIG2
  have hIG3 := hLaws.idealGasEquation .three
  rw [hP3, hV3] at hIG3
  have hIG4 := hLaws.idealGasEquation .four
  rw [hP4, hV4] at hIG4
  have hU1raw := hLaws.diatomicInternalEnergy .one
  have hU2raw := hLaws.diatomicInternalEnergy .two
  have hU3raw := hLaws.diatomicInternalEnergy .three
  have hU4raw := hLaws.diatomicInternalEnergy .four
  have hU1 :
      energyInJoules (engine.state .one).internalEnergy =
        (5 / 2 : ℝ) * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hIG1, hU1raw]
  have hU2 :
      energyInJoules (engine.state .two).internalEnergy =
        5 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hIG2, hU2raw]
  have hU3 :
      energyInJoules (engine.state .three).internalEnergy =
        10 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hIG3, hU3raw]
  have hU4 :
      energyInJoules (engine.state .four).internalEnergy =
        5 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hIG4, hU4raw]
  have hW12 := hLaws.isochoricBoundaryWork .oneToTwo (by rfl)
  have hW23raw := hLaws.isobaricBoundaryWork .twoToThree (by rfl)
  simp only [CycleLeg.initialVertex, CycleLeg.finalVertex] at hW23raw
  rw [hP2, hV3, hV2] at hW23raw
  have hW23 :
      energyInJoules (engine.workByGas .twoToThree) =
        2 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    calc
      energyInJoules (engine.workByGas .twoToThree) =
          2 * pressureInPascals engine.basePressure *
            (2 * volumeInCubicMeters engine.baseVolume -
              volumeInCubicMeters engine.baseVolume) := hW23raw
      _ = 2 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by ring
  have hW34 := hLaws.isochoricBoundaryWork .threeToFour (by rfl)
  have hW41raw := hLaws.isobaricBoundaryWork .fourToOne (by rfl)
  simp only [CycleLeg.initialVertex, CycleLeg.finalVertex] at hW41raw
  rw [hP4, hV1, hV4] at hW41raw
  have hW41 :
      energyInJoules (engine.workByGas .fourToOne) =
        -1 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    calc
      energyInJoules (engine.workByGas .fourToOne) =
          pressureInPascals engine.basePressure *
            (volumeInCubicMeters engine.baseVolume -
              2 * volumeInCubicMeters engine.baseVolume) := hW41raw
      _ = -1 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by ring
  have hQ12raw := hLaws.firstLaw .oneToTwo
  simp only [CycleLeg.initialVertex, CycleLeg.finalVertex] at hQ12raw
  have hQ12 :
      energyInJoules (engine.heatIntoGas .oneToTwo) =
        (5 / 2 : ℝ) * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hQ12raw, hU1, hU2, hW12]
  have hQ23raw := hLaws.firstLaw .twoToThree
  simp only [CycleLeg.initialVertex, CycleLeg.finalVertex] at hQ23raw
  have hQ23 :
      energyInJoules (engine.heatIntoGas .twoToThree) =
        7 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hQ23raw, hU2, hU3, hW23]
  have hQ34raw := hLaws.firstLaw .threeToFour
  simp only [CycleLeg.initialVertex, CycleLeg.finalVertex] at hQ34raw
  have hQ34 :
      energyInJoules (engine.heatIntoGas .threeToFour) =
        -5 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hQ34raw, hU3, hU4, hW34]
  have hQ41raw := hLaws.firstLaw .fourToOne
  simp only [CycleLeg.initialVertex, CycleLeg.finalVertex] at hQ41raw
  have hQ41 :
      energyInJoules (engine.heatIntoGas .fourToOne) =
        -(7 / 2 : ℝ) * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hQ41raw, hU1, hU4, hW41]
  exact ⟨hW12, hQ12, hW23, hQ23, hW34, hQ34, hW41, hQ41⟩

/-- The clockwise rectangle produces net work `p₀ V₀` and absorbs
`(19/2) p₀ V₀` of heat on its two heating legs. -/
lemma net_work_and_absorbed_heat_readouts
    (engine : RectangularDiatomicEngine)
    (hFigure : MatchesProblemStatementAndFigure engine)
    (hPhysical : HasPhysicalEngineParameters engine)
    (hLaws : SatisfiesDiatomicIdealGasCycleLaws engine) :
    energyInJoules engine.netWorkByGas =
        pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume ∧
      energyInJoules engine.absorbedHeat =
        (19 / 2 : ℝ) * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
  rcases leg_work_and_heat_readouts engine hFigure hLaws with
    ⟨hW12, hQ12, hW23, hQ23, hW34, hQ34, hW41, hQ41⟩
  have hPVpos :
      0 <
        pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume :=
    mul_pos hPhysical.basePressurePositive hPhysical.baseVolumePositive
  have hQ12nonneg :
      0 ≤
        (5 / 2 : ℝ) * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hPVpos]
  have hQ23nonneg :
      0 ≤
        7 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    nlinarith only [hPVpos]
  have hQ34nonpos :
      -5 * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume ≤ 0 := by
    nlinarith only [hPVpos]
  have hQ41nonpos :
      -(7 / 2 : ℝ) * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume ≤ 0 := by
    nlinarith only [hPVpos]
  constructor
  · rw [hLaws.netWorkIsSumOfLegWork, hW12, hW23, hW34, hW41]
    ring
  · rw [hLaws.absorbedHeatIsPositivePartOfLegHeat,
      hQ12, hQ23, hQ34, hQ41,
      max_eq_left hQ12nonneg, max_eq_left hQ23nonneg,
      max_eq_right hQ34nonpos, max_eq_right hQ41nonpos]
    ring

/-! ## Multiple-choice interpretation and target -/

/-- Labels printed beside the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed percentages converted to dimensionless efficiency ratios. -/
def displayedThermalEfficiency : AnswerChoice → ℝ
  | .A => 10 / 100
  | .B => 105 / 1000
  | .C => 159 / 1000
  | .D => 123 / 1000

/-- Agreement to half of the last displayed tenth of a percentage point. -/
def EfficiencyMatchesChoice
    (engine : RectangularDiatomicEngine) (choice : AnswerChoice) : Prop :=
  |engine.thermalEfficiency - displayedThermalEfficiency choice| ≤ 1 / 2000

/-- The dataset records answer choice B.  This is metadata, not a premise of
the physical theorem below. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The exact thermal efficiency is `2/19`, which rounds to `10.5%` and hence
matches answer B.

This is the formalization target `thm:physics:phyx_mini_0349:target`.
-/
theorem problem_phyx_mini_0349
    (engine : RectangularDiatomicEngine)
    (hFigure : MatchesProblemStatementAndFigure engine)
    (hPhysical : HasPhysicalEngineParameters engine)
    (hLaws : SatisfiesDiatomicIdealGasCycleLaws engine) :
    engine.thermalEfficiency = (2 / 19 : ℝ) ∧
      EfficiencyMatchesChoice engine .B := by
  rcases net_work_and_absorbed_heat_readouts
      engine hFigure hPhysical hLaws with ⟨hNet, hAbsorbed⟩
  have hAbsorbedNe : energyInJoules engine.absorbedHeat ≠ 0 :=
    ne_of_gt hPhysical.absorbedHeatPositive
  have hEfficiency :=
    hLaws.efficiencyIsNetWorkOverAbsorbedHeat hAbsorbedNe
  rw [hNet, hAbsorbed] at hEfficiency
  have hDenominatorPositive :
      0 <
        (19 / 2 : ℝ) * pressureInPascals engine.basePressure *
          volumeInCubicMeters engine.baseVolume := by
    exact
      mul_pos
        (mul_pos (by norm_num) hPhysical.basePressurePositive)
        hPhysical.baseVolumePositive
  have hEfficiencyExact : engine.thermalEfficiency = (2 / 19 : ℝ) := by
    calc
      engine.thermalEfficiency =
          (pressureInPascals engine.basePressure *
            volumeInCubicMeters engine.baseVolume) /
            ((19 / 2 : ℝ) * pressureInPascals engine.basePressure *
              volumeInCubicMeters engine.baseVolume) :=
        hEfficiency
      _ = (2 / 19 : ℝ) := by
        apply (div_eq_iff (ne_of_gt hDenominatorPositive)).2
        ring
  constructor
  · exact hEfficiencyExact
  · norm_num [EfficiencyMatchesChoice, displayedThermalEfficiency,
      hEfficiencyExact, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0349
