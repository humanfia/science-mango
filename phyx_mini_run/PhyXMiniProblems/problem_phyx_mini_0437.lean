import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0437

open Dimension

/-!
# Thermal efficiency of an ideal Otto cycle

The primary pressure--volume diagram has four states.  The legs `1 → 2` and
`3 → 4` are adiabatic compression and expansion, while `2 → 3` and `4 → 1`
are isochoric heat addition and rejection.  States `2, 3` have volume
`V_min`; states `1, 4` have volume `V_max`; and state `3` is labelled
`p_max`.

Pressure, volume, heat, and constant-volume heat capacity remain dimensional
physical quantities.  Temperatures use Physlib's absolute `Temperature`.
Real numbers occur only as coherent SI readouts or as the dimensionless
quantities `γ`, compression ratio `r`, and thermal efficiency `η`.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical cylinder volume, carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical heat capacity, carrying the dimension energy per temperature. -/
abbrev HeatCapacityQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Read a physical cylinder volume in cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read heat energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a physical heat capacity in joules per kelvin. -/
def heatCapacityInJoulesPerKelvin
    (heatCapacity : HeatCapacityQuantity) : ℝ :=
  (heatCapacity UnitChoices.SI).val

/-- Kelvin-proportional scalar readout of an absolute temperature. -/
def temperatureReadout (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Cycle labels and physical observables -/

/-- The four numbered equilibrium states shown in the supplied figure. -/
inductive CycleState where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- The four directed process legs shown by the cycle arrows. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed Otto-cycle leg. -/
def CycleLeg.initialState : CycleLeg → CycleState
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final state of a directed Otto-cycle leg. -/
def CycleLeg.finalState : CycleLeg → CycleState
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- Thermodynamic role of a directed cycle leg. -/
inductive ProcessKind where
  | adiabaticCompression
  | isochoricHeating
  | adiabaticExpansion
  | isochoricCooling
  deriving DecidableEq, Repr

/-- Whether a process kind is one of the two adiabatic strokes. -/
def ProcessKind.IsAdiabatic (kind : ProcessKind) : Prop :=
  kind = .adiabaticCompression ∨ kind = .adiabaticExpansion

/-- Whether a process kind is one of the two constant-volume strokes. -/
def ProcessKind.IsIsochoric (kind : ProcessKind) : Prop :=
  kind = .isochoricHeating ∨ kind = .isochoricCooling

/-- The idealized material model used for the fuel--air mixture. -/
inductive WorkingGasModel where
  | idealFuelAirMixture
  deriving DecidableEq, Repr

/-- Thermodynamic observables at one numbered equilibrium state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-- The two physical quantities assigned to the diagram axes. -/
inductive DiagramAxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- The two axes of the supplied pressure--volume diagram. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Unit text printed next to the pressure axis. -/
inductive PressureAxisUnit where
  | atmosphere
  deriving DecidableEq, Repr

/-- Qualitative geometry of a process path in the primary raster. -/
inductive PathShape where
  | adiabaticCurve
  | verticalSegment
  deriving DecidableEq, Repr

/-- The two purple heat-transfer labels visible in the figure. -/
inductive HeatAnnotation where
  | QH
  | QC
  deriving DecidableEq, Fintype, Repr

/-- Direction of a purple heat-transfer arrow relative to the working gas. -/
inductive HeatArrowDirection where
  | intoWorkingGas
  | outOfWorkingGas
  deriving DecidableEq, Repr

/-!
Literal labels, arrows, and path shapes read from the primary raster.  This
record contains no efficiency formula or answer choice.
-/
structure PressureVolumeFigure where
  axisQuantity : DiagramAxis → DiagramAxisQuantity
  pressureAxisUnit : PressureAxisUnit
  showsMinimumVolumeLabel : Bool
  showsMaximumVolumeLabel : Bool
  showsMaximumPressureLabel : Bool
  showsState : CycleState → Bool
  showsDirectedLeg : CycleLeg → Bool
  directedLegInitialState : CycleLeg → CycleState
  directedLegFinalState : CycleLeg → CycleState
  pathShape : CycleLeg → PathShape
  showsHeatAnnotation : HeatAnnotation → Bool
  heatAnnotationLeg : HeatAnnotation → CycleLeg
  heatArrowDirection : HeatAnnotation → HeatArrowDirection

/-!
Independent physical data of the Otto engine.  The compression ratio and
thermal efficiency are dimensionless observables, not definitions of the
requested closed form.
-/
structure OttoCycleSetup where
  workingGasModel : WorkingGasModel
  state : CycleState → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  minimumCylinderVolume : VolumeQuantity
  maximumCylinderVolume : VolumeQuantity
  maximumCyclePressure : DimPressure
  heatAddedFromHotReservoir : DimEnergy
  heatRejectedToColdReservoir : DimEnergy
  constantVolumeHeatCapacity : HeatCapacityQuantity
  heatCapacityRatioGamma : ℝ
  compressionRatio : ℝ
  thermalEfficiency : ℝ
  figure : PressureVolumeFigure

/-- Temperature readout at one numbered state. -/
def stateTemperature (setup : OttoCycleSetup) (state : CycleState) : ℝ :=
  temperatureReadout (setup.state state).temperature

/-- Volume readout at one numbered state, in cubic metres. -/
def stateVolume (setup : OttoCycleSetup) (state : CycleState) : ℝ :=
  volumeInCubicMetres (setup.state state).volume

/-! ## Problem data, figure evidence, and governing laws -/

/-!
The qualitative process assignment stated in the problem text.  No
efficiency value appears here.
-/
structure MatchesOttoCycleDescription (setup : OttoCycleSetup) : Prop where
  gasUsesIdealMixtureModel :
    setup.workingGasModel = .idealFuelAirMixture
  oneToTwoIsAdiabaticCompression :
    setup.processKind .oneToTwo = .adiabaticCompression
  twoToThreeIsIsochoricHeating :
    setup.processKind .twoToThree = .isochoricHeating
  threeToFourIsAdiabaticExpansion :
    setup.processKind .threeToFour = .adiabaticExpansion
  fourToOneIsIsochoricCooling :
    setup.processKind .fourToOne = .isochoricCooling

/-!
Axes, labels, directed arrows, heat annotations, and state coordinates read
from the primary image.  These are calibrated figure data, not the requested
efficiency conclusion.
-/
structure MatchesPrimaryOttoFigure (setup : OttoCycleSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  pressureAxisIsInAtmospheres :
    setup.figure.pressureAxisUnit = .atmosphere
  minimumVolumeLabelShown :
    setup.figure.showsMinimumVolumeLabel = true
  maximumVolumeLabelShown :
    setup.figure.showsMaximumVolumeLabel = true
  maximumPressureLabelShown :
    setup.figure.showsMaximumPressureLabel = true
  everyStateShown :
    ∀ state, setup.figure.showsState state = true
  everyDirectedLegShown :
    ∀ leg, setup.figure.showsDirectedLeg leg = true
  displayedInitialStatesMatchCycle :
    ∀ leg, setup.figure.directedLegInitialState leg = leg.initialState
  displayedFinalStatesMatchCycle :
    ∀ leg, setup.figure.directedLegFinalState leg = leg.finalState
  compressionAndExpansionAreCurved :
    setup.figure.pathShape .oneToTwo = .adiabaticCurve ∧
      setup.figure.pathShape .threeToFour = .adiabaticCurve
  heatTransferLegsAreVertical :
    setup.figure.pathShape .twoToThree = .verticalSegment ∧
      setup.figure.pathShape .fourToOne = .verticalSegment
  everyHeatAnnotationShown :
    ∀ annotation, setup.figure.showsHeatAnnotation annotation = true
  hotHeatArrowOnIgnition :
    setup.figure.heatAnnotationLeg .QH = .twoToThree
  hotHeatArrowPointsIntoGas :
    setup.figure.heatArrowDirection .QH = .intoWorkingGas
  coldHeatArrowOnExhaust :
    setup.figure.heatAnnotationLeg .QC = .fourToOne
  coldHeatArrowPointsOutOfGas :
    setup.figure.heatArrowDirection .QC = .outOfWorkingGas
  stateOneAtMaximumVolume :
    (setup.state .one).volume = setup.maximumCylinderVolume
  stateTwoAtMinimumVolume :
    (setup.state .two).volume = setup.minimumCylinderVolume
  stateThreeAtMinimumVolume :
    (setup.state .three).volume = setup.minimumCylinderVolume
  stateFourAtMaximumVolume :
    (setup.state .four).volume = setup.maximumCylinderVolume
  stateThreeAtMaximumPressure :
    (setup.state .three).pressure = setup.maximumCyclePressure
  maximumPressureBoundsAllStates :
    ∀ state,
      pressureInPascals (setup.state state).pressure ≤
        pressureInPascals setup.maximumCyclePressure

/-- Positivity and nondegeneracy conditions for a functioning Otto engine. -/
structure HasPhysicalOttoParameters (setup : OttoCycleSetup) : Prop where
  minimumVolumePositive :
    0 < volumeInCubicMetres setup.minimumCylinderVolume
  maximumVolumeGreaterThanMinimum :
    volumeInCubicMetres setup.minimumCylinderVolume <
      volumeInCubicMetres setup.maximumCylinderVolume
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.state state).pressure
  absoluteTemperaturePositive :
    ∀ state, 0 < stateTemperature setup state
  heatCapacityRatioGreaterThanOne :
    1 < setup.heatCapacityRatioGamma
  constantVolumeHeatCapacityPositive :
    0 < heatCapacityInJoulesPerKelvin setup.constantVolumeHeatCapacity
  addedHeatPositive :
    0 < energyInJoules setup.heatAddedFromHotReservoir
  rejectedHeatNonnegative :
    0 ≤ energyInJoules setup.heatRejectedToColdReservoir
  compressionRatioGreaterThanOne :
    1 < setup.compressionRatio

/-!
Governing relations for an ideal Otto cycle:

* `r = V_max / V_min`;
* isochoric legs preserve volume;
* an adiabatic leg satisfies
  `T_i / T_f = (V_f / V_i)^(γ - 1)`;
* heat exchanged on either isochore is `C_V` times the appropriate positive
  temperature difference;
* thermal efficiency is one minus rejected heat divided by added heat.

These laws are generic physical relations.  In particular, this structure
does not contain the requested expression `1 - 1 / r^(γ - 1)`.
-/
structure SatisfiesIdealOttoCycleLaws (setup : OttoCycleSetup) : Prop where
  compressionRatioDefinition :
    setup.compressionRatio =
      volumeInCubicMetres setup.maximumCylinderVolume /
        volumeInCubicMetres setup.minimumCylinderVolume
  isochoricVolumeLaw :
    ∀ leg,
      (setup.processKind leg).IsIsochoric →
        (setup.state leg.initialState).volume =
          (setup.state leg.finalState).volume
  adiabaticTemperatureVolumeLaw :
    ∀ leg,
      (setup.processKind leg).IsAdiabatic →
        stateTemperature setup leg.initialState /
            stateTemperature setup leg.finalState =
          Real.rpow
            (stateVolume setup leg.finalState /
              stateVolume setup leg.initialState)
            (setup.heatCapacityRatioGamma - 1)
  heatAddedOnIsochoricIgnition :
    energyInJoules setup.heatAddedFromHotReservoir =
      heatCapacityInJoulesPerKelvin setup.constantVolumeHeatCapacity *
        (stateTemperature setup .three - stateTemperature setup .two)
  heatRejectedOnIsochoricExhaust :
    energyInJoules setup.heatRejectedToColdReservoir =
      heatCapacityInJoulesPerKelvin setup.constantVolumeHeatCapacity *
        (stateTemperature setup .four - stateTemperature setup .one)
  efficiencyFromReservoirHeat :
    energyInJoules setup.heatAddedFromHotReservoir ≠ 0 →
      setup.thermalEfficiency =
        1 - energyInJoules setup.heatRejectedToColdReservoir /
          energyInJoules setup.heatAddedFromHotReservoir

/-!
The two adiabatic temperature--volume connections and the two isochoric heat
relations imply the standard Otto-cycle efficiency.  This formalizes
`thm:physics:phyx_mini_0437:target` and corresponds to answer choice D.
-/
theorem problem_phyx_mini_0437
    (setup : OttoCycleSetup)
    (hDescription : MatchesOttoCycleDescription setup)
    (hFigure : MatchesPrimaryOttoFigure setup)
    (hPhysical : HasPhysicalOttoParameters setup)
    (hLaws : SatisfiesIdealOttoCycleLaws setup) :
    setup.thermalEfficiency =
      1 - 1 /
        Real.rpow setup.compressionRatio
          (setup.heatCapacityRatioGamma - 1) := by
  have hr_pos : 0 < setup.compressionRatio :=
    lt_trans zero_lt_one hPhysical.compressionRatioGreaterThanOne
  let exponent := setup.heatCapacityRatioGamma - 1
  have hR_pos : 0 < setup.compressionRatio ^ exponent :=
    Real.rpow_pos_of_pos hr_pos _
  have hvmin_pos := hPhysical.minimumVolumePositive
  have hvmax_pos :
      0 < volumeInCubicMetres setup.maximumCylinderVolume :=
    lt_trans hvmin_pos hPhysical.maximumVolumeGreaterThanMinimum
  have hVolumeOne :
      stateVolume setup .one =
        volumeInCubicMetres setup.maximumCylinderVolume := by
    simpa [stateVolume] using
      congrArg volumeInCubicMetres hFigure.stateOneAtMaximumVolume
  have hVolumeTwo :
      stateVolume setup .two =
        volumeInCubicMetres setup.minimumCylinderVolume := by
    simpa [stateVolume] using
      congrArg volumeInCubicMetres hFigure.stateTwoAtMinimumVolume
  have hVolumeThree :
      stateVolume setup .three =
        volumeInCubicMetres setup.minimumCylinderVolume := by
    simpa [stateVolume] using
      congrArg volumeInCubicMetres hFigure.stateThreeAtMinimumVolume
  have hVolumeFour :
      stateVolume setup .four =
        volumeInCubicMetres setup.maximumCylinderVolume := by
    simpa [stateVolume] using
      congrArg volumeInCubicMetres hFigure.stateFourAtMaximumVolume
  have hRatioTwelve :
      stateVolume setup .two / stateVolume setup .one =
        setup.compressionRatio⁻¹ := by
    rw [hVolumeTwo, hVolumeOne, hLaws.compressionRatioDefinition]
    field_simp
  have hRatioThirtyFour :
      stateVolume setup .four / stateVolume setup .three =
        setup.compressionRatio := by
    rw [hVolumeFour, hVolumeThree]
    exact hLaws.compressionRatioDefinition.symm
  have hAdTwelve :=
    hLaws.adiabaticTemperatureVolumeLaw .oneToTwo (by
      simp [ProcessKind.IsAdiabatic,
        hDescription.oneToTwoIsAdiabaticCompression])
  have hAdThirtyFour :=
    hLaws.adiabaticTemperatureVolumeLaw .threeToFour (by
      simp [ProcessKind.IsAdiabatic,
        hDescription.threeToFourIsAdiabaticExpansion])
  simp only [CycleLeg.initialState, CycleLeg.finalState] at hAdTwelve hAdThirtyFour
  rw [hRatioTwelve] at hAdTwelve
  change
    stateTemperature setup .one / stateTemperature setup .two =
      (setup.compressionRatio⁻¹) ^ exponent at hAdTwelve
  rw [Real.inv_rpow (le_of_lt hr_pos)] at hAdTwelve
  rw [hRatioThirtyFour] at hAdThirtyFour
  change
    stateTemperature setup .three / stateTemperature setup .four =
      setup.compressionRatio ^ exponent at hAdThirtyFour
  have hTtwo_pos := hPhysical.absoluteTemperaturePositive .two
  have hTfour_pos := hPhysical.absoluteTemperaturePositive .four
  have hR_ne := ne_of_gt hR_pos
  field_simp [ne_of_gt hTtwo_pos, hR_ne] at hAdTwelve
  field_simp [ne_of_gt hTfour_pos] at hAdThirtyFour
  have hCv_pos := hPhysical.constantVolumeHeatCapacityPositive
  have hHotDelta_pos :
      0 < stateTemperature setup .three - stateTemperature setup .two := by
    have hQH_pos := hPhysical.addedHeatPositive
    rw [hLaws.heatAddedOnIsochoricIgnition] at hQH_pos
    nlinarith
  have hHeatRatio :
      energyInJoules setup.heatRejectedToColdReservoir /
          energyInJoules setup.heatAddedFromHotReservoir =
        1 / setup.compressionRatio ^ exponent := by
    rw [hLaws.heatRejectedOnIsochoricExhaust,
      hLaws.heatAddedOnIsochoricIgnition]
    field_simp [ne_of_gt hCv_pos, ne_of_gt hHotDelta_pos, hR_ne]
    nlinarith [hAdTwelve, hAdThirtyFour]
  have hEfficiency :=
    hLaws.efficiencyFromReservoirHeat
      (ne_of_gt hPhysical.addedHeatPositive)
  rw [hHeatRatio] at hEfficiency
  simpa [exponent] using hEfficiency

end PhyXMiniProblems.ProblemPhyXMini0437
