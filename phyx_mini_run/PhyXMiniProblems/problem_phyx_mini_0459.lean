import Mathlib
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Specific heat transfer during a polytropic expansion of nitrogen

A closed nitrogen sample in the gas region of the pictured piston-cylinder
starts at `750 K` and `1500 kPa`.  It expands polytropically with exponent
`n = 1.2` until its pressure is `750 kPa`.  The requested observable is the
signed heat transferred to the gas per unit mass.

The supplied bitmap also shows the cylinder walls, piston and rings,
connecting rod, crank, clockwise rotation arrow, and a spark plug.  Those
features are recorded separately from the thermodynamic laws: they identify
the apparatus but do not determine the numerical heat by definition.

Pressure and all other basic physical quantities below are unit-independent
`Dimensionful` values.  Real numbers are used only for explicitly named unit
readouts, the dimensionless polytropic exponent, and answer-choice values.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose and raster-image data;
* `HasPhysicalPolytropicStates` records positivity of physical state data;
* `HasNitrogenPropertyData` records the nitrogen gas constant and a calibrated
  internal-energy-change interval for this endpoint temperature range;
* `SatisfiesClosedIdealGasPolytropicLaws` states the ideal-gas, polytropic,
  boundary-work, and first-law relations; and
* `problem_phyx_mini_0459` concludes that the displayed `56.0 kJ/kg` choice is
  uniquely closest to the resulting specific heat transfer.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0459

open Dimension

/-! ## Dimensionful thermodynamic quantities and named-unit readouts -/

/-- A nonnegative physical specific volume, with dimension `L³ M⁻¹`. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹) NNReal)

/-- A nonnegative absolute temperature carrying the temperature dimension. -/
abbrev TemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/--
Signed energy per unit mass, with dimension `L² T⁻²`.  It is used for specific
internal energy, boundary work, and heat transfer.
-/
abbrev SpecificEnergyQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/--
The nonnegative specific gas constant, with dimension `L² T⁻² Θ⁻¹`.
-/
abbrev SpecificGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Kilopascal readout used in the problem statement. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Kelvin readout of a physical absolute temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/-- Cubic-metre-per-kilogram readout of a physical specific volume. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume UnitChoices.SI).val : ℝ)

/-- Joule-per-kilogram readout of signed specific energy. -/
def specificEnergyInJoulesPerKilogram
    (specificEnergy : SpecificEnergyQuantity) : ℝ :=
  (specificEnergy UnitChoices.SI).val

/-- Kilojoule-per-kilogram readout used by the answer choices. -/
def specificEnergyInKilojoulesPerKilogram
    (specificEnergy : SpecificEnergyQuantity) : ℝ :=
  specificEnergyInJoulesPerKilogram specificEnergy / 1000

/-- Joule-per-kilogram-kelvin readout of the specific gas constant. -/
def specificGasConstantInJoulesPerKilogramKelvin
    (gasConstant : SpecificGasConstantQuantity) : ℝ :=
  ((gasConstant UnitChoices.SI).val : ℝ)

/-- Kilojoule-per-kilogram-kelvin readout for equations written with kPa. -/
def specificGasConstantInKilojoulesPerKilogramKelvin
    (gasConstant : SpecificGasConstantQuantity) : ℝ :=
  specificGasConstantInJoulesPerKilogramKelvin gasConstant / 1000

/-! ## Thermodynamic state, process, and apparatus vocabulary -/

/-- The two equilibrium endpoints named by the expansion description. -/
inductive ProcessState where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- Chemical identity of the gas sample. -/
inductive GasSpecies where
  | nitrogen
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic system boundary relevant to the first law. -/
inductive SystemBoundary where
  | closedGasSample
  | other
  deriving DecidableEq, Repr

/-- Mechanical apparatus represented in the primary figure. -/
inductive ApparatusKind where
  | pistonCylinder
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic classification of the stated process. -/
inductive ProcessKind where
  | quasistaticPolytropicExpansion
  | other
  deriving DecidableEq, Repr

/-- Sign convention for process energy transfer. -/
inductive HeatSignConvention where
  | positiveIntoGas
  | other
  deriving DecidableEq, Repr

/-- Pressure, specific volume, temperature, and internal energy at an endpoint. -/
structure ThermodynamicState where
  pressure : DimPressure
  specificVolume : SpecificVolumeQuantity
  absoluteTemperature : TemperatureQuantity
  specificInternalEnergy : SpecificEnergyQuantity

/-!
The physical process and its independent observables.  In particular,
`specificHeatTransferredToGas` is not defined from any answer choice.
-/
structure NitrogenPolytropicExpansion where
  gasSpecies : GasSpecies
  systemBoundary : SystemBoundary
  apparatus : ApparatusKind
  processKind : ProcessKind
  heatSignConvention : HeatSignConvention
  stateAt : ProcessState → ThermodynamicState
  polytropicExponent : ℝ
  specificGasConstant : SpecificGasConstantQuantity
  specificBoundaryWorkDoneByGas : SpecificEnergyQuantity
  specificHeatTransferredToGas : SpecificEnergyQuantity

/-! ## Primary-figure evidence -/

/-- Physical objects visibly represented in the supplied raster image. -/
inductive FigureObject where
  | cylinderWalls
  | gasRegion
  | piston
  | pistonRings
  | connectingRod
  | crank
  | crankshaft
  | sparkPlug
  deriving DecidableEq, Fintype, Repr

/-- Literal text label visible in the primary figure. -/
inductive FigureLabel where
  | gas
  deriving DecidableEq, Fintype, Repr

/-- Orientation of the cylinder and piston travel in the drawing. -/
inductive CylinderAxisOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Sense of the blue crank-rotation arrow. -/
inductive RotationDirection where
  | clockwise
  | counterclockwise
  | unspecified
  deriving DecidableEq, Repr

/-- Qualitative evidence transcribed from the supplied piston-cylinder image. -/
structure PrimaryFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  cylinderAxisOrientation : CylinderAxisOrientation
  crankRotationDirection : RotationDirection
  gasRegionIsInsideCylinder : Bool
  pistonBoundsGasRegion : Bool
  connectingRodJoinsPistonToCrank : Bool

/-!
Problem-statement and image readouts.  These fields contain only supplied
endpoint data, process classification, and qualitative apparatus evidence.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : NitrogenPolytropicExpansion) (figure : PrimaryFigure) : Prop where
  workingFluidIsNitrogen : setup.gasSpecies = .nitrogen
  gasSampleIsClosed : setup.systemBoundary = .closedGasSample
  apparatusIsPistonCylinder : setup.apparatus = .pistonCylinder
  processIsPolytropicExpansion :
    setup.processKind = .quasistaticPolytropicExpansion
  heatIsPositiveIntoGas : setup.heatSignConvention = .positiveIntoGas
  initialTemperatureKelvins :
    temperatureInKelvins (setup.stateAt .initial).absoluteTemperature = 750
  initialPressureKilopascals :
    pressureInKilopascals (setup.stateAt .initial).pressure = 1500
  finalPressureKilopascals :
    pressureInKilopascals (setup.stateAt .final).pressure = 750
  exponentIsOnePointTwo : setup.polytropicExponent = 6 / 5
  showsEveryNamedObject : ∀ object, figure.showsObject object = true
  showsGasLabel : figure.showsLabel .gas = true
  cylinderIsHorizontal : figure.cylinderAxisOrientation = .horizontal
  crankArrowIsClockwise : figure.crankRotationDirection = .clockwise
  gasInsideCylinder : figure.gasRegionIsInsideCylinder = true
  pistonBoundsGas : figure.pistonBoundsGasRegion = true
  rodConnectsPistonAndCrank :
    figure.connectingRodJoinsPistonToCrank = true

/-! ## Physical-domain conditions and governing laws -/

/-- Positivity conditions needed for the ideal-gas and real-power relations. -/
structure HasPhysicalPolytropicStates
    (setup : NitrogenPolytropicExpansion) : Prop where
  pressurePositive : ∀ state,
    0 < pressureInKilopascals (setup.stateAt state).pressure
  specificVolumePositive : ∀ state,
    0 < specificVolumeInCubicMetersPerKilogram
      (setup.stateAt state).specificVolume
  absoluteTemperaturePositive : ∀ state,
    0 < temperatureInKelvins (setup.stateAt state).absoluteTemperature
  gasConstantPositive :
    0 < specificGasConstantInKilojoulesPerKilogramKelvin
      setup.specificGasConstant

/-- Specific internal-energy change from the initial state to the final state. -/
def specificInternalEnergyChangeInKilojoulesPerKilogram
    (setup : NitrogenPolytropicExpansion) : ℝ :=
  specificEnergyInKilojoulesPerKilogram
      (setup.stateAt .final).specificInternalEnergy -
    specificEnergyInKilojoulesPerKilogram
      (setup.stateAt .initial).specificInternalEnergy

/-!
Calibrated nitrogen-property data used with the variable-specific-heat ideal
gas model.  The internal-energy interval, `[-66, -65.5] kJ/kg`, brackets the
standard nitrogen caloric-property change across the endpoint temperature
range; it neither mentions heat transfer nor selects an answer choice.
-/
structure HasNitrogenPropertyData
    (setup : NitrogenPolytropicExpansion) : Prop where
  specificGasConstantValue :
    specificGasConstantInKilojoulesPerKilogramKelvin
        setup.specificGasConstant = 371 / 1250
  internalEnergyChangeLowerBound :
    -66 ≤ specificInternalEnergyChangeInKilojoulesPerKilogram setup
  internalEnergyChangeUpperBound :
    specificInternalEnergyChangeInKilojoulesPerKilogram setup ≤ -131 / 2

/-!
Governing equations for a closed ideal gas undergoing a quasistatic
polytropic process.  With pressure in kPa and specific volume in m³/kg, each
`p v` product is in kJ/kg.  Work is positive when done by the gas and heat is
positive when transferred into it, so the first law is `q = Δu + w`.
-/
structure SatisfiesClosedIdealGasPolytropicLaws
    (setup : NitrogenPolytropicExpansion) : Prop where
  idealGasEquationAtEndpoint : ∀ endpoint,
    pressureInKilopascals (setup.stateAt endpoint).pressure *
        specificVolumeInCubicMetersPerKilogram
          (setup.stateAt endpoint).specificVolume =
      specificGasConstantInKilojoulesPerKilogramKelvin
          setup.specificGasConstant *
        temperatureInKelvins
          (setup.stateAt endpoint).absoluteTemperature
  polytropicEndpointRelation :
    pressureInKilopascals (setup.stateAt .initial).pressure *
        Real.rpow
          (specificVolumeInCubicMetersPerKilogram
            (setup.stateAt .initial).specificVolume)
          setup.polytropicExponent =
      pressureInKilopascals (setup.stateAt .final).pressure *
        Real.rpow
          (specificVolumeInCubicMetersPerKilogram
            (setup.stateAt .final).specificVolume)
          setup.polytropicExponent
  polytropicBoundaryWork : setup.polytropicExponent ≠ 1 →
    specificEnergyInKilojoulesPerKilogram
        setup.specificBoundaryWorkDoneByGas =
      (pressureInKilopascals (setup.stateAt .final).pressure *
            specificVolumeInCubicMetersPerKilogram
              (setup.stateAt .final).specificVolume -
          pressureInKilopascals (setup.stateAt .initial).pressure *
            specificVolumeInCubicMetersPerKilogram
              (setup.stateAt .initial).specificVolume) /
        (1 - setup.polytropicExponent)
  closedSystemFirstLaw :
    specificEnergyInKilojoulesPerKilogram
        setup.specificHeatTransferredToGas =
      specificInternalEnergyChangeInKilojoulesPerKilogram setup +
        specificEnergyInKilojoulesPerKilogram
          setup.specificBoundaryWorkDoneByGas

/-! ## Derived endpoint and energy bounds -/

/-!
The ideal-gas and polytropic relations put the final temperature near
`668.17 K`; this deliberately states a derived intermediate result rather
than storing it in a premise structure.
-/
lemma final_temperature_in_caloric_table_interval
    (setup : NitrogenPolytropicExpansion)
    (figure : PrimaryFigure)
    (_data : MatchesProblemAndPrimaryFigure setup figure)
    (_physical : HasPhysicalPolytropicStates setup)
    (_properties : HasNitrogenPropertyData setup)
    (_laws : SatisfiesClosedIdealGasPolytropicLaws setup) :
    668 ≤ temperatureInKelvins
        (setup.stateAt .final).absoluteTemperature ∧
      temperatureInKelvins
          (setup.stateAt .final).absoluteTemperature ≤ 669 := by
  let v₁ :=
    specificVolumeInCubicMetersPerKilogram
      (setup.stateAt .initial).specificVolume
  let v₂ :=
    specificVolumeInCubicMetersPerKilogram
      (setup.stateAt .final).specificVolume
  let T₂ :=
    temperatureInKelvins (setup.stateAt .final).absoluteTemperature
  have hv₁pos : 0 < v₁ := _physical.specificVolumePositive .initial
  have hv₂pos : 0 < v₂ := _physical.specificVolumePositive .final
  have hT₂pos : 0 < T₂ := _physical.absoluteTemperaturePositive .final
  have hv₁ : v₁ = 371 / 2500 := by
    have h := _laws.idealGasEquationAtEndpoint .initial
    change
      pressureInKilopascals (setup.stateAt .initial).pressure * v₁ =
        specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant *
          temperatureInKelvins
            (setup.stateAt .initial).absoluteTemperature at h
    rw [_data.initialPressureKilopascals,
      _properties.specificGasConstantValue,
      _data.initialTemperatureKelvins] at h
    norm_num at h ⊢
    linarith
  have hv₂ : v₂ = 371 / 937500 * T₂ := by
    have h := _laws.idealGasEquationAtEndpoint .final
    change
      pressureInKilopascals (setup.stateAt .final).pressure * v₂ =
        specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant * T₂ at h
    rw [_data.finalPressureKilopascals,
      _properties.specificGasConstantValue] at h
    norm_num at h ⊢
    linarith
  have hrpow :
      2 * v₁ ^ (6 / 5 : ℝ) = v₂ ^ (6 / 5 : ℝ) := by
    have h := _laws.polytropicEndpointRelation
    change
      pressureInKilopascals (setup.stateAt .initial).pressure *
          v₁ ^ setup.polytropicExponent =
        pressureInKilopascals (setup.stateAt .final).pressure *
          v₂ ^ setup.polytropicExponent at h
    rw [_data.initialPressureKilopascals,
      _data.finalPressureKilopascals,
      _data.exponentIsOnePointTwo] at h
    norm_num at h ⊢
    linarith
  have hv₁rpow :
      (v₁ ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = v₁ ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv₁pos.le]
    norm_num [Real.rpow_natCast]
  have hv₂rpow :
      (v₂ ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = v₂ ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv₂pos.le]
    norm_num [Real.rpow_natCast]
  have hvolumes :=
    congrArg (fun x : ℝ => x ^ (5 : ℕ)) hrpow
  rw [mul_pow, hv₁rpow, hv₂rpow] at hvolumes
  norm_num at hvolumes
  rw [hv₁, hv₂] at hvolumes
  have hT₂sixth :
      2 * T₂ ^ (6 : ℕ) = (750 : ℝ) ^ (6 : ℕ) := by
    ring_nf at hvolumes ⊢
    nlinarith
  change 668 ≤ T₂ ∧ T₂ ≤ 669
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 6) (by norm_num) hT₂pos.le
    norm_num at hT₂sixth ⊢
    nlinarith
  · apply le_of_pow_le_pow_left₀ (n := 6) (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 669)
    norm_num at hT₂sixth ⊢
    nlinarith

/-- The polytropic expansion work is approximately `121.43 kJ/kg`. -/
lemma specific_boundary_work_in_expected_interval
    (setup : NitrogenPolytropicExpansion)
    (figure : PrimaryFigure)
    (_data : MatchesProblemAndPrimaryFigure setup figure)
    (_physical : HasPhysicalPolytropicStates setup)
    (_properties : HasNitrogenPropertyData setup)
    (_laws : SatisfiesClosedIdealGasPolytropicLaws setup) :
    121 ≤ specificEnergyInKilojoulesPerKilogram
        setup.specificBoundaryWorkDoneByGas ∧
      specificEnergyInKilojoulesPerKilogram
          setup.specificBoundaryWorkDoneByGas ≤ 122 := by
  have htemperature :=
    final_temperature_in_caloric_table_interval
      setup figure _data _physical _properties _laws
  let v₁ :=
    specificVolumeInCubicMetersPerKilogram
      (setup.stateAt .initial).specificVolume
  let v₂ :=
    specificVolumeInCubicMetersPerKilogram
      (setup.stateAt .final).specificVolume
  let T₂ :=
    temperatureInKelvins (setup.stateAt .final).absoluteTemperature
  change 668 ≤ T₂ ∧ T₂ ≤ 669 at htemperature
  have hv₁pos : 0 < v₁ := _physical.specificVolumePositive .initial
  have hv₂pos : 0 < v₂ := _physical.specificVolumePositive .final
  have hv₁ : v₁ = 371 / 2500 := by
    have h := _laws.idealGasEquationAtEndpoint .initial
    change
      pressureInKilopascals (setup.stateAt .initial).pressure * v₁ =
        specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant *
          temperatureInKelvins
            (setup.stateAt .initial).absoluteTemperature at h
    rw [_data.initialPressureKilopascals,
      _properties.specificGasConstantValue,
      _data.initialTemperatureKelvins] at h
    norm_num at h ⊢
    linarith
  have hv₂ : v₂ = 371 / 937500 * T₂ := by
    have h := _laws.idealGasEquationAtEndpoint .final
    change
      pressureInKilopascals (setup.stateAt .final).pressure * v₂ =
        specificGasConstantInKilojoulesPerKilogramKelvin
            setup.specificGasConstant * T₂ at h
    rw [_data.finalPressureKilopascals,
      _properties.specificGasConstantValue] at h
    norm_num at h ⊢
    linarith
  have hrpow :
      2 * v₁ ^ (6 / 5 : ℝ) = v₂ ^ (6 / 5 : ℝ) := by
    have h := _laws.polytropicEndpointRelation
    change
      pressureInKilopascals (setup.stateAt .initial).pressure *
          v₁ ^ setup.polytropicExponent =
        pressureInKilopascals (setup.stateAt .final).pressure *
          v₂ ^ setup.polytropicExponent at h
    rw [_data.initialPressureKilopascals,
      _data.finalPressureKilopascals,
      _data.exponentIsOnePointTwo] at h
    norm_num at h ⊢
    linarith
  have hv₁rpow :
      (v₁ ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = v₁ ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv₁pos.le]
    norm_num [Real.rpow_natCast]
  have hv₂rpow :
      (v₂ ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = v₂ ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv₂pos.le]
    norm_num [Real.rpow_natCast]
  have hvolumes :=
    congrArg (fun x : ℝ => x ^ (5 : ℕ)) hrpow
  rw [mul_pow, hv₁rpow, hv₂rpow] at hvolumes
  norm_num at hvolumes
  rw [hv₁, hv₂] at hvolumes
  have hT₂sixth :
      2 * T₂ ^ (6 : ℕ) = (750 : ℝ) ^ (6 : ℕ) := by
    ring_nf at hvolumes ⊢
    nlinarith
  have hT₂upper : T₂ ≤ 3341 / 5 := by
    apply le_of_pow_le_pow_left₀ (n := 6) (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 3341 / 5)
    norm_num at hT₂sixth ⊢
    nlinarith
  have hexponent : setup.polytropicExponent ≠ 1 := by
    rw [_data.exponentIsOnePointTwo]
    norm_num
  have hwork := _laws.polytropicBoundaryWork hexponent
  rw [_laws.idealGasEquationAtEndpoint .final,
    _laws.idealGasEquationAtEndpoint .initial,
    _properties.specificGasConstantValue,
    _data.initialTemperatureKelvins,
    _data.exponentIsOnePointTwo] at hwork
  norm_num at hwork
  change
    specificEnergyInKilojoulesPerKilogram
        setup.specificBoundaryWorkDoneByGas =
      (371 / 1250 * T₂ - 1113 / 5) / -(1 / 5) at hwork
  constructor <;> linarith

/-- The first law and nitrogen caloric data bracket the requested heat. -/
lemma specific_heat_transfer_in_expected_interval
    (setup : NitrogenPolytropicExpansion)
    (figure : PrimaryFigure)
    (_data : MatchesProblemAndPrimaryFigure setup figure)
    (_physical : HasPhysicalPolytropicStates setup)
    (_properties : HasNitrogenPropertyData setup)
    (_laws : SatisfiesClosedIdealGasPolytropicLaws setup) :
    55 ≤ specificEnergyInKilojoulesPerKilogram
        setup.specificHeatTransferredToGas ∧
      specificEnergyInKilojoulesPerKilogram
          setup.specificHeatTransferredToGas ≤ 113 / 2 := by
  have hwork :=
    specific_boundary_work_in_expected_interval
      setup figure _data _physical _properties _laws
  have hfirstLaw := _laws.closedSystemFirstLaw
  constructor
  · linarith [_properties.internalEnergyChangeLowerBound]
  · norm_num
    linarith [_properties.internalEnergyChangeUpperBound]

/-! ## Multiple-choice target -/

/-- Answer labels printed beside the four displayed heat-transfer values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed specific heat transfer in kilojoules per kilogram. -/
def displayedSpecificHeatTransferInKilojoulesPerKilogram :
    AnswerChoice → ℝ
  | .A => 303 / 5
  | .B => 45
  | .C => 789 / 10
  | .D => 56

/-- Dataset metadata records answer D; this definition is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A displayed value is uniquely closest to the process heat-transfer readout. -/
def IsUniqueClosestDisplayedAnswer
    (setup : NitrogenPolytropicExpansion) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |specificEnergyInKilojoulesPerKilogram
          setup.specificHeatTransferredToGas -
        displayedSpecificHeatTransferInKilojoulesPerKilogram choice| <
      |specificEnergyInKilojoulesPerKilogram
            setup.specificHeatTransferredToGas -
          displayedSpecificHeatTransferInKilojoulesPerKilogram other|

/-!
The requested specific heat transfer is within `1 kJ/kg` of the displayed
`56.0 kJ/kg` value, and that value is uniquely closest among the choices.

This formalizes blueprint label `thm:physics:phyx_mini_0459:target`.
-/
theorem problem_phyx_mini_0459
    (setup : NitrogenPolytropicExpansion)
    (figure : PrimaryFigure)
    (_data : MatchesProblemAndPrimaryFigure setup figure)
    (_physical : HasPhysicalPolytropicStates setup)
    (_properties : HasNitrogenPropertyData setup)
    (_laws : SatisfiesClosedIdealGasPolytropicLaws setup) :
    |specificEnergyInKilojoulesPerKilogram
          setup.specificHeatTransferredToGas -
        displayedSpecificHeatTransferInKilojoulesPerKilogram .D| ≤ 1 ∧
      IsUniqueClosestDisplayedAnswer setup .D := by
  have hheat :=
    specific_heat_transfer_in_expected_interval
      setup figure _data _physical _properties _laws
  let q :=
    specificEnergyInKilojoulesPerKilogram
      setup.specificHeatTransferredToGas
  change |q - displayedSpecificHeatTransferInKilojoulesPerKilogram .D| ≤ 1 ∧
    IsUniqueClosestDisplayedAnswer setup .D
  have hclosest : |q - 56| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  constructor
  · simpa [displayedSpecificHeatTransferInKilojoulesPerKilogram] using hclosest
  · intro other hother
    change
      |q - displayedSpecificHeatTransferInKilojoulesPerKilogram .D| <
        |q - displayedSpecificHeatTransferInKilojoulesPerKilogram other|
    cases other with
    | A =>
        simp only [displayedSpecificHeatTransferInKilojoulesPerKilogram]
        have hsign : q - 303 / 5 ≤ 0 := by linarith
        rw [abs_of_nonpos hsign]
        exact lt_of_le_of_lt hclosest (by norm_num; linarith)
    | B =>
        simp only [displayedSpecificHeatTransferInKilojoulesPerKilogram]
        have hsign : 0 ≤ q - 45 := by linarith
        rw [abs_of_nonneg hsign]
        exact lt_of_le_of_lt hclosest (by linarith)
    | C =>
        simp only [displayedSpecificHeatTransferInKilojoulesPerKilogram]
        have hsign : q - 789 / 10 ≤ 0 := by linarith
        rw [abs_of_nonpos hsign]
        exact lt_of_le_of_lt hclosest (by norm_num; linarith)
    | D =>
        exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0459
