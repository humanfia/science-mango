import Mathlib.Analysis.Real.Sqrt
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0334

open Dimension

/-!
# Stopping height for water discharged from a sealed, pressurized tank

The tank is cylindrical, has total height `4.00 m`, and has a hose attached
at a side outlet `1.00 m` above the base.  The water height `h` is measured
from the base.  Above the water is a sealed amount of compressed air whose
absolute pressure is `4.20 * 10^5 Pa` when `h = 3.50 m`.  The air expands
isothermally while water leaves the tank, and the hose discharges to an
atmosphere at absolute pressure `1.00 * 10^5 Pa`.

Basic physical quantities are represented by Physlib's unit-independent
`Dimensionful` types.  Real numbers occur only as coherent SI readouts and as
the dimensionless coefficients in the final algebraic relation.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative cross-sectional area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Absolute pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def nonnegativeQuantityReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- SI metre readout of a length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI length

/-- SI square-metre readout of an area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI area

/-- SI cubic-metre readout of a volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI volume

/-- SI kilogram-per-cubic-metre readout of a mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI density

/-- SI metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeQuantityReadout UnitChoices.SI acceleration

/-- SI pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-! ## Physical and primary-figure roles -/

/-- Shape of the vessel shown in the supplied figure. -/
inductive TankShape where
  | cylindrical
  deriving DecidableEq, Repr

/-- Boundary condition at the top of the tank. -/
inductive TankTopBoundary where
  | sealed
  deriving DecidableEq, Repr

/-- Liquid named in the problem statement. -/
inductive TankLiquid where
  | water
  deriving DecidableEq, Repr

/-- Gas occupying the headspace above the water. -/
inductive HeadspaceGas where
  | compressedAir
  deriving DecidableEq, Repr

/-- Environment to which the side hose discharges. -/
inductive OutletEnvironment where
  | atmosphere
  deriving DecidableEq, Repr

/-- Quantity symbols printed in the primary figure. -/
inductive FigureQuantityLabel where
  | p
  | h
  deriving DecidableEq, Repr

/-- Physical role of each printed quantity symbol. -/
inductive FigureQuantityRole where
  | absoluteAirPressureAtWaterSurface
  | waterHeightFromBaseToSurface
  deriving DecidableEq, Repr

/-- The two explicit vertical length markers in the primary figure. -/
inductive FigureLengthMarker where
  | totalTankHeight
  | outletHeightAboveBase
  deriving DecidableEq, Repr

/-- Geometric location at which the visible hose is attached. -/
inductive FigureLocation where
  | sideOutlet
  deriving DecidableEq, Repr

/-- Structured transcription of the labels and geometry in image `334.png`. -/
structure TankHoseFigure where
  tankShape : TankShape
  quantityRole : FigureQuantityLabel → FigureQuantityRole
  lengthMarker : FigureLengthMarker → LengthQuantity
  hoseConnection : FigureLocation
  hoseVisible : Bool

/-! ## Independent apparatus and state observables -/

/--
The physical apparatus and state-dependent observables.

Pressure, headspace volume, absolute temperature, and liquid pressure at the
inside of the outlet are independent fields here.  Their physical relations
are supplied by the governing-law predicates below; in particular, the
stopped height and the recorded answer are not definitions in this setup.
-/
structure SealedPressurizedTank where
  figure : TankHoseFigure
  topBoundary : TankTopBoundary
  liquid : TankLiquid
  headspaceGas : HeadspaceGas
  outletEnvironment : OutletEnvironment
  tankHeight : LengthQuantity
  outletHeightAboveBase : LengthQuantity
  initialWaterHeight : LengthQuantity
  crossSectionalArea : AreaQuantity
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  atmosphericPressure : PressureQuantity
  airPressureAtWaterHeight : LengthQuantity → PressureQuantity
  headspaceVolumeAtWaterHeight : LengthQuantity → VolumeQuantity
  airTemperatureAtWaterHeight : LengthQuantity → Temperature
  liquidPressureAtOutlet : LengthQuantity → PressureQuantity

/-- A water height lies inside the cylindrical vessel. -/
def IsAdmissibleWaterHeight
    (setup : SealedPressurizedTank) (height : LengthQuantity) : Prop :=
  0 ≤ lengthInMeters height ∧
    lengthInMeters height < lengthInMeters setup.tankHeight

/--
A height is on the decreasing-height branch reached after discharge begins:
the outlet is still covered and the height has not increased above its
initial value.
-/
def OccursAlongOutflowFromInitialState
    (setup : SealedPressurizedTank) (height : LengthQuantity) : Prop :=
  IsAdmissibleWaterHeight setup height ∧
    lengthInMeters setup.outletHeightAboveBase ≤ lengthInMeters height ∧
    lengthInMeters height ≤ lengthInMeters setup.initialWaterHeight

/-! ## Problem data and figure readouts -/

/--
The stated calibration and the readouts visible in the primary figure.

The pressure values are absolute.  The figure's `p` labels the compressed-air
pressure at the water surface, while `h` spans from the tank base to that
surface.  No stopped height or answer choice is included here.
-/
structure MatchesProblemAndFigureData (setup : SealedPressurizedTank) : Prop where
  sealedTop : setup.topBoundary = .sealed
  containsWater : setup.liquid = .water
  compressedAirHeadspace : setup.headspaceGas = .compressedAir
  hoseDischargesToAtmosphere : setup.outletEnvironment = .atmosphere
  cylindricalFigure : setup.figure.tankShape = .cylindrical
  pressureLabelRole :
    setup.figure.quantityRole .p = .absoluteAirPressureAtWaterSurface
  waterHeightLabelRole :
    setup.figure.quantityRole .h = .waterHeightFromBaseToSurface
  totalHeightMarkerMatchesTank :
    setup.figure.lengthMarker .totalTankHeight = setup.tankHeight
  outletMarkerMatchesOutlet :
    setup.figure.lengthMarker .outletHeightAboveBase =
      setup.outletHeightAboveBase
  hoseAttachedAtSideOutlet : setup.figure.hoseConnection = .sideOutlet
  hoseIsShown : setup.figure.hoseVisible = true
  tankHeightMeters : lengthInMeters setup.tankHeight = 4
  outletHeightMeters : lengthInMeters setup.outletHeightAboveBase = 1
  initialWaterHeightMeters : lengthInMeters setup.initialWaterHeight = 7 / 2
  initialAbsoluteAirPressurePascals :
    pressureInPascals
        (setup.airPressureAtWaterHeight setup.initialWaterHeight) = 420000
  atmosphericPressurePascals :
    pressureInPascals setup.atmosphericPressure = 100000

/--
Standard near-surface numerical model for water on Earth, in coherent SI
units.  These implicit textbook constants are separated from the values
explicitly printed in the problem.
-/
structure UsesStandardWaterAndGravity (setup : SealedPressurizedTank) : Prop where
  waterDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.waterMassDensity = 1000
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-! ## Governing physical laws -/

/--
For the cylindrical tank, headspace volume equals cross-sectional area times
the vertical distance from the water surface to the sealed top.
-/
structure HasCylindricalHeadspaceGeometry
    (setup : SealedPressurizedTank) : Prop where
  positiveCrossSectionalArea : 0 < areaInSquareMeters setup.crossSectionalArea
  headspaceVolumeLaw :
    ∀ height : LengthQuantity,
      IsAdmissibleWaterHeight setup height →
        volumeInCubicMeters (setup.headspaceVolumeAtWaterHeight height) =
          areaInSquareMeters setup.crossSectionalArea *
            (lengthInMeters setup.tankHeight - lengthInMeters height)

/--
The sealed headspace follows an isothermal ideal-gas process.  The first field
states constant absolute temperature; the second is Boyle's law `p V =
constant` for any two admissible water heights.
-/
structure SatisfiesIsothermalIdealGasLaw
    (setup : SealedPressurizedTank) : Prop where
  positiveAbsolutePressure :
    ∀ height : LengthQuantity,
      IsAdmissibleWaterHeight setup height →
        0 < pressureInPascals (setup.airPressureAtWaterHeight height)
  constantTemperature :
    ∀ height₁ height₂ : LengthQuantity,
      IsAdmissibleWaterHeight setup height₁ →
      IsAdmissibleWaterHeight setup height₂ →
        setup.airTemperatureAtWaterHeight height₁ =
          setup.airTemperatureAtWaterHeight height₂
  boyleLaw :
    ∀ height₁ height₂ : LengthQuantity,
      IsAdmissibleWaterHeight setup height₁ →
      IsAdmissibleWaterHeight setup height₂ →
        pressureInPascals (setup.airPressureAtWaterHeight height₁) *
            volumeInCubicMeters
              (setup.headspaceVolumeAtWaterHeight height₁) =
          pressureInPascals (setup.airPressureAtWaterHeight height₂) *
            volumeInCubicMeters
              (setup.headspaceVolumeAtWaterHeight height₂)

/--
Hydrostatic pressure at the inside of the side outlet equals the air pressure
at the water surface plus `rho * g` times the water depth above the outlet.
-/
structure SatisfiesHydrostaticOutletLaw
    (setup : SealedPressurizedTank) : Prop where
  outletPressureLaw :
    ∀ height : LengthQuantity,
      IsAdmissibleWaterHeight setup height →
      lengthInMeters setup.outletHeightAboveBase ≤ lengthInMeters height →
        pressureInPascals (setup.liquidPressureAtOutlet height) =
          pressureInPascals (setup.airPressureAtWaterHeight height) +
            densityInKilogramsPerCubicMeter setup.waterMassDensity *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              (lengthInMeters height -
                lengthInMeters setup.outletHeightAboveBase)

/--
Flow stops on the physical decreasing-height branch when the static liquid
pressure just inside the hose equals the atmospheric pressure outside it.
-/
def FlowStopsAt
    (setup : SealedPressurizedTank) (height : LengthQuantity) : Prop :=
  OccursAlongOutflowFromInitialState setup height ∧
    pressureInPascals (setup.liquidPressureAtOutlet height) =
      pressureInPascals setup.atmosphericPressure

/-! ## Algebraic consequences of the model -/

/-- Boyle's law and cylindrical geometry give the pressure-height relation. -/
lemma air_pressure_times_headspace_height_eq_initial
    (setup : SealedPressurizedTank)
    (geometry : HasCylindricalHeadspaceGeometry setup)
    (gasLaw : SatisfiesIsothermalIdealGasLaw setup)
    (height : LengthQuantity)
    (initialAdmissible :
      IsAdmissibleWaterHeight setup setup.initialWaterHeight)
    (heightAdmissible : IsAdmissibleWaterHeight setup height) :
    pressureInPascals (setup.airPressureAtWaterHeight height) *
        (lengthInMeters setup.tankHeight - lengthInMeters height) =
      pressureInPascals
          (setup.airPressureAtWaterHeight setup.initialWaterHeight) *
        (lengthInMeters setup.tankHeight -
          lengthInMeters setup.initialWaterHeight) := by
  have hBoyle := gasLaw.boyleLaw height setup.initialWaterHeight
    heightAdmissible initialAdmissible
  rw [geometry.headspaceVolumeLaw height heightAdmissible,
    geometry.headspaceVolumeLaw setup.initialWaterHeight initialAdmissible] at hBoyle
  nlinarith [geometry.positiveCrossSectionalArea]

/-- At a stopped height, hydrostatic outlet pressure balances atmosphere. -/
lemma stopped_height_pressure_balance
    (setup : SealedPressurizedTank)
    (hydrostaticLaw : SatisfiesHydrostaticOutletLaw setup)
    (height : LengthQuantity)
    (stops : FlowStopsAt setup height) :
    pressureInPascals (setup.airPressureAtWaterHeight height) +
          densityInKilogramsPerCubicMeter setup.waterMassDensity *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            (lengthInMeters height -
              lengthInMeters setup.outletHeightAboveBase) =
      pressureInPascals setup.atmosphericPressure := by
  exact
    (hydrostaticLaw.outletPressureLaw height stops.1.1 stops.1.2.1).symm.trans
      stops.2

/--
After inserting the printed data and standard water/gravity values, the
physical stopped height satisfies the resulting quadratic equation.
-/
lemma stopped_height_satisfies_quadratic
    (setup : SealedPressurizedTank)
    (data : MatchesProblemAndFigureData setup)
    (standard : UsesStandardWaterAndGravity setup)
    (geometry : HasCylindricalHeadspaceGeometry setup)
    (gasLaw : SatisfiesIsothermalIdealGasLaw setup)
    (hydrostaticLaw : SatisfiesHydrostaticOutletLaw setup)
    (height : LengthQuantity)
    (stops : FlowStopsAt setup height) :
    49 * (lengthInMeters height) ^ 2 -
          745 * lengthInMeters height + 1146 = 0 := by
  have initialAdmissible :
      IsAdmissibleWaterHeight setup setup.initialWaterHeight := by
    unfold IsAdmissibleWaterHeight
    rw [data.initialWaterHeightMeters, data.tankHeightMeters]
    norm_num
  have hBoyle :=
    air_pressure_times_headspace_height_eq_initial setup geometry gasLaw
      height initialAdmissible stops.1.1
  have hBalance :=
    stopped_height_pressure_balance setup hydrostaticLaw height stops
  rw [data.tankHeightMeters, data.initialWaterHeightMeters,
    data.initialAbsoluteAirPressurePascals] at hBoyle
  rw [standard.waterDensityKilogramsPerCubicMeter,
    standard.gravitationalAccelerationMetersPerSecondSquared,
    data.outletHeightMeters, data.atmosphericPressurePascals] at hBalance
  norm_num at hBoyle hBalance ⊢
  nlinarith

/-! ## Display precision and answer choices -/

/-- The four height choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre readout displayed beside an answer choice. -/
def displayedHeightMeters : AnswerChoice → ℝ
  | .A => 174 / 100
  | .B => 155 / 100
  | .C => 164 / 100
  | .D => 192 / 100

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- A physical height rounds to the displayed value at hundredth-metre precision. -/
def RoundsToDisplayedHundredthMeter
    (actualMeters displayedMeters : ℝ) : Prop :=
  |actualMeters - displayedMeters| < 1 / 200

/--
The physically relevant root is
`(745 - sqrt 330409) / 98 = 1.7366... m`; it rounds to `1.74 m`, and only
choice A matches at the precision of the displayed choices.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0334:target`.
-/
theorem problem_phyx_mini_0334
    (setup : SealedPressurizedTank)
    (data : MatchesProblemAndFigureData setup)
    (standard : UsesStandardWaterAndGravity setup)
    (geometry : HasCylindricalHeadspaceGeometry setup)
    (gasLaw : SatisfiesIsothermalIdealGasLaw setup)
    (hydrostaticLaw : SatisfiesHydrostaticOutletLaw setup)
    (stoppedHeight : LengthQuantity)
    (stops : FlowStopsAt setup stoppedHeight) :
    lengthInMeters stoppedHeight =
        (745 - Real.sqrt 330409) / 98 ∧
      RoundsToDisplayedHundredthMeter
        (lengthInMeters stoppedHeight)
        (displayedHeightMeters recordedDatasetAnswer) ∧
      ∀ choice : AnswerChoice,
        RoundsToDisplayedHundredthMeter
            (lengthInMeters stoppedHeight) (displayedHeightMeters choice) ↔
          choice = recordedDatasetAnswer := by
  have hQuadratic :=
    stopped_height_satisfies_quadratic setup data standard geometry gasLaw
      hydrostaticLaw stoppedHeight stops
  have hBranch : lengthInMeters stoppedHeight ≤ 7 / 2 := by
    rw [← data.initialWaterHeightMeters]
    exact stops.1.2.2
  have hSqrtSq : (Real.sqrt (330409 : ℝ)) ^ 2 = 330409 := by
    norm_num
  have hSqrtNonneg : 0 ≤ Real.sqrt (330409 : ℝ) := Real.sqrt_nonneg _
  have hRoot :
      lengthInMeters stoppedHeight = (745 - Real.sqrt 330409) / 98 := by
    nlinarith
  have hSqrtLower : 574 < Real.sqrt (330409 : ℝ) := by
    nlinarith
  have hSqrtUpper : Real.sqrt (330409 : ℝ) < 5749 / 10 := by
    nlinarith
  have hLower : 347 / 200 < lengthInMeters stoppedHeight := by
    rw [hRoot]
    nlinarith
  have hUpper : lengthInMeters stoppedHeight < 349 / 200 := by
    rw [hRoot]
    nlinarith
  have hRoundA :
      RoundsToDisplayedHundredthMeter (lengthInMeters stoppedHeight)
        (displayedHeightMeters recordedDatasetAnswer) := by
    rw [hRoot]
    simp only [RoundsToDisplayedHundredthMeter, recordedDatasetAnswer,
      displayedHeightMeters]
    rw [abs_lt]
    constructor <;> nlinarith
  have hNotB :
      ¬ RoundsToDisplayedHundredthMeter (lengthInMeters stoppedHeight)
        (displayedHeightMeters .B) := by
    simp only [RoundsToDisplayedHundredthMeter, displayedHeightMeters]
    rw [abs_of_pos (by nlinarith [hLower])]
    nlinarith [hLower]
  have hNotC :
      ¬ RoundsToDisplayedHundredthMeter (lengthInMeters stoppedHeight)
        (displayedHeightMeters .C) := by
    simp only [RoundsToDisplayedHundredthMeter, displayedHeightMeters]
    rw [abs_of_pos (by nlinarith [hLower])]
    nlinarith [hLower]
  have hNotD :
      ¬ RoundsToDisplayedHundredthMeter (lengthInMeters stoppedHeight)
        (displayedHeightMeters .D) := by
    simp only [RoundsToDisplayedHundredthMeter, displayedHeightMeters]
    rw [abs_of_neg (by nlinarith [hUpper])]
    nlinarith [hUpper]
  refine ⟨hRoot, hRoundA, ?_⟩
  intro choice
  cases choice with
  | A => simpa only [recordedDatasetAnswer, eq_self, iff_true] using hRoundA
  | B => simp [recordedDatasetAnswer, hNotB]
  | C => simp [recordedDatasetAnswer, hNotC]
  | D => simp [recordedDatasetAnswer, hNotD]

end PhyXMiniProblems.ProblemPhyXMini0334
