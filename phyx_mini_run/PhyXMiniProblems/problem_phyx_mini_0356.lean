import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0356

open Dimension

/-!
# Heat absorbed along a straight pressure--volume path

A fixed amount of gas can be taken from macrostate `A` to macrostate `B` along
several quasistatic paths in the supplied pressure--volume diagram.  The curved
reference path is adiabatic and obeys

`p̄ = α V⁻⁵ᐟ³`.

The requested path is the diagonal path `b`, on which the volume increases and
the mean pressure decreases linearly with volume while heat is supplied.

Pressure, volume, heat, work, and internal energy retain their physical
dimensions.  Real numbers below are only readouts in explicitly named units,
dimensionless exponents, or coordinates used to describe a pressure trace.
Work is positive when done by the gas and heat is positive when absorbed by
the gas, so the first law is written `Q = ΔU + W`.
-/

/-! ## Dimensionful quantities and named readouts -/

/-- A signed physical volume, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure, with dimension `M L⁻¹ T⁻²`. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy, used for heat, work, and internal energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/--
Read a physical volume in the horizontal-axis unit `10³ cm³`.
One such unit is one litre, or `10⁻³ m³`.
-/
def volumeInThousandsOfCubicCentimeters
    (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/--
Read a physical pressure in the vertical-axis unit `10⁶ dyn/cm²`.
Since `1 dyn/cm² = 0.1 Pa`, one axis unit is `10⁵ Pa`.
-/
def pressureInMillionsOfDynesPerSquareCentimeter
    (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 100000

/-- Read heat, work, or internal energy in SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- The dimensionless exponent printed on the adiabatic curve. -/
def statedAdiabaticExponent : ℝ := 5 / 3

/-! ## Macrostates, process paths, and primary-figure vocabulary -/

/-- The four state labels printed in the primary pressure--volume diagram. -/
inductive MacrostateLabel where
  | a
  | aPrime
  | b
  | bPrime
  deriving DecidableEq, Repr

/--
The four directed routes from `A` to `B` shown in the diagram.  Paths `a` and
`c` are the two rectangular routes, while path `b` is the requested diagonal.
-/
inductive ProcessPath where
  | a
  | b
  | c
  | adiabaticReference
  deriving DecidableEq, Repr

/-- Which thermodynamic quantity is assigned to a plotted axis. -/
inductive AxisQuantity where
  | volume
  | meanPressure
  deriving DecidableEq, Repr

/-- The scale printed beside the pressure axis. -/
inductive PressureAxisScale where
  | millionDynesPerSquareCentimeter
  deriving DecidableEq, Repr

/-- The scale printed beneath the volume axis. -/
inductive VolumeAxisScale where
  | thousandCubicCentimeters
  deriving DecidableEq, Repr

/-- Geometric form of a complete route from `A` to `B`. -/
inductive PathGeometry where
  | upperIsobaricThenRightIsochoric
  | straightDiagonal
  | leftIsochoricThenLowerIsobaric
  | smoothAdiabaticCurve
  deriving DecidableEq, Repr

/-- Thermal characterization stated for the two physically relevant paths. -/
inductive PathThermalDescription where
  | notSpecified
  | heatSupplied
  | adiabaticNoHeatExchange
  deriving DecidableEq, Repr

/--
Qualitative and geometric information visible in the primary bitmap.  The
physical coordinate values themselves live in `GasPVProcessSetup`.
-/
structure PressureVolumeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  pressureAxisScale : PressureAxisScale
  volumeAxisScale : VolumeAxisScale
  statePointShown : MacrostateLabel → Bool
  stateLabelShown : MacrostateLabel → Bool
  pathShown : ProcessPath → Bool
  pathArrowStart : ProcessPath → MacrostateLabel
  pathArrowFinish : ProcessPath → MacrostateLabel
  pathGeometry : ProcessPath → PathGeometry
  adiabaticEquationShown : Bool

/-!
Independent physical quantities for the gas and its processes.

`meanPressureTraceInPascals path v` is the scalar readout of the path's mean
pressure at SI volume coordinate `v` in cubic metres.  The coefficient `α` is
also stored as an SI scalar because its unit is the compound unit
`Pa·m⁵` once the stated exponent `5/3` is imposed.  Heat and work remain
independent dimensionful fields until the governing laws below relate them.
-/
structure GasPVProcessSetup where
  figure : PressureVolumeFigure
  volumeAt : MacrostateLabel → VolumeQuantity
  meanPressureAt : MacrostateLabel → PressureQuantity
  internalEnergyAt : MacrostateLabel → EnergyQuantity
  workDoneByGasAlong : ProcessPath → EnergyQuantity
  netHeatAbsorbedAlong : ProcessPath → EnergyQuantity
  meanPressureTraceInPascals : ProcessPath → ℝ → ℝ
  adiabaticCoefficientInPascalMeterPowFive : ℝ
  pressureVolumeExponent : ℝ
  thermalDescription : ProcessPath → PathThermalDescription

/-- The interval of SI volume coordinates traversed from `A` to `B`. -/
def BetweenEndpointVolumes
    (setup : GasPVProcessSetup) (volumeCubicMeters : ℝ) : Prop :=
  volumeCubicMeters ∈
    Set.Icc
      (volumeInCubicMeters (setup.volumeAt .a))
      (volumeInCubicMeters (setup.volumeAt .b))

/-! ## Figure and problem-statement data -/

/-!
Transcription of the primary image and prose.  The endpoint data are

* `A = (1 × 10³ cm³, 32 × 10⁶ dyn/cm²)`,
* `B = (8 × 10³ cm³,  1 × 10⁶ dyn/cm²)`.

The other two corners are `A'` and `B'`.  Every arrowed route starts at `A`
and ends at `B`; the requested route `b` is straight and heat-supplied, whereas
the curved reference is adiabatic.  No numerical heat, work, or internal-energy
value occurs in this structure.
-/
structure MatchesProblemStatementAndPrimaryFigure
    (setup : GasPVProcessSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsMeanPressure :
    setup.figure.verticalAxisQuantity = .meanPressure
  pressureScaleMatchesFigure :
    setup.figure.pressureAxisScale = .millionDynesPerSquareCentimeter
  volumeScaleMatchesFigure :
    setup.figure.volumeAxisScale = .thousandCubicCentimeters
  everyStatePointShown :
    ∀ state : MacrostateLabel, setup.figure.statePointShown state = true
  everyStateLabelShown :
    ∀ state : MacrostateLabel, setup.figure.stateLabelShown state = true
  everyPathShown :
    ∀ path : ProcessPath, setup.figure.pathShown path = true
  everyPathStartsAtA :
    ∀ path : ProcessPath, setup.figure.pathArrowStart path = .a
  everyPathFinishesAtB :
    ∀ path : ProcessPath, setup.figure.pathArrowFinish path = .b
  pathAHasShownGeometry :
    setup.figure.pathGeometry .a = .upperIsobaricThenRightIsochoric
  pathBIsStraightDiagonal :
    setup.figure.pathGeometry .b = .straightDiagonal
  pathCHasShownGeometry :
    setup.figure.pathGeometry .c = .leftIsochoricThenLowerIsobaric
  adiabaticPathIsSmoothCurve :
    setup.figure.pathGeometry .adiabaticReference = .smoothAdiabaticCurve
  adiabaticEquationIsPrinted : setup.figure.adiabaticEquationShown = true
  volumeAtA_axisUnits :
    volumeInThousandsOfCubicCentimeters (setup.volumeAt .a) = 1
  pressureAtA_axisUnits :
    pressureInMillionsOfDynesPerSquareCentimeter
        (setup.meanPressureAt .a) = 32
  volumeAtAPrime_axisUnits :
    volumeInThousandsOfCubicCentimeters (setup.volumeAt .aPrime) = 1
  pressureAtAPrime_axisUnits :
    pressureInMillionsOfDynesPerSquareCentimeter
        (setup.meanPressureAt .aPrime) = 1
  volumeAtB_axisUnits :
    volumeInThousandsOfCubicCentimeters (setup.volumeAt .b) = 8
  pressureAtB_axisUnits :
    pressureInMillionsOfDynesPerSquareCentimeter
        (setup.meanPressureAt .b) = 1
  volumeAtBPrime_axisUnits :
    volumeInThousandsOfCubicCentimeters (setup.volumeAt .bPrime) = 8
  pressureAtBPrime_axisUnits :
    pressureInMillionsOfDynesPerSquareCentimeter
        (setup.meanPressureAt .bPrime) = 32
  exponentIsFiveThirds :
    setup.pressureVolumeExponent = statedAdiabaticExponent
  requestedPathHasHeatSupplied :
    setup.thermalDescription .b = .heatSupplied
  referencePathIsAdiabatic :
    setup.thermalDescription .adiabaticReference = .adiabaticNoHeatExchange

/-- Positivity and nondegeneracy conditions for the physical process. -/
structure HasPhysicalPVParameters (setup : GasPVProcessSetup) : Prop where
  volumePositive : ∀ state : MacrostateLabel,
    0 < volumeInCubicMeters (setup.volumeAt state)
  pressurePositive : ∀ state : MacrostateLabel,
    0 < pressureInPascals (setup.meanPressureAt state)
  tracePressurePositive : ∀ path volumeCubicMeters,
    BetweenEndpointVolumes setup volumeCubicMeters →
      0 < setup.meanPressureTraceInPascals path volumeCubicMeters
  adiabaticCoefficientPositive :
    0 < setup.adiabaticCoefficientInPascalMeterPowFive
  exponentNotOne : setup.pressureVolumeExponent ≠ 1

/-! ## Governing pressure, work, and energy laws -/

/-!
The path traces agree with their endpoint states.  The curved reference obeys
the displayed polytropic relation, and path `b` is the affine interpolation of
the endpoint pressures as a function of volume.  Thus “pressure decreases
linearly with volume” is a physical path law, not a definition of the answer.
-/
structure SatisfiesStatedPressureVolumePathLaws
    (setup : GasPVProcessSetup) : Prop where
  traceStartsAtPathStart : ∀ path : ProcessPath,
    setup.meanPressureTraceInPascals path
        (volumeInCubicMeters
          (setup.volumeAt (setup.figure.pathArrowStart path))) =
      pressureInPascals
        (setup.meanPressureAt (setup.figure.pathArrowStart path))
  traceFinishesAtPathFinish : ∀ path : ProcessPath,
    setup.meanPressureTraceInPascals path
        (volumeInCubicMeters
          (setup.volumeAt (setup.figure.pathArrowFinish path))) =
      pressureInPascals
        (setup.meanPressureAt (setup.figure.pathArrowFinish path))
  adiabaticPressureVolumeRelation : ∀ volumeCubicMeters : ℝ,
    BetweenEndpointVolumes setup volumeCubicMeters →
      setup.meanPressureTraceInPascals
          .adiabaticReference volumeCubicMeters =
        setup.adiabaticCoefficientInPascalMeterPowFive *
          volumeCubicMeters ^ (-setup.pressureVolumeExponent)
  requestedPathPressureIsLinear : ∀ volumeCubicMeters : ℝ,
    BetweenEndpointVolumes setup volumeCubicMeters →
      setup.meanPressureTraceInPascals .b volumeCubicMeters =
        pressureInPascals (setup.meanPressureAt .a) +
          (pressureInPascals (setup.meanPressureAt .b) -
              pressureInPascals (setup.meanPressureAt .a)) *
            (volumeCubicMeters -
              volumeInCubicMeters (setup.volumeAt .a)) /
            (volumeInCubicMeters (setup.volumeAt .b) -
              volumeInCubicMeters (setup.volumeAt .a))

/-!
Quasistatic boundary-work laws, with work positive when done by the gas.

For a straight path, work is the trapezoid area under the pressure trace.  For
a polytropic path `p V^γ = constant`, `γ ≠ 1`, integration gives
`W = (pᵢVᵢ - p_fV_f)/(γ - 1)`.  These are general endpoint formulas and contain
none of this problem's requested heat or derived numerical work values.
-/
structure SatisfiesQuasistaticBoundaryWorkLaws
    (setup : GasPVProcessSetup) : Prop where
  straightPathBoundaryWork : ∀ path : ProcessPath,
    setup.figure.pathGeometry path = .straightDiagonal →
      energyInJoules (setup.workDoneByGasAlong path) =
        (pressureInPascals
              (setup.meanPressureAt (setup.figure.pathArrowStart path)) +
            pressureInPascals
              (setup.meanPressureAt (setup.figure.pathArrowFinish path))) / 2 *
          (volumeInCubicMeters
              (setup.volumeAt (setup.figure.pathArrowFinish path)) -
            volumeInCubicMeters
              (setup.volumeAt (setup.figure.pathArrowStart path)))
  polytropicPathBoundaryWork : ∀ path : ProcessPath,
    setup.figure.pathGeometry path = .smoothAdiabaticCurve →
      setup.pressureVolumeExponent ≠ 1 →
        energyInJoules (setup.workDoneByGasAlong path) =
          (pressureInPascals
                (setup.meanPressureAt (setup.figure.pathArrowStart path)) *
              volumeInCubicMeters
                (setup.volumeAt (setup.figure.pathArrowStart path)) -
            pressureInPascals
                (setup.meanPressureAt (setup.figure.pathArrowFinish path)) *
              volumeInCubicMeters
                (setup.volumeAt (setup.figure.pathArrowFinish path))) /
            (setup.pressureVolumeExponent - 1)

/-!
An adiabatic path exchanges no heat.  The statement is quantified over any
path carrying that thermal description and does not constrain the heat on the
requested heat-supplied path `b`.
-/
structure SatisfiesAdiabaticNoHeatCondition
    (setup : GasPVProcessSetup) : Prop where
  adiabaticPathHasZeroHeat : ∀ path : ProcessPath,
    setup.thermalDescription path = .adiabaticNoHeatExchange →
      energyInJoules (setup.netHeatAbsorbedAlong path) = 0

/-!
The closed-system first law on every route, with heat into the gas and work by
the gas positive: `Q = U_finish - U_start + W`.  Internal energy is stored by
macrostate, so the same endpoint change is shared by every path from `A` to
`B` without being separately postulated.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : GasPVProcessSetup) : Prop where
  firstLawOnPath : ∀ path : ProcessPath,
    energyInJoules (setup.netHeatAbsorbedAlong path) =
      energyInJoules
          (setup.internalEnergyAt (setup.figure.pathArrowFinish path)) -
        energyInJoules
          (setup.internalEnergyAt (setup.figure.pathArrowStart path)) +
        energyInJoules (setup.workDoneByGasAlong path)

/-! ## Derived process values and requested heat -/

/-- The four heat values printed beside the answer-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed heat readout, in joules, for each answer choice. -/
def displayedHeatInJoules : AnswerChoice → ℝ
  | .A => 7950
  | .B => 8950
  | .C => 5500
  | .D => 16000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
Along the adiabatic reference, the gas does `3600 J` of work and absorbs no
heat.  Consequently the state-function change from `A` to `B` is `-3600 J`.
Neither derived value is a premise of this lemma.
-/
lemma adiabaticReferenceWorkAndInternalEnergyChange
    (setup : GasPVProcessSetup)
    (_data : MatchesProblemStatementAndPrimaryFigure setup)
    (_physical : HasPhysicalPVParameters setup)
    (_workLaw : SatisfiesQuasistaticBoundaryWorkLaws setup)
    (_adiabatic : SatisfiesAdiabaticNoHeatCondition setup)
    (_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules
        (setup.workDoneByGasAlong .adiabaticReference) = 3600 ∧
      energyInJoules (setup.internalEnergyAt .b) -
          energyInJoules (setup.internalEnergyAt .a) = -3600 := by
  have hVolumeA :
      volumeInCubicMeters (setup.volumeAt .a) = (1 : ℝ) / 1000 := by
    have h := _data.volumeAtA_axisUnits
    rw [volumeInThousandsOfCubicCentimeters] at h
    norm_num at h ⊢
    linarith
  have hVolumeB :
      volumeInCubicMeters (setup.volumeAt .b) = (8 : ℝ) / 1000 := by
    have h := _data.volumeAtB_axisUnits
    rw [volumeInThousandsOfCubicCentimeters] at h
    norm_num at h ⊢
    linarith
  have hPressureA :
      pressureInPascals (setup.meanPressureAt .a) = 3200000 := by
    have h := _data.pressureAtA_axisUnits
    rw [pressureInMillionsOfDynesPerSquareCentimeter] at h
    linarith
  have hPressureB :
      pressureInPascals (setup.meanPressureAt .b) = 100000 := by
    have h := _data.pressureAtB_axisUnits
    rw [pressureInMillionsOfDynesPerSquareCentimeter] at h
    linarith
  have hWork :=
    _workLaw.polytropicPathBoundaryWork .adiabaticReference
      _data.adiabaticPathIsSmoothCurve _physical.exponentNotOne
  rw [_data.everyPathStartsAtA .adiabaticReference,
      _data.everyPathFinishesAtB .adiabaticReference,
      _data.exponentIsFiveThirds, hPressureA, hPressureB, hVolumeA, hVolumeB]
    at hWork
  norm_num [statedAdiabaticExponent] at hWork
  constructor
  · exact hWork
  · have hHeat :=
      _adiabatic.adiabaticPathHasZeroHeat .adiabaticReference
        _data.referencePathIsAdiabatic
    have hFirstLaw := _firstLaw.firstLawOnPath .adiabaticReference
    rw [_data.everyPathStartsAtA .adiabaticReference,
        _data.everyPathFinishesAtB .adiabaticReference] at hFirstLaw
    linarith

/-!
The area under the straight pressure trace is the trapezoid with endpoint
pressures `32 × 10⁶` and `1 × 10⁶ dyn/cm²` and volume change
`7 × 10³ cm³`, namely `11550 J`.
-/
lemma requestedStraightPathWorkInJoules
    (setup : GasPVProcessSetup)
    (_data : MatchesProblemStatementAndPrimaryFigure setup)
    (_physical : HasPhysicalPVParameters setup)
    (_pathLaw : SatisfiesStatedPressureVolumePathLaws setup)
    (_workLaw : SatisfiesQuasistaticBoundaryWorkLaws setup) :
    energyInJoules (setup.workDoneByGasAlong .b) = 11550 := by
  have hVolumeA :
      volumeInCubicMeters (setup.volumeAt .a) = (1 : ℝ) / 1000 := by
    have h := _data.volumeAtA_axisUnits
    rw [volumeInThousandsOfCubicCentimeters] at h
    norm_num at h ⊢
    linarith
  have hVolumeB :
      volumeInCubicMeters (setup.volumeAt .b) = (8 : ℝ) / 1000 := by
    have h := _data.volumeAtB_axisUnits
    rw [volumeInThousandsOfCubicCentimeters] at h
    norm_num at h ⊢
    linarith
  have hPressureA :
      pressureInPascals (setup.meanPressureAt .a) = 3200000 := by
    have h := _data.pressureAtA_axisUnits
    rw [pressureInMillionsOfDynesPerSquareCentimeter] at h
    linarith
  have hPressureB :
      pressureInPascals (setup.meanPressureAt .b) = 100000 := by
    have h := _data.pressureAtB_axisUnits
    rw [pressureInMillionsOfDynesPerSquareCentimeter] at h
    linarith
  have hWork :=
    _workLaw.straightPathBoundaryWork .b _data.pathBIsStraightDiagonal
  rw [_data.everyPathStartsAtA .b, _data.everyPathFinishesAtB .b,
      hPressureA, hPressureB, hVolumeA, hVolumeB] at hWork
  norm_num at hWork
  exact hWork

/-!
The adiabatic reference fixes `ΔU = -3600 J`.  The requested straight path has
`W = 11550 J`, so the first law gives `Q_b = ΔU + W = 7950 J`, answer A.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0356:target`.
-/
theorem netHeatAbsorbedAlongLinearPressurePathInJoules
    (setup : GasPVProcessSetup)
    (_data : MatchesProblemStatementAndPrimaryFigure setup)
    (_physical : HasPhysicalPVParameters setup)
    (_pathLaw : SatisfiesStatedPressureVolumePathLaws setup)
    (_workLaw : SatisfiesQuasistaticBoundaryWorkLaws setup)
    (_adiabatic : SatisfiesAdiabaticNoHeatCondition setup)
    (_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules (setup.netHeatAbsorbedAlong .b) = 7950 := by
  have hInternalEnergy :=
    (adiabaticReferenceWorkAndInternalEnergyChange setup _data _physical
      _workLaw _adiabatic _firstLaw).2
  have hRequestedWork :=
    requestedStraightPathWorkInJoules setup _data _physical _pathLaw _workLaw
  have hFirstLaw := _firstLaw.firstLawOnPath .b
  rw [_data.everyPathStartsAtA .b, _data.everyPathFinishesAtB .b] at hFirstLaw
  linarith

end PhyXMiniProblems.ProblemPhyXMini0356
