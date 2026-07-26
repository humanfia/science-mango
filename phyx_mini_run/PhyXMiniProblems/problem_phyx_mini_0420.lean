import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0420

open Dimension

/-!
# Efficiency of a triangular pressure--volume heat-engine cycle

The primary image shows the clockwise cycle

`lowerLeft → upperLeft → upperRight → lowerLeft`

with vertices `(100 cm³, 200 kPa)`, `(100 cm³, 400 kPa)`, and
`(200 cm³, 400 kPa)`.  The purple arrows show heat inputs of `30 J` on the
vertical leg and `84 J` on the horizontal leg.

Pressure, volume, work, heat, and internal-energy changes are represented by
dimensionful physical quantities.  Real numbers occur only as unit readouts,
dimensionless efficiencies, and displayed answer values.  Work is positive
when done by the working substance, and heat is positive into it.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical volume carrying the dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a dimensionful pressure in coherent SI units (pascals). -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in coherent SI units (cubic metres). -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a volume in the cubic centimetres printed on the horizontal axis. -/
def volumeInCubicCentimetres (volume : VolumeQuantity) : ℝ :=
  volumeInCubicMetres volume * 1000000

/-- Read a signed dimensionful energy in coherent SI units (joules). -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- The energy in joules represented by one `kPa · cm³` of diagram area. -/
def joulesPerKilopascalCubicCentimetre : ℝ :=
  1 / 1000

/-! ## Cycle states, directed legs, and primary-image data -/

/-- The three black vertices in the supplied pressure--volume diagram. -/
inductive CyclePoint where
  | lowerLeft
  | upperLeft
  | upperRight
  deriving DecidableEq, Fintype, Repr

/-- The three directed arrows making up the displayed closed cycle. -/
inductive CycleLeg where
  | vertical
  | horizontal
  | diagonalReturn
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint of each directed process leg. -/
def legStart : CycleLeg → CyclePoint
  | .vertical => .lowerLeft
  | .horizontal => .upperLeft
  | .diagonalReturn => .upperRight

/-- Final endpoint of each directed process leg. -/
def legFinish : CycleLeg → CyclePoint
  | .vertical => .upperLeft
  | .horizontal => .upperRight
  | .diagonalReturn => .lowerLeft

/-- Thermodynamic role of each oriented segment visible in the diagram. -/
inductive ProcessKind where
  | isochoricPressureRise
  | isobaricExpansion
  | straightLineCompression
  deriving DecidableEq, Repr

/-- Process classification fixed by the displayed endpoint geometry. -/
def expectedProcessKind : CycleLeg → ProcessKind
  | .vertical => .isochoricPressureRise
  | .horizontal => .isobaricExpansion
  | .diagonalReturn => .straightLineCompression

/-- A physical pressure--volume equilibrium state of the working substance. -/
structure PVState where
  pressure : DimPressure
  volume : VolumeQuantity

/-- The physical quantities assigned to the two axes in the raster. -/
inductive DiagramAxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- Units explicitly printed beside the diagram axes. -/
inductive DiagramAxisUnit where
  | kilopascal
  | cubicCentimetre
  deriving DecidableEq, Repr

/-- Text and numerical labels visible in the supplied raster. -/
inductive DiagramLabel where
  | pressureAxisP
  | volumeAxisV
  | originZero
  | pressure200
  | pressure400
  | volume100
  | volume200
  | heat30J
  | heat84J
  deriving DecidableEq, Fintype, Repr

/-- The two purple heat-transfer annotations in the primary image. -/
inductive HeatArrow where
  | thirtyJoule
  | eightyFourJoule
  deriving DecidableEq, Fintype, Repr

/-- Direction conveyed by a purple heat-transfer arrow. -/
inductive HeatArrowDirection where
  | intoWorkingSubstance
  | outOfWorkingSubstance
  deriving DecidableEq, Repr

/-!
Geometric, directional, and heat-annotation data supplied by the image.  This
structure contains no net-work, total-heat, efficiency, or answer conclusion.
-/
structure PressureVolumeCycleFigure where
  horizontalAxisQuantity : DiagramAxisQuantity
  verticalAxisQuantity : DiagramAxisQuantity
  horizontalAxisUnit : DiagramAxisUnit
  verticalAxisUnit : DiagramAxisUnit
  showsLabel : DiagramLabel → Bool
  showsVertex : CyclePoint → Bool
  plottedVolumeCubicCentimetres : CyclePoint → ℝ
  plottedPressureKilopascals : CyclePoint → ℝ
  showsDirectedLeg : CycleLeg → Bool
  directedEndpoints : CycleLeg → CyclePoint × CyclePoint
  drawsLegStraight : CycleLeg → Bool
  depictedProcessKind : CycleLeg → ProcessKind
  showsHeatArrow : HeatArrow → Bool
  heatArrowDirection : HeatArrow → HeatArrowDirection
  heatArrowLeg : HeatArrow → CycleLeg
  heatArrowEnergy : HeatArrow → DimEnergy

/-- Regime in which the plotted path supports quasistatic boundary work. -/
inductive ProcessRegime where
  | quasistaticEquilibriumPath
  | other
  deriving DecidableEq, Repr

/-- Independent physical observables for the closed engine cycle. -/
structure TriangularHeatEngineSetup (WorkingSubstance : Type) where
  workingSubstance : WorkingSubstance
  sameClosedSample : Bool
  processRegime : ProcessRegime
  stateAt : CyclePoint → PVState
  workDoneBySubstanceOnLeg : CycleLeg → DimEnergy
  heatTransferredIntoSubstanceOnLeg : CycleLeg → DimEnergy
  internalEnergyChangeOnLeg : CycleLeg → DimEnergy
  netWorkDoneBySubstance : DimEnergy
  figure : PressureVolumeCycleFigure

/-- Pressure readout of a cycle state in the image's kilopascals. -/
def statePressureInKilopascals
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance)
    (point : CyclePoint) : ℝ :=
  pressureInKilopascals (setup.stateAt point).pressure

/-- Volume readout of a cycle state in the image's cubic centimetres. -/
def stateVolumeInCubicCentimetres
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance)
    (point : CyclePoint) : ℝ :=
  volumeInCubicCentimetres (setup.stateAt point).volume

/-! ## Assumptions: scenario, figure readouts, and governing laws -/

/-- The closed-sample and quasistatic-path idealizations implied by the plot. -/
structure MatchesHeatEngineScenario
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance) : Prop where
  sameClosedWorkingSubstance : setup.sameClosedSample = true
  quasistaticPath : setup.processRegime = .quasistaticEquilibriumPath

/--
Primary-image evidence: axes, units, exact vertices, clockwise arrows,
straight-leg geometry, and the two inward heat labels.  The heat values are
calibrated figure readouts, not the requested efficiency.
-/
structure MatchesSuppliedPressureVolumeFigure
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimetres :
    setup.figure.horizontalAxisUnit = .cubicCentimetre
  verticalAxisUsesKilopascals :
    setup.figure.verticalAxisUnit = .kilopascal
  everyPrintedLabelShown :
    ∀ label : DiagramLabel, setup.figure.showsLabel label = true
  everyVertexShown :
    ∀ point : CyclePoint, setup.figure.showsVertex point = true
  lowerLeftCoordinate :
    setup.figure.plottedVolumeCubicCentimetres .lowerLeft = 100 ∧
      setup.figure.plottedPressureKilopascals .lowerLeft = 200
  upperLeftCoordinate :
    setup.figure.plottedVolumeCubicCentimetres .upperLeft = 100 ∧
      setup.figure.plottedPressureKilopascals .upperLeft = 400
  upperRightCoordinate :
    setup.figure.plottedVolumeCubicCentimetres .upperRight = 200 ∧
      setup.figure.plottedPressureKilopascals .upperRight = 400
  plottedCoordinatesRepresentPhysicalStates :
    ∀ point : CyclePoint,
      setup.figure.plottedVolumeCubicCentimetres point =
          stateVolumeInCubicCentimetres setup point ∧
        setup.figure.plottedPressureKilopascals point =
          statePressureInKilopascals setup point
  everyDirectedLegShown :
    ∀ leg : CycleLeg, setup.figure.showsDirectedLeg leg = true
  arrowsFollowClockwiseCycle :
    ∀ leg : CycleLeg,
      setup.figure.directedEndpoints leg = (legStart leg, legFinish leg)
  everyLegIsStraight :
    ∀ leg : CycleLeg, setup.figure.drawsLegStraight leg = true
  processKindsAgreeWithGeometry :
    ∀ leg : CycleLeg,
      setup.figure.depictedProcessKind leg = expectedProcessKind leg
  everyHeatArrowShown :
    ∀ arrow : HeatArrow, setup.figure.showsHeatArrow arrow = true
  everyHeatArrowPointsInward :
    ∀ arrow : HeatArrow,
      setup.figure.heatArrowDirection arrow = .intoWorkingSubstance
  thirtyJouleArrowOnVerticalLeg :
    setup.figure.heatArrowLeg .thirtyJoule = .vertical
  eightyFourJouleArrowOnHorizontalLeg :
    setup.figure.heatArrowLeg .eightyFourJoule = .horizontal
  thirtyJouleHeatLabel :
    energyInJoules (setup.figure.heatArrowEnergy .thirtyJoule) = 30
  eightyFourJouleHeatLabel :
    energyInJoules (setup.figure.heatArrowEnergy .eightyFourJoule) = 84
  heatAnnotationsRepresentLegHeatTransfers :
    ∀ arrow : HeatArrow,
      energyInJoules (setup.figure.heatArrowEnergy arrow) =
        energyInJoules
          (setup.heatTransferredIntoSubstanceOnLeg
            (setup.figure.heatArrowLeg arrow))

/-- Positivity and nondegeneracy of the physical states shown in the image. -/
structure HasPhysicalHeatEngineParameters
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance) : Prop where
  pressurePositive :
    ∀ point, 0 < statePressureInKilopascals setup point
  volumePositive :
    ∀ point, 0 < stateVolumeInCubicCentimetres setup point

/-!
The governing thermodynamics used by the problem:

* quasistatic boundary work on a straight `pV` segment is the signed volume
  change times the average endpoint pressure;
* `Q_into = ΔU + W_by` on each leg;
* internal energy is a state function, so its changes sum to zero around the
  closed cycle;
* net work is additive over the legs.

These laws are uniform and contain none of the requested numerical results.
-/
structure SatisfiesClosedCycleThermodynamics
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance) : Prop where
  straightSegmentBoundaryWork :
    setup.processRegime = .quasistaticEquilibriumPath →
      ∀ leg : CycleLeg,
        setup.figure.drawsLegStraight leg = true →
          energyInJoules (setup.workDoneBySubstanceOnLeg leg) =
            joulesPerKilopascalCubicCentimetre *
              (statePressureInKilopascals setup (legStart leg) +
                  statePressureInKilopascals setup (legFinish leg)) / 2 *
                (stateVolumeInCubicCentimetres setup (legFinish leg) -
                  stateVolumeInCubicCentimetres setup (legStart leg))
  firstLawOnEachLeg :
    ∀ leg : CycleLeg,
      energyInJoules (setup.heatTransferredIntoSubstanceOnLeg leg) =
        energyInJoules (setup.internalEnergyChangeOnLeg leg) +
          energyInJoules (setup.workDoneBySubstanceOnLeg leg)
  internalEnergyIsCyclic :
    energyInJoules (setup.internalEnergyChangeOnLeg .vertical) +
        energyInJoules (setup.internalEnergyChangeOnLeg .horizontal) +
        energyInJoules (setup.internalEnergyChangeOnLeg .diagonalReturn) = 0
  netWorkAdditivity :
    energyInJoules setup.netWorkDoneBySubstance =
      energyInJoules (setup.workDoneBySubstanceOnLeg .vertical) +
        energyInJoules (setup.workDoneBySubstanceOnLeg .horizontal) +
        energyInJoules (setup.workDoneBySubstanceOnLeg .diagonalReturn)

/-! ## Heat accounting, efficiency, and displayed answers -/

/-- Total absorbed heat is the sum of the positive parts of signed leg heat. -/
def totalHeatAbsorbedInJoules
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance) : ℝ :=
  max (energyInJoules
      (setup.heatTransferredIntoSubstanceOnLeg .vertical)) 0 +
    max (energyInJoules
      (setup.heatTransferredIntoSubstanceOnLeg .horizontal)) 0 +
    max (energyInJoules
      (setup.heatTransferredIntoSubstanceOnLeg .diagonalReturn)) 0

/-- Dimensionless thermal efficiency `W_net / Q_absorbed`. -/
def thermalEfficiency
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance) : ℝ :=
  energyInJoules setup.netWorkDoneBySubstance /
    totalHeatAbsorbedInJoules setup

/-- Labels of the four efficiency choices printed by the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless decimal value printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 37 / 50
  | .B => 33 / 100
  | .C => 114 / 125
  | .D => 11 / 125

/-- The exact efficiency rounds to a displayed three-decimal value. -/
def MatchesToNearestThousandth
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance)
    (choice : AnswerChoice) : Prop :=
  |thermalEfficiency setup - displayedEfficiency choice| < (1 / 2000 : ℝ)

/-- The specified choice is the unique nearest-thousandth display match. -/
def IsUniqueMatchingDisplayedEfficiency
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance)
    (choice : AnswerChoice) : Prop :=
  MatchesToNearestThousandth setup choice ∧
    ∀ other : AnswerChoice,
      MatchesToNearestThousandth setup other → other = choice

/--
The straight-segment law gives leg works `0 J`, `40 J`, and `-30 J`, hence
`10 J` of net work.  These are conclusions rather than law or figure fields.
-/
lemma legAndNetWork_exact
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance)
    (hScenario : MatchesHeatEngineScenario setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hLaws : SatisfiesClosedCycleThermodynamics setup) :
    energyInJoules (setup.workDoneBySubstanceOnLeg .vertical) = 0 ∧
      energyInJoules (setup.workDoneBySubstanceOnLeg .horizontal) = 40 ∧
      energyInJoules (setup.workDoneBySubstanceOnLeg .diagonalReturn) = -30 ∧
      energyInJoules setup.netWorkDoneBySubstance = 10 := by
  have hLLV : stateVolumeInCubicCentimetres setup .lowerLeft = 100 := by
    calc
      _ = setup.figure.plottedVolumeCubicCentimetres .lowerLeft :=
        (hFigure.plottedCoordinatesRepresentPhysicalStates .lowerLeft).1.symm
      _ = 100 := hFigure.lowerLeftCoordinate.1
  have hLLP : statePressureInKilopascals setup .lowerLeft = 200 := by
    calc
      _ = setup.figure.plottedPressureKilopascals .lowerLeft :=
        (hFigure.plottedCoordinatesRepresentPhysicalStates .lowerLeft).2.symm
      _ = 200 := hFigure.lowerLeftCoordinate.2
  have hULV : stateVolumeInCubicCentimetres setup .upperLeft = 100 := by
    calc
      _ = setup.figure.plottedVolumeCubicCentimetres .upperLeft :=
        (hFigure.plottedCoordinatesRepresentPhysicalStates .upperLeft).1.symm
      _ = 100 := hFigure.upperLeftCoordinate.1
  have hULP : statePressureInKilopascals setup .upperLeft = 400 := by
    calc
      _ = setup.figure.plottedPressureKilopascals .upperLeft :=
        (hFigure.plottedCoordinatesRepresentPhysicalStates .upperLeft).2.symm
      _ = 400 := hFigure.upperLeftCoordinate.2
  have hURV : stateVolumeInCubicCentimetres setup .upperRight = 200 := by
    calc
      _ = setup.figure.plottedVolumeCubicCentimetres .upperRight :=
        (hFigure.plottedCoordinatesRepresentPhysicalStates .upperRight).1.symm
      _ = 200 := hFigure.upperRightCoordinate.1
  have hURP : statePressureInKilopascals setup .upperRight = 400 := by
    calc
      _ = setup.figure.plottedPressureKilopascals .upperRight :=
        (hFigure.plottedCoordinatesRepresentPhysicalStates .upperRight).2.symm
      _ = 400 := hFigure.upperRightCoordinate.2
  have hVertical :
      energyInJoules (setup.workDoneBySubstanceOnLeg .vertical) = 0 := by
    rw [hLaws.straightSegmentBoundaryWork hScenario.quasistaticPath .vertical
      (hFigure.everyLegIsStraight .vertical)]
    norm_num [joulesPerKilopascalCubicCentimetre, legStart, legFinish,
      hLLV, hLLP, hULV, hULP]
  have hHorizontal :
      energyInJoules (setup.workDoneBySubstanceOnLeg .horizontal) = 40 := by
    rw [hLaws.straightSegmentBoundaryWork hScenario.quasistaticPath .horizontal
      (hFigure.everyLegIsStraight .horizontal)]
    norm_num [joulesPerKilopascalCubicCentimetre, legStart, legFinish,
      hULV, hULP, hURV, hURP]
  have hDiagonal :
      energyInJoules (setup.workDoneBySubstanceOnLeg .diagonalReturn) = -30 := by
    rw [hLaws.straightSegmentBoundaryWork hScenario.quasistaticPath .diagonalReturn
      (hFigure.everyLegIsStraight .diagonalReturn)]
    norm_num [joulesPerKilopascalCubicCentimetre, legStart, legFinish,
      hURV, hURP, hLLV, hLLP]
  refine ⟨hVertical, hHorizontal, hDiagonal, ?_⟩
  rw [hLaws.netWorkAdditivity, hVertical, hHorizontal, hDiagonal]
  norm_num

/--
The cyclic first law fixes the unlabelled diagonal heat at `-104 J`, so only
the two labelled inward heats contribute to the absorbed total `114 J`.
-/
lemma heatAccounting_exact
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance)
    (hScenario : MatchesHeatEngineScenario setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hLaws : SatisfiesClosedCycleThermodynamics setup) :
    energyInJoules
        (setup.heatTransferredIntoSubstanceOnLeg .vertical) = 30 ∧
      energyInJoules
        (setup.heatTransferredIntoSubstanceOnLeg .horizontal) = 84 ∧
      energyInJoules
        (setup.heatTransferredIntoSubstanceOnLeg .diagonalReturn) = -104 ∧
      totalHeatAbsorbedInJoules setup = 114 := by
  have hVertical :
      energyInJoules (setup.heatTransferredIntoSubstanceOnLeg .vertical) = 30 := by
    calc
      _ = energyInJoules
          (setup.heatTransferredIntoSubstanceOnLeg
            (setup.figure.heatArrowLeg .thirtyJoule)) := by
        rw [hFigure.thirtyJouleArrowOnVerticalLeg]
      _ = energyInJoules (setup.figure.heatArrowEnergy .thirtyJoule) :=
        (hFigure.heatAnnotationsRepresentLegHeatTransfers .thirtyJoule).symm
      _ = 30 := hFigure.thirtyJouleHeatLabel
  have hHorizontal :
      energyInJoules
        (setup.heatTransferredIntoSubstanceOnLeg .horizontal) = 84 := by
    calc
      _ = energyInJoules
          (setup.heatTransferredIntoSubstanceOnLeg
            (setup.figure.heatArrowLeg .eightyFourJoule)) := by
        rw [hFigure.eightyFourJouleArrowOnHorizontalLeg]
      _ = energyInJoules (setup.figure.heatArrowEnergy .eightyFourJoule) :=
        (hFigure.heatAnnotationsRepresentLegHeatTransfers .eightyFourJoule).symm
      _ = 84 := hFigure.eightyFourJouleHeatLabel
  obtain ⟨hWorkVertical, hWorkHorizontal, hWorkDiagonal, _⟩ :=
    legAndNetWork_exact setup hScenario hFigure hLaws
  have hDiagonal :
      energyInJoules
        (setup.heatTransferredIntoSubstanceOnLeg .diagonalReturn) = -104 := by
    linarith [hLaws.firstLawOnEachLeg .vertical,
      hLaws.firstLawOnEachLeg .horizontal,
      hLaws.firstLawOnEachLeg .diagonalReturn,
      hLaws.internalEnergyIsCyclic]
  refine ⟨hVertical, hHorizontal, hDiagonal, ?_⟩
  norm_num [totalHeatAbsorbedInJoules, hVertical, hHorizontal, hDiagonal]

/--
The exact efficiency is `10 / 114 = 5 / 57 ≈ 0.087719`, which rounds to
`0.088` and uniquely selects answer D.

This formalizes `thm:physics:phyx_mini_0420:target`.
-/
theorem problem_phyx_mini_0420
    {WorkingSubstance : Type}
    (setup : TriangularHeatEngineSetup WorkingSubstance)
    (hScenario : MatchesHeatEngineScenario setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hPhysical : HasPhysicalHeatEngineParameters setup)
    (hLaws : SatisfiesClosedCycleThermodynamics setup) :
    energyInJoules setup.netWorkDoneBySubstance = 10 ∧
      energyInJoules
        (setup.heatTransferredIntoSubstanceOnLeg .diagonalReturn) = -104 ∧
      totalHeatAbsorbedInJoules setup = 114 ∧
      thermalEfficiency setup = (5 / 57 : ℝ) ∧
      MatchesToNearestThousandth setup .D ∧
      IsUniqueMatchingDisplayedEfficiency setup .D := by
  obtain ⟨_, _, _, hNet⟩ :=
    legAndNetWork_exact setup hScenario hFigure hLaws
  obtain ⟨_, _, hDiagonal, hAbsorbed⟩ :=
    heatAccounting_exact setup hScenario hFigure hLaws
  have hEfficiency : thermalEfficiency setup = (5 / 57 : ℝ) := by
    norm_num [thermalEfficiency, hNet, hAbsorbed]
  have hMatchesD : MatchesToNearestThousandth setup .D := by
    norm_num [MatchesToNearestThousandth, hEfficiency, displayedEfficiency,
      abs_of_nonneg, abs_of_nonpos]
  have hUniqueD : IsUniqueMatchingDisplayedEfficiency setup .D := by
    refine ⟨hMatchesD, ?_⟩
    intro other hOther
    cases other with
    | A =>
        exfalso
        norm_num [MatchesToNearestThousandth, hEfficiency, displayedEfficiency,
          abs_of_nonneg, abs_of_nonpos] at hOther
    | B =>
        exfalso
        norm_num [MatchesToNearestThousandth, hEfficiency, displayedEfficiency,
          abs_of_nonneg, abs_of_nonpos] at hOther
    | C =>
        exfalso
        norm_num [MatchesToNearestThousandth, hEfficiency, displayedEfficiency,
          abs_of_nonneg, abs_of_nonpos] at hOther
    | D => rfl
  exact ⟨hNet, hDiagonal, hAbsorbed, hEfficiency, hMatchesD, hUniqueD⟩

end PhyXMiniProblems.ProblemPhyXMini0420
