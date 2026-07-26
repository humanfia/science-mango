import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0421

open Dimension

/-!
# Heat exhausted by a triangular pressure-volume heat-engine cycle

The primary image shows a gas traversing the triangular `p`-`V` cycle

* `(300 cm³, 100 kPa) → (300 cm³, 300 kPa)`,
* `(300 cm³, 300 kPa) → (600 cm³, 300 kPa)`, and
* `(600 cm³, 300 kPa) → (300 cm³, 100 kPa)`.

Thus the traversal is clockwise.  Purple arrows pointing into the first two
legs are labelled `90 J` and `225 J`, respectively.  The auxiliary prose
caption gives an inconsistent description of some endpoints; the coordinates
above are transcribed directly from the primary raster, as required.

Pressure, volume, internal energy, heat, work, and exhausted heat remain
dimensionful physical quantities.  Real numbers below are explicitly named
SI or figure-axis readouts, dimensionless diagram metadata, or displayed
multiple-choice values.
-/

/-! ## Dimensionful physical quantities and named readouts -/

/-- A signed physical volume, carrying the dimension of length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy, used for heat, work, and internal energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Cubic-centimetre readout used on the horizontal figure axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Kilopascal readout used on the vertical figure axis. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Joule readout of a signed physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Heat engine, cycle, and primary-figure vocabulary -/

/-- Thermodynamic role assigned to the cyclic device in the question. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- Reservoir roles used to distinguish the heat source from the cold sink. -/
inductive ReservoirRole where
  | hot
  | cold
  deriving DecidableEq, Repr

/-!
Semantic names for the three unlabelled black state markers in the raster.
These are not claimed to be literal text labels in the image.
-/
inductive CycleState where
  | lowPressureLeft
  | highPressureLeft
  | highPressureRight
  deriving DecidableEq, Fintype, Repr

/-- Directed process legs in the traversal order displayed by black arrows. -/
inductive CycleLeg where
  | leftIsochoricRise
  | topIsobaricExpansion
  | diagonalCompression
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic classification of each directed process leg. -/
inductive ProcessKind where
  | isochoric
  | isobaric
  | straightLineCompression
  deriving DecidableEq, Repr

/-- Geometric appearance of a path segment in the `p`-`V` plane. -/
inductive PathGeometry where
  | verticalStraightSegment
  | horizontalStraightSegment
  | diagonalStraightSegment
  deriving DecidableEq, Repr

/-- Spatial direction of a black traversal arrow in the primary image. -/
inductive TraversalArrowDirection where
  | up
  | right
  | downAndLeft
  deriving DecidableEq, Repr

/-- The two Cartesian axes of the pressure-volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to an axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside an axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | kilopascals
  deriving DecidableEq, Repr

/-- Literal physical symbol printed beside an axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Tick labels printed on the volume axis. -/
inductive VolumeAxisTick where
  | zero
  | threeHundred
  | sixHundred
  deriving DecidableEq, Fintype, Repr

/-- Cubic-centimetre value represented by a printed volume tick. -/
def displayedVolumeTickInCubicCentimeters : VolumeAxisTick → ℝ
  | .zero => 0
  | .threeHundred => 300
  | .sixHundred => 600

/-- Tick labels printed on the pressure axis. -/
inductive PressureAxisTick where
  | zero
  | oneHundred
  | twoHundred
  | threeHundred
  deriving DecidableEq, Fintype, Repr

/-- Kilopascal value represented by a printed pressure tick. -/
def displayedPressureTickInKilopascals : PressureAxisTick → ℝ
  | .zero => 0
  | .oneHundred => 100
  | .twoHundred => 200
  | .threeHundred => 300

/-- The two purple heat-transfer annotations in the supplied raster. -/
inductive HeatAnnotation where
  | ninetyJoules
  | twoHundredTwentyFiveJoules
  deriving DecidableEq, Fintype, Repr

/-- Joule magnitude printed beside a purple heat-transfer arrow. -/
def displayedHeatAnnotationInJoules : HeatAnnotation → ℝ
  | .ninetyJoules => 90
  | .twoHundredTwentyFiveJoules => 225

/-- Spatial direction of a purple heat-transfer arrow. -/
inductive HeatArrowDirection where
  | right
  | down
  deriving DecidableEq, Repr

/-- Physical flow role indicated by a purple arrow pointing into the cycle. -/
inductive HeatFlowRole where
  | intoWorkingGas
  deriving DecidableEq, Repr

/-!
Typed transcription surface for the primary `p`-`V` diagram.  Its plotted
coordinates remain dimensionful, while visibility and direction fields record
literal raster evidence.  Numerical coordinates and annotation values are
supplied only by `MatchesProblemAndPrimaryFigure` below.
-/
structure PressureVolumeDiagram where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  volumeTickVisible : VolumeAxisTick → Bool
  pressureTickVisible : PressureAxisTick → Bool
  stateMarkerVisible : CycleState → Bool
  plottedVolume : CycleState → VolumeQuantity
  plottedPressure : CycleState → PressureQuantity
  pathStart : CycleLeg → CycleState
  pathFinish : CycleLeg → CycleState
  pathGeometry : CycleLeg → PathGeometry
  traversalArrowDirection : CycleLeg → TraversalArrowDirection
  traversalArrowVisible : CycleLeg → Bool
  heatAnnotationVisible : HeatAnnotation → Bool
  heatAnnotationLeg : HeatAnnotation → CycleLeg
  heatArrowDirection : HeatAnnotation → HeatArrowDirection
  heatFlowRole : HeatAnnotation → HeatFlowRole

/-!
Independent physical observables for the engine cycle.  Heat is signed
positive into the working gas and boundary work is signed positive when done
by the gas.  The heat exhausted to the cold reservoir is an independent
nonnegative magnitude; it is not defined from an answer choice or from the
requested value.
-/
structure TriangularHeatEngineCycle where
  deviceRole : ThermodynamicDeviceRole
  exhaustDestination : ReservoirRole
  volumeAt : CycleState → VolumeQuantity
  pressureAt : CycleState → PressureQuantity
  internalEnergyAt : CycleState → EnergyQuantity
  workByGas : CycleLeg → EnergyQuantity
  heatIntoGas : CycleLeg → EnergyQuantity
  heatExhaustedToColdReservoir : EnergyQuantity
  exhaustLeg : CycleLeg
  processKind : CycleLeg → ProcessKind
  figure : PressureVolumeDiagram

/-! ## General cycle bookkeeping -/

/-- Net boundary work done by the gas during one three-leg traversal. -/
def cycleNetWorkByGasInJoules (setup : TriangularHeatEngineCycle) : ℝ :=
  energyInJoules (setup.workByGas .leftIsochoricRise) +
    energyInJoules (setup.workByGas .topIsobaricExpansion) +
    energyInJoules (setup.workByGas .diagonalCompression)

/-- Net signed heat entering the gas during one three-leg traversal. -/
def cycleNetHeatIntoGasInJoules (setup : TriangularHeatEngineCycle) : ℝ :=
  energyInJoules (setup.heatIntoGas .leftIsochoricRise) +
    energyInJoules (setup.heatIntoGas .topIsobaricExpansion) +
    energyInJoules (setup.heatIntoGas .diagonalCompression)

/-!
The sum of the two heat-input transfers explicitly drawn in the figure.  This
is ordinary bookkeeping over the annotated legs and contains neither the net
work nor the requested cold-reservoir exhaust value.
-/
def shownHeatInputInJoules (setup : TriangularHeatEngineCycle) : ℝ :=
  energyInJoules (setup.heatIntoGas .leftIsochoricRise) +
    energyInJoules (setup.heatIntoGas .topIsobaricExpansion)

/-- Joule readout of the independent exhausted-heat magnitude. -/
def exhaustedHeatInJoules (setup : TriangularHeatEngineCycle) : ℝ :=
  energyInJoules setup.heatExhaustedToColdReservoir

/-! ## Problem data and primary-figure readouts -/

/-!
Exact transcription of the question and primary raster.  In particular, the
figure places its vertices at `(300,100)`, `(300,300)`, and `(600,300)` in
`(cm³,kPa)` coordinates, traverses them clockwise, and labels the two incoming
heat arrows `90 J` and `225 J`.  This structure contains no net-work or
exhausted-heat result.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TriangularHeatEngineCycle) : Prop where
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  exhaustIsToColdReservoir : setup.exhaustDestination = .cold
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalAxisUnitIsKilopascals :
    setup.figure.axisDisplayUnit .vertical = .kilopascals
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  everyVolumeTickIsVisible :
    ∀ tick, setup.figure.volumeTickVisible tick = true
  everyPressureTickIsVisible :
    ∀ tick, setup.figure.pressureTickVisible tick = true
  everyStateMarkerIsVisible :
    ∀ state, setup.figure.stateMarkerVisible state = true
  plottedStatesAreCycleStates : ∀ state,
    setup.figure.plottedVolume state = setup.volumeAt state ∧
      setup.figure.plottedPressure state = setup.pressureAt state
  lowLeftVolumeCubicCentimeters :
    volumeInCubicCentimeters
        (setup.figure.plottedVolume .lowPressureLeft) = 300
  lowLeftPressureKilopascals :
    pressureInKilopascals
        (setup.figure.plottedPressure .lowPressureLeft) = 100
  highLeftVolumeCubicCentimeters :
    volumeInCubicCentimeters
        (setup.figure.plottedVolume .highPressureLeft) = 300
  highLeftPressureKilopascals :
    pressureInKilopascals
        (setup.figure.plottedPressure .highPressureLeft) = 300
  highRightVolumeCubicCentimeters :
    volumeInCubicCentimeters
        (setup.figure.plottedVolume .highPressureRight) = 600
  highRightPressureKilopascals :
    pressureInKilopascals
        (setup.figure.plottedPressure .highPressureRight) = 300
  riseStartsAtLowLeft :
    setup.figure.pathStart .leftIsochoricRise = .lowPressureLeft
  riseFinishesAtHighLeft :
    setup.figure.pathFinish .leftIsochoricRise = .highPressureLeft
  expansionStartsAtHighLeft :
    setup.figure.pathStart .topIsobaricExpansion = .highPressureLeft
  expansionFinishesAtHighRight :
    setup.figure.pathFinish .topIsobaricExpansion = .highPressureRight
  compressionStartsAtHighRight :
    setup.figure.pathStart .diagonalCompression = .highPressureRight
  compressionFinishesAtLowLeft :
    setup.figure.pathFinish .diagonalCompression = .lowPressureLeft
  riseIsVertical :
    setup.figure.pathGeometry .leftIsochoricRise = .verticalStraightSegment
  expansionIsHorizontal :
    setup.figure.pathGeometry .topIsobaricExpansion =
      .horizontalStraightSegment
  compressionIsDiagonal :
    setup.figure.pathGeometry .diagonalCompression = .diagonalStraightSegment
  riseIsIsochoric : setup.processKind .leftIsochoricRise = .isochoric
  expansionIsIsobaric :
    setup.processKind .topIsobaricExpansion = .isobaric
  returnIsStraightLineCompression :
    setup.processKind .diagonalCompression = .straightLineCompression
  riseArrowPointsUp :
    setup.figure.traversalArrowDirection .leftIsochoricRise = .up
  expansionArrowPointsRight :
    setup.figure.traversalArrowDirection .topIsobaricExpansion = .right
  returnArrowPointsDownAndLeft :
    setup.figure.traversalArrowDirection .diagonalCompression = .downAndLeft
  everyTraversalArrowIsVisible :
    ∀ leg, setup.figure.traversalArrowVisible leg = true
  everyHeatAnnotationIsVisible :
    ∀ annotation, setup.figure.heatAnnotationVisible annotation = true
  ninetyJouleArrowLabelsRise :
    setup.figure.heatAnnotationLeg .ninetyJoules = .leftIsochoricRise
  twoHundredTwentyFiveJouleArrowLabelsExpansion :
    setup.figure.heatAnnotationLeg .twoHundredTwentyFiveJoules =
      .topIsobaricExpansion
  ninetyJouleArrowPointsRight :
    setup.figure.heatArrowDirection .ninetyJoules = .right
  twoHundredTwentyFiveJouleArrowPointsDown :
    setup.figure.heatArrowDirection .twoHundredTwentyFiveJoules = .down
  everyPurpleArrowIsHeatIntoGas :
    ∀ annotation, setup.figure.heatFlowRole annotation = .intoWorkingGas
  annotatedHeatMatchesPhysicalTransfer : ∀ annotation,
    energyInJoules
        (setup.heatIntoGas (setup.figure.heatAnnotationLeg annotation)) =
      displayedHeatAnnotationInJoules annotation
  unannotatedReturnIsExhaustLeg :
    setup.exhaustLeg = .diagonalCompression

/-- Positivity conditions selecting the physically meaningful heat-engine branch. -/
structure HasPhysicalCycleParameters
    (setup : TriangularHeatEngineCycle) : Prop where
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.volumeAt state)
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.pressureAt state)
  exhaustedHeatNonnegative : 0 ≤ exhaustedHeatInJoules setup

/-! ## Governing thermodynamic laws -/

/-!
Boundary work for a straight path in the `p`-`V` plane.  When pressure varies
linearly along a leg, work done by the gas is average endpoint pressure times
the volume change.  It covers the vertical, horizontal, and diagonal legs and
contains no coordinates or answer-specific energy values.
-/
structure SatisfiesStraightPathBoundaryWorkLaw
    (setup : TriangularHeatEngineCycle) : Prop where
  workForStraightLeg : ∀ leg,
    energyInJoules (setup.workByGas leg) =
      ((pressureInPascals
            (setup.pressureAt (setup.figure.pathStart leg)) +
          pressureInPascals
            (setup.pressureAt (setup.figure.pathFinish leg))) / 2) *
        (volumeInCubicMeters
            (setup.volumeAt (setup.figure.pathFinish leg)) -
          volumeInCubicMeters
            (setup.volumeAt (setup.figure.pathStart leg)))

/-!
First law on each directed leg, with heat positive into the gas and work
positive when done by the gas: `Q = (U_finish - U_start) + W_by`.  Since the
path closes, summing these equations makes the internal-energy terms telescope
without postulating the requested heat exhaust.
-/
structure SatisfiesFirstLawOnEachLeg
    (setup : TriangularHeatEngineCycle) : Prop where
  firstLaw : ∀ leg,
    energyInJoules (setup.heatIntoGas leg) =
      energyInJoules
          (setup.internalEnergyAt (setup.figure.pathFinish leg)) -
        energyInJoules
          (setup.internalEnergyAt (setup.figure.pathStart leg)) +
        energyInJoules (setup.workByGas leg)

/-!
Sign convention relating the independent positive exhaust magnitude to the
signed heat transfer on whichever leg is designated as the exhaust leg.  This
general relation contains no figure annotation or numerical heat value.
-/
structure UsesColdReservoirExhaustSignConvention
    (setup : TriangularHeatEngineCycle) : Prop where
  heatOnExhaustLegIsNegativeExhaust :
    energyInJoules (setup.heatIntoGas setup.exhaustLeg) =
      -exhaustedHeatInJoules setup

/-! ## Derived accounting and multiple-choice target -/

/-!
The calibrated triangular `pV` area, equivalently the sum of the three
straight-leg boundary works, is `30 J`.  This is a derived intermediate
conclusion and is absent from all premise structures.
-/
lemma cycleNetWorkByGas_eq_thirty_joules
    (setup : TriangularHeatEngineCycle)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_workLaw : SatisfiesStraightPathBoundaryWorkLaw setup) :
    cycleNetWorkByGasInJoules setup = 30 := by
  have lowLeftVolumeCubicMeters :
      volumeInCubicMeters (setup.volumeAt .lowPressureLeft) = 3 / 10000 := by
    have h := _figure.lowLeftVolumeCubicCentimeters
    rw [(_figure.plottedStatesAreCycleStates .lowPressureLeft).1] at h
    norm_num [volumeInCubicCentimeters] at h ⊢
    linarith
  have highLeftVolumeCubicMeters :
      volumeInCubicMeters (setup.volumeAt .highPressureLeft) = 3 / 10000 := by
    have h := _figure.highLeftVolumeCubicCentimeters
    rw [(_figure.plottedStatesAreCycleStates .highPressureLeft).1] at h
    norm_num [volumeInCubicCentimeters] at h ⊢
    linarith
  have highRightVolumeCubicMeters :
      volumeInCubicMeters (setup.volumeAt .highPressureRight) = 3 / 5000 := by
    have h := _figure.highRightVolumeCubicCentimeters
    rw [(_figure.plottedStatesAreCycleStates .highPressureRight).1] at h
    norm_num [volumeInCubicCentimeters] at h ⊢
    linarith
  have lowLeftPressurePascals :
      pressureInPascals (setup.pressureAt .lowPressureLeft) = 100000 := by
    have h := _figure.lowLeftPressureKilopascals
    rw [(_figure.plottedStatesAreCycleStates .lowPressureLeft).2] at h
    norm_num [pressureInKilopascals] at h ⊢
    linarith
  have highLeftPressurePascals :
      pressureInPascals (setup.pressureAt .highPressureLeft) = 300000 := by
    have h := _figure.highLeftPressureKilopascals
    rw [(_figure.plottedStatesAreCycleStates .highPressureLeft).2] at h
    norm_num [pressureInKilopascals] at h ⊢
    linarith
  have highRightPressurePascals :
      pressureInPascals (setup.pressureAt .highPressureRight) = 300000 := by
    have h := _figure.highRightPressureKilopascals
    rw [(_figure.plottedStatesAreCycleStates .highPressureRight).2] at h
    norm_num [pressureInKilopascals] at h ⊢
    linarith
  have riseWork := _workLaw.workForStraightLeg .leftIsochoricRise
  have expansionWork := _workLaw.workForStraightLeg .topIsobaricExpansion
  have compressionWork := _workLaw.workForStraightLeg .diagonalCompression
  rw [_figure.riseStartsAtLowLeft, _figure.riseFinishesAtHighLeft] at riseWork
  rw [_figure.expansionStartsAtHighLeft, _figure.expansionFinishesAtHighRight]
    at expansionWork
  rw [_figure.compressionStartsAtHighRight, _figure.compressionFinishesAtLowLeft]
    at compressionWork
  unfold cycleNetWorkByGasInJoules
  rw [riseWork, expansionWork, compressionWork, lowLeftVolumeCubicMeters,
    highLeftVolumeCubicMeters, highRightVolumeCubicMeters,
    lowLeftPressurePascals, highLeftPressurePascals, highRightPressurePascals]
  norm_num

/-!
The two heat-input annotations sum to `90 J + 225 J = 315 J`.  This is also a
target-side consequence of the primary-figure readouts.
-/
lemma shownHeatInput_eq_three_hundred_fifteen_joules
    (setup : TriangularHeatEngineCycle)
    (_figure : MatchesProblemAndPrimaryFigure setup) :
    shownHeatInputInJoules setup = 315 := by
  have riseHeat :=
    _figure.annotatedHeatMatchesPhysicalTransfer .ninetyJoules
  have expansionHeat :=
    _figure.annotatedHeatMatchesPhysicalTransfer .twoHundredTwentyFiveJoules
  rw [_figure.ninetyJouleArrowLabelsRise] at riseHeat
  rw [_figure.twoHundredTwentyFiveJouleArrowLabelsExpansion] at expansionHeat
  norm_num [displayedHeatAnnotationInJoules] at riseHeat expansionHeat
  unfold shownHeatInputInJoules
  rw [riseHeat, expansionHeat]
  norm_num

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Exhausted-heat magnitude in joules printed beside each answer label. -/
def displayedExhaustedHeatInJoules : AnswerChoice → ℝ
  | .A => 30
  | .B => 315
  | .C => 255
  | .D => 285

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A displayed choice agrees exactly with the physical exhaust readout. -/
def IsCorrectDisplayedAnswer
    (setup : TriangularHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  exhaustedHeatInJoules setup = displayedExhaustedHeatInJoules choice

/-!
Over a closed cycle, the first-law internal-energy changes telescope, so net
heat into the gas equals the `30 J` net work.  The figure supplies `315 J` of
incoming heat; consequently `315 J - 30 J = 285 J` is exhausted to the cold
reservoir, selecting answer D.

Blueprint label: `thm:physics:phyx_mini_0421:target`.
-/
theorem heatExhaustedToColdReservoir_eq_two_hundred_eighty_five_joules
    (setup : TriangularHeatEngineCycle)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_workLaw : SatisfiesStraightPathBoundaryWorkLaw setup)
    (_firstLaw : SatisfiesFirstLawOnEachLeg setup)
    (_exhaustSign : UsesColdReservoirExhaustSignConvention setup) :
    exhaustedHeatInJoules setup = 285 ∧
      IsCorrectDisplayedAnswer setup recordedAnswerChoice := by
  have netWork := cycleNetWorkByGas_eq_thirty_joules setup _figure _workLaw
  have shownHeat :=
    shownHeatInput_eq_three_hundred_fifteen_joules setup _figure
  have riseFirstLaw := _firstLaw.firstLaw .leftIsochoricRise
  have expansionFirstLaw := _firstLaw.firstLaw .topIsobaricExpansion
  have compressionFirstLaw := _firstLaw.firstLaw .diagonalCompression
  rw [_figure.riseStartsAtLowLeft, _figure.riseFinishesAtHighLeft]
    at riseFirstLaw
  rw [_figure.expansionStartsAtHighLeft, _figure.expansionFinishesAtHighRight]
    at expansionFirstLaw
  rw [_figure.compressionStartsAtHighRight, _figure.compressionFinishesAtLowLeft]
    at compressionFirstLaw
  have netHeatEqualsNetWork :
      cycleNetHeatIntoGasInJoules setup = cycleNetWorkByGasInJoules setup := by
    unfold cycleNetHeatIntoGasInJoules cycleNetWorkByGasInJoules
    linarith
  have exhaustHeat := _exhaustSign.heatOnExhaustLegIsNegativeExhaust
  rw [_figure.unannotatedReturnIsExhaustLeg] at exhaustHeat
  have exhaustedHeat : exhaustedHeatInJoules setup = 285 := by
    unfold cycleNetHeatIntoGasInJoules at netHeatEqualsNetWork
    unfold shownHeatInputInJoules at shownHeat
    linarith
  refine ⟨exhaustedHeat, ?_⟩
  simpa [IsCorrectDisplayedAnswer, recordedAnswerChoice,
    displayedExhaustedHeatInJoules] using exhaustedHeat

end PhyXMiniProblems.ProblemPhyXMini0421
