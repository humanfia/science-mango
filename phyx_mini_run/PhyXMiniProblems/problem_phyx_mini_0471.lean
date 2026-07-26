import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0471

open Dimension

/-!
# Heat added along an alternative route in a rectangular p--V diagram

The primary image shows four thermodynamic states at the corners of a
rectangle.  Its arrows give two routes from `a` to `d`: `a → b → d` and
`a → c → d`.  The left and right legs are isochoric, and the lower and upper
legs are isobaric.  This corrects the auxiliary caption, which reverses the
geometric roles of the horizontal and vertical segments.

Heat is positive when added to the system and boundary work is positive when
done by the system.  Consequently the closed-system first law is represented
as `Q = U_final - U_initial + W_by`.  Pressure, volume, heat, work, and
internal energy retain physical dimensions; real numbers below are explicitly
named coherent-SI readouts or displayed answer values.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A signed physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed heat, work, or internal energy, using Physlib's energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical volume in coherent-SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical pressure in coherent-SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read physical heat, work, or internal energy in coherent-SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## State, process, and primary-figure vocabulary -/

/-- The four state labels printed beside the plotted points. -/
inductive StateLabel where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

/-- The four directed straight legs shown by blue arrows in the image. -/
inductive ProcessLeg where
  | ab
  | bd
  | ac
  | cd
  deriving DecidableEq, Repr

/-- Initial state of each displayed directed leg. -/
def ProcessLeg.initialState : ProcessLeg → StateLabel
  | .ab => .a
  | .bd => .b
  | .ac => .a
  | .cd => .c

/-- Final state of each displayed directed leg. -/
def ProcessLeg.finalState : ProcessLeg → StateLabel
  | .ab => .b
  | .bd => .d
  | .ac => .c
  | .cd => .d

/-- The two complete two-leg routes from state `a` to state `d`. -/
inductive ProcessPath where
  | abd
  | acd
  deriving DecidableEq, Repr

/-- First directed leg of a complete route. -/
def ProcessPath.firstLeg : ProcessPath → ProcessLeg
  | .abd => .ab
  | .acd => .ac

/-- Second directed leg of a complete route. -/
def ProcessPath.secondLeg : ProcessPath → ProcessLeg
  | .abd => .bd
  | .acd => .cd

/-- Both complete routes begin at state `a`. -/
def ProcessPath.initialState (_path : ProcessPath) : StateLabel := .a

/-- Both complete routes end at state `d`. -/
def ProcessPath.finalState (_path : ProcessPath) : StateLabel := .d

/-- Thermodynamic constraint represented by a straight p--V segment. -/
inductive ProcessKind where
  | isochoric
  | isobaric
  deriving DecidableEq, Repr

/-- Orientation of a displayed segment in the pressure--volume plane. -/
inductive SegmentOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- The two axes of the supplied plot. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity assigned to an axis of the supplied plot. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text carried by an axis of the supplied plot. -/
inductive AxisDisplayUnit where
  | cubicMetres
  | pascals
  deriving DecidableEq, Repr

/-- Mathematical symbol printed at an axis tip. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-!
Qualitative transcription of image `471.png`.  Physical state coordinates
are stored separately in `RectangularPVProcessSetup`; this structure records
the axes, units, labels, segment orientations, and directed arrows.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  originLabel : String
  stateLabelShown : StateLabel → Bool
  legShown : ProcessLeg → Bool
  arrowShown : ProcessLeg → Bool
  arrowStart : ProcessLeg → StateLabel
  arrowFinish : ProcessLeg → StateLabel
  segmentOrientation : ProcessLeg → SegmentOrientation

/-- Closed-system interpretation used for the fixed thermodynamic system. -/
inductive ThermodynamicSystemBoundary where
  | closedFixedSystem
  deriving DecidableEq, Repr

/-!
Independent physical observables of the system and its displayed processes.
Internal energy is state-dependent, while heat and work are process-dependent.
In particular, heat along `acd` is not defined from the recorded answer.
-/
structure RectangularPVProcessSetup where
  boundary : ThermodynamicSystemBoundary
  negligibleKineticEnergyChange : Bool
  negligiblePotentialEnergyChange : Bool
  figure : PressureVolumeFigure
  pressureAt : StateLabel → PressureQuantity
  volumeAt : StateLabel → VolumeQuantity
  internalEnergyAt : StateLabel → EnergyQuantity
  processKind : ProcessLeg → ProcessKind
  workDoneBySystemOnLeg : ProcessLeg → EnergyQuantity
  workDoneBySystemAlong : ProcessPath → EnergyQuantity
  heatAddedOnLeg : ProcessLeg → EnergyQuantity
  heatAddedAlong : ProcessPath → EnergyQuantity

/-! ## Scenario and primary-image/data readouts -/

/-- Qualitative closed-system conditions implicit in the p--V exercise. -/
structure MatchesClosedSystemScenario
    (setup : RectangularPVProcessSetup) : Prop where
  boundaryIsClosedFixedSystem : setup.boundary = .closedFixedSystem
  kineticEnergyChangeIsNegligible :
    setup.negligibleKineticEnergyChange = true
  potentialEnergyChangeIsNegligible :
    setup.negligiblePotentialEnergyChange = true

/-!
Exact transcription of the primary p--V image.  It records

* `p_a = p_c = 3.0 × 10⁴ Pa` and `p_b = p_d = 8.0 × 10⁴ Pa`;
* `V_a = V_b = 2.0 × 10⁻³ m³` and `V_c = V_d = 5.0 × 10⁻³ m³`;
* vertical isochoric legs `a → b` and `c → d`; and
* horizontal isobaric legs `a → c` and `b → d`.

No heat value, work value, or internal-energy value occurs in this structure.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : RectangularPVProcessSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUnitIsCubicMetres :
    setup.figure.axisDisplayUnit .horizontal = .cubicMetres
  verticalAxisUnitIsPascals :
    setup.figure.axisDisplayUnit .vertical = .pascals
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  originIsLabelledO : setup.figure.originLabel = "O"
  everyStateLabelIsShown : ∀ state, setup.figure.stateLabelShown state = true
  everyLegAndArrowIsShown : ∀ leg,
    setup.figure.legShown leg = true ∧ setup.figure.arrowShown leg = true
  arrowsHaveDisplayedEndpoints : ∀ leg,
    setup.figure.arrowStart leg = leg.initialState ∧
      setup.figure.arrowFinish leg = leg.finalState
  leftLegIsVertical : setup.figure.segmentOrientation .ab = .vertical
  upperLegIsHorizontal : setup.figure.segmentOrientation .bd = .horizontal
  lowerLegIsHorizontal : setup.figure.segmentOrientation .ac = .horizontal
  rightLegIsVertical : setup.figure.segmentOrientation .cd = .vertical
  leftLegIsIsochoric : setup.processKind .ab = .isochoric
  upperLegIsIsobaric : setup.processKind .bd = .isobaric
  lowerLegIsIsobaric : setup.processKind .ac = .isobaric
  rightLegIsIsochoric : setup.processKind .cd = .isochoric
  pressureAtAInPascals : pressureInPascals (setup.pressureAt .a) = 30000
  pressureAtBInPascals : pressureInPascals (setup.pressureAt .b) = 80000
  pressureAtCInPascals : pressureInPascals (setup.pressureAt .c) = 30000
  pressureAtDInPascals : pressureInPascals (setup.pressureAt .d) = 80000
  volumeAtAInCubicMetres : volumeInCubicMetres (setup.volumeAt .a) = 2 / 1000
  volumeAtBInCubicMetres : volumeInCubicMetres (setup.volumeAt .b) = 2 / 1000
  volumeAtCInCubicMetres : volumeInCubicMetres (setup.volumeAt .c) = 5 / 1000
  volumeAtDInCubicMetres : volumeInCubicMetres (setup.volumeAt .d) = 5 / 1000

/-!
The two heat transfers stated in the prose.  The heat along `acd` is absent:
it is the current target rather than a datum.
-/
structure MatchesGivenHeatReadouts
    (setup : RectangularPVProcessSetup) : Prop where
  heatAddedDuringABInJoules :
    energyInJoules (setup.heatAddedOnLeg .ab) = 150
  heatAddedDuringBDInJoules :
    energyInJoules (setup.heatAddedOnLeg .bd) = 600

/-- Positivity conditions selecting physical p--V coordinates. -/
structure HasPhysicalPressureVolumeCoordinates
    (setup : RectangularPVProcessSetup) : Prop where
  pressurePositive : ∀ state,
    0 < pressureInPascals (setup.pressureAt state)
  volumePositive : ∀ state,
    0 < volumeInCubicMetres (setup.volumeAt state)

/-! ## Governing thermodynamic laws -/

/-!
Quasistatic pressure--volume boundary work.  An isochoric leg does no work;
on an isobaric leg the work done by the system is `p (V_final - V_initial)`.
This law is uniform over all legs and contains no requested heat value.
-/
structure SatisfiesQuasistaticBoundaryWorkLaw
    (setup : RectangularPVProcessSetup) : Prop where
  isochoricLegHasZeroWork : ∀ leg,
    setup.processKind leg = .isochoric →
      energyInJoules (setup.workDoneBySystemOnLeg leg) = 0
  isobaricLegWork : ∀ leg,
    setup.processKind leg = .isobaric →
      energyInJoules (setup.workDoneBySystemOnLeg leg) =
        pressureInPascals (setup.pressureAt leg.initialState) *
          (volumeInCubicMetres (setup.volumeAt leg.finalState) -
            volumeInCubicMetres (setup.volumeAt leg.initialState))

/-- Work on either complete route is the sum of the work on its two legs. -/
structure SatisfiesPathWorkAdditivity
    (setup : RectangularPVProcessSetup) : Prop where
  workAlongTwoLegPath : ∀ path,
    energyInJoules (setup.workDoneBySystemAlong path) =
      energyInJoules (setup.workDoneBySystemOnLeg path.firstLeg) +
        energyInJoules (setup.workDoneBySystemOnLeg path.secondLeg)

/-!
The closed-system first law on each displayed leg and each complete path.
Internal energy is a function of state, so the two complete paths share the
same endpoint change.  Neither field prescribes a numerical heat on `acd`.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : RectangularPVProcessSetup) : Prop where
  firstLawOnLeg : ∀ leg,
    energyInJoules (setup.heatAddedOnLeg leg) =
      energyInJoules (setup.internalEnergyAt leg.finalState) -
          energyInJoules (setup.internalEnergyAt leg.initialState) +
        energyInJoules (setup.workDoneBySystemOnLeg leg)
  firstLawOnPath : ∀ path,
    energyInJoules (setup.heatAddedAlong path) =
      energyInJoules (setup.internalEnergyAt path.finalState) -
          energyInJoules (setup.internalEnergyAt path.initialState) +
        energyInJoules (setup.workDoneBySystemAlong path)

/-! ## Displayed answers and current target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Heat in joules printed beside each answer label. -/
def AnswerChoice.displayedHeatInJoules : AnswerChoice → ℝ
  | .A => 510
  | .B => 600
  | .C => 490
  | .D => 550

/-- Dataset answer metadata, kept separate from all theorem premises. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The modeled heat on `acd` agrees with the value printed for a choice. -/
def MatchesDisplayedHeat
    (setup : RectangularPVProcessSetup) (choice : AnswerChoice) : Prop :=
  energyInJoules (setup.heatAddedAlong .acd) = choice.displayedHeatInJoules

/-!
The given heats and the p--V work law imply

* `ΔU_ab = 150 J` because `a → b` is isochoric;
* `W_bd = (8.0 × 10⁴)(3.0 × 10⁻³) = 240 J`, hence
  `ΔU_bd = 360 J`;
* therefore `U_d - U_a = 510 J`; and
* `W_acd = (3.0 × 10⁴)(3.0 × 10⁻³) = 90 J`.

The first law on `a → c → d` consequently gives `Q_acd = 600 J`, answer B.

Blueprint label: `thm:physics:phyx_mini_0471:target`.
-/
theorem problem_phyx_mini_0471
    (setup : RectangularPVProcessSetup)
    (_scenario : MatchesClosedSystemScenario setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_givenHeat : MatchesGivenHeatReadouts setup)
    (_physical : HasPhysicalPressureVolumeCoordinates setup)
    (_boundaryWork : SatisfiesQuasistaticBoundaryWorkLaw setup)
    (_workAdditivity : SatisfiesPathWorkAdditivity setup)
    (_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules (setup.heatAddedAlong .acd) = 600 ∧
      MatchesDisplayedHeat setup .B := by
  have hWorkAB :
      energyInJoules (setup.workDoneBySystemOnLeg .ab) = 0 :=
    _boundaryWork.isochoricLegHasZeroWork .ab _figure.leftLegIsIsochoric
  have hWorkBD :
      energyInJoules (setup.workDoneBySystemOnLeg .bd) = 240 := by
    rw [_boundaryWork.isobaricLegWork .bd _figure.upperLegIsIsobaric]
    simp only [ProcessLeg.initialState, ProcessLeg.finalState]
    rw [_figure.pressureAtBInPascals,
      _figure.volumeAtDInCubicMetres, _figure.volumeAtBInCubicMetres]
    norm_num
  have hWorkAC :
      energyInJoules (setup.workDoneBySystemOnLeg .ac) = 90 := by
    rw [_boundaryWork.isobaricLegWork .ac _figure.lowerLegIsIsobaric]
    simp only [ProcessLeg.initialState, ProcessLeg.finalState]
    rw [_figure.pressureAtAInPascals,
      _figure.volumeAtCInCubicMetres, _figure.volumeAtAInCubicMetres]
    norm_num
  have hWorkCD :
      energyInJoules (setup.workDoneBySystemOnLeg .cd) = 0 :=
    _boundaryWork.isochoricLegHasZeroWork .cd _figure.rightLegIsIsochoric
  have hWorkACD :
      energyInJoules (setup.workDoneBySystemAlong .acd) = 90 := by
    rw [_workAdditivity.workAlongTwoLegPath .acd]
    simp only [ProcessPath.firstLeg, ProcessPath.secondLeg]
    rw [hWorkAC, hWorkCD]
    norm_num
  have hDeltaUAB :
      energyInJoules (setup.internalEnergyAt .b) -
          energyInJoules (setup.internalEnergyAt .a) = 150 := by
    have h := _firstLaw.firstLawOnLeg .ab
    simp only [ProcessLeg.finalState, ProcessLeg.initialState] at h
    rw [_givenHeat.heatAddedDuringABInJoules, hWorkAB] at h
    linarith
  have hDeltaUBD :
      energyInJoules (setup.internalEnergyAt .d) -
          energyInJoules (setup.internalEnergyAt .b) = 360 := by
    have h := _firstLaw.firstLawOnLeg .bd
    simp only [ProcessLeg.finalState, ProcessLeg.initialState] at h
    rw [_givenHeat.heatAddedDuringBDInJoules, hWorkBD] at h
    linarith
  have hDeltaUAD :
      energyInJoules (setup.internalEnergyAt .d) -
          energyInJoules (setup.internalEnergyAt .a) = 510 := by
    linarith
  have hHeatACD :
      energyInJoules (setup.heatAddedAlong .acd) = 600 := by
    have h := _firstLaw.firstLawOnPath .acd
    simp only [ProcessPath.finalState, ProcessPath.initialState] at h
    rw [hWorkACD] at h
    linarith
  exact ⟨hHeatACD, by
    simpa [MatchesDisplayedHeat, AnswerChoice.displayedHeatInJoules] using hHeatACD⟩

end PhyXMiniProblems.ProblemPhyXMini0471
