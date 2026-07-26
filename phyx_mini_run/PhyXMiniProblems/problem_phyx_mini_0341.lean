import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0341

open Dimension

/-!
# Heat transferred on one leg of a pressure--volume process

A fixed-mass thermodynamic system is taken from state `a` to state `c` along
either `a → b → c` or `a → d → c`.  The primary image is a rectangular
pressure--volume diagram.  In particular, `a → b` is a vertical,
constant-volume leg.

Energy, pressure, and volume are represented by unit-independent dimensionful
quantities.  Real numbers occur only as readouts in selected units.  Work is
positive when done by the system and heat is positive when transferred into
the system, so the first law is written `Q = ΔU + W`.
-/

/-- Physical energy, with dimension `mass * length^2 / time^2`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Thermodynamic pressure, with dimension `mass / (length * time^2)`. -/
abbrev PressureQuantity : Type := DimPressure

/-- Nonnegative physical volume, with dimension `length^3`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read an energy in the coherent unit induced by the selected base units. -/
def energyReadout (units : UnitChoices) (energy : EnergyQuantity) : ℝ :=
  (energy units).val

/-- Read a pressure in the coherent unit induced by the selected base units. -/
def pressureReadout (units : UnitChoices) (pressure : PressureQuantity) : ℝ :=
  (pressure units).val

/-- Read a volume in the cubic unit induced by a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- SI joule readout of an energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  energyReadout UnitChoices.SI energy

/-- SI pascal readout of a pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  pressureReadout UnitChoices.SI pressure

/-- Cubic-metre readout of a volume. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- The four thermodynamic states labelled in the diagram. -/
inductive ThermodynamicState where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

/-- The four directed process legs used by the two named paths. -/
inductive ProcessLeg where
  | ab
  | bc
  | ad
  | dc
  deriving DecidableEq, Repr

/-- Initial state of a directed process leg. -/
def ProcessLeg.initialState : ProcessLeg → ThermodynamicState
  | .ab => .a
  | .bc => .b
  | .ad => .a
  | .dc => .d

/-- Final state of a directed process leg. -/
def ProcessLeg.finalState : ProcessLeg → ThermodynamicState
  | .ab => .b
  | .bc => .c
  | .ad => .d
  | .dc => .c

/-- The two directed paths from `a` to `c` named in the problem. -/
inductive ThermodynamicPath where
  | abc
  | adc
  deriving DecidableEq, Repr

/-- Process classification conveyed by a straight segment in a `p`--`V` plot. -/
inductive ProcessKind where
  | isochoric
  | isobaric
  deriving DecidableEq, Repr

/-- The two physical quantities assigned to the plotted axes. -/
inductive FigureAxisQuantity where
  | pressureP
  | volumeV
  deriving DecidableEq, Repr

/-- Orientation of a process segment in the supplied diagram. -/
inductive SegmentOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- System-boundary idealizations relevant to the first-law sign convention. -/
inductive ThermodynamicSystemBoundary where
  | closedFixedMass
  | openToMassFlow
  deriving DecidableEq, Repr

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Printed heat readout, in joules, for each answer choice. -/
def displayedHeatInJoules : AnswerChoice → ℝ
  | .A => 15
  | .B => 90
  | .C => 55
  | .D => 32

/-- The answer label recorded by the dataset.  This is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Qualitative evidence retained from the primary bitmap.  Physical pressure and
volume live in `ThermodynamicProcessSetup`; this record stores visible axes,
labels, segments, arrows, and their orientations.
-/
structure PressureVolumeFigure where
  horizontalAxisQuantity : FigureAxisQuantity
  verticalAxisQuantity : FigureAxisQuantity
  originLabelOShown : Bool
  statePointShown : ThermodynamicState → Bool
  stateLabelShown : ThermodynamicState → Bool
  processSegmentShown : ProcessLeg → Bool
  arrowStart : ProcessLeg → ThermodynamicState
  arrowEnd : ProcessLeg → ThermodynamicState
  segmentOrientation : ProcessLeg → SegmentOrientation

/-!
Independent physical quantities for the four states and four process legs.
In particular, the heat on `ab` is an unconstrained field here.  It is related
to state energy and work only through the governing first law below.
-/
structure ThermodynamicProcessSetup where
  boundary : ThermodynamicSystemBoundary
  pressureAt : ThermodynamicState → PressureQuantity
  volumeAt : ThermodynamicState → VolumeQuantity
  internalEnergyAt : ThermodynamicState → EnergyQuantity
  processKind : ProcessLeg → ProcessKind
  workDoneBySystemOnLeg : ProcessLeg → EnergyQuantity
  heatTransferredToSystemOnLeg : ProcessLeg → EnergyQuantity
  workDoneBySystemAlongPath : ThermodynamicPath → EnergyQuantity
  figure : PressureVolumeFigure

/-- The fixed-mass closed-system interpretation used by the process model. -/
structure MatchesClosedSystemScenario
    (setup : ThermodynamicProcessSetup) : Prop where
  boundaryIsClosedFixedMass : setup.boundary = .closedFixedMass

/-!
Primary-image evidence.  The bitmap puts `a,b` at the same volume on the left,
`c,d` at the same larger volume on the right, `a,d` at the same lower pressure,
and `b,c` at the same higher pressure.  Its arrows form the paths `abc` and
`adc` from `a` to `c`.
-/
structure MatchesSuppliedPressureVolumeFigure
    (setup : ThermodynamicProcessSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volumeV
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressureP
  originLabelShown : setup.figure.originLabelOShown = true
  everyStatePointShown :
    ∀ state : ThermodynamicState, setup.figure.statePointShown state = true
  everyStateLabelShown :
    ∀ state : ThermodynamicState, setup.figure.stateLabelShown state = true
  everyProcessSegmentShown :
    ∀ leg : ProcessLeg, setup.figure.processSegmentShown leg = true
  everyArrowHasPhysicalEndpoints : ∀ leg : ProcessLeg,
    setup.figure.arrowStart leg = leg.initialState ∧
      setup.figure.arrowEnd leg = leg.finalState
  legABIsVertical : setup.figure.segmentOrientation .ab = .vertical
  legBCIsHorizontal : setup.figure.segmentOrientation .bc = .horizontal
  legADIsHorizontal : setup.figure.segmentOrientation .ad = .horizontal
  legDCIsVertical : setup.figure.segmentOrientation .dc = .vertical
  legABIsIsochoric : setup.processKind .ab = .isochoric
  legBCIsIsobaric : setup.processKind .bc = .isobaric
  legADIsIsobaric : setup.processKind .ad = .isobaric
  legDCIsIsochoric : setup.processKind .dc = .isochoric
  leftStatesHaveEqualVolume : setup.volumeAt .a = setup.volumeAt .b
  rightStatesHaveEqualVolume : setup.volumeAt .d = setup.volumeAt .c
  rightVolumeIsLarger :
    volumeInCubicMetres (setup.volumeAt .a) <
      volumeInCubicMetres (setup.volumeAt .d)
  lowerStatesHaveEqualPressure : setup.pressureAt .a = setup.pressureAt .d
  upperStatesHaveEqualPressure : setup.pressureAt .b = setup.pressureAt .c
  upperPressureIsLarger :
    pressureInPascals (setup.pressureAt .a) <
      pressureInPascals (setup.pressureAt .b)

/-!
Numerical data printed in the problem.  This includes all four state internal
energies and both total path works, but no heat value for any leg.
-/
structure MatchesProblemReadouts
    (setup : ThermodynamicProcessSetup) : Prop where
  internalEnergyAtA_J : energyInJoules (setup.internalEnergyAt .a) = 150
  internalEnergyAtB_J : energyInJoules (setup.internalEnergyAt .b) = 240
  internalEnergyAtC_J : energyInJoules (setup.internalEnergyAt .c) = 680
  internalEnergyAtD_J : energyInJoules (setup.internalEnergyAt .d) = 330
  workAlongABC_J :
    energyInJoules (setup.workDoneBySystemAlongPath .abc) = 450
  workAlongADC_J :
    energyInJoules (setup.workDoneBySystemAlongPath .adc) = 120

/-- Positivity conditions for the pressure and volume coordinates in the plot. -/
structure HasPhysicalPressureVolumeCoordinates
    (setup : ThermodynamicProcessSetup) : Prop where
  pressurePositive :
    ∀ state : ThermodynamicState, 0 < pressureInPascals (setup.pressureAt state)
  volumePositive :
    ∀ state : ThermodynamicState, 0 < volumeInCubicMetres (setup.volumeAt state)

/-!
Additivity of work on each two-leg path.  This relates the supplied path-work
totals to leg works without prescribing the requested heat.
-/
structure SatisfiesPathWorkAdditivity
    (setup : ThermodynamicProcessSetup) : Prop where
  pathABC : ∀ units : UnitChoices,
    energyReadout units (setup.workDoneBySystemAlongPath .abc) =
      energyReadout units (setup.workDoneBySystemOnLeg .ab) +
        energyReadout units (setup.workDoneBySystemOnLeg .bc)
  pathADC : ∀ units : UnitChoices,
    energyReadout units (setup.workDoneBySystemAlongPath .adc) =
      energyReadout units (setup.workDoneBySystemOnLeg .ad) +
        energyReadout units (setup.workDoneBySystemOnLeg .dc)

/-!
The pressure--volume boundary-work law needed here: every constant-volume
process has zero work.  This is general in both the process leg and unit choice
and does not assert the requested heat value.
-/
structure SatisfiesIsochoricWorkLaw
    (setup : ThermodynamicProcessSetup) : Prop where
  isochoricLegHasZeroWork : ∀ (leg : ProcessLeg) (units : UnitChoices),
    setup.processKind leg = .isochoric →
      energyReadout units (setup.workDoneBySystemOnLeg leg) = 0

/-!
The closed-system first law with the chosen sign convention:
`Q = U_final - U_initial + W`, where `W` is work done by the system.  This is a
general legwise relation and contains no numerical heat conclusion.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : ThermodynamicProcessSetup) : Prop where
  firstLawOnLeg : ∀ (leg : ProcessLeg) (units : UnitChoices),
    energyReadout units (setup.heatTransferredToSystemOnLeg leg) =
      energyReadout units (setup.internalEnergyAt leg.finalState) -
        energyReadout units (setup.internalEnergyAt leg.initialState) +
          energyReadout units (setup.workDoneBySystemOnLeg leg)

/-!
On `a → b`, the figure gives an isochoric leg, so its work is zero.  The first
law therefore gives `Q_ab = U_b - U_a = 240 J - 150 J = 90 J`.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0341:target`.
-/
theorem heatTransferredAlongAB_eq_ninety_joules
    (setup : ThermodynamicProcessSetup)
    (_scenario : MatchesClosedSystemScenario setup)
    (_figure : MatchesSuppliedPressureVolumeFigure setup)
    (_readouts : MatchesProblemReadouts setup)
    (_physical : HasPhysicalPressureVolumeCoordinates setup)
    (_pathWork : SatisfiesPathWorkAdditivity setup)
    (_isochoricWork : SatisfiesIsochoricWorkLaw setup)
    (_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules (setup.heatTransferredToSystemOnLeg .ab) = 90 := by
  have workABIsZero :
      energyInJoules (setup.workDoneBySystemOnLeg .ab) = 0 := by
    exact _isochoricWork.isochoricLegHasZeroWork
      .ab UnitChoices.SI _figure.legABIsIsochoric
  have firstLawAB :
      energyInJoules (setup.heatTransferredToSystemOnLeg .ab) =
        energyInJoules (setup.internalEnergyAt .b) -
          energyInJoules (setup.internalEnergyAt .a) +
            energyInJoules (setup.workDoneBySystemOnLeg .ab) := by
    exact _firstLaw.firstLawOnLeg .ab UnitChoices.SI
  rw [firstLawAB, _readouts.internalEnergyAtB_J,
    _readouts.internalEnergyAtA_J, workABIsZero]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0341
