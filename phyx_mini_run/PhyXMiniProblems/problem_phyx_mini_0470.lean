import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0470

open Dimension

/-!
# Heat transfer in a counterclockwise pressure--volume cycle

The primary image is a `p`--`V` diagram with states `a` and `b`.  The system
travels from `a` to `b` along the lower curve and returns from `b` to `a` along
the upper curve, making a counterclockwise cycle.  The image annotation says
that the signed enclosed area is the total work done by the system and that
this work is negative.  The prose supplies the calibrated value `-500 J`.

Heat is signed positive into the system and work is signed positive when done
by the system, so the closed-system first law is written
`Q_into = ΔU + W_by`.  Consequently the signed net heat is negative in this
problem.  The positive number printed among the answer choices is its
magnitude: the system rejects `500 J` over the complete cycle.

Pressure, volume, internal energy, heat, and work retain physical dimensions.
Real numbers below occur only as explicitly named SI readouts, diagram
coordinates, and displayed answer-choice values.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical volume, carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical pressure, represented by Physlib's dimensionful pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy, used for internal energy, heat, and work. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read signed dimensionful energy in coherent SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Cycle, states, and diagram vocabulary -/

/-- The two labelled equilibrium points in the supplied diagram. -/
inductive DiagramPoint where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- Stages used to distinguish the initial and final visits to state `a`. -/
inductive ProcessStage where
  | initialAtA
  | atB
  | finalAtA
  deriving DecidableEq, Fintype, Repr

/-- The two directed legs of the closed process. -/
inductive CycleLeg where
  | aToB
  | bToA
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to one axis of the plot. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Qualitative location of one curved leg in the primary image. -/
inductive CurveLocation where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- Orientation of a closed path in the pressure--volume plane. -/
inductive CycleOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Sign displayed for the work done by the system. -/
inductive WorkSign where
  | negative
  | zero
  | positive
  deriving DecidableEq, Repr

/-- Physical meaning assigned to the shaded enclosed area by the annotation. -/
inductive EnclosedAreaMeaning where
  | totalWorkDoneBySystem
  deriving DecidableEq, Repr

/-- Pressure, volume, and internal energy at one equilibrium stage. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  internalEnergy : EnergyQuantity

/-!
Literal and calibrated data belonging to the supplied `p`--`V` image.
The signed enclosed-area readout has energy units because pressure times
volume has the dimension of work.
-/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  pointShown : DiagramPoint → Bool
  pointLabelShown : DiagramPoint → Bool
  pressureCoordinate : DiagramPoint → PressureQuantity
  volumeCoordinate : DiagramPoint → VolumeQuantity
  arrowStart : CycleLeg → DiagramPoint
  arrowFinish : CycleLeg → DiagramPoint
  curveLocation : CycleLeg → CurveLocation
  orientation : CycleOrientation
  enclosedAreaMeaning : EnclosedAreaMeaning
  signedEnclosedAreaInJoules : ℝ
  displayedWorkSign : WorkSign

/-!
Independent observables for the complete cycle.  In particular, net heat is
an unconstrained dimensionful field here; it is related to work and internal
energy only by the governing first-law hypothesis below.
-/
structure CyclicPVProcess where
  stagePoint : ProcessStage → DiagramPoint
  stateAt : ProcessStage → ThermodynamicState
  netInternalEnergyChange : EnergyQuantity
  netWorkDoneBySystem : EnergyQuantity
  netHeatTransferredIntoSystem : EnergyQuantity
  diagram : PressureVolumeDiagram

/-! ## Problem data and primary-image readouts -/

/-!
Facts supplied by the prose: the route starts at `a`, visits `b`, returns to
the same thermodynamic state `a`, and has total work `-500 J`.  No heat value
is assumed.
-/
structure MatchesProblemStatement (setup : CyclicPVProcess) : Prop where
  initialStageIsA : setup.stagePoint .initialAtA = .a
  intermediateStageIsB : setup.stagePoint .atB = .b
  finalStageIsA : setup.stagePoint .finalAtA = .a
  initialAndFinalStatesAgree :
    setup.stateAt .initialAtA = setup.stateAt .finalAtA
  totalWorkDoneBySystemInJoules :
    energyInJoules setup.netWorkDoneBySystem = -500

/-!
Primary-image evidence: volume is horizontal, pressure is vertical,
`V_a < V_b`, `p_b < p_a`, both states and labels are shown, and the arrows
trace the lower `a → b` curve followed by the upper `b → a` curve.  The
annotation identifies the signed enclosed area with negative work by the
system, but does not assign any heat.
-/
structure MatchesPrimaryPressureVolumeDiagram
    (setup : CyclicPVProcess) : Prop where
  horizontalAxisIsVolume :
    setup.diagram.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.diagram.verticalAxisQuantity = .pressure
  everyPointShown :
    ∀ point : DiagramPoint, setup.diagram.pointShown point = true
  everyPointLabelShown :
    ∀ point : DiagramPoint, setup.diagram.pointLabelShown point = true
  pressureAtAUsesInitialState :
    setup.diagram.pressureCoordinate .a =
      (setup.stateAt .initialAtA).pressure
  volumeAtAUsesInitialState :
    setup.diagram.volumeCoordinate .a =
      (setup.stateAt .initialAtA).volume
  pressureAtBUsesIntermediateState :
    setup.diagram.pressureCoordinate .b = (setup.stateAt .atB).pressure
  volumeAtBUsesIntermediateState :
    setup.diagram.volumeCoordinate .b = (setup.stateAt .atB).volume
  aHasHigherPressure :
    pressureInPascals (setup.diagram.pressureCoordinate .b) <
      pressureInPascals (setup.diagram.pressureCoordinate .a)
  bHasLargerVolume :
    volumeInCubicMeters (setup.diagram.volumeCoordinate .a) <
      volumeInCubicMeters (setup.diagram.volumeCoordinate .b)
  lowerCurveStartsAtA : setup.diagram.arrowStart .aToB = .a
  lowerCurveFinishesAtB : setup.diagram.arrowFinish .aToB = .b
  returnCurveStartsAtB : setup.diagram.arrowStart .bToA = .b
  returnCurveFinishesAtA : setup.diagram.arrowFinish .bToA = .a
  aToBIsLowerCurve : setup.diagram.curveLocation .aToB = .lower
  bToAIsUpperCurve : setup.diagram.curveLocation .bToA = .upper
  pathIsCounterclockwise :
    setup.diagram.orientation = .counterclockwise
  shadedAreaRepresentsWorkBySystem :
    setup.diagram.enclosedAreaMeaning = .totalWorkDoneBySystem
  displayedWorkIsNegative : setup.diagram.displayedWorkSign = .negative
  signedAreaIsNegative : setup.diagram.signedEnclosedAreaInJoules < 0

/-- Positivity conditions selecting genuine pressure--volume states. -/
structure HasPhysicalStateReadouts (setup : CyclicPVProcess) : Prop where
  pressurePositive :
    ∀ stage, 0 < pressureInPascals (setup.stateAt stage).pressure
  volumePositive :
    ∀ stage, 0 < volumeInCubicMeters (setup.stateAt stage).volume

/-!
The quasi-static `p`--`V` work law for the complete closed path: its signed
enclosed area equals the net work done by the system.  This is a governing
relation, not the requested heat conclusion.
-/
structure SatisfiesPressureVolumeWorkAreaLaw
    (setup : CyclicPVProcess) : Prop where
  netWorkEqualsSignedEnclosedArea :
    energyInJoules setup.netWorkDoneBySystem =
      setup.diagram.signedEnclosedAreaInJoules

/-!
Closed-system thermodynamics for the complete traversal.  Internal energy is
a state function, and with heat positive into the system and work positive by
the system the first law is `Q_into = ΔU + W_by`.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : CyclicPVProcess) : Prop where
  internalEnergyChangeIsStateDifference :
    energyInJoules setup.netInternalEnergyChange =
      energyInJoules (setup.stateAt .finalAtA).internalEnergy -
        energyInJoules (setup.stateAt .initialAtA).internalEnergy
  firstLawForCompleteCycle :
    energyInJoules setup.netHeatTransferredIntoSystem =
      energyInJoules setup.netInternalEnergyChange +
        energyInJoules setup.netWorkDoneBySystem

/-! ## Derived readouts and answer choices -/

/-- Magnitude of the net heat transfer, in joules. -/
def netHeatTransferMagnitudeInJoules (setup : CyclicPVProcess) : ℝ :=
  abs (energyInJoules setup.netHeatTransferredIntoSystem)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Positive energy amount printed beside each choice, in joules. -/
def displayedHeatAmountInJoules : AnswerChoice → ℝ
  | .A => 350
  | .B => 500
  | .C => 333
  | .D => 450

/-- The dataset records answer label B. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
Because the initial and final thermodynamic states coincide, their internal
energies coincide and the net internal-energy change is zero.
-/
lemma netInternalEnergyChangeInJoules_eq_zero
    (setup : CyclicPVProcess)
    (h_problem : MatchesProblemStatement setup)
    (h_first_law : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules setup.netInternalEnergyChange = 0 := by
  calc
    energyInJoules setup.netInternalEnergyChange =
        energyInJoules (setup.stateAt .finalAtA).internalEnergy -
          energyInJoules (setup.stateAt .initialAtA).internalEnergy :=
      h_first_law.internalEnergyChangeIsStateDifference
    _ = 0 := by
      rw [h_problem.initialAndFinalStatesAgree]
      ring

/-!
The first law for the closed cycle gives signed heat `Q_into = -500 J`.
Thus the system rejects `500 J`; the magnitude is the value displayed by
recorded answer B.
-/
theorem heatTransferDuringCycle_matches_recordedChoice
    (setup : CyclicPVProcess)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPressureVolumeDiagram setup)
    (h_physical : HasPhysicalStateReadouts setup)
    (h_work_area : SatisfiesPressureVolumeWorkAreaLaw setup)
    (h_first_law : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules setup.netHeatTransferredIntoSystem = -500 ∧
      netHeatTransferMagnitudeInJoules setup =
        displayedHeatAmountInJoules recordedAnswerChoice := by
  have h_internal_energy :
      energyInJoules setup.netInternalEnergyChange = 0 :=
    netInternalEnergyChangeInJoules_eq_zero setup h_problem h_first_law
  have h_heat :
      energyInJoules setup.netHeatTransferredIntoSystem = -500 := by
    calc
      energyInJoules setup.netHeatTransferredIntoSystem =
          energyInJoules setup.netInternalEnergyChange +
            energyInJoules setup.netWorkDoneBySystem :=
        h_first_law.firstLawForCompleteCycle
      _ = -500 := by
        rw [h_internal_energy, h_problem.totalWorkDoneBySystemInJoules]
        norm_num
  constructor
  · exact h_heat
  · simp [netHeatTransferMagnitudeInJoules, displayedHeatAmountInJoules,
      recordedAnswerChoice, h_heat]

end PhyXMiniProblems.ProblemPhyXMini0470
