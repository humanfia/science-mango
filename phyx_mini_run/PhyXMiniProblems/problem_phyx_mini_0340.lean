import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/-!
# Heat transferred along an alternative path in a p-V diagram

This file formalizes problem `phyx_mini_0340`.  A thermodynamic system moves
between the same states `a` and `b` along two displayed paths.  Along `acb`,
`90 J` of heat enters the system and the system does `60 J` of work.  Along
`adb`, the system does `15 J` of work.  The first law and the fact that
internal energy depends only on the endpoint state determine the heat on
`adb`.

The primary image is read as follows: `a` is the lower-left state, `b` the
upper-right state, `c` the upper-left state, and `d` the lower-right state.
Thus `a -> c -> b` is isochoric then isobaric, `a -> d -> b` is isobaric then
isochoric, and the blue curved arrow runs from `b` back to `a`.  This corrects
the inconsistent auxiliary caption.

Pressure, volume, heat, work, and internal energy remain dimensionful physical
quantities.  Real numbers occur only as coherent SI readouts in pascals,
cubic metres, or joules.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0340

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- Physical volume, with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Physical pressure, with dimension `M L⁻¹ T⁻²`. -/
abbrev PressureQuantity : Type := DimPressure

/-- Heat, work, or internal energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- SI joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Thermodynamic states, paths, and the supplied figure -/

/-- A point in the p-V state space of the system. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity

/-- Qualitative process type indicated by a segment in the p-V figure. -/
inductive ProcessKind where
  | isochoric
  | isobaric
  | curved

/-- One directed leg of a thermodynamic path. -/
structure ProcessLeg where
  startState : ThermodynamicState
  endState : ThermodynamicState
  kind : ProcessKind

/-- A directed thermodynamic path, including its displayed legs. -/
structure ThermodynamicPath where
  startState : ThermodynamicState
  endState : ThermodynamicState
  legs : List ProcessLeg

/-- The physical quantity assigned to an axis in the supplied diagram. -/
inductive AxisQuantity where
  | pressure
  | volume

/-- Raw labels, states, and directed paths read from the supplied p-V image. -/
structure PVFigure where
  verticalAxisQuantity : AxisQuantity
  horizontalAxisQuantity : AxisQuantity
  originLabel : String
  stateA : ThermodynamicState
  stateB : ThermodynamicState
  stateC : ThermodynamicState
  stateD : ThermodynamicState
  pathACB : ThermodynamicPath
  pathADB : ThermodynamicPath
  pathBA : ThermodynamicPath

/-- A displayed two-leg path from `startState` through `middleState` to
`endState`, with the indicated process type on each leg. -/
def IsTwoLegPathVia
    (path : ThermodynamicPath)
    (startState middleState endState : ThermodynamicState)
    (firstKind secondKind : ProcessKind) : Prop :=
  path.startState = startState ∧
    path.endState = endState ∧
    path.legs =
      [{ startState := startState, endState := middleState, kind := firstKind },
       { startState := middleState, endState := endState, kind := secondKind }]

/-- A displayed direct one-leg path with the indicated process type. -/
def IsOneLegPath
    (path : ThermodynamicPath)
    (startState endState : ThermodynamicState)
    (kind : ProcessKind) : Prop :=
  path.startState = startState ∧
    path.endState = endState ∧
    path.legs = [{ startState := startState, endState := endState, kind := kind }]

/-- The rectangular placement of `a`, `b`, `c`, and `d` in the primary image.
The strict SI inequalities record which pressure and volume levels are the
lower and higher ones; the equalities record the isochoric and isobaric
alignments. -/
def HasDisplayedPVGeometry
    (a b c d : ThermodynamicState) : Prop :=
  a.volume = c.volume ∧
    b.volume = d.volume ∧
    a.pressure = d.pressure ∧
    b.pressure = c.pressure ∧
    volumeInCubicMetres a.volume < volumeInCubicMetres b.volume ∧
    pressureInPascals a.pressure < pressureInPascals b.pressure

/-- Exact axis, label, geometry, and arrow-direction information extracted
from the supplied p-V image. -/
def MatchesSuppliedFigure (figure : PVFigure) : Prop :=
  figure.verticalAxisQuantity = .pressure ∧
    figure.horizontalAxisQuantity = .volume ∧
    figure.originLabel = "O" ∧
    HasDisplayedPVGeometry
      figure.stateA figure.stateB figure.stateC figure.stateD ∧
    IsTwoLegPathVia figure.pathACB
      figure.stateA figure.stateC figure.stateB .isochoric .isobaric ∧
    IsTwoLegPathVia figure.pathADB
      figure.stateA figure.stateD figure.stateB .isobaric .isochoric ∧
    IsOneLegPath figure.pathBA figure.stateB figure.stateA .curved

/-! ## Thermodynamic model and governing law -/

/-- State-dependent internal energy and path-dependent heat and work.
`heatIntoSystem` is positive for heat entering the system, while
`workDoneBySystem` is positive for work done by the system. -/
structure ThermodynamicModel where
  internalEnergy : ThermodynamicState → EnergyQuantity
  heatIntoSystem : ThermodynamicPath → EnergyQuantity
  workDoneBySystem : ThermodynamicPath → EnergyQuantity

/-- The first law with the sign convention `ΔU = Q - W_by`, expressed in
coherent SI joule readouts.  Internal energy is a function of state, whereas
heat and work are functions of the complete path. -/
def SatisfiesFirstLaw (model : ThermodynamicModel) : Prop :=
  ∀ path : ThermodynamicPath,
    energyInJoules (model.internalEnergy path.endState) -
        energyInJoules (model.internalEnergy path.startState) =
      energyInJoules (model.heatIntoSystem path) -
        energyInJoules (model.workDoneBySystem path)

/-! ## Displayed answer choices -/

/-- Answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D

/-- Joule value printed beside each answer label. -/
def AnswerChoice.jouleValue : AnswerChoice → ℝ
  | .A => 15
  | .B => 45
  | .C => 25
  | .D => 32

/-! ## Main target -/

/-- Along `acb`, the supplied heat and work give an internal-energy increase
of `30 J`.  Endpoint-dependence of internal energy and the first law then
force the heat entering along `adb` to be `45 J`, answer choice B.

Blueprint label: `thm:physics:phyx_mini_0340:target`.
-/
theorem heatIntoSystemAlongADB_eq_45_joules
    (figure : PVFigure)
    (model : ThermodynamicModel)
    (hFigure : MatchesSuppliedFigure figure)
    (hFirstLaw : SatisfiesFirstLaw model)
    (hHeatACB : energyInJoules (model.heatIntoSystem figure.pathACB) = 90)
    (hWorkACB : energyInJoules (model.workDoneBySystem figure.pathACB) = 60)
    (hWorkADB : energyInJoules (model.workDoneBySystem figure.pathADB) = 15) :
    energyInJoules (model.heatIntoSystem figure.pathADB) = 45 := by
  rcases hFigure with ⟨_, _, _, _, hPathACB, hPathADB, _⟩
  rcases hPathACB with ⟨hStartACB, hEndACB, _⟩
  rcases hPathADB with ⟨hStartADB, hEndADB, _⟩
  have hFirstLawACB := hFirstLaw figure.pathACB
  have hFirstLawADB := hFirstLaw figure.pathADB
  rw [hStartACB, hEndACB, hHeatACB, hWorkACB] at hFirstLawACB
  rw [hStartADB, hEndADB, hWorkADB] at hFirstLawADB
  linarith

end PhyXMiniProblems.ProblemPhyXMini0340
