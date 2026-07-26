import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0344

open Dimension

/-!
# Heat transferred to helium along the path `a → b → c`

One third of a mole of helium follows the two solid straight segments of the
pressure-volume diagram.  The primary image gives

* `a = (0.002 m³, 1.0 × 10⁵ Pa)`,
* `b = (0.006 m³, 3.5 × 10⁵ Pa)`, and
* `c = (0.010 m³, 1.0 × 10⁵ Pa)`.

The dashed horizontal segment from `c` back to `a` is retained as figure
information, but it is not part of the questioned path `abc`.

Pressure, volume, temperature, internal energy, work, and heat are represented
as physical quantities.  Real numbers below are explicitly SI or mole
readouts, schematic coordinates, or the numerical values printed in the
answer choices.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical pressure, represented by Physlib's pressure quantity. -/
abbrev PressureQuantity : Type := DimPressure

/-- A physical energy; its sign records the direction of an energy transfer. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI volume readout, in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- SI pressure readout, in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- SI energy readout, in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Gas states, path labels, and primary-figure roles -/

/-- The three labeled equilibrium states in the supplied `p`-`V` diagram. -/
inductive GasState where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The three drawn connections between labeled states. -/
inductive ProcessLeg where
  | aToB
  | bToC
  | cToA
  deriving DecidableEq, Repr

/-- The chemical species named in the problem. -/
inductive GasSpecies where
  | helium
  | other
  deriving DecidableEq, Repr

/-- The thermodynamic model requested in the problem statement. -/
inductive GasModel where
  | ideal
  | nonideal
  deriving DecidableEq, Repr

/-- The equilibrium-process regime needed to interpret the drawn `p`-`V` path. -/
inductive ProcessRegime where
  | quasistatic
  | nonquasistatic
  deriving DecidableEq, Repr

/-- The two axes of the primary diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical roles of the plotted axes. -/
inductive AxisRole where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Units printed beside the axes. -/
inductive AxisDisplayUnit where
  | cubicMeters
  | pascals
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the diagram. -/
inductive FigureLabel where
  | a
  | b
  | c
  | volumeV
  | pressureP
  deriving DecidableEq, Repr

/-- Appearance of a process leg in the supplied bitmap. -/
inductive LegStyle where
  | solidBlue
  | solidPurple
  | dashedBlack
  deriving DecidableEq, Repr

/-- Geometric shape of a plotted process leg. -/
inductive LegGeometry where
  | straightLine
  | other
  deriving DecidableEq, Repr

/-!
The diagram as an independent source of state coordinates and path metadata.
Keeping these coordinates separate from the gas state lets the data predicate
say explicitly that the physical process passes through the plotted points.
-/
structure PressureVolumeFigure where
  axisRole : FigureAxis → AxisRole
  axisUnit : FigureAxis → AxisDisplayUnit
  axisLabel : FigureAxis → FigureLabel
  stateLabel : GasState → FigureLabel
  plottedVolume : GasState → VolumeQuantity
  plottedPressure : GasState → PressureQuantity
  legStart : ProcessLeg → GasState
  legEnd : ProcessLeg → GasState
  legStyle : ProcessLeg → LegStyle
  legGeometry : ProcessLeg → LegGeometry
  directionArrowShown : ProcessLeg → Bool

/-!
The physical helium sample and its path-dependent energy transfers.

`amountOfGasMoles` and `molarGasConstantJoulesPerMoleKelvin` are named scalar
readouts because Physlib's unit system has no amount-of-substance dimension.
The signed heat convention is positive for heat transferred into the gas, and
work is positive when done by the gas on its environment.  No field is defined
from the requested numerical heat.
-/
structure HeliumPVProcess where
  species : GasSpecies
  model : GasModel
  regime : ProcessRegime
  amountOfGasMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  pressure : GasState → PressureQuantity
  volume : GasState → VolumeQuantity
  temperature : GasState → Temperature
  internalEnergy : GasState → EnergyQuantity
  processLegStart : ProcessLeg → GasState
  processLegEnd : ProcessLeg → GasState
  questionedPath : List ProcessLeg
  workDoneByGasOnLeg : ProcessLeg → EnergyQuantity
  workDoneByGasAlongABC : EnergyQuantity
  signedHeatIntoGasAlongABC : EnergyQuantity
  figure : PressureVolumeFigure

/-! ## Figure/data readouts and physical admissibility -/

/-!
Facts stated in the prose or transcribed from the primary bitmap.  The point
`b` lies halfway between the `3 × 10⁵ Pa` and `4 × 10⁵ Pa` ticks.  The two
solid directed legs form the questioned path; the dashed `c`-to-`a` leg merely
shows the closure.  None of these fields mentions heat, work, or internal
energy.
-/
structure MatchesProblemStatementAndFigure
    (setup : HeliumPVProcess) : Prop where
  gasIsHelium : setup.species = .helium
  gasIsTreatedAsIdeal : setup.model = .ideal
  amountIsOneThirdMole : setup.amountOfGasMoles = 1 / 3
  horizontalAxisIsVolume : setup.figure.axisRole .horizontal = .volume
  verticalAxisIsPressure : setup.figure.axisRole .vertical = .pressure
  horizontalUnitIsCubicMeters :
    setup.figure.axisUnit .horizontal = .cubicMeters
  verticalUnitIsPascals : setup.figure.axisUnit .vertical = .pascals
  horizontalLabelIsV : setup.figure.axisLabel .horizontal = .volumeV
  verticalLabelIsP : setup.figure.axisLabel .vertical = .pressureP
  labelsMatchStates :
    setup.figure.stateLabel .a = .a ∧
      setup.figure.stateLabel .b = .b ∧
      setup.figure.stateLabel .c = .c
  figureCoordinatesAreGasStates : ∀ state : GasState,
    setup.figure.plottedVolume state = setup.volume state ∧
      setup.figure.plottedPressure state = setup.pressure state
  volumeAtA : volumeInCubicMeters (setup.figure.plottedVolume .a) = 1 / 500
  pressureAtA : pressureInPascals (setup.figure.plottedPressure .a) = 100000
  volumeAtB : volumeInCubicMeters (setup.figure.plottedVolume .b) = 3 / 500
  pressureAtB : pressureInPascals (setup.figure.plottedPressure .b) = 350000
  volumeAtC : volumeInCubicMeters (setup.figure.plottedVolume .c) = 1 / 100
  pressureAtC : pressureInPascals (setup.figure.plottedPressure .c) = 100000
  physicalLegsMatchFigure : ∀ leg : ProcessLeg,
    setup.processLegStart leg = setup.figure.legStart leg ∧
      setup.processLegEnd leg = setup.figure.legEnd leg
  aToBEndpoints :
    setup.figure.legStart .aToB = .a ∧ setup.figure.legEnd .aToB = .b
  bToCEndpoints :
    setup.figure.legStart .bToC = .b ∧ setup.figure.legEnd .bToC = .c
  cToAEndpoints :
    setup.figure.legStart .cToA = .c ∧ setup.figure.legEnd .cToA = .a
  questionedPathIsABC : setup.questionedPath = [.aToB, .bToC]
  aToBIsSolidBlue : setup.figure.legStyle .aToB = .solidBlue
  bToCIsSolidPurple : setup.figure.legStyle .bToC = .solidPurple
  cToAIsDashedBlack : setup.figure.legStyle .cToA = .dashedBlack
  allLegsAreStraight : ∀ leg : ProcessLeg,
    setup.figure.legGeometry leg = .straightLine
  aToBDirectionShown : setup.figure.directionArrowShown .aToB = true
  bToCDirectionShown : setup.figure.directionArrowShown .bToC = true
  closureHasNoDirectionArrow :
    setup.figure.directionArrowShown .cToA = false

/-!
Positivity and nondegeneracy assumptions selecting a physical ideal-gas
process.  In particular, no sign condition is imposed on the requested heat or
on the derived work.
-/
structure HasPhysicalGasParameters (setup : HeliumPVProcess) : Prop where
  amountPositive : 0 < setup.amountOfGasMoles
  molarGasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  pressurePositive : ∀ state : GasState,
    0 < pressureInPascals (setup.pressure state)
  volumePositive : ∀ state : GasState,
    0 < volumeInCubicMeters (setup.volume state)
  temperaturePositive : ∀ state : GasState,
    0 < (setup.temperature state).toReal

/-! ## Governing thermodynamic laws -/

/-!
Macroscopic ideal-gas and monatomic-helium energy laws in coherent SI
readouts.  The first relation is `pV = nRT`; the second is
`U = (3/2)nRT`.  They apply at every state and contain no heat-transfer
conclusion.
-/
structure SatisfiesIdealMonatomicGasLaws
    (setup : HeliumPVProcess) : Prop where
  idealGasLaw : ∀ state : GasState,
    pressureInPascals (setup.pressure state) *
        volumeInCubicMeters (setup.volume state) =
      setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          (setup.temperature state).toReal
  monatomicInternalEnergyLaw : ∀ state : GasState,
    energyInJoules (setup.internalEnergy state) =
      (3 / 2 : ℝ) * setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          (setup.temperature state).toReal

/-!
For each straight quasistatic leg on `abc`, integrating `p dV` gives the
trapezoid formula: average endpoint pressure times the volume change.  Work
along the questioned path is additive over its two legs.  This is a generic
work law and does not assume the derived `1800 J` value.
-/
structure SatisfiesStraightPVWorkLaw
    (setup : HeliumPVProcess) : Prop where
  processIsQuasistatic : setup.regime = .quasistatic
  straightLegWork : ∀ leg : ProcessLeg, leg ∈ setup.questionedPath →
    energyInJoules (setup.workDoneByGasOnLeg leg) =
      (pressureInPascals (setup.pressure (setup.processLegStart leg)) +
          pressureInPascals (setup.pressure (setup.processLegEnd leg))) /
        2 *
      (volumeInCubicMeters (setup.volume (setup.processLegEnd leg)) -
        volumeInCubicMeters (setup.volume (setup.processLegStart leg)))
  pathWorkIsSumOfLegs :
    energyInJoules setup.workDoneByGasAlongABC =
      energyInJoules (setup.workDoneByGasOnLeg .aToB) +
        energyInJoules (setup.workDoneByGasOnLeg .bToC)

/-!
First-law sign convention on the path `a → b → c`:

`Q_into = (U_c - U_a) + W_by_gas`.

This governing relation leaves every term as an independent physical energy;
it does not insert the requested numerical value or its sign.
-/
structure SatisfiesFirstLawAlongABC
    (setup : HeliumPVProcess) : Prop where
  firstLaw :
    energyInJoules setup.signedHeatIntoGasAlongABC =
      (energyInJoules (setup.internalEnergy .c) -
        energyInJoules (setup.internalEnergy .a)) +
      energyInJoules setup.workDoneByGasAlongABC

/-! ## Derived route and requested multiple-choice result -/

/-- The endpoint products and the monatomic law give `ΔU = 1200 J`. -/
lemma internalEnergyChangeAlongABC_eq_1200_joules
    (setup : HeliumPVProcess)
    (_data : MatchesProblemStatementAndFigure setup)
    (_physical : HasPhysicalGasParameters setup)
    (_gasLaws : SatisfiesIdealMonatomicGasLaws setup) :
    energyInJoules (setup.internalEnergy .c) -
        energyInJoules (setup.internalEnergy .a) = 1200 := by
  have hVolumeA :
      volumeInCubicMeters (setup.volume .a) = 1 / 500 := by
    rw [← (_data.figureCoordinatesAreGasStates .a).1]
    exact _data.volumeAtA
  have hPressureA :
      pressureInPascals (setup.pressure .a) = 100000 := by
    rw [← (_data.figureCoordinatesAreGasStates .a).2]
    exact _data.pressureAtA
  have hVolumeC :
      volumeInCubicMeters (setup.volume .c) = 1 / 100 := by
    rw [← (_data.figureCoordinatesAreGasStates .c).1]
    exact _data.volumeAtC
  have hPressureC :
      pressureInPascals (setup.pressure .c) = 100000 := by
    rw [← (_data.figureCoordinatesAreGasStates .c).2]
    exact _data.pressureAtC
  have hIdealA := _gasLaws.idealGasLaw .a
  have hIdealC := _gasLaws.idealGasLaw .c
  have hEnergyA := _gasLaws.monatomicInternalEnergyLaw .a
  have hEnergyC := _gasLaws.monatomicInternalEnergyLaw .c
  rw [hPressureA, hVolumeA] at hIdealA
  rw [hPressureC, hVolumeC] at hIdealC
  norm_num at hIdealA hIdealC
  nlinarith [hEnergyA, hEnergyC]

/-- The two straight-line trapezoids give `W_by_gas = 1800 J`. -/
lemma workDoneByGasAlongABC_eq_1800_joules
    (setup : HeliumPVProcess)
    (_data : MatchesProblemStatementAndFigure setup)
    (_workLaw : SatisfiesStraightPVWorkLaw setup) :
    energyInJoules setup.workDoneByGasAlongABC = 1800 := by
  have hVolumeA :
      volumeInCubicMeters (setup.volume .a) = 1 / 500 := by
    rw [← (_data.figureCoordinatesAreGasStates .a).1]
    exact _data.volumeAtA
  have hPressureA :
      pressureInPascals (setup.pressure .a) = 100000 := by
    rw [← (_data.figureCoordinatesAreGasStates .a).2]
    exact _data.pressureAtA
  have hVolumeB :
      volumeInCubicMeters (setup.volume .b) = 3 / 500 := by
    rw [← (_data.figureCoordinatesAreGasStates .b).1]
    exact _data.volumeAtB
  have hPressureB :
      pressureInPascals (setup.pressure .b) = 350000 := by
    rw [← (_data.figureCoordinatesAreGasStates .b).2]
    exact _data.pressureAtB
  have hVolumeC :
      volumeInCubicMeters (setup.volume .c) = 1 / 100 := by
    rw [← (_data.figureCoordinatesAreGasStates .c).1]
    exact _data.volumeAtC
  have hPressureC :
      pressureInPascals (setup.pressure .c) = 100000 := by
    rw [← (_data.figureCoordinatesAreGasStates .c).2]
    exact _data.pressureAtC
  have hStartAB : setup.processLegStart .aToB = .a :=
    (_data.physicalLegsMatchFigure .aToB).1.trans _data.aToBEndpoints.1
  have hEndAB : setup.processLegEnd .aToB = .b :=
    (_data.physicalLegsMatchFigure .aToB).2.trans _data.aToBEndpoints.2
  have hStartBC : setup.processLegStart .bToC = .b :=
    (_data.physicalLegsMatchFigure .bToC).1.trans _data.bToCEndpoints.1
  have hEndBC : setup.processLegEnd .bToC = .c :=
    (_data.physicalLegsMatchFigure .bToC).2.trans _data.bToCEndpoints.2
  have hABMem : ProcessLeg.aToB ∈ setup.questionedPath := by
    rw [_data.questionedPathIsABC]
    simp
  have hBCMem : ProcessLeg.bToC ∈ setup.questionedPath := by
    rw [_data.questionedPathIsABC]
    simp
  have hWorkAB := _workLaw.straightLegWork .aToB hABMem
  have hWorkBC := _workLaw.straightLegWork .bToC hBCMem
  rw [hStartAB, hEndAB, hPressureA, hPressureB, hVolumeA, hVolumeB] at hWorkAB
  rw [hStartBC, hEndBC, hPressureB, hPressureC, hVolumeB, hVolumeC] at hWorkBC
  norm_num at hWorkAB hWorkBC
  linarith [_workLaw.pathWorkIsSumOfLegs]

/-- Labels of the four displayed heat-transfer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Signed heat readout, in joules, printed beside each answer label. -/
def answerHeatInJoules : AnswerChoice → ℝ
  | .A => 1650
  | .B => 3000
  | .C => 1950
  | .D => -1450

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The internal-energy increase is `1200 J` and the gas does `1800 J` of work,
so the first law gives a positive `3000 J`: heat is transferred into the gas,
selecting answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0344:target`.
-/
theorem problem_phyx_mini_0344
    (setup : HeliumPVProcess)
    (_data : MatchesProblemStatementAndFigure setup)
    (_physical : HasPhysicalGasParameters setup)
    (_gasLaws : SatisfiesIdealMonatomicGasLaws setup)
    (_workLaw : SatisfiesStraightPVWorkLaw setup)
    (_firstLaw : SatisfiesFirstLawAlongABC setup) :
    energyInJoules setup.signedHeatIntoGasAlongABC = 3000 ∧
      0 < energyInJoules setup.signedHeatIntoGasAlongABC ∧
      energyInJoules setup.signedHeatIntoGasAlongABC =
        answerHeatInJoules recordedAnswerChoice := by
  have hInternalEnergy :=
    internalEnergyChangeAlongABC_eq_1200_joules
      setup _data _physical _gasLaws
  have hWork :=
    workDoneByGasAlongABC_eq_1800_joules setup _data _workLaw
  have hHeat :
      energyInJoules setup.signedHeatIntoGasAlongABC = 3000 := by
    linarith [_firstLaw.firstLaw]
  refine ⟨hHeat, ?_, ?_⟩
  · rw [hHeat]
    norm_num
  · simpa [answerHeatInJoules, recordedAnswerChoice] using hHeat

end PhyXMiniProblems.ProblemPhyXMini0344
