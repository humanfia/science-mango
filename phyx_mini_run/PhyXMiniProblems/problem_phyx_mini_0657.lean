import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0657

open Dimension

/-!
# Ground-state energy from a rigid-box wave-function plot

The supplied graph is a plot of `psi(x)` for an electron confined to a
one-dimensional rigid box.  It has three lobes (positive, negative, positive)
and two interior nodes, so the depicted stationary state has quantum number
`n = 3`.  Its measured energy is `12.0 eV`.  The infinite-square-well scaling
law `E_n = n^2 E_1` therefore determines the ground-state energy.

The quantum state and its energies use Physlib's Hilbert-space and
dimensionful-energy types.  Real numbers below are used only for explicitly
labelled unit readouts or for the uncalibrated coordinates of the raster plot.
In particular, the ground-state energy is an independent level of the setup;
it is not defined to be the recorded answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Coherent-SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a physical energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Energy readout in electron volts, grounded by `DimEnergy.electronVolt`. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-! ## Scenario roles and literal vocabulary of image 657 -/

/-- Particle species appearing in the problem statement. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- The idealized confinement model meant by a one-dimensional rigid box. -/
inductive ConfinementModel where
  | oneDimensionalInfiniteSquareWell
  | other
  deriving DecidableEq, Repr

/-- The two axes drawn in the supplied wave-function graph. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical or mathematical role assigned to an axis label. -/
inductive PlotAxisQuantity where
  | positionX
  | waveFunctionPsiOfX
  deriving DecidableEq, Repr

/-- The four zeroes visible from the left to the right box boundary. -/
inductive FigureNode where
  | leftBoundary
  | firstInterior
  | secondInterior
  | rightBoundary
  deriving DecidableEq, Fintype, Repr

/-- The three consecutive lobes of the plotted stationary wave function. -/
inductive FigureLobe where
  | leftPositive
  | centralNegative
  | rightPositive
  deriving DecidableEq, Fintype, Repr

/-- Color of the curve in the supplied raster image. -/
inductive PlotCurveColor where
  | red
  | other
  deriving DecidableEq, Repr

/-!
Literal, uncalibrated graph data from image `657.png`.  Plot coordinates and
amplitudes are real display coordinates, not substitutes for the physical box
width or for the quantum state in the Hilbert space.
-/
structure RigidBoxWaveFunctionFigure where
  axisQuantity : PlotAxis → PlotAxisQuantity
  axisLabelShown : PlotAxis → Bool
  curveColor : PlotCurveColor
  traceIsSinusoidal : Bool
  traceOutsideBoxIsOnBaseline : Bool
  nodeCoordinate : FigureNode → ℝ
  lobeSampleCoordinate : FigureLobe → ℝ
  plottedAmplitude : ℝ → ℝ
  interiorNodeCount : ℕ
  lobeCount : ℕ

/-!
Independent physical data for the depicted electron state.  The state itself
uses Physlib's one-dimensional quantum Hilbert space, while `boxWidth` and all
level energies retain their physical dimensions.
-/
structure ElectronRigidBoxSetup where
  particleSpecies : ParticleSpecies
  spatialDimension : ℕ
  confinementModel : ConfinementModel
  boxWidth : LengthQuantity
  depictedStationaryState : QuantumMechanics.OneDimension.HilbertSpace
  depictedStateIsEnergyEigenstate : Bool
  figureDepictsStationaryState : Bool
  depictedQuantumNumber : ℕ
  energyLevel : ℕ → DimEnergy
  figure : RigidBoxWaveFunctionFigure

/-! ## Scenario, primary-figure readout, and governing laws -/

/-- The prose scenario: an electron stationary state in a one-dimensional rigid box. -/
structure MatchesElectronRigidBoxScenario
    (setup : ElectronRigidBoxSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  oneSpatialDimension : setup.spatialDimension = 1
  rigidBoxIsInfiniteSquareWell :
    setup.confinementModel = .oneDimensionalInfiniteSquareWell
  depictedStateIsEigenstate : setup.depictedStateIsEnergyEigenstate = true
  figureShowsThatState : setup.figureDepictsStationaryState = true

/-!
Primary-image evidence: axes labelled `x` and `psi(x)`, a red sinusoidal trace,
four ordered boundary/node crossings, and the positive-negative-positive lobe
pattern.  This premise contains no energy level or answer-choice value.
-/
structure MatchesSuppliedWaveFunctionFigure
    (figure : RigidBoxWaveFunctionFigure) : Prop where
  horizontalAxisIsPosition :
    figure.axisQuantity .horizontal = .positionX
  verticalAxisIsWaveFunction :
    figure.axisQuantity .vertical = .waveFunctionPsiOfX
  horizontalAxisLabelShown : figure.axisLabelShown .horizontal = true
  verticalAxisLabelShown : figure.axisLabelShown .vertical = true
  redTrace : figure.curveColor = .red
  sinusoidalTrace : figure.traceIsSinusoidal = true
  outsideBoxOnBaseline : figure.traceOutsideBoxIsOnBaseline = true
  everyMarkedNodeIsZero : ∀ node,
    figure.plottedAmplitude (figure.nodeCoordinate node) = 0
  nodesAndLobeSamplesAreOrdered :
    figure.nodeCoordinate .leftBoundary <
        figure.lobeSampleCoordinate .leftPositive ∧
      figure.lobeSampleCoordinate .leftPositive <
        figure.nodeCoordinate .firstInterior ∧
      figure.nodeCoordinate .firstInterior <
        figure.lobeSampleCoordinate .centralNegative ∧
      figure.lobeSampleCoordinate .centralNegative <
        figure.nodeCoordinate .secondInterior ∧
      figure.nodeCoordinate .secondInterior <
        figure.lobeSampleCoordinate .rightPositive ∧
      figure.lobeSampleCoordinate .rightPositive <
        figure.nodeCoordinate .rightBoundary
  leftLobePositive :
    0 < figure.plottedAmplitude
      (figure.lobeSampleCoordinate .leftPositive)
  centralLobeNegative :
    figure.plottedAmplitude
      (figure.lobeSampleCoordinate .centralNegative) < 0
  rightLobePositive :
    0 < figure.plottedAmplitude
      (figure.lobeSampleCoordinate .rightPositive)
  exactlyTwoInteriorNodes : figure.interiorNodeCount = 2
  exactlyThreeLobes : figure.lobeCount = 3

/-! The `12.0 eV` energy belongs to the state depicted in the graph. -/
structure MatchesGivenDepictedEnergy
    (setup : ElectronRigidBoxSetup) : Prop where
  depictedEnergyElectronVolts :
    energyInElectronVolts
      (setup.energyLevel setup.depictedQuantumNumber) = 12.0

/-- Positivity conditions selecting a nondegenerate physical rigid box. -/
structure HasPhysicalRigidBoxParameters
    (setup : ElectronRigidBoxSetup) : Prop where
  positiveBoxWidth : 0 < lengthInMeters setup.boxWidth
  positiveDepictedQuantumNumber : 0 < setup.depictedQuantumNumber
  positiveLevelEnergy : ∀ n : ℕ, 0 < n →
    0 < energyInJoules (setup.energyLevel n)

/-!
Nodal law for one-dimensional infinite-well stationary states: the `n`th
state has `n` lobes and `n - 1` interior nodes.  It is a general governing
relation between the raw figure counts and the state's independent quantum
number, not an assumption that the depicted state is specifically `n = 3`.
-/
structure SatisfiesInfiniteSquareWellNodalLaw
    (setup : ElectronRigidBoxSetup) : Prop where
  lobeCountEqualsQuantumNumber :
    setup.figure.lobeCount = setup.depictedQuantumNumber
  interiorNodesPlusOneEqualsQuantumNumber :
    setup.figure.interiorNodeCount + 1 = setup.depictedQuantumNumber

/-!
Energy scaling for a particle in a fixed one-dimensional infinite square
well: `E_n = n^2 E_1` for each positive integer `n`.  This is the smallest
local governing-law interface needed here; it neither fixes `E_1` nor mentions
the displayed answer.
-/
structure SatisfiesInfiniteSquareWellEnergyScaling
    (setup : ElectronRigidBoxSetup) : Prop where
  energyScalesQuadratically : ∀ n : ℕ, 0 < n →
    energyInElectronVolts (setup.energyLevel n) =
      (n : ℝ) ^ 2 * energyInElectronVolts (setup.energyLevel 1)

/-! ## Derived state identification and answer semantics -/

/-- The two interior nodes and three lobes identify the plotted state as `n = 3`. -/
lemma suppliedFigure_depicts_thirdStationaryState
    (setup : ElectronRigidBoxSetup)
    (_figure : MatchesSuppliedWaveFunctionFigure setup.figure)
    (_nodalLaw : SatisfiesInfiniteSquareWellNodalLaw setup) :
    setup.depictedQuantumNumber = 3 := by
  exact
    _nodalLaw.lobeCountEqualsQuantumNumber.symm.trans
      _figure.exactlyThreeLobes

/-- Labels of the four ground-state-energy choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Energy printed beside each answer choice, in electron volts. -/
def AnswerChoice.energyElectronVolts : AnswerChoice → ℝ
  | .A => 0.8
  | .B => 1.1
  | .C => 1.3
  | .D => 1.7

/-- Dataset metadata recording answer C; deliberately not used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Absolute error between the physical ground energy and a displayed choice. -/
def groundStateChoiceErrorElectronVolts
    (setup : ElectronRigidBoxSetup) (choice : AnswerChoice) : ℝ :=
  |energyInElectronVolts (setup.energyLevel 1) -
    choice.energyElectronVolts|

/-- Agreement with an energy displayed to the nearest tenth of an electron volt. -/
def AgreesWhenRoundedToNearestTenthElectronVolt
    (setup : ElectronRigidBoxSetup) (choice : AnswerChoice) : Prop :=
  groundStateChoiceErrorElectronVolts setup choice < (1 / 20 : ℝ)

/-- The selected choice is strictly nearer than every other displayed energy. -/
def IsUniqueNearestGroundStateEnergyChoice
    (setup : ElectronRigidBoxSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    groundStateChoiceErrorElectronVolts setup choice <
      groundStateChoiceErrorElectronVolts setup other

/-!
The three-lobed plot identifies `n = 3`.  Since `E_3 = 12.0 eV` and rigid-box
energies scale as `n^2`, the exact ground energy is `4/3 eV`, which rounds to
`1.3 eV` and uniquely selects choice C.

This formalizes `thm:physics:phyx_mini_0657:target`.  Neither `4/3 eV`,
`1.3 eV`, nor choice C occurs in any theorem premise.
-/
theorem problem_phyx_mini_0657
    (setup : ElectronRigidBoxSetup)
    (_scenario : MatchesElectronRigidBoxScenario setup)
    (_figure : MatchesSuppliedWaveFunctionFigure setup.figure)
    (_energyReadout : MatchesGivenDepictedEnergy setup)
    (_physical : HasPhysicalRigidBoxParameters setup)
    (_nodalLaw : SatisfiesInfiniteSquareWellNodalLaw setup)
    (_energyLaw : SatisfiesInfiniteSquareWellEnergyScaling setup) :
    energyInElectronVolts (setup.energyLevel 1) = (4 / 3 : ℝ) ∧
      AgreesWhenRoundedToNearestTenthElectronVolt setup .C ∧
      IsUniqueNearestGroundStateEnergyChoice setup .C := by
  have hQuantum :=
    suppliedFigure_depicts_thirdStationaryState setup _figure _nodalLaw
  have hMeasured := _energyReadout.depictedEnergyElectronVolts
  rw [hQuantum] at hMeasured
  have hScaling := _energyLaw.energyScalesQuadratically 3 (by norm_num)
  norm_num at hScaling hMeasured
  have hGround :
      energyInElectronVolts (setup.energyLevel 1) = (4 / 3 : ℝ) := by
    linarith [hScaling, hMeasured]
  have hC :
      groundStateChoiceErrorElectronVolts setup .C = (1 / 30 : ℝ) := by
    norm_num [groundStateChoiceErrorElectronVolts, hGround,
      AnswerChoice.energyElectronVolts, abs_of_nonneg, abs_of_nonpos]
  have hA :
      groundStateChoiceErrorElectronVolts setup .A = (8 / 15 : ℝ) := by
    norm_num [groundStateChoiceErrorElectronVolts, hGround,
      AnswerChoice.energyElectronVolts, abs_of_nonneg, abs_of_nonpos]
  have hB :
      groundStateChoiceErrorElectronVolts setup .B = (7 / 30 : ℝ) := by
    norm_num [groundStateChoiceErrorElectronVolts, hGround,
      AnswerChoice.energyElectronVolts, abs_of_nonneg, abs_of_nonpos]
  have hD :
      groundStateChoiceErrorElectronVolts setup .D = (11 / 30 : ℝ) := by
    norm_num [groundStateChoiceErrorElectronVolts, hGround,
      AnswerChoice.energyElectronVolts, abs_of_nonneg, abs_of_nonpos]
  refine ⟨hGround, ?_, ?_⟩
  · rw [AgreesWhenRoundedToNearestTenthElectronVolt, hC]
    norm_num
  · rw [IsUniqueNearestGroundStateEnergyChoice]
    intro other hother
    cases other
    · rw [hC, hA]
      norm_num
    · rw [hC, hB]
      norm_num
    · simp at hother
    · rw [hC, hD]
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0657
