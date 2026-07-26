import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0377

open Dimension
open scoped BigOperators

/-!
# RMS speed of a six-molecule two-dimensional gas

The primary figure gives one planar velocity vector for each of six labelled
molecules.  The vector coordinates are coherent-SI readouts in metres per
second.  The physical velocity vectors and RMS speed remain unit-independent
dimensionful quantities; real numbers are used only for coordinate readouts,
squared-speed readouts, and the displayed multiple-choice values.
-/

/-! ## Dimensionful velocities and coherent-SI readouts -/

/-- The two coordinate directions denoted by `i-hat` and `j-hat` in the figure. -/
inductive PlanarAxis where
  | iHat
  | jHat
  deriving DecidableEq, Fintype, Repr

/-!
A planar physical velocity.  Its Euclidean vector carries the dimension
`length / time`, independently of any chosen unit system.
-/
abbrev PlanarVelocity : Type :=
  Dimensionful
    (WithDim (L𝓭 * T𝓭⁻¹) (EuclideanSpace ℝ PlanarAxis))

/-- The vector of `i-hat` and `j-hat` velocity components in metres per second. -/
def componentsInMetersPerSecond (velocity : PlanarVelocity) :
    EuclideanSpace ℝ PlanarAxis :=
  (velocity UnitChoices.SI).val

/-- The squared Euclidean speed readout, in square metres per square second. -/
def speedSquaredInMetersSquaredPerSecondSquared
    (velocity : PlanarVelocity) : ℝ :=
  ‖componentsInMetersPerSecond velocity‖ ^ 2

/-- The coherent-SI readout of a dimensionful speed, in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Molecule labels and primary-figure data -/

/-- The six black dots labelled `1` through `6` in the primary figure. -/
inductive MoleculeLabel where
  | one
  | two
  | three
  | four
  | five
  | six
  deriving DecidableEq, Fintype, Repr

/-!
The physical state pictured in the problem.  Each molecule has an independent
dimensionful planar velocity; no RMS value or answer choice is stored here.
-/
structure SixMoleculeGasSnapshot where
  velocity : MoleculeLabel → PlanarVelocity

/-!
The twelve signed component readouts printed next to the six velocity arrows.
The image is treated as primary evidence: in particular molecule `4` is read
as `-10 i-hat - 2 j-hat` metres per second.
-/
structure MatchesProblemAndPrimaryFigure
    (snapshot : SixMoleculeGasSnapshot) : Prop where
  molecule_one_i :
    componentsInMetersPerSecond (snapshot.velocity .one) .iHat = 10
  molecule_one_j :
    componentsInMetersPerSecond (snapshot.velocity .one) .jHat = -10
  molecule_two_i :
    componentsInMetersPerSecond (snapshot.velocity .two) .iHat = 2
  molecule_two_j :
    componentsInMetersPerSecond (snapshot.velocity .two) .jHat = 15
  molecule_three_i :
    componentsInMetersPerSecond (snapshot.velocity .three) .iHat = -8
  molecule_three_j :
    componentsInMetersPerSecond (snapshot.velocity .three) .jHat = 6
  molecule_four_i :
    componentsInMetersPerSecond (snapshot.velocity .four) .iHat = -10
  molecule_four_j :
    componentsInMetersPerSecond (snapshot.velocity .four) .jHat = -2
  molecule_five_i :
    componentsInMetersPerSecond (snapshot.velocity .five) .iHat = 6
  molecule_five_j :
    componentsInMetersPerSecond (snapshot.velocity .five) .jHat = 5
  molecule_six_i :
    componentsInMetersPerSecond (snapshot.velocity .six) .iHat = 0
  molecule_six_j :
    componentsInMetersPerSecond (snapshot.velocity .six) .jHat = -14

/-! ## Governing RMS law -/

/-!
The RMS speed is the nonnegative speed whose square is the arithmetic mean of
the molecules' squared Euclidean speeds.  The law is generic over the pictured
snapshot and contains none of the numerical answer values.
-/
structure SatisfiesRmsSpeedLaw
    (snapshot : SixMoleculeGasSnapshot) (rmsSpeed : DimSpeed) : Prop where
  rms_speed_squared_is_mean :
    (speedInMetersPerSecond rmsSpeed) ^ 2 =
      (∑ molecule : MoleculeLabel,
          speedSquaredInMetersSquaredPerSecondSquared
            (snapshot.velocity molecule)) /
        (Fintype.card MoleculeLabel : ℝ)

/-! ## Derived exact value and displayed answer -/

/-!
The six squared speeds shown in the figure sum to
`200 + 229 + 100 + 104 + 61 + 196 = 890 m²/s²`.
-/
lemma sumOfSquaredSpeeds_fromPrimaryFigure
    (snapshot : SixMoleculeGasSnapshot)
    (_figure : MatchesProblemAndPrimaryFigure snapshot) :
    (∑ molecule : MoleculeLabel,
        speedSquaredInMetersSquaredPerSecondSquared
          (snapshot.velocity molecule)) = 890 := by
  classical
  simp only [speedSquaredInMetersSquaredPerSecondSquared,
    EuclideanSpace.real_norm_sq_eq]
  have hAxes : (Finset.univ : Finset PlanarAxis) = {.iHat, .jHat} := by
    decide
  have hMolecules : (Finset.univ : Finset MoleculeLabel) =
      {.one, .two, .three, .four, .five, .six} := by
    decide
  have hSquaredSpeed (molecule : MoleculeLabel) :
      (∑ axis : PlanarAxis,
          (componentsInMetersPerSecond
            (snapshot.velocity molecule)) axis ^ 2) =
        (componentsInMetersPerSecond
            (snapshot.velocity molecule)) .iHat ^ 2 +
          (componentsInMetersPerSecond
            (snapshot.velocity molecule)) .jHat ^ 2 := by
    rw [hAxes, Finset.sum_pair (by decide : PlanarAxis.iHat ≠ .jHat)]
  rw [hMolecules]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide : MoleculeLabel.five ≠ .six)]
  simp_rw [hSquaredSpeed]
  norm_num [
    _figure.molecule_one_i, _figure.molecule_one_j,
    _figure.molecule_two_i, _figure.molecule_two_j,
    _figure.molecule_three_i, _figure.molecule_three_j,
    _figure.molecule_four_i, _figure.molecule_four_j,
    _figure.molecule_five_i, _figure.molecule_five_j,
    _figure.molecule_six_i, _figure.molecule_six_j]

/-!
The exact RMS speed readout is `sqrt (890 / 6) = sqrt (445 / 3)` metres per
second.  This is kept separate from the rounded multiple-choice display.
-/
lemma rmsSpeed_exact
    (snapshot : SixMoleculeGasSnapshot)
    (rmsSpeed : DimSpeed)
    (_figure : MatchesProblemAndPrimaryFigure snapshot)
    (_rmsLaw : SatisfiesRmsSpeedLaw snapshot rmsSpeed) :
    speedInMetersPerSecond rmsSpeed = Real.sqrt ((445 : ℝ) / 3) := by
  have hSquared := _rmsLaw.rms_speed_squared_is_mean
  rw [sumOfSquaredSpeeds_fromPrimaryFigure snapshot _figure] at hSquared
  have hCard : Fintype.card MoleculeLabel = 6 := by
    decide
  rw [hCard] at hSquared
  norm_num at hSquared
  have hNonnegative : 0 ≤ speedInMetersPerSecond rmsSpeed := by
    exact NNReal.coe_nonneg _
  calc
    speedInMetersPerSecond rmsSpeed =
        |speedInMetersPerSecond rmsSpeed| := by
      rw [abs_of_nonneg hNonnegative]
    _ = Real.sqrt ((speedInMetersPerSecond rmsSpeed) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ((445 : ℝ) / 3) := congrArg Real.sqrt hSquared

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The speed displayed beside each answer label, in metres per second. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 61 / 5
  | .B => 25 / 2
  | .C => 91 / 5
  | .D => 51 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
Agreement with a speed displayed to the nearest `0.1 m/s`.  The tolerance is
`0.05 m/s`, half a unit in the last displayed digit.
-/
def MatchesAnswerChoice (rmsSpeed : DimSpeed) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond rmsSpeed - choice.speedInMetersPerSecond| ≤
    1 / 20

/-!
For the six dimensionful velocities in the primary figure, the exact RMS
speed is `sqrt (445 / 3) m/s`, which rounds to recorded answer A, `12.2 m/s`.

Blueprint: `thm:physics:phyx_mini_0377:target`.
-/
theorem problem_phyx_mini_0377
    (snapshot : SixMoleculeGasSnapshot)
    (rmsSpeed : DimSpeed)
    (_figure : MatchesProblemAndPrimaryFigure snapshot)
    (_rmsLaw : SatisfiesRmsSpeedLaw snapshot rmsSpeed) :
    speedInMetersPerSecond rmsSpeed = Real.sqrt ((445 : ℝ) / 3) ∧
      MatchesAnswerChoice rmsSpeed recordedAnswerChoice := by
  have hExact := rmsSpeed_exact snapshot rmsSpeed _figure _rmsLaw
  refine ⟨hExact, ?_⟩
  simp only [MatchesAnswerChoice, recordedAnswerChoice,
    AnswerChoice.speedInMetersPerSecond, hExact]
  rw [abs_le]
  constructor
  · have hLower :
        (243 : ℝ) / 20 ≤ Real.sqrt ((445 : ℝ) / 3) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    norm_num at hLower ⊢
    linarith
  · have hUpper :
        Real.sqrt ((445 : ℝ) / 3) ≤ (49 : ℝ) / 4 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    norm_num at hUpper ⊢
    linarith

end PhyXMiniProblems.ProblemPhyXMini0377
