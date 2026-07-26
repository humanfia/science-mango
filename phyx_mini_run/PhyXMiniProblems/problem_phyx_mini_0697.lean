import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0697

open Dimension

/-!
# Center of mass and pointwise tangential acceleration of a uniform rod

The pictured thin rod occupies the interval from `0` to `L` on the positive
x-axis.  A cell of width `dx` at coordinate `x` has the displayed mass law
`dm = (M / L) dx`.  The corresponding first-moment law places the center of
mass halfway along the rod.

The numerical rod has length `1.60 m`, rotates about its center of mass, and
has angular-acceleration magnitude `6.0 rad/s²`.  Tangential acceleration is
not constant along a rod: at coordinate `x` its magnitude is
`α * |x - xCM|`.  Consequently, the recorded value `4.8 m/s²` is the value at
either endpoint (and the maximum over the rod), while the center has value
zero.  No endpoint interpretation is included among the source assumptions.

Physical quantities below use Physlib's unit-independent `Dimensionful`
representation.  Real numbers are used only for coherent SI readouts,
coordinates in the figure, and displayed numerical answer values.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative mass per unit length. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- An angular-acceleration magnitude; radians are dimensionless. -/
abbrev AngularAccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative tangential-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Kilogram-per-metre readout of a linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Radian-per-second-squared readout of angular-acceleration magnitude. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of tangential-acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Rod, numerical experiment, and primary-figure vocabulary -/

/-- A thin uniform rod together with its independent center-of-mass observable. -/
structure ThinUniformRod where
  totalMass : MassQuantity
  totalLength : LengthQuantity
  linearMassDensity : LinearMassDensityQuantity
  centerOfMassFromLeftEndpoint : LengthQuantity

/-- Features explicitly visible or printed in the supplied image. -/
inductive FigureFeature where
  | horizontalXAxis
  | verticalYAxis
  | originLabel
  | rod
  | lengthLabelL
  | highlightedCell
  | positionLabelX
  | widthLabelDx
  | cellMassAnnotation
  deriving DecidableEq, Fintype, Repr

/-- Orientation of the rod relative to the Cartesian axes in the image. -/
inductive RodFigureOrientation where
  | alongPositiveXAxis
  | other
  deriving DecidableEq, Repr

/-!
Literal geometric and scalar data transcribed from the primary image.  Cell
values are SI coordinate readouts of the schematic `x`, `dx`, and `dm`; the
underlying rod quantities remain dimensionful.
-/
structure UniformRodFigure where
  shows : FigureFeature → Bool
  rodOrientation : RodFigureOrientation
  rodLeftCoordinateInMeters : ℝ
  rodRightCoordinateInMeters : ℝ
  cellPositionInMeters : ℝ
  cellWidthInMeters : ℝ
  cellMassInKilograms : ℝ

/-- Axis about which the numerical rod rotates. -/
inductive RotationAxis where
  | throughCenterOfMass
  | other
  deriving DecidableEq, Repr

/-!
The physical rotating-rod experiment.  Tangential acceleration is a
dimensionful observable at every SI coordinate, rather than a single scalar
attached to the entire rod.  Its governing law is imposed only on coordinates
inside the material interval.
-/
structure RotatingRodExperiment where
  rod : ThinUniformRod
  figure : UniformRodFigure
  rotationAxis : RotationAxis
  angularAccelerationMagnitude : AngularAccelerationMagnitudeQuantity
  tangentialAccelerationMagnitudeAtPositionInMeters :
    ℝ → AccelerationMagnitudeQuantity

/-! ## Figure evidence, source data, and governing physical laws -/

/-!
Primary-image transcription.  The last field is exactly the small-cell law
`dm = (M/L) dx`; it records source evidence about uniformity and contains no
center-of-mass or acceleration conclusion.
-/
structure MatchesPrimaryRodFigure
    (experiment : RotatingRodExperiment) : Prop where
  everyNamedFeatureShown :
    ∀ feature, experiment.figure.shows feature = true
  rodLiesOnPositiveXAxis :
    experiment.figure.rodOrientation = .alongPositiveXAxis
  rodStartsAtOrigin :
    experiment.figure.rodLeftCoordinateInMeters = 0
  rodEndsAtLengthLabel :
    experiment.figure.rodRightCoordinateInMeters =
      lengthInMeters experiment.rod.totalLength
  cellPositionNonnegative :
    0 ≤ experiment.figure.cellPositionInMeters
  cellWidthPositive :
    0 < experiment.figure.cellWidthInMeters
  cellLiesWithinRod :
    experiment.figure.cellPositionInMeters +
        experiment.figure.cellWidthInMeters ≤
      lengthInMeters experiment.rod.totalLength
  annotatedCellMassLaw :
    experiment.figure.cellMassInKilograms =
      (massInKilograms experiment.rod.totalMass /
          lengthInMeters experiment.rod.totalLength) *
        experiment.figure.cellWidthInMeters

/-!
The continuum model for a uniform thin rod on `[0,L]`.  It states positivity,
constant density, recovery of total mass by integration, and the first-moment
characterization of the independent center-of-mass observable.  It does not
state that the center is at `L/2`.
-/
structure ObeysThinUniformRodMassModel (rod : ThinUniformRod) : Prop where
  totalLengthPositive :
    0 < lengthInMeters rod.totalLength
  totalMassPositive :
    0 < massInKilograms rod.totalMass
  densityIsMassPerLength :
    linearMassDensityInKilogramsPerMeter rod.linearMassDensity =
      massInKilograms rod.totalMass / lengthInMeters rod.totalLength
  totalMassIsDensityIntegral :
    massInKilograms rod.totalMass =
      ∫ _positionMeters in (0 : ℝ)..lengthInMeters rod.totalLength,
        linearMassDensityInKilogramsPerMeter rod.linearMassDensity
  centerOfMassSatisfiesFirstMomentLaw :
    massInKilograms rod.totalMass *
        lengthInMeters rod.centerOfMassFromLeftEndpoint =
      ∫ positionMeters in (0 : ℝ)..lengthInMeters rod.totalLength,
        positionMeters *
          linearMassDensityInKilogramsPerMeter rod.linearMassDensity

/-!
Only the printed numerical data and stated rotation axis are recorded here.
In particular, the source does not select a requested endpoint or assert a
single tangential acceleration for the entire rod.
-/
structure MatchesRotatingRodProblem
    (experiment : RotatingRodExperiment) : Prop where
  rodLengthMeters :
    lengthInMeters experiment.rod.totalLength = 8 / 5
  angularAccelerationRadiansPerSecondSquared :
    angularAccelerationInRadiansPerSecondSquared
        experiment.angularAccelerationMagnitude = 6
  rotatesAboutCenterOfMass :
    experiment.rotationAxis = .throughCenterOfMass

/-!
Pointwise rigid-rotation kinematics.  When the axis is through the center of
mass, the radius of material coordinate `x` is `|x - xCM|`, and the standard
magnitude law is `aₜ = α r`.  No numerical endpoint value occurs in this law.
-/
structure ObeysRigidRotationKinematics
    (experiment : RotatingRodExperiment) : Prop where
  tangentialAccelerationLawAtPosition :
    experiment.rotationAxis = .throughCenterOfMass →
      ∀ positionMeters : ℝ,
        0 ≤ positionMeters →
        positionMeters ≤ lengthInMeters experiment.rod.totalLength →
        accelerationInMetersPerSecondSquared
            (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
              positionMeters) =
          angularAccelerationInRadiansPerSecondSquared
              experiment.angularAccelerationMagnitude *
            abs (positionMeters -
              lengthInMeters
                experiment.rod.centerOfMassFromLeftEndpoint)

/-!
This predicate expresses the literal but physically inappropriate reading
that one tangential-acceleration value applies at every point of the rod.
Its negation is a derived conclusion for the nonzero-angular-acceleration
experiment.
-/
def HasPositionIndependentTangentialAcceleration
    (experiment : RotatingRodExperiment) : Prop :=
  ∃ accelerationReadout : ℝ,
    ∀ positionMeters : ℝ,
      0 ≤ positionMeters →
      positionMeters ≤ lengthInMeters experiment.rod.totalLength →
      accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
            positionMeters) = accelerationReadout

/-! ## Center-of-mass and pointwise acceleration conclusions -/

/-- Uniform density and the first-moment law put the center at `L/2`. -/
lemma thinUniformRod_centerOfMass
    (rod : ThinUniformRod)
    (h_massModel : ObeysThinUniformRodMassModel rod) :
    lengthInMeters rod.centerOfMassFromLeftEndpoint =
      lengthInMeters rod.totalLength / 2 := by
  let L := lengthInMeters rod.totalLength
  have h_integral_id : (∫ x in (0 : ℝ)..L, x) = L ^ 2 / 2 := by
    have hsymm :
        (∫ x in (0 : ℝ)..L, L - x) = ∫ x in (0 : ℝ)..L, x := by
      simpa using
        (intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) L
          (a := (0 : ℝ)) (b := L))
    have hsub :
        (∫ x in (0 : ℝ)..L, L - x) =
          (∫ _x in (0 : ℝ)..L, L) - ∫ x in (0 : ℝ)..L, x := by
      exact intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable 0 L)
        (continuous_id.intervalIntegrable 0 L)
    rw [intervalIntegral.integral_const] at hsub
    norm_num at hsub
    nlinarith [hsymm, hsub]
  have h_firstMoment :=
    h_massModel.centerOfMassSatisfiesFirstMomentLaw
  rw [intervalIntegral.integral_mul_const, h_integral_id,
    h_massModel.densityIsMassPerLength] at h_firstMoment
  have hL : L ≠ 0 := ne_of_gt h_massModel.totalLengthPositive
  dsimp [L] at hL h_firstMoment ⊢
  field_simp [hL] at h_firstMoment
  nlinarith [h_firstMoment, h_massModel.totalMassPositive]

/-- For the stated `1.60 m` rod, the midpoint is `0.80 m`. -/
lemma numericalRod_centerOfMass
    (experiment : RotatingRodExperiment)
    (h_massModel : ObeysThinUniformRodMassModel experiment.rod)
    (h_problem : MatchesRotatingRodProblem experiment) :
    lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint = 4 / 5 := by
  calc
    lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint =
        lengthInMeters experiment.rod.totalLength / 2 :=
      thinUniformRod_centerOfMass experiment.rod h_massModel
    _ = 4 / 5 := by rw [h_problem.rodLengthMeters]; norm_num

/-- The acceleration profile is `6 * |x - 0.8| m/s²` on the rod. -/
lemma numericalRod_tangentialAccelerationProfile
    (experiment : RotatingRodExperiment)
    (h_massModel : ObeysThinUniformRodMassModel experiment.rod)
    (h_problem : MatchesRotatingRodProblem experiment)
    (h_rotation : ObeysRigidRotationKinematics experiment) :
    ∀ positionMeters : ℝ,
      0 ≤ positionMeters →
      positionMeters ≤ lengthInMeters experiment.rod.totalLength →
      accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
            positionMeters) =
        6 * abs (positionMeters - 4 / 5) := by
  intro positionMeters h_position_nonnegative h_position_le_length
  have h_acceleration :=
    h_rotation.tangentialAccelerationLawAtPosition
      h_problem.rotatesAboutCenterOfMass positionMeters
      h_position_nonnegative h_position_le_length
  rw [h_problem.angularAccelerationRadiansPerSecondSquared,
    numericalRod_centerOfMass experiment h_massModel h_problem] at h_acceleration
  exact h_acceleration

/-- Both endpoints have tangential-acceleration magnitude `4.8 m/s²`. -/
lemma endpoint_tangentialAccelerations
    (experiment : RotatingRodExperiment)
    (h_massModel : ObeysThinUniformRodMassModel experiment.rod)
    (h_problem : MatchesRotatingRodProblem experiment)
    (h_rotation : ObeysRigidRotationKinematics experiment) :
    accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters 0) =
        24 / 5 ∧
      accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
            (lengthInMeters experiment.rod.totalLength)) =
        24 / 5 := by
  have h_length_nonnegative :
      0 ≤ lengthInMeters experiment.rod.totalLength := by
    rw [h_problem.rodLengthMeters]
    norm_num
  have h_profile :=
    numericalRod_tangentialAccelerationProfile experiment h_massModel
      h_problem h_rotation
  constructor
  · have h_left := h_profile 0 (by norm_num) h_length_nonnegative
    norm_num at h_left
    exact h_left
  · have h_right :=
      h_profile (lengthInMeters experiment.rod.totalLength)
        h_length_nonnegative le_rfl
    rw [h_problem.rodLengthMeters] at h_right
    norm_num at h_right
    rw [h_problem.rodLengthMeters]
    exact h_right

/-- The point on the rotation axis has zero tangential acceleration. -/
lemma center_tangentialAcceleration
    (experiment : RotatingRodExperiment)
    (h_massModel : ObeysThinUniformRodMassModel experiment.rod)
    (h_problem : MatchesRotatingRodProblem experiment)
    (h_rotation : ObeysRigidRotationKinematics experiment) :
    accelerationInMetersPerSecondSquared
        (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
          (lengthInMeters
            experiment.rod.centerOfMassFromLeftEndpoint)) = 0 := by
  have h_center_nonnegative :
      0 ≤ lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint := by
    rw [numericalRod_centerOfMass experiment h_massModel h_problem]
    norm_num
  have h_center_le_length :
      lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint ≤
        lengthInMeters experiment.rod.totalLength := by
    rw [numericalRod_centerOfMass experiment h_massModel h_problem,
      h_problem.rodLengthMeters]
    norm_num
  have h_acceleration :=
    h_rotation.tangentialAccelerationLawAtPosition
      h_problem.rotatesAboutCenterOfMass
      (lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint)
      h_center_nonnegative h_center_le_length
  rw [sub_self, abs_zero, mul_zero] at h_acceleration
  exact h_acceleration

/-- `4.8 m/s²` is an upper bound attained at both rod endpoints. -/
lemma tangentialAcceleration_le_endpointValue
    (experiment : RotatingRodExperiment)
    (h_massModel : ObeysThinUniformRodMassModel experiment.rod)
    (h_problem : MatchesRotatingRodProblem experiment)
    (h_rotation : ObeysRigidRotationKinematics experiment) :
    ∀ positionMeters : ℝ,
      0 ≤ positionMeters →
      positionMeters ≤ lengthInMeters experiment.rod.totalLength →
      accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
            positionMeters) ≤ 24 / 5 := by
  intro positionMeters h_position_nonnegative h_position_le_length
  have h_position_le_numerical_length : positionMeters ≤ 8 / 5 := by
    rw [h_problem.rodLengthMeters] at h_position_le_length
    exact h_position_le_length
  have h_abs : abs (positionMeters - 4 / 5) ≤ 4 / 5 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [numericalRod_tangentialAccelerationProfile experiment h_massModel
    h_problem h_rotation positionMeters h_position_nonnegative
    h_position_le_length]
  nlinarith

/-- The rod does not have one position-independent tangential acceleration. -/
lemma tangentialAcceleration_not_positionIndependent
    (experiment : RotatingRodExperiment)
    (h_massModel : ObeysThinUniformRodMassModel experiment.rod)
    (h_problem : MatchesRotatingRodProblem experiment)
    (h_rotation : ObeysRigidRotationKinematics experiment) :
    ¬ HasPositionIndependentTangentialAcceleration experiment := by
  rintro ⟨accelerationReadout, h_constant⟩
  have h_length_nonnegative :
      0 ≤ lengthInMeters experiment.rod.totalLength := by
    rw [h_problem.rodLengthMeters]
    norm_num
  have h_center_nonnegative :
      0 ≤ lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint := by
    rw [numericalRod_centerOfMass experiment h_massModel h_problem]
    norm_num
  have h_center_le_length :
      lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint ≤
        lengthInMeters experiment.rod.totalLength := by
    rw [numericalRod_centerOfMass experiment h_massModel h_problem,
      h_problem.rodLengthMeters]
    norm_num
  have h_at_left := h_constant 0 (by norm_num) h_length_nonnegative
  have h_at_center :=
    h_constant
      (lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint)
      h_center_nonnegative h_center_le_length
  have h_left_value :=
    (endpoint_tangentialAccelerations experiment h_massModel h_problem
      h_rotation).1
  have h_center_value :=
    center_tangentialAcceleration experiment h_massModel h_problem h_rotation
  rw [h_left_value] at h_at_left
  rw [h_center_value] at h_at_center
  norm_num at h_at_left h_at_center
  linarith

/-! ## Displayed-answer metadata -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- SI tangential-acceleration number printed beside each answer label. -/
def AnswerChoice.tangentialAccelerationInMetersPerSecondSquared :
    AnswerChoice → ℝ
  | .A => 19 / 5
  | .B => 29 / 5
  | .C => 24 / 5
  | .D => 43 / 10

/-- Answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A displayed number matches the physical acceleration at a specified material
coordinate.  Requiring the coordinate prevents answer metadata from silently
selecting an endpoint.
-/
def MatchesDisplayedTangentialAccelerationAtPosition
    (experiment : RotatingRodExperiment)
    (positionMeters : ℝ) (choice : AnswerChoice) : Prop :=
  accelerationInMetersPerSecondSquared
      (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
        positionMeters) =
    choice.tangentialAccelerationInMetersPerSecondSquared

/-!
Blueprint label: `thm:physics:phyx_mini_0697:target`.

The model derives `xCM = L/2 = 0.80 m` and the full pointwise acceleration
profile.  Both endpoints attain the recorded `4.8 m/s²`, the center has zero
acceleration, every material point is bounded by the endpoint value, and the
rod has no single position-independent tangential acceleration.  Thus the
recorded choice is supported only as an endpoint/maximum value, not as a
source-specified acceleration of the rod as a whole.
-/
theorem problem_phyx_mini_0697
    (experiment : RotatingRodExperiment)
    (h_figure : MatchesPrimaryRodFigure experiment)
    (h_massModel : ObeysThinUniformRodMassModel experiment.rod)
    (h_problem : MatchesRotatingRodProblem experiment)
    (h_rotation : ObeysRigidRotationKinematics experiment) :
    lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint =
        lengthInMeters experiment.rod.totalLength / 2 ∧
      lengthInMeters experiment.rod.centerOfMassFromLeftEndpoint = 4 / 5 ∧
      (∀ positionMeters : ℝ,
        0 ≤ positionMeters →
        positionMeters ≤ lengthInMeters experiment.rod.totalLength →
        accelerationInMetersPerSecondSquared
            (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
              positionMeters) =
          6 * abs (positionMeters - 4 / 5)) ∧
      accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters 0) =
        24 / 5 ∧
      accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
            (lengthInMeters experiment.rod.totalLength)) =
        24 / 5 ∧
      accelerationInMetersPerSecondSquared
          (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
            (lengthInMeters
              experiment.rod.centerOfMassFromLeftEndpoint)) = 0 ∧
      (∀ positionMeters : ℝ,
        0 ≤ positionMeters →
        positionMeters ≤ lengthInMeters experiment.rod.totalLength →
        accelerationInMetersPerSecondSquared
            (experiment.tangentialAccelerationMagnitudeAtPositionInMeters
              positionMeters) ≤ 24 / 5) ∧
      MatchesDisplayedTangentialAccelerationAtPosition
        experiment 0 recordedAnswerChoice ∧
      MatchesDisplayedTangentialAccelerationAtPosition experiment
        (lengthInMeters experiment.rod.totalLength) recordedAnswerChoice ∧
      ¬ HasPositionIndependentTangentialAcceleration experiment := by
  have _h_figure := h_figure
  have h_center_of_mass :=
    thinUniformRod_centerOfMass experiment.rod h_massModel
  have h_numerical_center :=
    numericalRod_centerOfMass experiment h_massModel h_problem
  have h_profile :=
    numericalRod_tangentialAccelerationProfile experiment h_massModel
      h_problem h_rotation
  rcases endpoint_tangentialAccelerations experiment h_massModel h_problem
      h_rotation with ⟨h_left_endpoint, h_right_endpoint⟩
  have h_center_acceleration :=
    center_tangentialAcceleration experiment h_massModel h_problem h_rotation
  have h_upper_bound :=
    tangentialAcceleration_le_endpointValue experiment h_massModel h_problem
      h_rotation
  have h_not_constant :=
    tangentialAcceleration_not_positionIndependent experiment h_massModel
      h_problem h_rotation
  refine ⟨h_center_of_mass, h_numerical_center, h_profile,
    h_left_endpoint, h_right_endpoint, h_center_acceleration, h_upper_bound,
    ?_, ?_, h_not_constant⟩
  · simpa [MatchesDisplayedTangentialAccelerationAtPosition,
      recordedAnswerChoice,
      AnswerChoice.tangentialAccelerationInMetersPerSecondSquared] using
      h_left_endpoint
  · simpa [MatchesDisplayedTangentialAccelerationAtPosition,
      recordedAnswerChoice,
      AnswerChoice.tangentialAccelerationInMetersPerSecondSquared] using
      h_right_endpoint

end PhyXMiniProblems.ProblemPhyXMini0697
