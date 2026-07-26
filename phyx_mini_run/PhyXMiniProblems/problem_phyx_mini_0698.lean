import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0698

open Dimension

/-!
# Angular speed of a triangular three-mass widget

Three point masses are joined by lightweight rods to form a right triangle.
The widget rotates in the plane of the supplied figure about the axle through
the right-angle corner.  The primary bitmap places the `300 g` mass on the
axle, the `250 g` mass `8.0 cm` horizontally from it, and the `150 g` mass
`6.0 cm` vertically from it.  The curved arrow labelled `ω` is
counterclockwise.

Mass, length, angular speed, moment of inertia, and energy retain their
physical dimensions through Physlib's unit-independent `Dimensionful` type.
Real numbers occur only in named-unit readouts, Physlib's SI-coordinate rigid-
body interface, and the displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative point-mass magnitude. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative length magnitude. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A scalar moment of inertia about the fixed axle, of dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Rotational energy, of dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical mass in the grams printed in the figure. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in the centimetres printed in the figure. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read angular speed in radians per coherent-SI second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Convert a radian-per-second angular-speed readout to revolutions per minute. -/
def angularSpeedInRevolutionsPerMinute
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  angularSpeedInRadiansPerSecond angularSpeed * 60 / (2 * Real.pi)

/-- Read a scalar axial moment of inertia in `kg m²`. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules, calibrated by Physlib's joule. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a physical energy in millijoules. -/
def energyInMillijoules (energy : EnergyQuantity) : ℝ :=
  1000 * energyInJoules energy

/-! ## Primary-figure vocabulary and geometry -/

/-- The three block locations in the supplied triangular diagram. -/
inductive WidgetVertex where
  | bottomLeft
  | top
  | axleCorner
  deriving DecidableEq, Fintype, Repr

/-- The three lightweight rods forming the triangular frame. -/
inductive ConnectingRod where
  | bottomHorizontal
  | rightVertical
  | diagonal
  deriving DecidableEq, Fintype, Repr

/-- Coarse orientation of each rod as it appears on the page. -/
inductive RodOrientation where
  | horizontal
  | vertical
  | diagonalUpRight
  deriving DecidableEq, Repr

/-- The angle marker implied at the junction of the 8 cm and 6 cm rods. -/
inductive VertexAngleKind where
  | rightAngle
  deriving DecidableEq, Repr

/-- Sense of the curved `ω` arrow in the primary bitmap. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Plane in which the problem states that the widget moves. -/
inductive MotionPlane where
  | planeOfPage
  deriving DecidableEq, Repr

/-- Orientation of the axle relative to the page. -/
inductive AxleOrientation where
  | perpendicularToPage
  deriving DecidableEq, Repr

/-- Idealization justified by the description of the rods as lightweight. -/
inductive RodMassModel where
  | negligibleComparedWithBlocks
  deriving DecidableEq, Repr

/-- Qualitative and printed information transcribed from the primary bitmap. -/
structure TriangularWidgetFigure where
  showsBlock : WidgetVertex → Bool
  showsRod : ConnectingRod → Bool
  rodEndpoints : ConnectingRod → WidgetVertex × WidgetVertex
  rodOrientation : ConnectingRod → RodOrientation
  printedMassGrams : WidgetVertex → ℝ
  printedRodLengthCentimeters : ConnectingRod → Option ℝ
  rightAngleVertex : WidgetVertex
  rightAngleKind : VertexAngleKind
  axleVertex : WidgetVertex
  showsOmegaLabel : Bool
  rotationArrowSense : RotationSense

/-! ## Physical setup, image readouts, and governing laws -/

/-!
The physical quantities of the widget.  `rotationalEnergyAt` is an independent
physical energy for each angular speed; it is related to Physlib's rigid-body
energy only in the governing-law structure below.  In particular, neither it
nor any other field is defined from the displayed `92 rpm` answer.
-/
structure TriangularWidgetSetup where
  figure : TriangularWidgetFigure
  pointMass : WidgetVertex → MassQuantity
  rodLength : ConnectingRod → LengthQuantity
  distanceFromAxle : WidgetVertex → LengthQuantity
  momentOfInertiaAboutAxle : MomentOfInertiaQuantity
  targetRotationalEnergy : EnergyQuantity
  rotationalEnergyAt : AngularSpeedQuantity → EnergyQuantity
  rigidBodySI : RigidBody 3
  axleAxis : Fin 3
  angularVelocityVectorRadiansPerSecond :
    AngularSpeedQuantity → Fin 3 → ℝ
  motionPlane : MotionPlane
  axleOrientation : AxleOrientation
  rodMassModel : ConnectingRod → RodMassModel

/-!
Primary-image evidence: all three blocks and rods, their printed mass and
length labels, the right-angle/axle corner, and the counterclockwise `ω` arrow.
The distances from the axle are also read from the two adjacent rods.
-/
structure MatchesPrimaryFigure (setup : TriangularWidgetSetup) : Prop where
  allBlocksShown :
    ∀ vertex : WidgetVertex, setup.figure.showsBlock vertex = true
  allRodsShown :
    ∀ rod : ConnectingRod, setup.figure.showsRod rod = true
  bottomRodEndpoints :
    setup.figure.rodEndpoints .bottomHorizontal =
      (.bottomLeft, .axleCorner)
  verticalRodEndpoints :
    setup.figure.rodEndpoints .rightVertical = (.axleCorner, .top)
  diagonalRodEndpoints :
    setup.figure.rodEndpoints .diagonal = (.bottomLeft, .top)
  bottomRodIsHorizontal :
    setup.figure.rodOrientation .bottomHorizontal = .horizontal
  rightRodIsVertical :
    setup.figure.rodOrientation .rightVertical = .vertical
  thirdRodIsDiagonal :
    setup.figure.rodOrientation .diagonal = .diagonalUpRight
  bottomLeftPrintedMass :
    setup.figure.printedMassGrams .bottomLeft = 250
  topPrintedMass : setup.figure.printedMassGrams .top = 150
  axleCornerPrintedMass :
    setup.figure.printedMassGrams .axleCorner = 300
  physicalMassesMatchPrintedLabels :
    ∀ vertex : WidgetVertex,
      massInGrams (setup.pointMass vertex) =
        setup.figure.printedMassGrams vertex
  bottomRodPrintedLength :
    setup.figure.printedRodLengthCentimeters .bottomHorizontal = some 8
  verticalRodPrintedLength :
    setup.figure.printedRodLengthCentimeters .rightVertical = some 6
  diagonalHasNoPrintedLength :
    setup.figure.printedRodLengthCentimeters .diagonal = none
  physicalBottomRodMatchesLabel :
    lengthInCentimeters (setup.rodLength .bottomHorizontal) = 8
  physicalVerticalRodMatchesLabel :
    lengthInCentimeters (setup.rodLength .rightVertical) = 6
  rightAngleAtAxleCorner :
    setup.figure.rightAngleVertex = .axleCorner ∧
      setup.figure.rightAngleKind = .rightAngle
  axleAtRightAngleCorner : setup.figure.axleVertex = .axleCorner
  bottomLeftDistanceFromAxle :
    lengthInMeters (setup.distanceFromAxle .bottomLeft) = 8 / 100
  topDistanceFromAxle :
    lengthInMeters (setup.distanceFromAxle .top) = 6 / 100
  axleCornerDistanceFromAxle :
    lengthInMeters (setup.distanceFromAxle .axleCorner) = 0
  omegaLabelShown : setup.figure.showsOmegaLabel = true
  arrowIsCounterclockwise :
    setup.figure.rotationArrowSense = .counterclockwise

/-!
Problem-text data and the stated `100 mJ` energy condition.  The rods are
treated as having negligible inertia relative to the three labeled blocks.
-/
structure MatchesProblemData (setup : TriangularWidgetSetup) : Prop where
  rotatesInPlaneOfPage : setup.motionPlane = .planeOfPage
  axleIsPerpendicularToPage :
    setup.axleOrientation = .perpendicularToPage
  rodsHaveNegligibleMass :
    ∀ rod : ConnectingRod,
      setup.rodMassModel rod = .negligibleComparedWithBlocks
  targetEnergyIs100Millijoules :
    energyInMillijoules setup.targetRotationalEnergy = 100

/-- Positivity/nondegeneracy needed to select the physical positive root. -/
structure HasPhysicalParameters (setup : TriangularWidgetSetup) : Prop where
  allPointMassesPositive :
    ∀ vertex : WidgetVertex, 0 < massInKilograms (setup.pointMass vertex)
  bottomRodLengthPositive :
    0 < lengthInMeters (setup.rodLength .bottomHorizontal)
  verticalRodLengthPositive :
    0 < lengthInMeters (setup.rodLength .rightVertical)
  targetEnergyPositive : 0 < energyInJoules setup.targetRotationalEnergy

/-!
Governing laws for the idealized widget.

* Negligible rods leave the three point masses as the complete axial-inertia
  sum `Σ m r²`.
* The scalar inertia is the axle-axis tensor entry of a Physlib `RigidBody 3`.
* Angular velocity points along that axle.
* The physical rotational energy agrees with
  `RigidBody.rotationalKineticEnergy`.

These are general model laws.  They contain neither a target angular speed nor
the displayed `92 rpm` conclusion.
-/
structure SatisfiesTriangularWidgetRotationalLaws
    (setup : TriangularWidgetSetup) : Prop where
  pointMassMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAxle =
      massInKilograms (setup.pointMass .bottomLeft) *
          lengthInMeters (setup.distanceFromAxle .bottomLeft) ^ 2 +
        massInKilograms (setup.pointMass .top) *
          lengthInMeters (setup.distanceFromAxle .top) ^ 2 +
        massInKilograms (setup.pointMass .axleCorner) *
          lengthInMeters (setup.distanceFromAxle .axleCorner) ^ 2
  rigidBodyMassIsSumOfPointMasses :
    setup.rigidBodySI.mass =
      massInKilograms (setup.pointMass .bottomLeft) +
        massInKilograms (setup.pointMass .top) +
        massInKilograms (setup.pointMass .axleCorner)
  axleTensorEntryMatchesScalarInertia :
    setup.rigidBodySI.inertiaTensor setup.axleAxis setup.axleAxis =
      momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAxle
  angularVelocityIsAlongAxle :
    ∀ (angularSpeed : AngularSpeedQuantity) (component : Fin 3),
      setup.angularVelocityVectorRadiansPerSecond angularSpeed component =
        if component = setup.axleAxis then
          angularSpeedInRadiansPerSecond angularSpeed
        else 0
  rotationalEnergyUsesPhyslib :
    ∀ angularSpeed : AngularSpeedQuantity,
      energyInJoules (setup.rotationalEnergyAt angularSpeed) =
        setup.rigidBodySI.rotationalKineticEnergy
          (setup.angularVelocityVectorRadiansPerSecond angularSpeed)

/-! ## Derived physical relations and answer metadata -/

/-- The figure data and point-mass law give `I = 0.00214 kg m²`. -/
lemma momentOfInertiaAboutAxle_eq_107_over_50000
    (setup : TriangularWidgetSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_laws : SatisfiesTriangularWidgetRotationalLaws setup) :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAxle = 107 / 50000 := by
  rw [_laws.pointMassMomentOfInertia]
  have hbl := _figure.physicalMassesMatchPrintedLabels .bottomLeft
  have ht := _figure.physicalMassesMatchPrintedLabels .top
  have ha := _figure.physicalMassesMatchPrintedLabels .axleCorner
  rw [_figure.bottomLeftPrintedMass] at hbl
  rw [_figure.topPrintedMass] at ht
  rw [_figure.axleCornerPrintedMass] at ha
  unfold massInGrams at hbl ht ha
  rw [_figure.bottomLeftDistanceFromAxle, _figure.topDistanceFromAxle,
    _figure.axleCornerDistanceFromAxle]
  norm_num at hbl ht ha ⊢
  nlinarith

/-!
Physlib's tensor contraction reduces to the familiar scalar relation
`K = I ω² / 2` when angular velocity is along the axle.
-/
lemma rotationalEnergy_eq_half_inertia_mul_angularSpeed_sq
    (setup : TriangularWidgetSetup)
    (_laws : SatisfiesTriangularWidgetRotationalLaws setup)
    (angularSpeed : AngularSpeedQuantity) :
    energyInJoules (setup.rotationalEnergyAt angularSpeed) =
      (1 / 2 : ℝ) *
        momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAxle *
        angularSpeedInRadiansPerSecond angularSpeed ^ 2 := by
  rw [_laws.rotationalEnergyUsesPhyslib]
  simp only [RigidBody.rotationalKineticEnergy, dotProduct, Matrix.mulVec]
  simp_rw [_laws.angularVelocityIsAlongAxle]
  simp [_laws.axleTensorEntryMatchesScalarInertia]
  ring

/-!
At `100 mJ`, the positive angular speed therefore satisfies
`ω² = 10000 / 107` in `(rad/s)²`.
-/
lemma targetAngularSpeed_squared_eq_10000_over_107
    (setup : TriangularWidgetSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesTriangularWidgetRotationalLaws setup)
    (angularSpeed : AngularSpeedQuantity)
    (_hasTargetEnergy :
      energyInJoules (setup.rotationalEnergyAt angularSpeed) =
        energyInJoules setup.targetRotationalEnergy) :
    angularSpeedInRadiansPerSecond angularSpeed ^ 2 = 10000 / 107 := by
  have hI := momentOfInertiaAboutAxle_eq_107_over_50000 setup _figure _laws
  have hK := rotationalEnergy_eq_half_inertia_mul_angularSpeed_sq
    setup _laws angularSpeed
  have hE := _data.targetEnergyIs100Millijoules
  unfold energyInMillijoules at hE
  rw [_hasTargetEnergy] at hK
  norm_num at hE hI hK ⊢
  nlinarith

/-- The exact positive-root radian-per-second readout. -/
lemma targetAngularSpeed_eq_sqrt_10000_over_107
    (setup : TriangularWidgetSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesTriangularWidgetRotationalLaws setup)
    (angularSpeed : AngularSpeedQuantity)
    (_angularSpeedPositive :
      0 < angularSpeedInRadiansPerSecond angularSpeed)
    (_hasTargetEnergy :
      energyInJoules (setup.rotationalEnergyAt angularSpeed) =
        energyInJoules setup.targetRotationalEnergy) :
    angularSpeedInRadiansPerSecond angularSpeed =
      Real.sqrt (10000 / 107) := by
  have hsq := targetAngularSpeed_squared_eq_10000_over_107
    setup _figure _data _laws angularSpeed _hasTargetEnergy
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_pos _angularSpeedPositive]

/-- Labels of the four angular-speed choices displayed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Revolutions-per-minute value printed beside each answer label. -/
def AnswerChoice.revolutionsPerMinute : AnswerChoice → ℝ
  | .A => 90
  | .B => 88
  | .C => 92
  | .D => 86

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The physical angular speed agrees with a displayed whole-rpm choice when its
rpm readout rounds to that integer.  This avoids claiming that the unrounded
speed is exactly `92 rpm`.
-/
def RoundsToDisplayedRevolutionsPerMinute
    (angularSpeed : AngularSpeedQuantity) (choice : AnswerChoice) : Prop :=
  choice.revolutionsPerMinute - 1 / 2 ≤
      angularSpeedInRevolutionsPerMinute angularSpeed ∧
    angularSpeedInRevolutionsPerMinute angularSpeed <
      choice.revolutionsPerMinute + 1 / 2

/-!
The exact positive solution is approximately `92.32 rpm`, hence rounds to
`92 rpm`, answer choice `C`.

This formalizes blueprint label `thm:physics:phyx_mini_0698:target`.
-/
theorem angularSpeedAt100Millijoules_matches_answerC
    (setup : TriangularWidgetSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesTriangularWidgetRotationalLaws setup)
    (angularSpeed : AngularSpeedQuantity)
    (_angularSpeedPositive :
      0 < angularSpeedInRadiansPerSecond angularSpeed)
    (_hasTargetEnergy :
      energyInJoules (setup.rotationalEnergyAt angularSpeed) =
        energyInJoules setup.targetRotationalEnergy) :
    RoundsToDisplayedRevolutionsPerMinute angularSpeed .C := by
  have hsq := targetAngularSpeed_squared_eq_10000_over_107
    setup _figure _data _laws angularSpeed _hasTargetEnergy
  have hsinPiBounds :
      (49 / 500 : ℝ) < Real.sin (Real.pi / 32) ∧
        Real.sin (Real.pi / 32) < (981 / 10000 : ℝ) := by
    rw [Real.sin_pi_div_thirty_two]
    have h2 : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    have h2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h22 : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
        2 + Real.sqrt 2 :=
      Real.sq_sqrt (by positivity)
    have h22n : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
      Real.sqrt_nonneg _
    have h222 :
        (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
          2 + Real.sqrt (2 + Real.sqrt 2) :=
      Real.sq_sqrt (by positivity)
    have h222n :
        0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
      Real.sqrt_nonneg _
    have hout :
        (Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))) ^ 2 =
            2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
      Real.sq_sqrt (by
        have h := Real.sqrtTwoAddSeries_lt_two 3
        simpa [Real.sqrtTwoAddSeries] using h.le)
    have houtn :
        0 ≤ Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
      Real.sqrt_nonneg _
    constructor
    · nlinarith [sq_nonneg (Real.sqrt 2 - 14143 / 10000),
        sq_nonneg
          (Real.sqrt (2 + Real.sqrt 2) - 18478 / 10000),
        sq_nonneg
          (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) -
            19616 / 10000)]
    · nlinarith [sq_nonneg (Real.sqrt 2 - 14143 / 10000),
        sq_nonneg
          (Real.sqrt (2 + Real.sqrt 2) - 18478 / 10000),
        sq_nonneg
          (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) -
            19615 / 10000)]
  have hsin314 :
      Real.sin (157 / 1600 : ℝ) < 49 / 500 := by
    have h := Real.sin_bound (x := (157 / 1600 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 157 / 1600)] at h
    nlinarith [le_abs_self
      (Real.sin (157 / 1600 : ℝ) -
        ((157 / 1600 : ℝ) - (157 / 1600 : ℝ) ^ 3 / 6))]
  have hsin315 :
      (981 / 10000 : ℝ) < Real.sin (63 / 640 : ℝ) := by
    have h := Real.sin_bound (x := (63 / 640 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 63 / 640)] at h
    nlinarith [neg_abs_le
      (Real.sin (63 / 640 : ℝ) -
        ((63 / 640 : ℝ) - (63 / 640 : ℝ) ^ 3 / 6))]
  have hpiLower : (3.14 : ℝ) < Real.pi := by
    by_contra hpi
    have hpi' : Real.pi ≤ 157 / 50 := by
      norm_num at hpi ⊢
      exact hpi
    have hmono :
        Real.sin (Real.pi / 32) ≤ Real.sin (157 / 1600 : ℝ) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.two_le_pi]
      · nlinarith
    linarith [hsinPiBounds.1]
  have hpiUpper : Real.pi < (3.15 : ℝ) := by
    by_contra hpi
    have hpi' : (63 / 20 : ℝ) ≤ Real.pi := by
      norm_num at hpi ⊢
      exact hpi
    have hmono :
        Real.sin (63 / 640 : ℝ) ≤ Real.sin (Real.pi / 32) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
      · nlinarith
    linarith [hsinPiBounds.2]
  unfold RoundsToDisplayedRevolutionsPerMinute
  simp only [AnswerChoice.revolutionsPerMinute,
    angularSpeedInRevolutionsPerMinute]
  norm_num
  constructor
  · rw [le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have hp2 : Real.pi ^ 2 < (315 / 100 : ℝ) ^ 2 :=
      (sq_lt_sq₀ Real.pi_nonneg (by norm_num)).2 (by
        norm_num at hpiUpper ⊢
        exact hpiUpper)
    nlinarith
  · rw [div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    have hp2 : (314 / 100 : ℝ) ^ 2 < Real.pi ^ 2 :=
      (sq_lt_sq₀ (by norm_num) Real.pi_nonneg).2 (by
        norm_num at hpiLower ⊢
        exact hpiLower)
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0698
