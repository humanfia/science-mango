import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0699

open Dimension

/-!
# Speed of the tip of a falling hinged rod

A uniform slender rod is hinged to a wall at one end.  It is released from
rest while horizontal and rotates clockwise through a quarter turn until it
lies vertically downward against the wall.  The requested observable is the
speed magnitude of the free tip at that instant.

Physical magnitudes are represented by Physlib dimensionful quantities.
Real numbers occur only as coherent SI readouts, signed Cartesian coordinate
readouts, and displayed answer values.  The impact speed is an independent
field of the setup; neither it nor answer choice `C` is assumed by the data or
governing-law interfaces below.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length magnitude. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length, used for Cartesian coordinates and heights. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular-speed magnitude, with dimension `T⁻¹`. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative moment of inertia about an axis, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A physical energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Metre readout of a signed physical coordinate or height. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Radian-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  nonnegativeSIReadout angularSpeed

/-- Kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Metre-per-second readout of a physical speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Motion events, physical roles, and primary-image vocabulary -/

/-- The two rod configurations compared by conservation of energy. -/
inductive MotionEvent where
  | release
  | impactAtWall
  deriving DecidableEq, Fintype, Repr

/-- The axes explicitly labelled in the supplied image. -/
inductive CartesianAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Distinguished points of the idealized rod. -/
inductive RodPoint where
  | hinge
  | centerOfMass
  | tip
  deriving DecidableEq, Fintype, Repr

/-- The two physical orientations shown in the before/after diagram. -/
inductive RodPose where
  | horizontalAlongPositiveX
  | verticalAlongNegativeY
  deriving DecidableEq, Repr

/-- Text and mathematical labels visibly printed in the primary image. -/
inductive FigureLabel where
  | hinge
  | rodLengthL
  | centerOfMassHeightBefore
  | angularSpeedBefore
  | rodMassM
  | centerOfMassHeightAfter
  | tipVelocity
  deriving DecidableEq, Fintype, Repr

/-- Sense of the grey quarter-turn arrow in the image. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Direction of the green tip-velocity arrow at wall impact. -/
inductive TipVelocityDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Idealized mass distribution of the pictured rod. -/
inductive RodMassDistribution where
  | uniformSlenderRod
  deriving DecidableEq, Repr

/-- Constraint model at the wall attachment. -/
inductive HingeModel where
  | fixedFrictionlessHinge
  deriving DecidableEq, Repr

/-- Gravity model used during the fall. -/
inductive GravityModel where
  | uniformDownwardNearEarth
  deriving DecidableEq, Repr

/-- Qualitative and label evidence read directly from the supplied bitmap. -/
structure HingedRodFigure where
  showsAxis : CartesianAxis → Bool
  axisLabel : CartesianAxis → String
  hingeAtAxesOrigin : Bool
  depictsPose : MotionEvent → RodPose
  showsCenterOfMassMarker : MotionEvent → Bool
  showsLabel : FigureLabel → Bool
  rotationArrowSense : RotationSense
  impactTipVelocityDirection : TipVelocityDirection

/-!
Independent physical quantities and geometry of the experiment.  Point
coordinates are signed dimensionful lengths relative to the hinge.  The
inertia, energies, angular speeds, and impact-tip speed are stored
independently; their relations are supplied only by the governing laws.
-/
structure HingedRodSetup where
  figure : HingedRodFigure
  rodLength_L : LengthQuantity
  rodMass_m : MassQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  pointCoordinate : MotionEvent → RodPoint → CartesianAxis → SignedLengthQuantity
  centerOfMassHeight : MotionEvent → SignedLengthQuantity
  angularSpeed : MotionEvent → AngularSpeedQuantity
  tipSpeedAtImpact : SpeedQuantity
  momentOfInertiaAboutHinge : MomentOfInertiaQuantity
  gravitationalPotentialEnergy : MotionEvent → EnergyQuantity
  rotationalKineticEnergy : MotionEvent → EnergyQuantity
  rigidBodySI : RigidBody 3
  rigidBodyReferencePoint : RodPoint
  rotationAxis : Fin 3
  angularVelocityVectorRadPerSecond : MotionEvent → Fin 3 → ℝ
  physicalPose : MotionEvent → RodPose
  rodMassDistribution : RodMassDistribution
  hingeModel : HingeModel
  gravityModel : GravityModel

/-! ## Figure readout, scenario data, geometry, and governing laws -/

/-!
Primary-image evidence.  The bitmap, unlike one sentence of the auxiliary
caption, clearly shows the release rod along `+x` and the impact rod along
`-y`.  It also shows the hinge at the axes' intersection, center-of-mass
markers in both poses, clockwise rotation, and a leftward impact velocity.
-/
structure MatchesPrimaryHingedRodFigure
    (setup : HingedRodSetup) : Prop where
  bothAxesShown : ∀ axis, setup.figure.showsAxis axis = true
  xAxisText : setup.figure.axisLabel .x = "x"
  yAxisText : setup.figure.axisLabel .y = "y"
  hingeAtOrigin : setup.figure.hingeAtAxesOrigin = true
  releasePoseShown :
    setup.figure.depictsPose .release = .horizontalAlongPositiveX
  impactPoseShown :
    setup.figure.depictsPose .impactAtWall = .verticalAlongNegativeY
  bothCenterOfMassMarkersShown :
    ∀ event, setup.figure.showsCenterOfMassMarker event = true
  everyPrintedLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  clockwiseRotationArrow :
    setup.figure.rotationArrowSense = .clockwise
  impactVelocityArrowPointsLeft :
    setup.figure.impactTipVelocityDirection = .negativeX

/-!
Numerical and qualitative problem data.  The diagram gives `L = 1.0 m`,
`m = 0.20 kg`, `y_cm,0 = 0`, and `ω₀ = 0`; standard near-Earth gravity is
calibrated as `9.8 m/s²`.  No impact angular speed or tip speed occurs here.
-/
structure MatchesHingedRodProblemData
    (setup : HingedRodSetup) : Prop where
  rodLengthMeters : lengthInMeters setup.rodLength_L = 1
  rodMassKilograms : massInKilograms setup.rodMass_m = 1 / 5
  standardGravity :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 49 / 5
  initialCenterOfMassHeight :
    signedLengthInMeters (setup.centerOfMassHeight .release) = 0
  releasedFromRest :
    angularSpeedInRadiansPerSecond (setup.angularSpeed .release) = 0
  releasePose :
    setup.physicalPose .release = .horizontalAlongPositiveX
  impactPose :
    setup.physicalPose .impactAtWall = .verticalAlongNegativeY
  rodIsUniformAndSlender :
    setup.rodMassDistribution = .uniformSlenderRod
  hingeIsFixedAndFrictionless :
    setup.hingeModel = .fixedFrictionlessHinge
  gravityIsUniformAndDownward :
    setup.gravityModel = .uniformDownwardNearEarth
  rigidBodyIsReferencedAtHinge :
    setup.rigidBodyReferencePoint = .hinge

/-!
Physical coordinates implied by a length-`L` uniform rod hinged at the
origin.  At release the tip is `(L, 0)` and the center of mass is `(L/2, 0)`;
at impact they are `(0, -L)` and `(0, -L/2)` respectively.  These are figure
and uniform-rod geometry, not the requested speed.
-/
structure MatchesHingedRodGeometry
    (setup : HingedRodSetup) : Prop where
  hingeAtOrigin : ∀ event axis,
    signedLengthInMeters (setup.pointCoordinate event .hinge axis) = 0
  releaseTipX :
    signedLengthInMeters (setup.pointCoordinate .release .tip .x) =
      lengthInMeters setup.rodLength_L
  releaseTipY :
    signedLengthInMeters (setup.pointCoordinate .release .tip .y) = 0
  impactTipX :
    signedLengthInMeters (setup.pointCoordinate .impactAtWall .tip .x) = 0
  impactTipY :
    signedLengthInMeters (setup.pointCoordinate .impactAtWall .tip .y) =
      -lengthInMeters setup.rodLength_L
  releaseCenterOfMassX :
    signedLengthInMeters
        (setup.pointCoordinate .release .centerOfMass .x) =
      lengthInMeters setup.rodLength_L / 2
  releaseCenterOfMassY :
    signedLengthInMeters
        (setup.pointCoordinate .release .centerOfMass .y) = 0
  impactCenterOfMassX :
    signedLengthInMeters
        (setup.pointCoordinate .impactAtWall .centerOfMass .x) = 0
  impactCenterOfMassY :
    signedLengthInMeters
        (setup.pointCoordinate .impactAtWall .centerOfMass .y) =
      -lengthInMeters setup.rodLength_L / 2
  centerOfMassHeightIsYCoordinate : ∀ event,
    signedLengthInMeters (setup.centerOfMassHeight event) =
      signedLengthInMeters
        (setup.pointCoordinate event .centerOfMass .y)

/-- Positivity and nondegeneracy of the physical rod and gravity. -/
structure HasPhysicalHingedRodParameters
    (setup : HingedRodSetup) : Prop where
  rodLengthPositive : 0 < lengthInMeters setup.rodLength_L
  rodMassPositive : 0 < massInKilograms setup.rodMass_m
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  hingeMomentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutHinge

/-!
Governing relations for a uniform rod rotating about a fixed hinge:

* the hinge-axis moment is `I = m L² / 3`;
* gravitational potential energy is `m g y_cm`;
* rotational energy is Physlib's `RigidBody.rotationalKineticEnergy` for the
  angular-velocity vector and hinge-referenced inertia tensor;
* mechanical energy is conserved from release to wall impact;
* fixed-axis kinematics gives `v_tip = ω₁ L`.

None of these fields states the square-root speed, `5.4 m/s`, or an answer
choice.
-/
structure SatisfiesFallingHingedRodLaws
    (setup : HingedRodSetup) : Prop where
  rigidBodyMassMatchesRod :
    setup.rigidBodySI.mass = massInKilograms setup.rodMass_m
  hingeAxisInertiaTensorEntry :
    setup.rigidBodySI.inertiaTensor setup.rotationAxis setup.rotationAxis =
      momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutHinge
  angularVelocityIsAlongHingeAxis : ∀ event component,
    setup.angularVelocityVectorRadPerSecond event component =
      if component = setup.rotationAxis then
        angularSpeedInRadiansPerSecond (setup.angularSpeed event)
      else 0
  uniformRodHingeMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutHinge =
      massInKilograms setup.rodMass_m *
        lengthInMeters setup.rodLength_L ^ 2 / 3
  gravitationalPotentialEnergyLaw : ∀ event,
    energyInJoules (setup.gravitationalPotentialEnergy event) =
      massInKilograms setup.rodMass_m *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        signedLengthInMeters (setup.centerOfMassHeight event)
  rotationalKineticEnergyUsesPhyslib : ∀ event,
    energyInJoules (setup.rotationalKineticEnergy event) =
      setup.rigidBodySI.rotationalKineticEnergy
        (setup.angularVelocityVectorRadPerSecond event)
  mechanicalEnergyConservation :
    energyInJoules (setup.gravitationalPotentialEnergy .release) +
        energyInJoules (setup.rotationalKineticEnergy .release) =
      energyInJoules
          (setup.gravitationalPotentialEnergy .impactAtWall) +
        energyInJoules (setup.rotationalKineticEnergy .impactAtWall)
  fixedAxisTipKinematics :
    speedInMetersPerSecond setup.tipSpeedAtImpact =
      angularSpeedInRadiansPerSecond
          (setup.angularSpeed .impactAtWall) *
        lengthInMeters setup.rodLength_L

/-! ## Derived speed relation and displayed answers -/

/-!
Energy conservation, the center-of-mass drop `L/2`, the hinge inertia
`m L²/3`, and `v_tip = ω₁ L` imply `v_tip² = 3 g L`.  This is a derived
mechanics result rather than a law premise.
-/
lemma impact_tip_speed_squared
    (setup : HingedRodSetup)
    (_data : MatchesHingedRodProblemData setup)
    (_geometry : MatchesHingedRodGeometry setup)
    (_physical : HasPhysicalHingedRodParameters setup)
    (_laws : SatisfiesFallingHingedRodLaws setup) :
    speedInMetersPerSecond setup.tipSpeedAtImpact ^ 2 =
      3 *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        lengthInMeters setup.rodLength_L := by
  have rotationalEnergy (event : MotionEvent) :
      energyInJoules (setup.rotationalKineticEnergy event) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared
            setup.momentOfInertiaAboutHinge *
          angularSpeedInRadiansPerSecond (setup.angularSpeed event) ^ 2 := by
    rw [_laws.rotationalKineticEnergyUsesPhyslib,
      RigidBody.rotationalKineticEnergy]
    have hω :
        setup.angularVelocityVectorRadPerSecond event =
          fun component =>
            if component = setup.rotationAxis then
              angularSpeedInRadiansPerSecond (setup.angularSpeed event)
            else 0 :=
      funext fun component =>
        _laws.angularVelocityIsAlongHingeAxis event component
    rw [hω]
    simp [dotProduct, Matrix.mulVec,
      _laws.hingeAxisInertiaTensorEntry]
    ring
  have potentialAtRelease :
      energyInJoules (setup.gravitationalPotentialEnergy .release) = 0 := by
    rw [_laws.gravitationalPotentialEnergyLaw,
      _data.initialCenterOfMassHeight]
    ring
  have potentialAtImpact :
      energyInJoules
          (setup.gravitationalPotentialEnergy .impactAtWall) =
        -(49 / 50 : ℝ) := by
    rw [_laws.gravitationalPotentialEnergyLaw,
      _geometry.centerOfMassHeightIsYCoordinate,
      _geometry.impactCenterOfMassY,
      _data.rodLengthMeters,
      _data.rodMassKilograms,
      _data.standardGravity]
    norm_num
  have hingeInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutHinge = (1 / 15 : ℝ) := by
    rw [_laws.uniformRodHingeMomentOfInertia,
      _data.rodMassKilograms, _data.rodLengthMeters]
    norm_num
  have conservation := _laws.mechanicalEnergyConservation
  rw [potentialAtRelease, rotationalEnergy .release,
    potentialAtImpact, rotationalEnergy .impactAtWall,
    _data.releasedFromRest, hingeInertia] at conservation
  have impactAngularSpeedSquared :
      angularSpeedInRadiansPerSecond
          (setup.angularSpeed .impactAtWall) ^ 2 = (147 / 5 : ℝ) := by
    norm_num at conservation ⊢
    linarith
  rw [_laws.fixedAxisTipKinematics, _data.rodLengthMeters,
    mul_one, impactAngularSpeedSquared,
    _data.standardGravity]
  norm_num

/-- Labels of the four numerical answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in metres per second printed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 26 / 5
  | .B => 28 / 5
  | .C => 27 / 5
  | .D => 29 / 5

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- One unit in the final displayed decimal place. -/
def displayedSpeedResolution : ℝ := 1 / 10

/-- Agreement with a speed displayed to the nearest tenth of a metre/second. -/
def MatchesDisplayedSpeed
    (speed : SpeedQuantity) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond speed - choice.metersPerSecond| <
    displayedSpeedResolution / 2

/-!
For `L = 1.0 m` and `g = 9.8 m/s²`, the exact impact-tip speed is
`sqrt (147/5) m/s`, approximately `5.42 m/s`.  It rounds to `5.4 m/s` and is
uniquely closest to displayed choice `C`.

This formalizes blueprint label `thm:physics:phyx_mini_0699:target`.
-/
theorem problem_phyx_mini_0699
    (setup : HingedRodSetup)
    (_figure : MatchesPrimaryHingedRodFigure setup)
    (_data : MatchesHingedRodProblemData setup)
    (_geometry : MatchesHingedRodGeometry setup)
    (_physical : HasPhysicalHingedRodParameters setup)
    (_laws : SatisfiesFallingHingedRodLaws setup) :
    speedInMetersPerSecond setup.tipSpeedAtImpact =
        Real.sqrt (147 / 5) ∧
      MatchesDisplayedSpeed setup.tipSpeedAtImpact recordedAnswerChoice ∧
      ∀ choice : AnswerChoice, choice ≠ recordedAnswerChoice →
        |speedInMetersPerSecond setup.tipSpeedAtImpact -
            recordedAnswerChoice.metersPerSecond| <
          |speedInMetersPerSecond setup.tipSpeedAtImpact -
            choice.metersPerSecond| := by
  have speedSquared :=
    impact_tip_speed_squared setup _data _geometry _physical _laws
  rw [_data.standardGravity, _data.rodLengthMeters] at speedSquared
  norm_num at speedSquared
  have speedNonnegative :
      0 ≤ speedInMetersPerSecond setup.tipSpeedAtImpact := by
    unfold speedInMetersPerSecond
    positivity
  have radicandNonnegative : (0 : ℝ) ≤ 147 / 5 := by
    norm_num
  have squareRootSquared :
      Real.sqrt (147 / 5 : ℝ) ^ 2 = 147 / 5 :=
    Real.sq_sqrt radicandNonnegative
  have squareRootNonnegative :
      0 ≤ Real.sqrt (147 / 5 : ℝ) :=
    Real.sqrt_nonneg _
  have speedValue :
      speedInMetersPerSecond setup.tipSpeedAtImpact =
        Real.sqrt (147 / 5) := by
    nlinarith
  have squareRootLower :
      (27 / 5 : ℝ) < Real.sqrt (147 / 5) := by
    nlinarith
  have squareRootUpper :
      Real.sqrt (147 / 5 : ℝ) < 109 / 20 := by
    nlinarith
  refine ⟨speedValue, ?_, ?_⟩
  · change
      |speedInMetersPerSecond setup.tipSpeedAtImpact - 27 / 5| <
        (1 / 10 : ℝ) / 2
    rw [speedValue,
      abs_of_nonneg (by linarith [squareRootLower])]
    linarith
  · intro choice choiceNotRecorded
    rw [speedValue]
    cases choice with
    | A =>
        change
          |Real.sqrt (147 / 5 : ℝ) - 27 / 5| <
            |Real.sqrt (147 / 5 : ℝ) - 26 / 5|
        rw [abs_of_nonneg (by linarith [squareRootLower]),
          abs_of_nonneg (by linarith [squareRootLower])]
        linarith
    | B =>
        change
          |Real.sqrt (147 / 5 : ℝ) - 27 / 5| <
            |Real.sqrt (147 / 5 : ℝ) - 28 / 5|
        rw [abs_of_nonneg (by linarith [squareRootLower]),
          abs_of_nonpos (by linarith [squareRootUpper])]
        linarith
    | C =>
        exact (choiceNotRecorded rfl).elim
    | D =>
        change
          |Real.sqrt (147 / 5 : ℝ) - 27 / 5| <
            |Real.sqrt (147 / 5 : ℝ) - 29 / 5|
        rw [abs_of_nonneg (by linarith [squareRootLower]),
          abs_of_nonpos (by linarith [squareRootUpper])]
        linarith

end PhyXMiniProblems.ProblemPhyXMini0699
