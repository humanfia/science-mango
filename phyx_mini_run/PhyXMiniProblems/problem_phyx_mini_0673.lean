import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0673

open Dimension

/-!
# Perpendicular sliders joined by a rigid rod

Object A moves on the horizontal guide rail and object B moves on the
perpendicular vertical guide rail.  Their hinges are joined by a rigid rod of
length `L`.  At the observation time the rod makes the acute angle `θ` with
the leftward horizontal ray from A, and A is moving left with constant speed
`v`.

Physical length and speed magnitudes are represented by Physlib dimensionful
quantities.  Real-valued trajectories occur only as signed coordinate
readouts in metres as functions of time read in seconds.  In particular, the
signed velocity of B is an independent physical quantity whose SI readout is
related to the derivative of its vertical coordinate by a governing-law
hypothesis; it is not defined to equal the requested answer.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- The physical dimension of a signed velocity component. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- A signed, unit-independent velocity component along one guide rail. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a nonnegative physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a signed velocity component in metres per second. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-! ## Figure labels and perpendicular-rail geometry -/

/-- The two hinged objects labelled in the supplied figure. -/
inductive SliderLabel where
  | objectA
  | objectB
  deriving DecidableEq, Repr

/-- The perpendicular guide rails shown through the point labelled `O`. -/
inductive GuideRail where
  | horizontalX
  | verticalY
  deriving DecidableEq, Repr

/-- Object A belongs to the horizontal rail and object B to the vertical rail. -/
def guideRailOf : SliderLabel → GuideRail
  | .objectA => .horizontalX
  | .objectB => .verticalY

/-- The Euclidean plane used by the side-view diagram, with coordinates in metres. -/
abbrev DiagramPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- Construct a diagram point from its horizontal and vertical metre readouts. -/
def planePoint (x y : ℝ) : DiagramPlane :=
  EuclideanSpace.single (0 : Fin 2) x +
    EuclideanSpace.single (1 : Fin 2) y

/-- The rail intersection labelled `O` in the figure. -/
def diagramOrigin : DiagramPlane := planePoint 0 0

/-!
The coordinate curves are scalar readouts, not aliases for physical length:
`xCoordinateInMeters t` and `yCoordinateInMeters t` are the two figure-derived
components at the time readout `t`.  The allowed motion times form a separate
set so that the idealized constant-speed motion need only hold while the rod
remains between the rails.
-/
structure PerpendicularSliderRodSetup where
  xCoordinateInMeters : ℝ → ℝ
  yCoordinateInMeters : ℝ → ℝ
  allowedTimesInSeconds : Set ℝ
  rodLength : LengthQuantity
  objectASpeedMagnitude : DimSpeed
  objectBVelocityAtObservation : SignedVelocityQuantity

/-- The instantaneous time and angle read from the pictured configuration. -/
structure FigureObservation where
  timeInSeconds : ℝ
  angleInRadians : ℝ

/-- Position of either hinge in the perpendicular-rail coordinate frame. -/
def sliderPosition
    (setup : PerpendicularSliderRodSetup)
    (slider : SliderLabel) (timeInSeconds : ℝ) : DiagramPlane :=
  match slider with
  | .objectA => planePoint (setup.xCoordinateInMeters timeInSeconds) 0
  | .objectB => planePoint 0 (setup.yCoordinateInMeters timeInSeconds)

/-! ## Assumptions: parameters, figure readout, and governing kinematics -/

/-- Positivity and time-domain conditions for a nondegenerate physical setup. -/
structure HasPhysicalSliderRodParameters
    (setup : PerpendicularSliderRodSetup)
    (observation : FigureObservation) : Prop where
  positiveRodLength : 0 < lengthInMeters setup.rodLength
  positiveObjectASpeed :
    0 < speedInMetersPerSecond setup.objectASpeedMagnitude
  allowedTimesAreOpen : IsOpen setup.allowedTimesInSeconds
  observationTimeIsAllowed :
    observation.timeInSeconds ∈ setup.allowedTimesInSeconds

/-!
Primary-image geometry at the observation time.  Since `θ` is drawn between
the rod and the leftward horizontal ray from A, `x = L cos θ` and
`y = L sin θ` are the adjacent and opposite projections of the rod.
-/
structure MatchesSuppliedFigure
    (setup : PerpendicularSliderRodSetup)
    (observation : FigureObservation) : Prop where
  horizontalDistancePositive :
    0 < setup.xCoordinateInMeters observation.timeInSeconds
  verticalDistancePositive :
    0 < setup.yCoordinateInMeters observation.timeInSeconds
  angleIsAcute :
    observation.angleInRadians ∈ Set.Ioo 0 (Real.pi / 2)
  horizontalRodProjection :
    setup.xCoordinateInMeters observation.timeInSeconds =
      lengthInMeters setup.rodLength * Real.cos observation.angleInRadians
  verticalRodProjection :
    setup.yCoordinateInMeters observation.timeInSeconds =
      lengthInMeters setup.rodLength * Real.sin observation.angleInRadians

/-!
The governing physical laws.  `fixedHingeSeparation` states rigidity directly
as constant Euclidean distance between the two hinge positions.  The next
field formalizes A's constant leftward motion, hence the minus sign in its
horizontal derivative.  The final field is only the definition of the signed
velocity readout of B as the derivative of its vertical coordinate.
-/
structure ObeysRigidRodKinematics
    (setup : PerpendicularSliderRodSetup)
    (observation : FigureObservation) : Prop where
  fixedHingeSeparation :
    ∀ timeInSeconds ∈ setup.allowedTimesInSeconds,
      dist (sliderPosition setup .objectA timeInSeconds)
          (sliderPosition setup .objectB timeInSeconds) =
        lengthInMeters setup.rodLength
  objectAMovesLeftAtConstantSpeed :
    ∀ timeInSeconds ∈ setup.allowedTimesInSeconds,
      HasDerivAt setup.xCoordinateInMeters
        (-speedInMetersPerSecond setup.objectASpeedMagnitude)
        timeInSeconds
  objectBVelocityIsVerticalDerivative :
    HasDerivAt setup.yCoordinateInMeters
      (signedVelocityInMetersPerSecond
        setup.objectBVelocityAtObservation)
      observation.timeInSeconds

/-! ## Geometric and kinematic consequences -/

/-- Fixed Euclidean hinge separation gives the familiar right-triangle constraint. -/
theorem squared_coordinate_constraint_of_fixed_rod
    (setup : PerpendicularSliderRodSetup)
    (timeInSeconds : ℝ)
    (hfixed :
      dist (sliderPosition setup .objectA timeInSeconds)
          (sliderPosition setup .objectB timeInSeconds) =
        lengthInMeters setup.rodLength) :
    setup.xCoordinateInMeters timeInSeconds ^ 2 +
        setup.yCoordinateInMeters timeInSeconds ^ 2 =
      lengthInMeters setup.rodLength ^ 2 := by
  have hsquare := congrArg (fun distance : ℝ => distance ^ 2) hfixed
  rw [EuclideanSpace.dist_sq_eq] at hsquare
  simpa [sliderPosition, planePoint, Fin.sum_univ_two, Real.dist_eq] using
    hsquare

/-!
Differentiating the fixed-length constraint at the observation time gives
`x * x' + y * y' = 0`.  Here `x' = -v` and `y' = v_B` by the two velocity laws.
-/
theorem instantaneous_rigid_rod_velocity_constraint
    (setup : PerpendicularSliderRodSetup)
    (observation : FigureObservation)
    (parameters : HasPhysicalSliderRodParameters setup observation)
    (kinematics : ObeysRigidRodKinematics setup observation) :
    setup.xCoordinateInMeters observation.timeInSeconds *
          (-speedInMetersPerSecond setup.objectASpeedMagnitude) +
        setup.yCoordinateInMeters observation.timeInSeconds *
          signedVelocityInMetersPerSecond
            setup.objectBVelocityAtObservation =
      0 := by
  have allowedTimesAreNeighborhood :
      setup.allowedTimesInSeconds ∈ nhds observation.timeInSeconds :=
    parameters.allowedTimesAreOpen.mem_nhds
      parameters.observationTimeIsAllowed
  have squaredConstraintEventually :
      Filter.EventuallyEq (nhds observation.timeInSeconds)
        (setup.xCoordinateInMeters * setup.xCoordinateInMeters +
          setup.yCoordinateInMeters * setup.yCoordinateInMeters)
        (fun _ => lengthInMeters setup.rodLength ^ 2) := by
    filter_upwards [allowedTimesAreNeighborhood] with timeInSeconds
      timeIsAllowed
    simpa [pow_two] using
      squared_coordinate_constraint_of_fixed_rod setup timeInSeconds
        (kinematics.fixedHingeSeparation timeInSeconds timeIsAllowed)
  have horizontalDerivative :=
    kinematics.objectAMovesLeftAtConstantSpeed
      observation.timeInSeconds parameters.observationTimeIsAllowed
  have squaredCoordinateDerivative :=
    (horizontalDerivative.mul horizontalDerivative).add
      (kinematics.objectBVelocityIsVerticalDerivative.mul
        kinematics.objectBVelocityIsVerticalDerivative)
  have constantSquaredLengthDerivative :
      HasDerivAt
        (setup.xCoordinateInMeters * setup.xCoordinateInMeters +
          setup.yCoordinateInMeters * setup.yCoordinateInMeters)
        0 observation.timeInSeconds :=
    (hasDerivAt_const observation.timeInSeconds
      (lengthInMeters setup.rodLength ^ 2)).congr_of_eventuallyEq
        squaredConstraintEventually
  have derivativeEquality :=
    squaredCoordinateDerivative.unique constantSquaredLengthDerivative
  nlinarith

/-!
At every admissible pictured configuration, the signed upward velocity of B
is `v / tan θ`, where `v` is the positive speed magnitude of A.  This is answer
choice C in the recorded problem.
-/
theorem objectB_velocity_as_function_of_angle
    (setup : PerpendicularSliderRodSetup)
    (observation : FigureObservation)
    (parameters : HasPhysicalSliderRodParameters setup observation)
    (figure : MatchesSuppliedFigure setup observation)
    (kinematics : ObeysRigidRodKinematics setup observation) :
    signedVelocityInMetersPerSecond
        setup.objectBVelocityAtObservation =
      (1 / Real.tan observation.angleInRadians) *
        speedInMetersPerSecond setup.objectASpeedMagnitude := by
  have velocityConstraint :=
    instantaneous_rigid_rod_velocity_constraint setup observation parameters
      kinematics
  rw [figure.horizontalRodProjection, figure.verticalRodProjection] at velocityConstraint
  have positiveLengthTimesSine :
      0 <
        lengthInMeters setup.rodLength *
          Real.sin observation.angleInRadians := by
    rw [← figure.verticalRodProjection]
    exact figure.verticalDistancePositive
  have positiveSine : 0 < Real.sin observation.angleInRadians := by
    rcases (mul_pos_iff.mp positiveLengthTimesSine) with positive | negative
    · exact positive.2
    · exfalso
      linarith [parameters.positiveRodLength]
  have sineTimesVelocity :
      Real.sin observation.angleInRadians *
          signedVelocityInMetersPerSecond
            setup.objectBVelocityAtObservation =
        Real.cos observation.angleInRadians *
          speedInMetersPerSecond setup.objectASpeedMagnitude := by
    have nonzeroLength :
        lengthInMeters setup.rodLength ≠ 0 :=
      ne_of_gt parameters.positiveRodLength
    apply mul_left_cancel₀ nonzeroLength
    nlinarith
  rw [Real.tan_eq_sin_div_cos, one_div_div, div_mul_eq_mul_div]
  apply (eq_div_iff positiveSine.ne').2
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0673
