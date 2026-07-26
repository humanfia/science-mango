import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Gravitational torque on a supported steel beam

The supplied figure shows a horizontal `4.00 m`, `500 kg` steel beam.  Its
center of mass is left of a triangular support: the labelled center-to-support
distance is `0.80 m`, and the labelled support-to-right-end distance is
`1.20 m`.  The beam's weight, labelled `Mg`, acts vertically downward at the
center of mass.

Physical scalars and vectors below use Physlib's unit-independent
`Dimensionful (WithDim ...)` representation.  Real vectors occur only as
readouts in a coherent unit system.  The positive `x` direction is rightward,
the positive `y` direction is upward, and the positive torque axis is `z`, out
of the page.

Assumption/target boundary:

* `MatchesProblemData` contains the stated material, orientation, length, and
  mass.
* `MatchesPrimaryFigure` contains only labels, placements, distances, and
  directions visible in the primary image.
* `UsesStandardEarthGravity` supplies the conventional `9.80 m/s^2` downward
  gravitational acceleration implicit in the recorded numerical answer.
* `SatisfiesGravityAndTorqueLaws` states `F_g = m g` and
  `tau = r cross F_g` in every coherent unit system.
* There are no previous-part results.  The requested `3920 N m` value and
  answer C occur only on the conclusion/displayed-answer side.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0702

open Dimension

/-! ## Dimensionful physical quantities and vector operations -/

/-- Three-dimensional Euclidean vectors used for coherent-unit readouts. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Acceleration has physical dimension `L T^-2`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has physical dimension `M L T^-2`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Torque has physical dimension `M L^2 T^-2`. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A spatial position or displacement with physical length dimension. -/
abbrev PositionVectorQuantity : Type :=
  Dimensionful (WithDim L𝓭 SpatialVector)

/-- A spatial gravitational-acceleration vector. -/
abbrev AccelerationVectorQuantity : Type :=
  Dimensionful (WithDim accelerationDimension SpatialVector)

/-- A spatial force vector. -/
abbrev ForceVectorQuantity : Type :=
  Dimensionful (WithDim forceDimension SpatialVector)

/-- A spatial torque vector about the support. -/
abbrev TorqueVectorQuantity : Type :=
  Dimensionful (WithDim torqueDimension SpatialVector)

/-- Read a nonnegative scalar physical quantity in a coherent unit system. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a physical vector in a coherent unit system. -/
def vectorReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d SpatialVector)) : SpatialVector :=
  (quantity units).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI mass

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI length

/-- Cartesian metre readout of a position or displacement. -/
def positionInMeters (position : PositionVectorQuantity) : SpatialVector :=
  vectorReadout UnitChoices.SI position

/-- Cartesian metres-per-second-squared readout of an acceleration vector. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationVectorQuantity) : SpatialVector :=
  vectorReadout UnitChoices.SI acceleration

/-- Cartesian newton readout of a force vector. -/
def forceInNewtons (force : ForceVectorQuantity) : SpatialVector :=
  vectorReadout UnitChoices.SI force

/-- Cartesian newton-metre readout of a torque vector. -/
def torqueInNewtonMeters (torque : TorqueVectorQuantity) : SpatialVector :=
  vectorReadout UnitChoices.SI torque

/-- The ordinary three-dimensional cross product transported to Euclidean space. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- The dimensionless Cartesian unit vector pointing rightward along the beam. -/
def xHat : SpatialVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- The dimensionless Cartesian unit vector pointing vertically upward. -/
def yHat : SpatialVector :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- The dimensionless Cartesian unit vector pointing out of the page. -/
def zHat : SpatialVector :=
  EuclideanSpace.single (2 : Fin 3) 1

/-! ## Physical roles and primary-figure vocabulary -/

/-- Distinguished points ordered along the pictured beam. -/
inductive BeamPoint where
  | leftEnd
  | centerOfMass
  | support
  | rightEnd
  deriving DecidableEq, Repr

/-- Individually identifiable objects shown in the primary image. -/
inductive FigureComponent where
  | horizontalBeam
  | triangularSupport
  | downwardWeightArrow
  deriving DecidableEq, Repr

/-- Literal text labels attached to the center of mass and weight arrow. -/
inductive FigureTextLabel where
  | cm
  | Mg
  deriving DecidableEq, Repr

/-- The three calibrated distance labels drawn in the image. -/
inductive FigureDistanceLabel where
  | beamLength4Point00Meters
  | centerToSupport0Point80Meters
  | supportToRightEnd1Point20Meters
  deriving DecidableEq, Repr

/-- Direction of the red gravitational-force arrow. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Material named in the problem statement. -/
inductive BeamMaterial where
  | steel
  | other
  deriving DecidableEq, Repr

/-- Orientation of the beam in the supplied side view. -/
inductive BeamOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- The numerical value printed by each calibrated distance label, in metres. -/
def distanceLabelValueInMeters : FigureDistanceLabel → ℝ
  | .beamLength4Point00Meters => 4
  | .centerToSupport0Point80Meters => 4 / 5
  | .supportToRightEnd1Point20Meters => 6 / 5

/-- Labels and incidences transcribed from the supplied primary bitmap. -/
structure SuppliedBeamFigure where
  showsComponent : FigureComponent → Bool
  textLabelPoint : FigureTextLabel → BeamPoint
  distanceEndpoints : FigureDistanceLabel → BeamPoint × BeamPoint
  gravityArrowTail : BeamPoint
  gravityArrowDirection : VerticalDirection
  leftToRightOrder : List BeamPoint

/--
The independent physical quantities of the beam-and-support setup.  In
particular, the gravitational force and torque are not defined from the
requested numerical answer; the governing laws below constrain them.
-/
structure SupportedBeamSetup where
  beamMaterial : BeamMaterial
  beamOrientation : BeamOrientation
  beamLength : LengthQuantity
  beamMass : MassQuantity
  positionOf : BeamPoint → PositionVectorQuantity
  gravitationalAcceleration : AccelerationVectorQuantity
  gravitationalForceAtCenterOfMass : ForceVectorQuantity
  gravitationalTorqueAboutSupport : TorqueVectorQuantity
  figure : SuppliedBeamFigure

/-! ## Problem data, figure readouts, and governing laws -/

/-- Numerical and categorical information stated in the prose. -/
structure MatchesProblemData (setup : SupportedBeamSetup) : Prop where
  materialIsSteel : setup.beamMaterial = .steel
  beamIsHorizontal : setup.beamOrientation = .horizontal
  beamLengthMeters : lengthInMeters setup.beamLength = 4
  beamMassKilograms : massInKilograms setup.beamMass = 500

/--
The labels, order, and calibrated geometry visible in image `702.png`.
Coordinates use the left endpoint as the origin.  These fields supply only
figure evidence; no force or torque value appears here.
-/
structure MatchesPrimaryFigure (setup : SupportedBeamSetup) : Prop where
  everyComponentShown : ∀ component, setup.figure.showsComponent component = true
  centerOfMassLabelPlacement : setup.figure.textLabelPoint .cm = .centerOfMass
  weightLabelPlacement : setup.figure.textLabelPoint .Mg = .centerOfMass
  totalLengthEndpoints :
    setup.figure.distanceEndpoints .beamLength4Point00Meters =
      (.leftEnd, .rightEnd)
  centerToSupportEndpoints :
    setup.figure.distanceEndpoints .centerToSupport0Point80Meters =
      (.centerOfMass, .support)
  supportToRightEndEndpoints :
    setup.figure.distanceEndpoints .supportToRightEnd1Point20Meters =
      (.support, .rightEnd)
  gravityStartsAtCenterOfMass : setup.figure.gravityArrowTail = .centerOfMass
  gravityPointsDownward : setup.figure.gravityArrowDirection = .downward
  pointOrder :
    setup.figure.leftToRightOrder =
      [.leftEnd, .centerOfMass, .support, .rightEnd]
  leftEndAtOrigin : positionInMeters (setup.positionOf .leftEnd) = 0
  centerOfMassPosition :
    positionInMeters (setup.positionOf .centerOfMass) = (2 : ℝ) • xHat
  supportPosition :
    positionInMeters (setup.positionOf .support) = (14 / 5 : ℝ) • xHat
  rightEndPosition :
    positionInMeters (setup.positionOf .rightEnd) = (4 : ℝ) • xHat
  labelledDistanceGeometry :
    ∀ label,
      let endpoints := setup.figure.distanceEndpoints label
      ‖positionInMeters (setup.positionOf endpoints.2) -
          positionInMeters (setup.positionOf endpoints.1)‖ =
        distanceLabelValueInMeters label

/-- The standard near-Earth field value implicit in the recorded answer. -/
structure UsesStandardEarthGravity (setup : SupportedBeamSetup) : Prop where
  accelerationVector :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      (-49 / 5 : ℝ) • yHat

/-- Positivity conditions selecting a physical beam and gravitational field. -/
structure HasPhysicalBeamParameters (setup : SupportedBeamSetup) : Prop where
  beamLengthPositive : 0 < lengthInMeters setup.beamLength
  beamMassPositive : 0 < massInKilograms setup.beamMass
  gravitationalAccelerationNonzero :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration ≠ 0

/--
The two governing mechanics laws used by the calculation.  They are stated in
every coherent unit system: gravitational force is mass times acceleration,
and torque about the support is the cross product of the support-to-center
lever arm with that force.  Neither law mentions a numerical torque answer.
-/
structure SatisfiesGravityAndTorqueLaws
    (setup : SupportedBeamSetup) : Prop where
  gravitationalForceLaw :
    ∀ units : UnitChoices,
      vectorReadout units setup.gravitationalForceAtCenterOfMass =
        nonnegativeReadout units setup.beamMass •
          vectorReadout units setup.gravitationalAcceleration
  torqueAboutSupportLaw :
    ∀ units : UnitChoices,
      vectorReadout units setup.gravitationalTorqueAboutSupport =
        spatialCross
          (vectorReadout units (setup.positionOf .centerOfMass) -
            vectorReadout units (setup.positionOf .support))
          (vectorReadout units setup.gravitationalForceAtCenterOfMass)

/-! ## Displayed answers and target -/

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
Numerical torque magnitudes displayed by the choices, interpreted in
newton-metres.  The source abbreviates their unit as `N`, although the
question asks for torque.
-/
def displayedTorqueMagnitudeInNewtonMeters : AnswerChoice → ℝ
  | .A => 3720
  | .B => 3820
  | .C => 3920
  | .D => 4020

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- SI magnitude of the gravitational torque about the support. -/
def gravitationalTorqueMagnitudeInNewtonMeters
    (setup : SupportedBeamSetup) : ℝ :=
  ‖torqueInNewtonMeters setup.gravitationalTorqueAboutSupport‖

/-- A displayed choice agrees with the calculated physical torque magnitude. -/
def MatchesDisplayedTorqueAnswer
    (setup : SupportedBeamSetup) (choice : AnswerChoice) : Prop :=
  gravitationalTorqueMagnitudeInNewtonMeters setup =
    displayedTorqueMagnitudeInNewtonMeters choice

/--
The gravitational torque about the support has magnitude `3920 N m`, so it
agrees with displayed answer C.

Blueprint: `thm:physics:phyx_mini_0702:target`.
-/
theorem problem_phyx_mini_0702
    (setup : SupportedBeamSetup)
    (_problemData : MatchesProblemData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_earthGravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalBeamParameters setup)
    (_laws : SatisfiesGravityAndTorqueLaws setup) :
    gravitationalTorqueMagnitudeInNewtonMeters setup = 3920 ∧
      MatchesDisplayedTorqueAnswer setup .C := by
  have hTorqueVector :
      torqueInNewtonMeters setup.gravitationalTorqueAboutSupport =
        (3920 : ℝ) • zHat := by
    rw [torqueInNewtonMeters,
      _laws.torqueAboutSupportLaw UnitChoices.SI]
    rw [show
          vectorReadout UnitChoices.SI
              (setup.positionOf .centerOfMass) =
            (2 : ℝ) • xHat by
          exact _figure.centerOfMassPosition,
      show
          vectorReadout UnitChoices.SI (setup.positionOf .support) =
            (14 / 5 : ℝ) • xHat by
          exact _figure.supportPosition,
      _laws.gravitationalForceLaw UnitChoices.SI,
      show
          nonnegativeReadout UnitChoices.SI setup.beamMass = 500 by
        exact _problemData.beamMassKilograms,
      show
          vectorReadout UnitChoices.SI setup.gravitationalAcceleration =
            (-49 / 5 : ℝ) • yHat by
        exact _earthGravity.accelerationVector]
    ext i
    fin_cases i
    all_goals
      simp [spatialCross, xHat, yHat, zHat, EuclideanSpace.single,
        crossProduct]
    norm_num
  have hMagnitude :
      gravitationalTorqueMagnitudeInNewtonMeters setup = 3920 := by
    rw [gravitationalTorqueMagnitudeInNewtonMeters, hTorqueVector, norm_smul]
    norm_num [zHat, EuclideanSpace.single]
  exact ⟨hMagnitude, by
    simpa [MatchesDisplayedTorqueAnswer,
      displayedTorqueMagnitudeInNewtonMeters] using hMagnitude⟩

end PhyXMiniProblems.ProblemPhyXMini0702
