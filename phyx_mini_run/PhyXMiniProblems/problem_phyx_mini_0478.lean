import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0478

open Dimension Filter
open scoped Topology

/-!
# Spherical-mirror magnification with a mismatched supplied raster

The prose describes a graph of dimensionless lateral magnification `m` against
object-distance magnitude `p` for an object moving along the central axis of a
spherical mirror.  It supplies only the horizontal scale `p_s = 10 cm` and asks
for the magnification at `p = 21 cm`.

The primary raster is not that graph: it is an unrelated six-point vector
diagram.  In particular, it supplies no optical calibration such as
`m(10 cm) = 0.5`.  The displayed numerical answers, including the dataset's
recorded choice D, are therefore retained below only as source metadata.

The strongest supported optical conclusion is symbolic.  The Gaussian mirror
relation is obtained from a genuinely local reflection residual at the optical
axis, and lateral magnification is the derivative of transverse image height.
Thus the paraxial relations are first-order consequences with little-`o`
remainders, rather than global exact finite-ray assumptions.
-/

/-! ## Dimensionful optical lengths and scalar readouts -/

/-- A nonnegative, unit-independent physical length magnitude. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent optical length, used for focal and image distances. -/
abbrev SignedOpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with a selected unit replacing the SI length unit. -/
noncomputable def unitChoicesWithLengthUnit (unit : LengthUnit) : UnitChoices :=
  { UnitChoices.SI with length := unit }

/-- Scalar readout of a nonnegative physical length in a selected unit. -/
def lengthMagnitudeReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length (unitChoicesWithLengthUnit unit)).val : ℝ)

/-- Scalar readout of a signed optical length in a selected unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedOpticalLength) : ℝ :=
  (length (unitChoicesWithLengthUnit unit)).val

/-- Centimeter readout of a nonnegative physical length. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  lengthMagnitudeReadout LengthUnit.centimeters length

/-- Centimeter readout of a signed optical length. -/
def signedLengthInCentimeters (length : SignedOpticalLength) : ℝ :=
  signedLengthReadout LengthUnit.centimeters length

/-! ## Scenario, graph vocabulary, and primary-raster provenance -/

/-- Geometry of the reflecting optical element narrated by the problem. -/
inductive MirrorGeometry where
  | spherical
  | other
  deriving DecidableEq, Repr

/-- Path along which the object is moved. -/
inductive ObjectMotionPath where
  | centralAxis
  | other
  deriving DecidableEq, Repr

/-- The model used for the local near-axis optical response. -/
inductive OpticalApproximation where
  | firstOrderParaxial
  | finiteRayTracing
  deriving DecidableEq, Repr

/-- Quantities named on the axes of the graph described in the prose. -/
inductive GraphQuantity where
  | objectDistanceP
  | lateralMagnificationM
  deriving DecidableEq, Repr

/-- The two incompatible scenes present in the source package. -/
inductive SourceScene where
  | sphericalMirrorMagnificationGraph
  | electricFieldVectorDiagram
  deriving DecidableEq, Repr

/-- Evidence policy forced by the mismatch between the prose and primary raster. -/
inductive EvidencePolicy where
  | proseOnlyForOpticalSetup
  deriving DecidableEq, Repr

/-- Numbered points printed in the supplied vector-diagram raster. -/
inductive RasterPoint where
  | one
  | two
  | three
  | four
  | five
  | six
  deriving DecidableEq, Fintype, Repr

/-!
Literal, dimensionless integer component labels in the unrelated raster.
`none` records that the numbered point has no arrow/component label.
-/
structure SuppliedRasterAudit where
  scene : SourceScene
  arrowComponentLabel : RasterPoint → Option (ℤ × ℤ)

/-- Exact transcription of the five vector labels and the unlabelled sixth point. -/
structure RecordsSuppliedRasterMismatch (audit : SuppliedRasterAudit) : Prop where
  rasterScene : audit.scene = .electricFieldVectorDiagram
  pointOneLabel : audit.arrowComponentLabel .one = some (10, -10)
  pointTwoLabel : audit.arrowComponentLabel .two = some (2, 15)
  pointThreeLabel : audit.arrowComponentLabel .three = some (-8, 6)
  pointFourLabel : audit.arrowComponentLabel .four = some (-10, -2)
  pointFiveLabel : audit.arrowComponentLabel .five = some (6, 5)
  pointSixHasNoArrow : audit.arrowComponentLabel .six = none

/-!
Coordinate data for the graph narrated in the prose.  Horizontal coordinates
are centimeter readouts of physical object distances; vertical coordinates
are signed dimensionless lateral magnifications.  No field fixes the value at
either `10 cm` or `21 cm`.
-/
structure MagnificationDistanceGraph where
  horizontalAxis : GraphQuantity
  verticalAxis : GraphQuantity
  horizontalUnit : LengthUnit
  horizontalScalePS : LengthMagnitude
  magnificationAtCentimeterReadout : ℝ → ℝ

/-!
The physical experiment.  The focal length, image-distance response, graph,
transverse image-height response, and exact reflection residual are independent
data.  In particular, none is defined from a displayed answer.

The reflection residual is a signed radian mismatch for an axial ray striking
the mirror at the supplied centimeter height.  Its geometric first derivative
is constrained below, at the optical axis only.
-/
structure MirrorMagnificationExperiment where
  mirrorGeometry : MirrorGeometry
  objectMotionPath : ObjectMotionPath
  approximation : OpticalApproximation
  signedFocalLength : SignedOpticalLength
  graph : MagnificationDistanceGraph
  queriedObjectDistance : LengthMagnitude
  signedImageDistanceAt : LengthMagnitude → SignedOpticalLength
  imageHeightCentimetersAt : LengthMagnitude → ℝ → ℝ
  axialReflectionResidualRadiansAtHeightCm : LengthMagnitude → ℝ → ℝ
  narratedScene : SourceScene
  evidencePolicy : EvidencePolicy
  suppliedRaster : SuppliedRasterAudit

/-- The graph's dimensionless magnification at a physical object distance. -/
def lateralMagnificationAt
    (setup : MirrorMagnificationExperiment)
    (objectDistance : LengthMagnitude) : ℝ :=
  setup.graph.magnificationAtCentimeterReadout
    (lengthInCentimeters objectDistance)

/-!
The transverse first-order remainder at object distance `p`.  If its
derivative at zero is zero, then

`imageHeight(h) = -(q/p) * h + o(h)`.

Together with the independent derivative definition of graph magnification,
this yields the signed lateral-magnification law locally at the optical axis.
-/
def transverseImagingRemainderInCentimeters
    (setup : MirrorMagnificationExperiment)
    (objectDistance : LengthMagnitude)
    (objectHeightCentimeters : ℝ) : ℝ :=
  setup.imageHeightCentimetersAt objectDistance objectHeightCentimeters +
    signedLengthInCentimeters
        (setup.signedImageDistanceAt objectDistance) /
      lengthInCentimeters objectDistance * objectHeightCentimeters

/-! ## Assumptions: source readouts, physical branch, and local optical laws -/

/-!
The spherical, on-axis scenario narrated by the prose, together with an audit
of the incompatible primary raster.  The policy field prevents the raster from
being used as an optical calibration.
-/
structure MatchesSphericalMirrorScenario
    (setup : MirrorMagnificationExperiment) : Prop where
  mirrorIsSpherical : setup.mirrorGeometry = .spherical
  objectMovesOnCentralAxis : setup.objectMotionPath = .centralAxis
  usesFirstOrderParaxialModel : setup.approximation = .firstOrderParaxial
  proseNarratesMagnificationGraph :
    setup.narratedScene = .sphericalMirrorMagnificationGraph
  opticalEvidenceComesOnlyFromProse :
    setup.evidencePolicy = .proseOnlyForOpticalSetup
  suppliedRasterRecord : RecordsSuppliedRasterMismatch setup.suppliedRaster

/-!
Only the graph facts stated in the main problem prose: the axis roles, the
centimeter unit, and `p_s = 10 cm`.  Curve shape, a half-height tick, and a
value `m(10 cm) = 0.5` are deliberately absent because the primary raster does
not support them.
-/
structure MatchesTextuallyDescribedMagnificationGraph
    (setup : MirrorMagnificationExperiment) : Prop where
  horizontalAxisLabel : setup.graph.horizontalAxis = .objectDistanceP
  verticalAxisLabel : setup.graph.verticalAxis = .lateralMagnificationM
  horizontalAxisUsesCentimeters :
    setup.graph.horizontalUnit = LengthUnit.centimeters
  horizontalScaleCentimeters :
    lengthInCentimeters setup.graph.horizontalScalePS = 10

/-- The object-distance readout explicitly named by the question. -/
structure MatchesQuestionReadout
    (setup : MirrorMagnificationExperiment) : Prop where
  queriedDistanceCentimeters :
    lengthInCentimeters setup.queriedObjectDistance = 21

/-!
Positivity and nondegeneracy conditions for the physical branch.  They assign
no numerical value to the focal length, image distance, or magnification.
-/
structure HasPhysicalMirrorParameters
    (setup : MirrorMagnificationExperiment) : Prop where
  focalLengthNonzero :
    signedLengthInCentimeters setup.signedFocalLength ≠ 0
  graphScalePositive :
    0 < lengthInCentimeters setup.graph.horizontalScalePS
  queriedDistancePositive :
    0 < lengthInCentimeters setup.queriedObjectDistance
  imageDistanceNonzero :
    ∀ objectDistance : LengthMagnitude,
      0 < lengthInCentimeters objectDistance →
        signedLengthInCentimeters
            (setup.signedImageDistanceAt objectDistance) ≠ 0

/-!
Local first-order spherical-mirror physics.

* Exact reflection makes the angular residual vanish on some neighborhood of
  zero ray height.
* Exact spherical geometry gives its derivative
  `1/f - 1/p - 1/q` at the optical axis.  Since `HasDerivAt` carries a
  little-`o` remainder, this is a local paraxial contract, not a global
  finite-ray equality.
* The transverse map fixes the axis and has the graph magnification as its
  derivative there.
* The transverse residual is `o(h)`, locally relating that derivative to
  `-q/p`.

None of these fields supplies a numerical graph value at `10 cm` or `21 cm`.
-/
structure SatisfiesParaxialSphericalMirrorLaws
    (setup : MirrorMagnificationExperiment) : Prop where
  exactReflectionLawNearAxis :
    ∀ objectDistance : LengthMagnitude,
      0 < lengthInCentimeters objectDistance →
        ∀ᶠ rayHeightCentimeters : ℝ in 𝓝 0,
          setup.axialReflectionResidualRadiansAtHeightCm
              objectDistance rayHeightCentimeters = 0
  reflectionResidualHasGeometricDerivative :
    ∀ objectDistance : LengthMagnitude,
      0 < lengthInCentimeters objectDistance →
        HasDerivAt
          (setup.axialReflectionResidualRadiansAtHeightCm objectDistance)
          (1 / signedLengthInCentimeters setup.signedFocalLength -
            1 / lengthInCentimeters objectDistance -
            1 / signedLengthInCentimeters
              (setup.signedImageDistanceAt objectDistance))
          0
  opticalAxisMapsToItself :
    ∀ objectDistance : LengthMagnitude,
      0 < lengthInCentimeters objectDistance →
        setup.imageHeightCentimetersAt objectDistance 0 = 0
  lateralMagnificationIsLocalDerivative :
    ∀ objectDistance : LengthMagnitude,
      0 < lengthInCentimeters objectDistance →
        HasDerivAt
          (setup.imageHeightCentimetersAt objectDistance)
          (lateralMagnificationAt setup objectDistance)
          0
  transverseRemainderIsLittleO :
    ∀ objectDistance : LengthMagnitude,
      0 < lengthInCentimeters objectDistance →
        HasDerivAt
          (transverseImagingRemainderInCentimeters setup objectDistance)
          0
          0

/-! ## Symbolic target-side consequences -/

/-!
Differentiating the exact reflection law at the optical axis gives the
division-free Gaussian mirror relation at the queried object distance.
-/
lemma gaussianMirrorRelationAtQuery
    (setup : MirrorMagnificationExperiment)
    (_question : MatchesQuestionReadout setup)
    (_physical : HasPhysicalMirrorParameters setup)
    (_laws : SatisfiesParaxialSphericalMirrorLaws setup) :
    signedLengthInCentimeters setup.signedFocalLength *
        (lengthInCentimeters setup.queriedObjectDistance +
          signedLengthInCentimeters
            (setup.signedImageDistanceAt setup.queriedObjectDistance)) =
      lengthInCentimeters setup.queriedObjectDistance *
        signedLengthInCentimeters
          (setup.signedImageDistanceAt setup.queriedObjectDistance) := by
  sorry

/-!
The derivative definition of lateral magnification and the local transverse
remainder give `m p = -q` at the queried object distance.
-/
lemma transverseMagnificationRelationAtQuery
    (setup : MirrorMagnificationExperiment)
    (_question : MatchesQuestionReadout setup)
    (_physical : HasPhysicalMirrorParameters setup)
    (_laws : SatisfiesParaxialSphericalMirrorLaws setup) :
    lateralMagnificationAt setup setup.queriedObjectDistance *
        lengthInCentimeters setup.queriedObjectDistance =
      -signedLengthInCentimeters
        (setup.signedImageDistanceAt setup.queriedObjectDistance) := by
  sorry

/-! ## Displayed-answer metadata -/

/-- Labels of the four answer choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless magnification printed beside each answer choice. -/
def displayedMagnification : AnswerChoice → ℝ
  | .A => 0.16
  | .B => 0.22
  | .C => 0.28
  | .D => 0.32

/-- The answer label recorded by the dataset, retained as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a displayed magnification to the nearest hundredth. -/
def MatchesDisplayedMagnification
    (magnification : ℝ) (choice : AnswerChoice) : Prop :=
  |magnification - displayedMagnification choice| ≤ 0.005

/-!
Because the supplied raster contains no mirror graph, the data do not fix a
numerical focal length or select one of the displayed choices.  What the local
spherical-mirror model does determine is the symbolic first-order relation

`m(p) * (f - p) = f`.

At the question's `p = 21 cm`, a numerical magnification still requires an
independent focal-length or genuine graph calibration.  The historical target
name is retained, while choice D remains metadata rather than a conclusion.

This formalizes blueprint label `thm:physics:phyx_mini_0478:target`, subject to
the blueprint redraft requested in the task result.
-/
theorem problem_phyx_mini_0478
    (setup : MirrorMagnificationExperiment)
    (_scenario : MatchesSphericalMirrorScenario setup)
    (_graph : MatchesTextuallyDescribedMagnificationGraph setup)
    (_question : MatchesQuestionReadout setup)
    (_physical : HasPhysicalMirrorParameters setup)
    (_laws : SatisfiesParaxialSphericalMirrorLaws setup) :
    lateralMagnificationAt setup setup.queriedObjectDistance *
        (signedLengthInCentimeters setup.signedFocalLength -
          lengthInCentimeters setup.queriedObjectDistance) =
      signedLengthInCentimeters setup.signedFocalLength := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0478
