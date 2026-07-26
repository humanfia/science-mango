import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0907

open Dimension
open scoped BigOperators

/-!
# Magnitude of the downward force on the `-1.0 nC` charge

The primary image `907.png` shows three point charges at the vertices of a
`30°`--`60°`--`90°` triangle.  A `+10 nC` charge is at the left endpoint of
the `5.0 cm` horizontal base, the target `-1.0 nC` charge is above the base,
and a charge of unspecified value `q` is at the right endpoint.  The displayed
net-force arrow on the target charge points vertically downward.

Charges, lengths, positions, force vectors, and force magnitudes are modelled
as unit-independent Physlib quantities.  Real numbers occur only as explicit
coherent-SI readouts, dimensionless angles, or literal values transcribed from
the figure and answer choices.

Assumption/target split:

* governing laws: signed vector Coulomb force for each source, force
  superposition, and the relation between force magnitude and vector norm;
* previous-part results: none;
* figure/data readouts: the two known charge values, the unspecified `q`, the
  `5.0 cm` base, the `60°` and `30°` labels, the dashed altitude and right-angle
  marker, and only the downward direction of the displayed force arrow;
* current target conclusions: the force magnitude lies between
  `1.65 * 10⁻⁴ N` and `1.75 * 10⁻⁴ N`, hence rounds to
  `1.7 * 10⁻⁴ N`, and choice C is uniquely closest.

No force magnitude or answer label occurs in a setup field or premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A unit-independent position vector in the plane of the figure. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent force vector in the plane of the figure. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- A nonnegative, unit-independent physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Coordinate `0`, pointing right along the horizontal base. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, pointing upward in the image. -/
def yAxis : Fin 2 := 1

/-- Coherent-SI readout of a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the base label in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI readout of a signed charge in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the two numerical charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI Cartesian position vector, with coordinates in metres. -/
def positionVectorInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Coherent-SI Cartesian force vector, with components in newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- Coherent-SI readout of a force magnitude in newtons. -/
def forceMagnitudeInNewtons (magnitude : ForceMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-- Read the principal representative of an angle in degrees. -/
def angleInDegrees (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-! ## Figure vocabulary and independent physical setup -/

/-- The three charged objects, named by their roles in the supplied image. -/
inductive Particle where
  | positive10nC
  | targetNegative1nC
  | unknownQ
  deriving DecidableEq, Fintype, Repr

/-- The two particles exerting electrostatic force on the target charge. -/
inductive ForceSource where
  | positive10nC
  | unknownQ
  deriving DecidableEq, Fintype, Repr

/-- Regard a force source as one of the three pictured particles. -/
def ForceSource.toParticle : ForceSource → Particle
  | .positive10nC => .positive10nC
  | .unknownQ => .unknownQ

/-- Geometric site occupied by each charge in the triangle. -/
inductive ChargeSite where
  | leftBase
  | upperVertex
  | rightBase
  deriving DecidableEq, Fintype, Repr

/-- Site at which each named particle appears. -/
def expectedParticleSite : Particle → ChargeSite
  | .positive10nC => .leftBase
  | .targetNegative1nC => .upperVertex
  | .unknownQ => .rightBase

/-- Text printed beside each charge circle. -/
def expectedParticleLabel : Particle → String
  | .positive10nC => "10 nC"
  | .targetNegative1nC => "-1.0 nC"
  | .unknownQ => "q"

/-- Numerical nanocoulomb data printed in the image; `q` is unspecified. -/
def expectedPrintedChargeNanocoulombs : Particle → Option ℝ
  | .positive10nC => some 10
  | .targetNegative1nC => some (-1)
  | .unknownQ => none

/-- Sign glyph drawn inside a charge circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The unknown `q` circle has no sign glyph in the supplied image. -/
def expectedChargeSign : Particle → Option FigureChargeSign
  | .positive10nC => some .plus
  | .targetNegative1nC => some .minus
  | .unknownQ => none

/-- Fill colour of a charge circle in the supplied raster. -/
inductive FigureChargeColor where
  | red
  | cyan
  | gray
  deriving DecidableEq, Repr

/-- Expected circle colour of each particle. -/
def expectedChargeColor : Particle → FigureChargeColor
  | .positive10nC => .red
  | .targetNegative1nC => .cyan
  | .unknownQ => .gray

/-- The two printed acute angles at the endpoints of the base. -/
inductive BaseVertex where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Angle in degrees printed at each base vertex. -/
def expectedBaseAngleDegrees : BaseVertex → ℝ
  | .left => 60
  | .right => 30

/-- The three dashed sides forming the charge triangle. -/
inductive TriangleSide where
  | leftToUpper
  | upperToRight
  | base
  deriving DecidableEq, Fintype, Repr

/-- Direction of the single red force arrow. -/
inductive ArrowDirection where
  | down
  deriving DecidableEq, Repr

/-- Literal presentation data transcribed from primary image `907.png`. -/
structure ThreeChargeTriangleFigure where
  particleSite : Particle → ChargeSite
  printedParticleLabel : Particle → String
  printedChargeNanocoulombs : Particle → Option ℝ
  chargeSignGlyph : Particle → Option FigureChargeSign
  chargeCircleColor : Particle → FigureChargeColor
  triangleSideDashed : TriangleSide → Bool
  printedBaseLengthCentimeters : ℝ
  printedBaseAngleDegrees : BaseVertex → ℝ
  altitudeFromUpperVertexDashed : Bool
  rightAngleMarkerAtAltitudeFoot : Bool
  forceArrowShown : Bool
  forceArrowStartsAtTargetCharge : Bool
  forceArrowRepresentsNetForce : Bool
  forceArrowDirection : ArrowDirection
  forceArrowHasNumericalMagnitude : Bool

/-!
Independent physical quantities and force observables.  In particular, the
unknown charge, pairwise forces, net force, and net-force magnitude are not
defined from the recorded answer.
-/
structure ThreeChargeTriangleSetup where
  figure : ThreeChargeTriangleFigure
  modeledAsPointCharge : Particle → Bool
  charge : Particle → SignedChargeQuantity
  position : Particle → PlanarPositionQuantity
  baseSeparation : LengthQuantity
  altitudeFoot : PlanarPositionQuantity
  baseAngle : BaseVertex → Real.Angle
  electromagneticSystem : Electromagnetism.EMSystem
  forceOnTargetFrom : ForceSource → PlanarForceQuantity
  resultantForceOnTarget : PlanarForceQuantity
  resultantForceMagnitude : ForceMagnitudeQuantity

/-- Displacement from a source particle to the target particle, in metres. -/
def displacementFromSourceToTargetInMeters
    (setup : ThreeChargeTriangleSetup)
    (source : ForceSource) : EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters (setup.position .targetNegative1nC) -
    positionVectorInMeters (setup.position source.toParticle)

/-! ## Scenario, primary-image evidence, and triangle geometry -/

/-- All three small charged objects are idealized as point charges. -/
structure MatchesThreePointChargeScenario
    (setup : ThreeChargeTriangleSetup) : Prop where
  allParticlesArePointCharges :
    ∀ particle, setup.modeledAsPointCharge particle = true

/-!
Literal qualitative content of the primary raster.  The arrow information
records only which force is depicted and its direction, never its magnitude.
-/
structure MatchesSuppliedThreeChargeTriangleFigure
    (setup : ThreeChargeTriangleSetup) : Prop where
  particleLocations : ∀ particle,
    setup.figure.particleSite particle = expectedParticleSite particle
  printedParticleLabels : ∀ particle,
    setup.figure.printedParticleLabel particle = expectedParticleLabel particle
  printedChargeValues : ∀ particle,
    setup.figure.printedChargeNanocoulombs particle =
      expectedPrintedChargeNanocoulombs particle
  printedChargeSigns : ∀ particle,
    setup.figure.chargeSignGlyph particle = expectedChargeSign particle
  printedChargeColors : ∀ particle,
    setup.figure.chargeCircleColor particle = expectedChargeColor particle
  everyTriangleSideIsDashed : ∀ side,
    setup.figure.triangleSideDashed side = true
  baseLengthLabel : setup.figure.printedBaseLengthCentimeters = 5
  baseAngleLabels : ∀ vertex,
    setup.figure.printedBaseAngleDegrees vertex =
      expectedBaseAngleDegrees vertex
  altitudeIsDashed : setup.figure.altitudeFromUpperVertexDashed = true
  rightAngleMarkerIsShown :
    setup.figure.rightAngleMarkerAtAltitudeFoot = true
  netForceArrowIsShown : setup.figure.forceArrowShown = true
  netForceArrowStartsAtTarget :
    setup.figure.forceArrowStartsAtTargetCharge = true
  arrowRepresentsNetForce :
    setup.figure.forceArrowRepresentsNetForce = true
  arrowPointsDown : setup.figure.forceArrowDirection = .down
  noForceMagnitudeIsPrinted :
    setup.figure.forceArrowHasNumericalMagnitude = false

/-!
Calibration of the numerical figure labels to physical quantities.  The
unknown charge `q` deliberately has no numerical calibration here.
-/
structure MatchesProblemPhysicalReadouts
    (setup : ThreeChargeTriangleSetup) : Prop where
  positiveChargeLabel :
    chargeInNanocoulombs (setup.charge .positive10nC) = 10
  targetChargeLabel :
    chargeInNanocoulombs (setup.charge .targetNegative1nC) = -1
  baseLengthLabel : lengthInCentimeters setup.baseSeparation = 5
  leftAngleLabel : angleInDegrees (setup.baseAngle .left) = 60
  rightAngleLabel : angleInDegrees (setup.baseAngle .right) = 30

/-!
A coordinate realization of the displayed `30°`--`60°`--`90°` triangle.
The left base charge is the origin, the right base charge is on the positive
horizontal axis, and the altitude foot is one quarter of the base length from
the left endpoint.
-/
structure SatisfiesDisplayedTriangleGeometry
    (setup : ThreeChargeTriangleSetup) : Prop where
  baseSeparationPositive : 0 < lengthInMeters setup.baseSeparation
  leftAngleRadians : (setup.baseAngle .left).toReal = Real.pi / 3
  rightAngleRadians : (setup.baseAngle .right).toReal = Real.pi / 6
  leftChargeAtOrigin :
    positionVectorInMeters (setup.position .positive10nC) = !₂[0, 0]
  rightChargeOnBase :
    positionVectorInMeters (setup.position .unknownQ) =
      !₂[lengthInMeters setup.baseSeparation, 0]
  altitudeFootCoordinates :
    positionVectorInMeters setup.altitudeFoot =
      !₂[lengthInMeters setup.baseSeparation / 4, 0]
  targetCoordinates :
    positionVectorInMeters (setup.position .targetNegative1nC) =
      !₂[lengthInMeters setup.baseSeparation / 4,
        Real.sqrt 3 * lengthInMeters setup.baseSeparation / 4]

/-!
The rounded textbook value of Coulomb's constant.  Physlib's scalar is read
coherently in `N m²/C²` in the force law below.
-/
structure UsesSchoolCoulombConstant
    (setup : ThreeChargeTriangleSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-- Nondegeneracy and positivity conditions selecting the physical branch. -/
structure HasPhysicalElectrostaticParameters
    (setup : ThreeChargeTriangleSetup) : Prop where
  targetChargeNonzero :
    chargeInCoulombs (setup.charge .targetNegative1nC) ≠ 0
  positiveSourceChargeNonzero :
    chargeInCoulombs (setup.charge .positive10nC) ≠ 0
  unknownChargeNonzero : chargeInCoulombs (setup.charge .unknownQ) ≠ 0
  everySourceSeparatedFromTarget : ∀ source,
    0 < ‖displacementFromSourceToTargetInMeters setup source‖
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
The figure's downward arrow is calibrated to the independently modelled net
force: its horizontal component vanishes and its vertical component is
negative.  This supplies direction only, not the requested magnitude.
-/
structure CalibratesDisplayedDownwardForceDirection
    (setup : ThreeChargeTriangleSetup) : Prop where
  horizontalComponentVanishes :
    forceVectorInNewtons setup.resultantForceOnTarget xAxis = 0
  verticalComponentIsNegative :
    forceVectorInNewtons setup.resultantForceOnTarget yAxis < 0

/-! ## Governing electrostatic laws -/

/-!
For source charge `qₛ`, target charge `qₜ`, and displacement `r` from source
to target, the force on the target is

`F = k qₜ qₛ r / ‖r‖³`.

The signed product of the charges supplies attraction or repulsion.  This is
a general pairwise law and contains no requested net-force magnitude.
-/
structure SatisfiesVectorCoulombForceLaw
    (setup : ThreeChargeTriangleSetup) : Prop where
  forceOfEachSource : ∀ source,
    forceVectorInNewtons (setup.forceOnTargetFrom source) =
      (setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge .targetNegative1nC) *
          chargeInCoulombs (setup.charge source.toParticle) /
        ‖displacementFromSourceToTargetInMeters setup source‖ ^ 3) •
          displacementFromSourceToTargetInMeters setup source

/-- The net force is the vector sum of the two pairwise Coulomb forces. -/
structure SatisfiesElectrostaticForceSuperposition
    (setup : ThreeChargeTriangleSetup) : Prop where
  resultantIsSourceSum :
    forceVectorInNewtons setup.resultantForceOnTarget =
      ∑ source : ForceSource,
        forceVectorInNewtons (setup.forceOnTargetFrom source)

/-! The physical magnitude observable is the norm of the net force vector. -/
structure SatisfiesResultantForceMagnitudeLaw
    (setup : ThreeChargeTriangleSetup) : Prop where
  magnitudeIsNorm :
    forceMagnitudeInNewtons setup.resultantForceMagnitude =
      ‖forceVectorInNewtons setup.resultantForceOnTarget‖

/-! ## Derived geometry and displayed-answer target -/

/-!
The coordinate realization gives the two source-to-target distances of the
`30°`--`60°`--`90°` triangle.
-/
lemma source_target_distances_from_triangle
    (setup : ThreeChargeTriangleSetup)
    (_geometry : SatisfiesDisplayedTriangleGeometry setup) :
    ‖displacementFromSourceToTargetInMeters setup .positive10nC‖ =
        lengthInMeters setup.baseSeparation / 2 ∧
      ‖displacementFromSourceToTargetInMeters setup .unknownQ‖ =
        Real.sqrt 3 * lengthInMeters setup.baseSeparation / 2 := by
  constructor
  · simp only [displacementFromSourceToTargetInMeters, ForceSource.toParticle,
      _geometry.targetCoordinates, _geometry.leftChargeAtOrigin]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
    rw [show
        (lengthInMeters setup.baseSeparation / 4) ^ 2 +
            (Real.sqrt 3 * lengthInMeters setup.baseSeparation / 4) ^ 2 =
          (lengthInMeters setup.baseSeparation / 2) ^ 2 by
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (div_pos _geometry.baseSeparationPositive (by norm_num))]
  · simp only [displacementFromSourceToTargetInMeters, ForceSource.toParticle,
      _geometry.targetCoordinates, _geometry.rightChargeOnBase]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
    rw [show
        (lengthInMeters setup.baseSeparation / 4 -
              lengthInMeters setup.baseSeparation) ^ 2 +
            (Real.sqrt 3 * lengthInMeters setup.baseSeparation / 4) ^ 2 =
          (Real.sqrt 3 * lengthInMeters setup.baseSeparation / 2) ^ 2 by
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (div_pos
        (mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))
          _geometry.baseSeparationPositive) (by norm_num))]

/-- Labels attached to the four force-magnitude choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnitude in newtons printed beside each displayed answer label. -/
def displayedForceMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 725 / 1000000
  | .B => 635 / 1000000
  | .C => 17 / 100000
  | .D => 133 / 1000000

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
`value` rounds to `displayed` at the stated resolution when it lies strictly
within half a resolution step.  The last digit of `1.7 * 10⁻⁴ N` has
resolution `0.1 * 10⁻⁴ N = 10⁻⁵ N`.
-/
def RoundsToAtResolution
    (value displayed resolution : ℝ) : Prop :=
  0 < resolution ∧ |value - displayed| < resolution / 2

/-- A displayed choice is uniquely closest to the physical force magnitude. -/
def IsUniqueClosestDisplayedForceChoice
    (setup : ThreeChargeTriangleSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |forceMagnitudeInNewtons setup.resultantForceMagnitude -
        displayedForceMagnitudeInNewtons choice| <
      |forceMagnitudeInNewtons setup.resultantForceMagnitude -
        displayedForceMagnitudeInNewtons other|

/-!
The geometry, downward direction, Coulomb law, and superposition determine the
otherwise unspecified charge `q` sufficiently to bound the net-force
magnitude between `1.65 * 10⁻⁴ N` and `1.75 * 10⁻⁴ N`.
-/
lemma resultant_force_magnitude_numerical_bounds
    (setup : ThreeChargeTriangleSetup)
    (_readouts : MatchesProblemPhysicalReadouts setup)
    (_geometry : SatisfiesDisplayedTriangleGeometry setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalElectrostaticParameters setup)
    (_direction : CalibratesDisplayedDownwardForceDirection setup)
    (_coulomb : SatisfiesVectorCoulombForceLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup)
    (_magnitude : SatisfiesResultantForceMagnitudeLaw setup) :
    (33 : ℝ) / 200000 <
        forceMagnitudeInNewtons setup.resultantForceMagnitude ∧
      forceMagnitudeInNewtons setup.resultantForceMagnitude <
        (7 : ℝ) / 40000 := by
  have baseLength :
      lengthInMeters setup.baseSeparation = (1 : ℝ) / 20 := by
    have h := _readouts.baseLengthLabel
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have targetCharge :
      chargeInCoulombs (setup.charge .targetNegative1nC) =
        (-1 : ℝ) / 1000000000 := by
    have h := _readouts.targetChargeLabel
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have positiveCharge :
      chargeInCoulombs (setup.charge .positive10nC) =
        (1 : ℝ) / 100000000 := by
    have h := _readouts.positiveChargeLabel
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have coulombConstant :
      setup.electromagneticSystem.coulombConstant = (9000000000 : ℝ) := by
    have h := _constant.coulombConstantCalibration
    norm_num at h ⊢
    exact h
  obtain ⟨positiveDistance, _⟩ :=
    source_target_distances_from_triangle setup _geometry
  have positiveForceX :
      forceVectorInNewtons (setup.forceOnTargetFrom .positive10nC) xAxis =
        (-9 : ℝ) / 125000 := by
    have h := congrArg
      (fun force : EuclideanSpace ℝ (Fin 2) => force xAxis)
      (_coulomb.forceOfEachSource .positive10nC)
    rw [coulombConstant, targetCharge] at h
    simp only [ForceSource.toParticle] at h
    rw [positiveCharge, positiveDistance, baseLength] at h
    simp [displacementFromSourceToTargetInMeters, ForceSource.toParticle,
      _geometry.targetCoordinates, _geometry.leftChargeAtOrigin,
      baseLength, xAxis] at h ⊢
    norm_num at h ⊢
    exact h
  have positiveForceY :
      forceVectorInNewtons (setup.forceOnTargetFrom .positive10nC) yAxis =
        (-9 : ℝ) * Real.sqrt 3 / 125000 := by
    have h := congrArg
      (fun force : EuclideanSpace ℝ (Fin 2) => force yAxis)
      (_coulomb.forceOfEachSource .positive10nC)
    rw [coulombConstant, targetCharge] at h
    simp only [ForceSource.toParticle] at h
    rw [positiveCharge, positiveDistance, baseLength] at h
    simp [displacementFromSourceToTargetInMeters, ForceSource.toParticle,
      _geometry.targetCoordinates, _geometry.leftChargeAtOrigin,
      baseLength, yAxis] at h ⊢
    norm_num at h ⊢
    ring_nf at h ⊢
    exact h
  have unknownForceComponentRelation :
      3 * forceVectorInNewtons (setup.forceOnTargetFrom .unknownQ) yAxis +
        Real.sqrt 3 *
          forceVectorInNewtons (setup.forceOnTargetFrom .unknownQ) xAxis = 0 := by
    have hx := congrArg
      (fun force : EuclideanSpace ℝ (Fin 2) => force xAxis)
      (_coulomb.forceOfEachSource .unknownQ)
    have hy := congrArg
      (fun force : EuclideanSpace ℝ (Fin 2) => force yAxis)
      (_coulomb.forceOfEachSource .unknownQ)
    simp [displacementFromSourceToTargetInMeters, ForceSource.toParticle,
      _geometry.targetCoordinates, _geometry.rightChargeOnBase,
      baseLength, xAxis] at hx
    simp [displacementFromSourceToTargetInMeters, ForceSource.toParticle,
      _geometry.targetCoordinates, _geometry.rightChargeOnBase,
      baseLength, yAxis] at hy
    simp only [xAxis, yAxis]
    rw [hx, hy]
    ring
  have sumTwoSources (f : ForceSource → ℝ) :
      ∑ source, f source = f .positive10nC + f .unknownQ := by
    rw [show Finset.univ = {.positive10nC, .unknownQ} by
      ext source
      cases source <;> simp]
    simp
  have resultantX :
      forceVectorInNewtons setup.resultantForceOnTarget xAxis =
        forceVectorInNewtons (setup.forceOnTargetFrom .positive10nC) xAxis +
          forceVectorInNewtons (setup.forceOnTargetFrom .unknownQ) xAxis := by
    calc
      forceVectorInNewtons setup.resultantForceOnTarget xAxis =
          (∑ source : ForceSource,
            forceVectorInNewtons (setup.forceOnTargetFrom source)) xAxis :=
        congrArg (fun force : EuclideanSpace ℝ (Fin 2) => force xAxis)
          _superposition.resultantIsSourceSum
      _ = ∑ source : ForceSource,
          forceVectorInNewtons (setup.forceOnTargetFrom source) xAxis := by
            simp
      _ = _ := sumTwoSources _
  have resultantY :
      forceVectorInNewtons setup.resultantForceOnTarget yAxis =
        forceVectorInNewtons (setup.forceOnTargetFrom .positive10nC) yAxis +
          forceVectorInNewtons (setup.forceOnTargetFrom .unknownQ) yAxis := by
    calc
      forceVectorInNewtons setup.resultantForceOnTarget yAxis =
          (∑ source : ForceSource,
            forceVectorInNewtons (setup.forceOnTargetFrom source)) yAxis :=
        congrArg (fun force : EuclideanSpace ℝ (Fin 2) => force yAxis)
          _superposition.resultantIsSourceSum
      _ = ∑ source : ForceSource,
          forceVectorInNewtons (setup.forceOnTargetFrom source) yAxis := by
            simp
      _ = _ := sumTwoSources _
  have unknownForceX :
      forceVectorInNewtons (setup.forceOnTargetFrom .unknownQ) xAxis =
        (9 : ℝ) / 125000 := by
    linarith [_direction.horizontalComponentVanishes, resultantX, positiveForceX]
  have unknownForceY :
      forceVectorInNewtons (setup.forceOnTargetFrom .unknownQ) yAxis =
        (-3 : ℝ) * Real.sqrt 3 / 125000 := by
    rw [unknownForceX] at unknownForceComponentRelation
    nlinarith
  have netForceY :
      forceVectorInNewtons setup.resultantForceOnTarget yAxis =
        (-12 : ℝ) * Real.sqrt 3 / 125000 := by
    rw [resultantY, positiveForceY, unknownForceY]
    ring
  have netForceNorm :
      ‖forceVectorInNewtons setup.resultantForceOnTarget‖ =
        -forceVectorInNewtons setup.resultantForceOnTarget yAxis := by
    have horizontalZero :
        forceVectorInNewtons setup.resultantForceOnTarget (0 : Fin 2) = 0 := by
      simpa [xAxis] using _direction.horizontalComponentVanishes
    have verticalNegative :
        forceVectorInNewtons setup.resultantForceOnTarget (1 : Fin 2) < 0 := by
      simpa [yAxis] using _direction.verticalComponentIsNegative
    simp only [yAxis]
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [horizontalZero, zero_pow (by norm_num : 2 ≠ 0), zero_add,
      Real.sqrt_sq_eq_abs,
      abs_of_neg verticalNegative]
  have magnitudeValue :
      forceMagnitudeInNewtons setup.resultantForceMagnitude =
        (12 : ℝ) * Real.sqrt 3 / 125000 := by
    rw [_magnitude.magnitudeIsNorm, netForceNorm, netForceY]
    ring
  rw [magnitudeValue]
  constructor <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg (3 : ℝ)]

/-!
The force magnitude is approximately `1.66 * 10⁻⁴ N`, so it rounds to the
displayed `1.7 * 10⁻⁴ N` and choice C is uniquely closest.

This declaration formalizes
`thm:physics:phyx_mini_0907:target`.
-/
theorem problem_phyx_mini_0907
    (setup : ThreeChargeTriangleSetup)
    (_scenario : MatchesThreePointChargeScenario setup)
    (_figure : MatchesSuppliedThreeChargeTriangleFigure setup)
    (_readouts : MatchesProblemPhysicalReadouts setup)
    (_geometry : SatisfiesDisplayedTriangleGeometry setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalElectrostaticParameters setup)
    (_direction : CalibratesDisplayedDownwardForceDirection setup)
    (_coulomb : SatisfiesVectorCoulombForceLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup)
    (_magnitude : SatisfiesResultantForceMagnitudeLaw setup) :
    (33 : ℝ) / 200000 <
        forceMagnitudeInNewtons setup.resultantForceMagnitude ∧
      forceMagnitudeInNewtons setup.resultantForceMagnitude <
        (7 : ℝ) / 40000 ∧
      RoundsToAtResolution
        (forceMagnitudeInNewtons setup.resultantForceMagnitude)
        (displayedForceMagnitudeInNewtons recordedDatasetAnswer)
        (1 / 100000) ∧
      IsUniqueClosestDisplayedForceChoice setup recordedDatasetAnswer := by
  have bounds := resultant_force_magnitude_numerical_bounds setup _readouts
    _geometry _constant _physical _direction _coulomb _superposition _magnitude
  let value := forceMagnitudeInNewtons setup.resultantForceMagnitude
  have closeToC : |value - 17 / 100000| < (1 : ℝ) / 200000 := by
    rw [abs_lt]
    dsimp [value]
    constructor <;> linarith [bounds.1, bounds.2]
  refine ⟨bounds.1, bounds.2, ?_, ?_⟩
  · refine ⟨by norm_num, ?_⟩
    change |value - 17 / 100000| < (1 : ℝ) / 100000 / 2
    convert closeToC using 1
    · norm_num
  · intro other other_ne
    change |value - displayedForceMagnitudeInNewtons recordedDatasetAnswer| <
      |value - displayedForceMagnitudeInNewtons other|
    have closeToRecorded :
        |value - displayedForceMagnitudeInNewtons recordedDatasetAnswer| <
          (1 : ℝ) / 200000 := by
      simpa [recordedDatasetAnswer, displayedForceMagnitudeInNewtons] using closeToC
    fin_cases other
    · apply lt_trans closeToRecorded
      rw [displayedForceMagnitudeInNewtons, abs_of_neg]
      · dsimp [value]
        linarith [bounds.2]
      · dsimp [value]
        linarith [bounds.2]
    · apply lt_trans closeToRecorded
      rw [displayedForceMagnitudeInNewtons, abs_of_neg]
      · dsimp [value]
        linarith [bounds.2]
      · dsimp [value]
        linarith [bounds.2]
    · exact (other_ne rfl).elim
    · apply lt_trans closeToRecorded
      rw [displayedForceMagnitudeInNewtons, abs_of_pos]
      · dsimp [value]
        linarith [bounds.1]
      · dsimp [value]
        linarith [bounds.1]

end PhyXMiniProblems.ProblemPhyXMini0907
