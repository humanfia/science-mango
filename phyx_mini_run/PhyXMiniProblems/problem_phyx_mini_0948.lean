import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0948

open Dimension Space Matrix

/-!
# Magnetic field supporting a pivoted rectangular current loop

A rectangular wire loop is pivoted without friction about its side `ab`.  The
primary figure labels `ab` as `6.00 cm`, the transverse side as `8.00 cm`, and
shows current flowing from `a` to `b`.  The wire has linear mass density
`0.15 g/cm` and carries `8.2 A`.  We seek the magnetic field parallel to the
`y`-axis for which the loop is in rotational equilibrium when its plane is
tilted `30.0°` away from the `yz`-plane.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers are used only for coherent-SI or explicitly converted scalar
readouts, and for the dimensionless angle.

Assumption/target split:

* governing laws: wire mass equals linear density times perimeter, magnetic
  torque is `I A B cos θ`, gravitational torque is
  `m g (h/2) sin θ`, the two torques balance, and the right-hand/cross-product
  direction laws determine the torque direction;
* previous-part results: none;
* figure/data readouts: the `6.00 cm` pivot edge `ab` lies along positive `z`,
  the reference `8.00 cm` edge lies along negative `y`, current traverses
  `a → b → c → d → a`, the swing is positive about `z`, the angle is `30.0°`,
  the linear density is `0.15 g/cm`, and the current is `8.2 A`;
* current target conclusion: the field magnitude rounds to `0.024 T` and its
  direction is positive `y`.

The target magnitude and sign are not fields of any premise structure.
-/

/-! ## Dimensionful physical quantities and scalar readouts -/

/-- The dimension `M T⁻¹ C⁻¹` of magnetic flux density (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C T⁻¹` of electric current (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- The dimension `M L⁻¹` of linear mass density. -/
def linearMassDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹

/-- The dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent mass. -/
abbrev MassMagnitude : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent mass per unit length. -/
abbrev LinearMassDensityMagnitude : Type :=
  Dimensionful (WithDim linearMassDensityDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent torque magnitude. -/
abbrev TorqueMagnitude : Type :=
  Dimensionful (WithDim torqueDimension NNReal)

/-- Coherent-SI readout of magnetic flux density, in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  ((fieldMagnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of electric current, in amperes. -/
def electricCurrentInAmperes
    (current : ElectricCurrentMagnitude) : ℝ :=
  ((current UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of length, in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout obtained from the coherent-SI length readout. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI readout of mass, in kilograms. -/
def massInKilograms (mass : MassMagnitude) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of linear mass density, in kilograms per metre. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityMagnitude) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Grams-per-centimetre readout; `1 kg/m = 10 g/cm`. -/
def linearMassDensityInGramsPerCentimeter
    (density : LinearMassDensityMagnitude) : ℝ :=
  10 * linearMassDensityInKilogramsPerMeter density

/-- Coherent-SI readout of acceleration, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of torque, in newton metres. -/
def torqueInNewtonMeters (torque : TorqueMagnitude) : ℝ :=
  ((torque UnitChoices.SI).val : ℝ)

/-! ## Axes, oriented loop geometry, and primary-figure labels -/

/-- The coordinate axes printed in the primary figure. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- The six signed coordinate-axis directions. -/
inductive SignedAxisDirection where
  | positiveX
  | negativeX
  | positiveY
  | negativeY
  | positiveZ
  | negativeZ
  deriving DecidableEq, Fintype, Repr

/-- The unsigned coordinate axis underlying a signed direction. -/
def SignedAxisDirection.axis : SignedAxisDirection → CoordinateAxis
  | .positiveX | .negativeX => .x
  | .positiveY | .negativeY => .y
  | .positiveZ | .negativeZ => .z

/-- Cartesian spatial vectors used for the field and right-hand rules. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Unit vector along a signed coordinate-axis direction. -/
def SignedAxisDirection.unitVector : SignedAxisDirection → SpatialVector
  | .positiveX => EuclideanSpace.single 0 1
  | .negativeX => EuclideanSpace.single 0 (-1)
  | .positiveY => EuclideanSpace.single 1 1
  | .negativeY => EuclideanSpace.single 1 (-1)
  | .positiveZ => EuclideanSpace.single 2 1
  | .negativeZ => EuclideanSpace.single 2 (-1)

/-- A nonzero vector is a positive multiple of the indicated signed axis. -/
def HasSignedAxisDirection
    (vector : SpatialVector) (direction : SignedAxisDirection) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧
    vector = magnitude • direction.unitVector

/-- The Physlib cross product of two signed unit directions has a third one. -/
def CrossesToDirection
    (first second result : SignedAxisDirection) : Prop :=
  first.unitVector ⨯ₑ₃ second.unitVector = result.unitVector

/-- Lettered vertices of the rectangular loop. -/
inductive LoopVertex where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- Oriented boundary edges, named by their first and second endpoint. -/
inductive LoopEdge where
  | ab
  | bc
  | cd
  | da
  deriving DecidableEq, Fintype, Repr

/-- Which way current traverses a named boundary edge. -/
inductive EdgeTraversal where
  | firstToSecond
  | secondToFirst
  deriving DecidableEq, Repr

/-- Shape classification of the current-carrying wire loop. -/
inductive LoopShape where
  | rectangular
  | other
  deriving DecidableEq, Repr

/-!
Literal geometric and directional information carried by image `948.png`.
The unknown magnetic field is deliberately absent from this record.
-/
structure RectangularLoopFigure where
  axisShown : CoordinateAxis → Bool
  pivotEdge : LoopEdge
  pivotDirectionFromAToB : SignedAxisDirection
  referenceTransverseDirectionFromBToC : SignedAxisDirection
  currentTraversal : LoopEdge → EdgeTraversal
  edgeLengthLabelCentimeters : LoopEdge → Option ℝ
  angleMarkerDegrees : ℝ
  swingDirectionAboutPivot : SignedAxisDirection

/-! ## Apparatus, problem data, and governing laws -/

/-- Independent physical quantities describing the pivoted current loop. -/
structure PivotedCurrentLoopSetup where
  loopShape : LoopShape
  pivotIsFrictionless : Bool
  magneticField : Electromagnetism.MagneticField 3
  uniformFieldRegion : Set (Time × Space 3)
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  magneticFieldDirection : SignedAxisDirection
  currentMagnitude : ElectricCurrentMagnitude
  wireLinearMassDensity : LinearMassDensityMagnitude
  pivotEdgeLength : LengthMagnitude
  transverseEdgeLength : LengthMagnitude
  totalWireMass : MassMagnitude
  gravitationalAcceleration : AccelerationMagnitude
  equilibriumAngleRadians : ℝ
  referenceMagneticMomentDirection : SignedAxisDirection
  magneticTorqueDirection : SignedAxisDirection
  magneticTorqueMagnitude : TorqueMagnitude
  gravitationalTorqueMagnitude : TorqueMagnitude
  figure : RectangularLoopFigure

/-!
Primary-raster evidence: axes, edge labels, current arrows, the `30.0°` swing,
and the direction of that swing.  It contains no magnetic-field answer.
-/
structure MatchesPrimaryFigure (setup : PivotedCurrentLoopSetup) : Prop where
  xAxisShown : setup.figure.axisShown .x = true
  yAxisShown : setup.figure.axisShown .y = true
  zAxisShown : setup.figure.axisShown .z = true
  pivotEdgeIsAB : setup.figure.pivotEdge = .ab
  pivotPointsFromAToBAlongPositiveZ :
    setup.figure.pivotDirectionFromAToB = .positiveZ
  referenceSidePointsFromBToCAlongNegativeY :
    setup.figure.referenceTransverseDirectionFromBToC = .negativeY
  pivotEdgeLabelIsSixCentimeters :
    setup.figure.edgeLengthLabelCentimeters .ab = some 6
  transverseEdgeLabelIsEightCentimeters :
    setup.figure.edgeLengthLabelCentimeters .bc = some 8
  currentFlowsFromAToB :
    setup.figure.currentTraversal .ab = .firstToSecond
  currentFlowsFromBToC :
    setup.figure.currentTraversal .bc = .firstToSecond
  currentFlowsFromCToD :
    setup.figure.currentTraversal .cd = .firstToSecond
  currentFlowsFromDToA :
    setup.figure.currentTraversal .da = .firstToSecond
  angleMarkerIsThirtyDegrees : setup.figure.angleMarkerDegrees = 30
  swingIsPositiveAboutPivot :
    setup.figure.swingDirectionAboutPivot = .positiveZ

/-!
Problem-statement data and conversions.  `fieldIsParallelToYAxis` restricts the
unknown field to one of the two `y` directions but does not choose its sign.
-/
structure MatchesProblemDescription
    (setup : PivotedCurrentLoopSetup) : Prop where
  loopIsRectangular : setup.loopShape = .rectangular
  pivotIsFrictionless : setup.pivotIsFrictionless = true
  linearDensityInGramsPerCentimeter :
    linearMassDensityInGramsPerCentimeter setup.wireLinearMassDensity = 0.15
  currentInAmperes : electricCurrentInAmperes setup.currentMagnitude = 8.2
  pivotLengthInCentimeters : lengthInCentimeters setup.pivotEdgeLength = 6
  transverseLengthInCentimeters :
    lengthInCentimeters setup.transverseEdgeLength = 8
  angleMatchesFigureMarker :
    setup.equilibriumAngleRadians =
      setup.figure.angleMarkerDegrees * Real.pi / 180
  fieldIsParallelToYAxis : setup.magneticFieldDirection.axis = .y

/-- Standard near-Earth gravitational acceleration used by the textbook model. -/
structure HasStandardNearEarthGravity
    (setup : PivotedCurrentLoopSetup) : Prop where
  gravitationalAccelerationIsNinePointEight :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 9.8

/-- Positivity and nondegeneracy conditions for the physical equilibrium. -/
structure HasPhysicalLoopParameters
    (setup : PivotedCurrentLoopSetup) : Prop where
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  currentPositive : 0 < electricCurrentInAmperes setup.currentMagnitude
  pivotLengthPositive : 0 < lengthInMeters setup.pivotEdgeLength
  transverseLengthPositive : 0 < lengthInMeters setup.transverseEdgeLength
  densityPositive :
    0 < linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity
  massPositive : 0 < massInKilograms setup.totalWireMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  angleNonnegative : 0 ≤ setup.equilibriumAngleRadians
  angleAcute : setup.equilibriumAngleRadians < Real.pi / 2
  fieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The Physlib magnetic vector field is uniform in magnitude and has the signed
axis direction recorded independently in the setup.
-/
structure HasUniformAppliedMagneticField
    (setup : PivotedCurrentLoopSetup) : Prop where
  uniformMagnitude : ∀ time position,
    (time, position) ∈ setup.uniformFieldRegion →
      ‖setup.magneticField time position‖ =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  uniformSignedDirection : ∀ time position,
    (time, position) ∈ setup.uniformFieldRegion →
      HasSignedAxisDirection
        (setup.magneticField time position) setup.magneticFieldDirection

/-- The mass of the wire is its linear density times its rectangular perimeter. -/
structure SatisfiesRectangularWireMassLaw
    (setup : PivotedCurrentLoopSetup) : Prop where
  massEqualsLinearDensityTimesPerimeter :
    massInKilograms setup.totalWireMass =
      linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity *
        (2 * (lengthInMeters setup.pivotEdgeLength +
          lengthInMeters setup.transverseEdgeLength))

/-!
Torque-magnitude laws about the frictionless pivot.  The angle is measured
from the `yz` reference plane.  The magnetic moment's component perpendicular
to a `y`-directed field contributes `cos θ`; the center-of-mass lever arm for
gravity contributes `sin θ`.
-/
structure SatisfiesPivotTorqueMagnitudeLaws
    (setup : PivotedCurrentLoopSetup) : Prop where
  magneticTorqueLaw :
    torqueInNewtonMeters setup.magneticTorqueMagnitude =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        electricCurrentInAmperes setup.currentMagnitude *
          lengthInMeters setup.pivotEdgeLength *
            lengthInMeters setup.transverseEdgeLength *
              Real.cos setup.equilibriumAngleRadians
  gravitationalTorqueLaw :
    torqueInNewtonMeters setup.gravitationalTorqueMagnitude =
      massInKilograms setup.totalWireMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          (lengthInMeters setup.transverseEdgeLength / 2) *
            Real.sin setup.equilibriumAngleRadians

/-!
General right-hand rules for this oriented loop.  The first equation obtains
the reference magnetic-moment normal from the two current-oriented sides.  The
second is the direction law `τ = μ × B`; the component of `μ` parallel to `B`
at nonzero tilt contributes no torque.  The third relates torque sign to the
shown swing.
-/
structure SatisfiesCurrentLoopDirectionLaws
    (setup : PivotedCurrentLoopSetup) : Prop where
  momentDirectionFromCurrentAndGeometry :
    CrossesToDirection
        setup.figure.pivotDirectionFromAToB
        setup.figure.referenceTransverseDirectionFromBToC
        setup.referenceMagneticMomentDirection
  magneticTorqueDirectionLaw :
    CrossesToDirection
        setup.referenceMagneticMomentDirection
        setup.magneticFieldDirection
        setup.magneticTorqueDirection
  torqueProducesShownSwing :
    setup.magneticTorqueDirection = setup.figure.swingDirectionAboutPivot

/-- Static rotational equilibrium about the frictionless side `ab`. -/
structure IsInRotationalEquilibrium
    (setup : PivotedCurrentLoopSetup) : Prop where
  torqueMagnitudesBalance :
    torqueInNewtonMeters setup.magneticTorqueMagnitude =
      torqueInNewtonMeters setup.gravitationalTorqueMagnitude

/-!
The general scalar consequence of wire mass, the two torque laws, and torque
balance.  It is a derived relation, not a premise containing the requested
numeric answer.
-/
lemma equilibrium_field_magnitude_formula
    (setup : PivotedCurrentLoopSetup)
    (_physical : HasPhysicalLoopParameters setup)
    (_massLaw : SatisfiesRectangularWireMassLaw setup)
    (_torqueLaws : SatisfiesPivotTorqueMagnitudeLaws setup)
    (_equilibrium : IsInRotationalEquilibrium setup) :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude =
      linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity *
        (lengthInMeters setup.pivotEdgeLength +
          lengthInMeters setup.transverseEdgeLength) *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        Real.tan setup.equilibriumAngleRadians /
        (electricCurrentInAmperes setup.currentMagnitude *
          lengthInMeters setup.pivotEdgeLength) := by
  have hcos_pos : 0 < Real.cos setup.equilibriumAngleRadians := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [_physical.angleNonnegative]
    · exact _physical.angleAcute
  have hbalance :
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          electricCurrentInAmperes setup.currentMagnitude *
          lengthInMeters setup.pivotEdgeLength *
          lengthInMeters setup.transverseEdgeLength *
          Real.cos setup.equilibriumAngleRadians =
        linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity *
          (2 * (lengthInMeters setup.pivotEdgeLength +
            lengthInMeters setup.transverseEdgeLength)) *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          (lengthInMeters setup.transverseEdgeLength / 2) *
          Real.sin setup.equilibriumAngleRadians := by
    calc
      _ = torqueInNewtonMeters setup.magneticTorqueMagnitude :=
        _torqueLaws.magneticTorqueLaw.symm
      _ = torqueInNewtonMeters setup.gravitationalTorqueMagnitude :=
        _equilibrium.torqueMagnitudesBalance
      _ = massInKilograms setup.totalWireMass *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          (lengthInMeters setup.transverseEdgeLength / 2) *
          Real.sin setup.equilibriumAngleRadians :=
        _torqueLaws.gravitationalTorqueLaw
      _ = _ := by
        rw [_massLaw.massEqualsLinearDensityTimesPerimeter]
  rw [Real.tan_eq_sin_div_cos]
  have hcurrent_ne :
      electricCurrentInAmperes setup.currentMagnitude ≠ 0 :=
    ne_of_gt _physical.currentPositive
  have hpivot_ne : lengthInMeters setup.pivotEdgeLength ≠ 0 :=
    ne_of_gt _physical.pivotLengthPositive
  have htransverse_ne : lengthInMeters setup.transverseEdgeLength ≠ 0 :=
    ne_of_gt _physical.transverseLengthPositive
  have hcos_ne : Real.cos setup.equilibriumAngleRadians ≠ 0 :=
    ne_of_gt hcos_pos
  have hcancel :
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthInMeters setup.pivotEdgeLength *
          Real.cos setup.equilibriumAngleRadians *
          electricCurrentInAmperes setup.currentMagnitude =
        linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity *
          (lengthInMeters setup.pivotEdgeLength +
            lengthInMeters setup.transverseEdgeLength) *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          Real.sin setup.equilibriumAngleRadians := by
    apply mul_left_cancel₀ htransverse_ne
    calc
      lengthInMeters setup.transverseEdgeLength *
          (magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
            lengthInMeters setup.pivotEdgeLength *
            Real.cos setup.equilibriumAngleRadians *
            electricCurrentInAmperes setup.currentMagnitude) =
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
            electricCurrentInAmperes setup.currentMagnitude *
            lengthInMeters setup.pivotEdgeLength *
            lengthInMeters setup.transverseEdgeLength *
            Real.cos setup.equilibriumAngleRadians := by ring
      _ = _ := hbalance
      _ = lengthInMeters setup.transverseEdgeLength *
          (linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity *
            (lengthInMeters setup.pivotEdgeLength +
              lengthInMeters setup.transverseEdgeLength) *
            accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
            Real.sin setup.equilibriumAngleRadians) := by ring
  field_simp [hcurrent_ne, hpivot_ne, hcos_ne]
  exact hcancel

/-! ## Reported answer and final direction -/

/-- Labels of the four displayed magnetic-field choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-flux-density magnitude in teslas printed by each answer choice. -/
def AnswerChoice.fieldMagnitudeInTeslas : AnswerChoice → ℝ
  | .A => 0.048
  | .B => 0.024
  | .C => 0.012
  | .D => 0.044

/-!
A computed field agrees with a three-decimal-place answer choice.  The strict
half-millitesla tolerance is the usual rounding interval for the displayed
precision.
-/
def MagnitudeRoundsToChoice
    (setup : PivotedCurrentLoopSetup) (choice : AnswerChoice) : Prop :=
  |magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude -
      choice.fieldMagnitudeInTeslas| < 0.0005

/-!
The balancing field is answer choice B in magnitude and points in the positive
`y` direction.  The sign follows from the shown current and positive-`z` swing;
the magnitude follows from mass and torque balance.
-/
theorem balancing_magnetic_field
    (setup : PivotedCurrentLoopSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_problem : MatchesProblemDescription setup)
    (_gravity : HasStandardNearEarthGravity setup)
    (_physical : HasPhysicalLoopParameters setup)
    (_uniformField : HasUniformAppliedMagneticField setup)
    (_massLaw : SatisfiesRectangularWireMassLaw setup)
    (_torqueLaws : SatisfiesPivotTorqueMagnitudeLaws setup)
    (_directionLaws : SatisfiesCurrentLoopDirectionLaws setup)
    (_equilibrium : IsInRotationalEquilibrium setup) :
    MagnitudeRoundsToChoice setup .B ∧
      setup.magneticFieldDirection = .positiveY := by
  have hdensity :
      linearMassDensityInKilogramsPerMeter setup.wireLinearMassDensity =
        0.015 := by
    have h := _problem.linearDensityInGramsPerCentimeter
    norm_num [linearMassDensityInGramsPerCentimeter] at h ⊢
    linarith
  have hpivot : lengthInMeters setup.pivotEdgeLength = 0.06 := by
    have h := _problem.pivotLengthInCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have htransverse : lengthInMeters setup.transverseEdgeLength = 0.08 := by
    have h := _problem.transverseLengthInCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hangle : setup.equilibriumAngleRadians = Real.pi / 6 := by
    rw [_problem.angleMatchesFigureMarker,
      _figure.angleMarkerIsThirtyDegrees]
    ring
  have hfield := equilibrium_field_magnitude_formula setup _physical
    _massLaw _torqueLaws _equilibrium
  rw [hdensity, _problem.currentInAmperes, hpivot, htransverse,
    _gravity.gravitationalAccelerationIsNinePointEight, hangle,
    Real.tan_pi_div_six] at hfield
  norm_num at hfield
  have hsqrt_pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hfield_exact :
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude =
        343 / (8200 * Real.sqrt 3) := by
    rw [hfield]
    field_simp
    ring
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (3430 : ℝ) / 2009 < Real.sqrt 3 := by
    nlinarith
  have hsqrt_upper : Real.sqrt 3 < (3430 : ℝ) / 1927 := by
    nlinarith
  have hdenominator_pos : 0 < (8200 : ℝ) * Real.sqrt 3 :=
    mul_pos (by norm_num) hsqrt_pos
  have hfield_lower :
      (0.0235 : ℝ) < 343 / (8200 * Real.sqrt 3) := by
    apply (lt_div_iff₀ hdenominator_pos).2
    nlinarith
  have hfield_upper :
      343 / (8200 * Real.sqrt 3) < (0.0245 : ℝ) := by
    apply (div_lt_iff₀ hdenominator_pos).2
    nlinarith
  constructor
  · change
      |magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude -
        (0.024 : ℝ)| < 0.0005
    rw [hfield_exact, abs_lt]
    constructor <;> nlinarith
  · have hcross_zy :
        CrossesToDirection .positiveZ .negativeY .positiveX := by
      unfold CrossesToDirection
      ext i
      fin_cases i <;>
        simp [SignedAxisDirection.unitVector, cross_apply]
    have hmoment_law :=
      _directionLaws.momentDirectionFromCurrentAndGeometry
    rw [_figure.pivotPointsFromAToBAlongPositiveZ,
      _figure.referenceSidePointsFromBToCAlongNegativeY] at hmoment_law
    have hmoment_vector :
        SignedAxisDirection.positiveX.unitVector =
          setup.referenceMagneticMomentDirection.unitVector :=
      hcross_zy.symm.trans hmoment_law
    have hmoment_direction :
        setup.referenceMagneticMomentDirection = .positiveX := by
      have hcoordinates :=
        congrArg (fun vector : SpatialVector =>
          (vector 0, vector 1, vector 2)) hmoment_vector
      cases hreference : setup.referenceMagneticMomentDirection with
      | positiveX => rfl
      | negativeX =>
          exfalso
          rw [hreference] at hcoordinates
          simp [SignedAxisDirection.unitVector] at hcoordinates
          norm_num at hcoordinates
      | positiveY =>
          exfalso
          rw [hreference] at hcoordinates
          simp [SignedAxisDirection.unitVector] at hcoordinates
      | negativeY =>
          exfalso
          rw [hreference] at hcoordinates
          simp [SignedAxisDirection.unitVector] at hcoordinates
      | positiveZ =>
          exfalso
          rw [hreference] at hcoordinates
          simp [SignedAxisDirection.unitVector] at hcoordinates
      | negativeZ =>
          exfalso
          rw [hreference] at hcoordinates
          simp [SignedAxisDirection.unitVector] at hcoordinates
    have htorque_direction :
        setup.magneticTorqueDirection = .positiveZ :=
      _directionLaws.torqueProducesShownSwing.trans
        _figure.swingIsPositiveAboutPivot
    have hfield_cases :
        setup.magneticFieldDirection = .positiveY ∨
          setup.magneticFieldDirection = .negativeY := by
      cases hfield_direction : setup.magneticFieldDirection with
      | positiveX =>
          exfalso
          have haxis := _problem.fieldIsParallelToYAxis
          rw [hfield_direction] at haxis
          cases haxis
      | negativeX =>
          exfalso
          have haxis := _problem.fieldIsParallelToYAxis
          rw [hfield_direction] at haxis
          cases haxis
      | positiveY => exact Or.inl rfl
      | negativeY => exact Or.inr rfl
      | positiveZ =>
          exfalso
          have haxis := _problem.fieldIsParallelToYAxis
          rw [hfield_direction] at haxis
          cases haxis
      | negativeZ =>
          exfalso
          have haxis := _problem.fieldIsParallelToYAxis
          rw [hfield_direction] at haxis
          cases haxis
    rcases hfield_cases with hpositive | hnegative
    · exact hpositive
    · have htorque_law := _directionLaws.magneticTorqueDirectionLaw
      rw [hmoment_direction, hnegative, htorque_direction] at htorque_law
      have htorque_component :=
        congrArg (fun vector : SpatialVector => vector 2) htorque_law
      norm_num [CrossesToDirection, SignedAxisDirection.unitVector,
        cross_apply] at htorque_component
      simp [Matrix.cons_val_two] at htorque_component
      norm_num at htorque_component

end PhyXMiniProblems.ProblemPhyXMini0948
