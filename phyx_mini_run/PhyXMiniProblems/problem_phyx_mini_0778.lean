import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0778

open Dimension

/-!
# Acceleration of a box driven by a hanging weight and a massive pulley

The primary image shows a box labelled `12.0 kg` on a horizontal table.  A
single wire runs from that box horizontally to a fixed pulley at the table
edge and then vertically down to a hanging weight labelled `5.00 kg`.  The
problem prose additionally specifies that the table and pulley axle are
frictionless, the wire is thin and light, and the pulley is a uniform solid
disk of mass `2.00 kg` and diameter `0.500 m`.

Masses, lengths, acceleration magnitudes, forces, angular accelerations,
moments of inertia, and torques are represented by unit-independent Physlib
quantities.  Real numbers occur only in explicitly named coherent-SI readouts
and in the printed multiple-choice values.

Assumption/target split:

* governing laws: the common-wire acceleration constraint, no slip at the
  pulley rim, Newton's second law for each translating body, torque from the
  two unequal wire tensions, rotational Newton's second law, the radius-
  diameter relation, and the uniform-solid-disk inertia law;
* previous-part results: none;
* figure/data readouts: the pictured objects and wire route, the `12.0 kg` and
  `5.00 kg` labels, pulley mass `2.00 kg`, pulley diameter `0.500 m`, and the
  standard near-Earth value `g = 9.8 m/s^2` used by the recorded answer;
* current target conclusions: the exact box acceleration `49 / 18 m/s^2`, its
  agreement at the printed precision with `2.72 m/s^2`, and choice B.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `L T⁻²` of a linear acceleration magnitude. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of a force magnitude. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Angular acceleration has dimension `T⁻²`; radians are dimensionless. -/
def angularAccelerationDimension : Dimension := T𝓭⁻¹ * T𝓭⁻¹

/-- A scalar axial moment of inertia has dimension `M L²`. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A torque magnitude has dimension `M L² T⁻²`. -/
def torqueDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent linear acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceQuantity : Type := Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative angular-acceleration magnitude about the pulley axle. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim angularAccelerationDimension NNReal)

/-- A nonnegative scalar moment of inertia about the pulley axle. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative torque magnitude about the pulley axle. -/
abbrev TorqueQuantity : Type := Dimensionful (WithDim torqueDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI base units. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ := coherentSIReadout mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ := coherentSIReadout length

/-- Metres-per-second-squared readout of a linear acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  coherentSIReadout acceleration

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ := coherentSIReadout force

/-- Radians-per-second-squared readout of angular acceleration. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationQuantity) : ℝ :=
  coherentSIReadout acceleration

/-- Kilogram-metre-squared readout of a scalar moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  coherentSIReadout inertia

/-- Newton-metre readout of an axial torque magnitude. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  coherentSIReadout torque

/-! ## Primary-figure vocabulary -/

/-- The three principal bodies visible in the supplied raster. -/
inductive PicturedBody where
  | tabletopBox
  | hangingWeight
  | pulley
  deriving DecidableEq, Fintype, Repr

/-- Individually identifiable physical objects in image `778.png`. -/
inductive FigureObject where
  | tabletopBox
  | hangingWeight
  | horizontalSurface
  | fixedPulley
  | supportClamp
  | horizontalWireSegment
  | verticalWireSegment
  deriving DecidableEq, Fintype, Repr

/-- Literal numerical labels printed in the image. -/
inductive FigureTextLabel where
  | twelvePointZeroKilograms
  | fivePointZeroKilograms
  deriving DecidableEq, Fintype, Repr

/-- The two endpoints of the pictured wire. -/
inductive WireEndpoint where
  | tabletopEnd
  | hangingEnd
  deriving DecidableEq, Fintype, Repr

/-- Bodies to which a wire endpoint can be attached in this setup. -/
inductive EndpointAttachment where
  | tabletopBox
  | hangingWeight
  deriving DecidableEq, Repr

/-- The route of the single wire visible in the primary image. -/
inductive WireRoute where
  | horizontallyFromBoxOverPulleyThenVerticallyDown
  deriving DecidableEq, Repr

/-!
Typed evidence transcribed from the supplied image.  The pulley itself has no
mass or diameter label in the raster; those two numerical values come from the
problem prose instead.
-/
structure SuppliedPulleyFigure where
  showsObject : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  printedMassKilograms : PicturedBody → Option ℝ
  endpointAttachment : WireEndpoint → EndpointAttachment
  wireRoute : WireRoute
  tabletopBoxIsLeftOfPulley : Bool
  hangingWeightIsBelowPulley : Bool
  tableSurfaceIsHorizontal : Bool
  pulleyHasProseDataPrintedInImage : Bool

/-! ## Physical setup and qualitative model -/

/-- Model of the horizontal surface described in the prose. -/
inductive SurfaceModel where
  | horizontalFrictionless
  deriving DecidableEq, Repr

/-- Idealization of the connecting wire stated in the problem. -/
inductive WireMassModel where
  | thinAndLight
  deriving DecidableEq, Repr

/-- Geometric mass model of the pulley. -/
inductive PulleyShapeModel where
  | uniformSolidDisk
  deriving DecidableEq, Repr

/-- Mechanical model of the fixed pulley axle. -/
inductive PulleyAxleModel where
  | fixedAndFrictionless
  deriving DecidableEq, Repr

/-- The instant at which the requested acceleration is evaluated. -/
inductive SystemState where
  | immediatelyAfterRelease
  deriving DecidableEq, Repr

/-!
Independent physical quantities for the two bodies, wire segments, and
massive pulley.  In particular, `boxAcceleration` is an independent observable
and is not defined from any answer choice or target value.
-/
structure TabletopPulleySetup where
  figure : SuppliedPulleyFigure
  tabletopBoxMass : MassQuantity
  hangingWeightMass : MassQuantity
  pulleyMass : MassQuantity
  pulleyDiameter : LengthQuantity
  pulleyRadius : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  boxAcceleration : AccelerationQuantity
  hangingWeightAcceleration : AccelerationQuantity
  pulleyAngularAcceleration : AngularAccelerationQuantity
  tabletopSegmentTension : ForceQuantity
  hangingSegmentTension : ForceQuantity
  pulleyMomentOfInertia : MomentOfInertiaQuantity
  netPulleyTorque : TorqueQuantity
  surfaceModel : SurfaceModel
  wireMassModel : WireMassModel
  pulleyShapeModel : PulleyShapeModel
  pulleyAxleModel : PulleyAxleModel
  systemState : SystemState

/-! ## Scenario, image evidence, and numerical readouts -/

/-- Qualitative conditions stated by the problem prose. -/
structure MatchesWrittenScenario (setup : TabletopPulleySetup) : Prop where
  horizontalFrictionlessSurface :
    setup.surfaceModel = .horizontalFrictionless
  thinLightWire : setup.wireMassModel = .thinAndLight
  pulleyIsUniformSolidDisk :
    setup.pulleyShapeModel = .uniformSolidDisk
  fixedFrictionlessPulleyAxle :
    setup.pulleyAxleModel = .fixedAndFrictionless
  evaluatedAfterRelease : setup.systemState = .immediatelyAfterRelease

/-- Geometry, connectivity, and printed labels read directly from image `778.png`. -/
structure MatchesPrimaryFigure (setup : TabletopPulleySetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  bothTextLabelsShown : ∀ label, setup.figure.showsTextLabel label = true
  tabletopMassLabel :
    setup.figure.printedMassKilograms .tabletopBox = some 12
  hangingMassLabel :
    setup.figure.printedMassKilograms .hangingWeight = some 5
  pulleyHasNoNumericalMassLabel :
    setup.figure.printedMassKilograms .pulley = none
  tabletopWireEndpoint :
    setup.figure.endpointAttachment .tabletopEnd = .tabletopBox
  hangingWireEndpoint :
    setup.figure.endpointAttachment .hangingEnd = .hangingWeight
  routeReadout :
    setup.figure.wireRoute =
      .horizontallyFromBoxOverPulleyThenVerticallyDown
  boxLeftOfPulley : setup.figure.tabletopBoxIsLeftOfPulley = true
  weightBelowPulley : setup.figure.hangingWeightIsBelowPulley = true
  tableIsHorizontal : setup.figure.tableSurfaceIsHorizontal = true
  pulleyProseDataNotPrintedInRaster :
    setup.figure.pulleyHasProseDataPrintedInImage = false

/-!
Physical numerical data from the two image labels and the problem prose.
`0.500 m` is represented exactly as `1 / 2 m`.  The radius is not assigned
here; it is related to the stated diameter by a general disk-geometry law.
-/
structure MatchesProblemReadouts (setup : TabletopPulleySetup) : Prop where
  tabletopBoxMassKilograms : massInKilograms setup.tabletopBoxMass = 12
  hangingWeightMassKilograms : massInKilograms setup.hangingWeightMass = 5
  pulleyMassKilograms : massInKilograms setup.pulleyMass = 2
  pulleyDiameterMeters : lengthInMeters setup.pulleyDiameter = 1 / 2

/-!
The gravitational calibration implicit in the recorded textbook answer,
separated from the values explicitly printed in the problem.
-/
structure UsesStandardNearEarthGravity (setup : TabletopPulleySetup) : Prop where
  gravitationalAccelerationIs9Point8 :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-- Positivity and nondegeneracy conditions for the massive-pulley model. -/
structure HasPhysicalParameters (setup : TabletopPulleySetup) : Prop where
  tabletopMassPositive : 0 < massInKilograms setup.tabletopBoxMass
  hangingMassPositive : 0 < massInKilograms setup.hangingWeightMass
  pulleyMassPositive : 0 < massInKilograms setup.pulleyMass
  pulleyDiameterPositive : 0 < lengthInMeters setup.pulleyDiameter
  pulleyRadiusPositive : 0 < lengthInMeters setup.pulleyRadius
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  tabletopTensionPositive :
    0 < forceInNewtons setup.tabletopSegmentTension
  hangingTensionPositive :
    0 < forceInNewtons setup.hangingSegmentTension
  pulleyInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.pulleyMomentOfInertia

/-! ## Governing translational, rotational, and kinematic laws -/

/-!
The ideal-wire and massive-disk-pulley equations at the instant after release.
All signs are fixed by taking motion of the box toward the pulley, motion of
the hanging weight downward, and pulley rotation in the corresponding sense
as positive.  The two wire tensions remain independent because a massive
pulley requires a nonzero tension difference.

None of these general laws mentions `49 / 18`, `2.72`, or an answer label.
-/
structure SatisfiesMassivePulleyDynamics
    (setup : TabletopPulleySetup) : Prop where
  radiusDiameterRelation :
    2 * lengthInMeters setup.pulleyRadius =
      lengthInMeters setup.pulleyDiameter
  commonWireAcceleration :
    accelerationInMetersPerSecondSquared setup.boxAcceleration =
      accelerationInMetersPerSecondSquared setup.hangingWeightAcceleration
  wireDoesNotSlipOnPulley :
    accelerationInMetersPerSecondSquared setup.boxAcceleration =
      angularAccelerationInRadiansPerSecondSquared
          setup.pulleyAngularAcceleration *
        lengthInMeters setup.pulleyRadius
  tabletopBoxNewtonSecondLaw :
    forceInNewtons setup.tabletopSegmentTension =
      massInKilograms setup.tabletopBoxMass *
        accelerationInMetersPerSecondSquared setup.boxAcceleration
  hangingWeightNewtonSecondLaw :
    massInKilograms setup.hangingWeightMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration -
        forceInNewtons setup.hangingSegmentTension =
      massInKilograms setup.hangingWeightMass *
        accelerationInMetersPerSecondSquared setup.hangingWeightAcceleration
  pulleyTorqueFromTensions :
    torqueInNewtonMeters setup.netPulleyTorque =
      (forceInNewtons setup.hangingSegmentTension -
          forceInNewtons setup.tabletopSegmentTension) *
        lengthInMeters setup.pulleyRadius
  pulleyRotationalNewtonSecondLaw :
    torqueInNewtonMeters setup.netPulleyTorque =
      momentOfInertiaInKilogramMetersSquared
          setup.pulleyMomentOfInertia *
        angularAccelerationInRadiansPerSecondSquared
          setup.pulleyAngularAcceleration
  uniformSolidDiskMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.pulleyMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms setup.pulleyMass *
        lengthInMeters setup.pulleyRadius ^ 2

/-! ## Exact acceleration and the displayed multiple-choice answer -/

/-!
The governing equations yield
`a = m_h g / (m_box + m_h + I / r²)`.  For a uniform disk,
`I / r² = m_pulley / 2`, so the supplied data give the exact acceleration
`49 / 18 m/s²`.
-/
lemma boxAcceleration_exact
    (setup : TabletopPulleySetup)
    (h_scenario : MatchesWrittenScenario setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_data : MatchesProblemReadouts setup)
    (h_gravity : UsesStandardNearEarthGravity setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesMassivePulleyDynamics setup) :
    accelerationInMetersPerSecondSquared setup.boxAcceleration =
      49 / 18 := by
  have h_radius :
      lengthInMeters setup.pulleyRadius = 1 / 4 := by
    nlinarith [h_laws.radiusDiameterRelation,
      h_data.pulleyDiameterMeters]
  have h_inertia :=
    h_laws.uniformSolidDiskMomentOfInertia
  rw [h_data.pulleyMassKilograms, h_radius] at h_inertia
  norm_num at h_inertia
  have h_no_slip := h_laws.wireDoesNotSlipOnPulley
  rw [h_radius] at h_no_slip
  norm_num at h_no_slip
  have h_tabletop := h_laws.tabletopBoxNewtonSecondLaw
  rw [h_data.tabletopBoxMassKilograms] at h_tabletop
  have h_hanging := h_laws.hangingWeightNewtonSecondLaw
  rw [h_data.hangingWeightMassKilograms,
    h_gravity.gravitationalAccelerationIs9Point8] at h_hanging
  norm_num at h_hanging
  have h_torque := h_laws.pulleyTorqueFromTensions
  rw [h_radius] at h_torque
  norm_num at h_torque
  have h_rotation := h_laws.pulleyRotationalNewtonSecondLaw
  rw [h_inertia] at h_rotation
  nlinarith [h_laws.commonWireAcceleration]

/-- Labels of the four answers printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Acceleration printed beside each answer label, in `m/s²`. -/
def AnswerChoice.accelerationInMetersPerSecondSquared : AnswerChoice → ℝ
  | .A => 34 / 25
  | .B => 68 / 25
  | .C => 43 / 25
  | .D => 497 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
Agreement with an acceleration printed to two decimal places.  The tolerance
`0.005 m/s² = 1/200 m/s²` is half a unit in the last displayed digit, so this
does not falsely identify the unrounded value `49 / 18` with the decimal
`2.72`.
-/
def MatchesDisplayedAnswer
    (setup : TabletopPulleySetup) (choice : AnswerChoice) : Prop :=
  abs (accelerationInMetersPerSecondSquared setup.boxAcceleration -
      choice.accelerationInMetersPerSecondSquared) ≤ 1 / 200

/-!
The box acceleration is exactly `49 / 18 m/s²` and rounds to the recorded
choice B, `2.72 m/s²`.

Blueprint: `thm:physics:phyx_mini_0778:target`.
-/
theorem problem_phyx_mini_0778
    (setup : TabletopPulleySetup)
    (h_scenario : MatchesWrittenScenario setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_data : MatchesProblemReadouts setup)
    (h_gravity : UsesStandardNearEarthGravity setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesMassivePulleyDynamics setup) :
    accelerationInMetersPerSecondSquared setup.boxAcceleration = 49 / 18 ∧
      MatchesDisplayedAnswer setup recordedAnswerChoice := by
  have h_exact := boxAcceleration_exact setup h_scenario h_figure h_data
    h_gravity h_physical h_laws
  constructor
  · exact h_exact
  · rw [MatchesDisplayedAnswer, h_exact]
    norm_num [recordedAnswerChoice,
      AnswerChoice.accelerationInMetersPerSecondSquared, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0778
