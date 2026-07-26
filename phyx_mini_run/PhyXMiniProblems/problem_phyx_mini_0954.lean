import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0954

open Dimension

/-!
# Half-turn threshold for a magnetic lift

A cylindrical magnetic lift of radius `R` and axial width `W` carries `N`
turns of conducting wire in a diametral plane.  A uniform external magnetic
field points downward, the current has the sense drawn in the supplied image,
and a mass `M` hangs from a cable fixed to a material point on the rim lying on
the coil axis.  The mass is released from rest at its top height `h_top`.

Physical magnitudes are represented by Physlib `Dimensionful` quantities.
Real numbers below are used only for coherent-unit readouts, dimensionless
angles, time coordinates in seconds, and answer-sheet sigma metadata.

Assumption/target split:

* governing laws: loop area, magnetic dipole moment, uniform-field direction,
  rigid rim-attachment geometry, gravitational and magnetic potential energy,
  the corresponding axial torques, trajectory continuity, angular-velocity
  kinematics, rotational kinetic energy, and conservation of mechanical
  energy;
* previous-part results: none are present in the supplied source report;
* figure/data readouts: the cylinder, diametral winding, horizontal axle,
  cable, mass, downward field, depicted upward current, the labels `R`, `W`,
  `I`, `B`, `M`, and `h` printed in the raster, the prose parameter `N`, and
  the pale ghost of the mass at its lowest position;
* current target conclusion: if rotation exceeds `pi` radians, then every
  intermediate travel from `0` through `pi` is reached with potential energy
  no greater than the release energy, together with the corresponding kinetic
  energy identity.

The supplied problem never defines `sigma`.  Its displayed threshold and
recorded choice B are therefore retained only as answer-sheet metadata; no
dimensionless scalar disconnected from the apparatus occurs in the physical
setup or theorem.  The primary raster does identify a fixed point on the rim
and a pale lowest-position ghost of the same mass, which supports the standard
height law `h = R * (1 - cos theta)` and `h_top = 2 R`.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- Electric current has dimension charge per unit time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Magnetic flux density (tesla) has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Acceleration has dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A current loop's magnetic dipole moment has dimension `C L² T⁻¹`. -/
def magneticMomentDimension : Dimension :=
  C𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- Moment of inertia has dimension `M L²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- Torque has the same dimension as energy, `M L² T⁻²`. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Angular velocity is an inverse-time quantity; radians are dimensionless. -/
def angularVelocityDimension : Dimension := T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaMagnitude : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative, unit-independent mass. -/
abbrev MassMagnitude : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent magnetic dipole moment magnitude. -/
abbrev MagneticMomentMagnitude : Type :=
  Dimensionful (WithDim magneticMomentDimension NNReal)

/-- A nonnegative, unit-independent moment of inertia. -/
abbrev MomentOfInertiaMagnitude : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A signed axial torque. -/
abbrev AxialTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- A signed angular velocity. -/
abbrev AngularVelocityQuantity : Type :=
  Dimensionful (WithDim angularVelocityDimension ℝ)

/-- A signed mechanical energy; this is Physlib's dimensioned energy type. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a nonnegative dimensionful scalar in a coherent system of units. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed dimensionful scalar in a coherent system of units. -/
def signedReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  signedReadout UnitChoices.SI energy

/-! ## Figure objects, labels, and qualitative geometry -/

/-- Physical objects visible in image `954.png`. -/
inductive FigureObject where
  | cylinder
  | diametralWinding
  | axle
  | cable
  | hangingMass
  | externalMagneticField
  | lowestPositionGhost
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels present in the source or the supplied raster. -/
inductive FigureLabel where
  | R
  | W
  | N
  | I
  | B
  | M
  | h
  deriving DecidableEq, Fintype, Repr

/-- Named vertical directions needed to transcribe the arrows in the figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The winding geometry described by the prose and shown on the cylinder. -/
inductive WindingGeometry where
  | turnsInDiametralPlane
  | other
  deriving DecidableEq, Repr

/-- The cable attachment described in the problem statement. -/
inductive CableAttachment where
  | fixedToRimOnCoilAxis
  | other
  deriving DecidableEq, Repr

/-- The current-arrow sense directly visible on the front winding segment. -/
inductive DepictedCurrentSense where
  | upwardOnVisibleSegment
  | downwardOnVisibleSegment
  deriving DecidableEq, Repr

/-!
Typed qualitative data copied from the primary raster.  The pale lower mass is
recorded as a ghost of the same mass at its lowest possible position, not as a
second physical load.
-/
structure MagneticLiftFigure where
  objectShown : FigureObject → Bool
  labelShownInRaster : FigureLabel → Bool
  labelSuppliedByProse : FigureLabel → Bool
  magneticFieldArrowDirection : VerticalDirection
  currentArrowSense : DepictedCurrentSense
  windingGeometry : WindingGeometry
  cableAttachment : CableAttachment
  radiusGuideRunsFromAxisToRim : Bool
  widthLabelRunsAlongCylinderAxis : Bool
  axleIsDrawnHorizontal : Bool
  cableIsDrawnVertical : Bool
  massGhostMarksLowestPossiblePosition : Bool
  ghostRepresentsSameMass : Bool

/-! ## Independent physical setup -/

/-- Three-dimensional Euclidean vectors used for magnetic-field readouts. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Unit coordinate vector chosen to represent the downward vertical. -/
def downwardUnitVector : SpatialVector :=
  EuclideanSpace.single (2 : Fin 3) (-1)

/-!
The physical apparatus, its one-degree-of-freedom trajectory, and independent
energy and torque observables.  The attachment angle is measured from the
downward vertical.  The source's undefined `sigma` is deliberately absent:
including a free scalar here would not connect the displayed answer to the
apparatus.
-/
structure MagneticLiftSetup where
  cylinderRadius : LengthMagnitude
  cylinderWidth : LengthMagnitude
  windingCount : ℕ
  coilArea : AreaMagnitude
  currentMagnitude : ElectricCurrentMagnitude
  externalMagneticField : Electromagnetism.MagneticField 3
  magneticFieldMagnitude : MagneticFluxDensityMagnitude
  magneticMomentMagnitude : MagneticMomentMagnitude
  hangingMass : MassMagnitude
  gravitationalAcceleration : AccelerationMagnitude
  /-- Effective inertia of every part moving with the cylinder and cable. -/
  effectiveRotationalInertia : MomentOfInertiaMagnitude
  topHeight : LengthMagnitude
  massHeightAtCylinderAngle : ℝ → LengthMagnitude
  magneticMomentAngleFromDownward : ℝ → ℝ
  gravitationalPotentialAtAngle : ℝ → EnergyQuantity
  magneticPotentialAtAngle : ℝ → EnergyQuantity
  gravitationalTorqueAtAngle : ℝ → AxialTorqueQuantity
  magneticTorqueAtAngle : ℝ → AxialTorqueQuantity
  netTorqueAtAngle : ℝ → AxialTorqueQuantity
  angularPositionRadiansAtTime : ℝ → ℝ
  angularVelocityAtTime : ℝ → AngularVelocityQuantity
  kineticEnergyAtTime : ℝ → EnergyQuantity
  /-- `1` or `-1`, selecting the rotation sense used to measure travel. -/
  releaseRotationSign : ℝ
  figure : MagneticLiftFigure

/-- Initial attachment angle, at the release time `t = 0`. -/
def initialAttachmentAngle (setup : MagneticLiftSetup) : ℝ :=
  setup.angularPositionRadiansAtTime 0

/-- Mechanical potential energy at a specified attachment angle. -/
def totalPotentialEnergyInJoules
    (setup : MagneticLiftSetup) (attachmentAngle : ℝ) : ℝ :=
  energyInJoules (setup.gravitationalPotentialAtAngle attachmentAngle) +
    energyInJoules (setup.magneticPotentialAtAngle attachmentAngle)

/-- Total mechanical energy at a specified time after release. -/
def mechanicalEnergyInJoulesAtTime
    (setup : MagneticLiftSetup) (timeSeconds : ℝ) : ℝ :=
  energyInJoules (setup.kineticEnergyAtTime timeSeconds) +
    totalPotentialEnergyInJoules setup
      (setup.angularPositionRadiansAtTime timeSeconds)

/-- Signed angular travel measured in the release rotation sense. -/
def orientedAngularTravelAtTime
    (setup : MagneticLiftSetup) (timeSeconds : ℝ) : ℝ :=
  setup.releaseRotationSign *
    (setup.angularPositionRadiansAtTime timeSeconds -
      initialAttachmentAngle setup)

/-!
The requested motion event: at some positive time the cylinder's angular
travel in the release sense is strictly more than one half-turn.
-/
def RotatesMoreThanHalfTurn (setup : MagneticLiftSetup) : Prop :=
  ∃ timeSeconds : ℝ,
    0 < timeSeconds ∧
      Real.pi < orientedAngularTravelAtTime setup timeSeconds

/-! ## Problem statement and primary-image readouts -/

/-!
Prose and raster evidence.  No threshold inequality, rotation event, or
normalized-energy identity occurs in this structure.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : MagneticLiftSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everySourceLabelSupplied : ∀ label,
    setup.figure.labelSuppliedByProse label = true
  rasterShowsRadiusLabel : setup.figure.labelShownInRaster .R = true
  rasterShowsWidthLabel : setup.figure.labelShownInRaster .W = true
  rasterShowsCurrentLabel : setup.figure.labelShownInRaster .I = true
  rasterShowsFieldLabel : setup.figure.labelShownInRaster .B = true
  rasterShowsMassLabel : setup.figure.labelShownInRaster .M = true
  rasterShowsHeightLabel : setup.figure.labelShownInRaster .h = true
  rasterDoesNotPrintTurnCount : setup.figure.labelShownInRaster .N = false
  fieldArrowPointsDown :
    setup.figure.magneticFieldArrowDirection = .downward
  currentArrowPointsUpOnVisibleSegment :
    setup.figure.currentArrowSense = .upwardOnVisibleSegment
  windingIsDiametral :
    setup.figure.windingGeometry = .turnsInDiametralPlane
  cableAttachesOnRimAndCoilAxis :
    setup.figure.cableAttachment = .fixedToRimOnCoilAxis
  radiusGuideIsRadial :
    setup.figure.radiusGuideRunsFromAxisToRim = true
  widthIsAxial : setup.figure.widthLabelRunsAlongCylinderAxis = true
  axleIsHorizontal : setup.figure.axleIsDrawnHorizontal = true
  cableIsVertical : setup.figure.cableIsDrawnVertical = true
  lowerMassIsPositionGhost :
    setup.figure.massGhostMarksLowestPossiblePosition = true
  lowerGhostIsNotASecondMass : setup.figure.ghostRepresentsSameMass = true
  releasedAtTopHeight : ∀ units,
    nonnegativeReadout units
        (setup.massHeightAtCylinderAngle (initialAttachmentAngle setup)) =
      nonnegativeReadout units setup.topHeight
  releasedFromRest : ∀ units,
    signedReadout units (setup.angularVelocityAtTime 0) = 0

/-- Positivity and nondegeneracy conditions for the magnetic lift. -/
structure HasPhysicalMagneticLiftParameters
    (setup : MagneticLiftSetup) : Prop where
  radiusPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.cylinderRadius
  widthPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.cylinderWidth
  windingCountPositive : 0 < setup.windingCount
  areaPositive : 0 < nonnegativeReadout UnitChoices.SI setup.coilArea
  currentPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.currentMagnitude
  fieldMagnitudePositive :
    0 < nonnegativeReadout UnitChoices.SI setup.magneticFieldMagnitude
  magneticMomentPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.magneticMomentMagnitude
  hangingMassPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.hangingMass
  gravitationalAccelerationPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.gravitationalAcceleration
  momentOfInertiaPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.effectiveRotationalInertia
  topHeightPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.topHeight
  releaseSenseIsSign :
    setup.releaseRotationSign = 1 ∨ setup.releaseRotationSign = -1

/-! ## Governing electromagnetic, geometric, and mechanical laws -/

/-!
The current loop has area `2 R W`, moment magnitude `N I A`, and is immersed
in a uniform downward field.  These are general physical laws and do not
mention the requested `sigma` threshold.
-/
structure SatisfiesCurrentLoopAndUniformFieldLaws
    (setup : MagneticLiftSetup) : Prop where
  coilAreaLaw : ∀ units,
    nonnegativeReadout units setup.coilArea =
      2 * nonnegativeReadout units setup.cylinderRadius *
        nonnegativeReadout units setup.cylinderWidth
  magneticMomentLaw : ∀ units,
    nonnegativeReadout units setup.magneticMomentMagnitude =
      (setup.windingCount : ℝ) *
        nonnegativeReadout units setup.currentMagnitude *
        nonnegativeReadout units setup.coilArea
  fieldIsUniformAndDownward : ∀ time position,
    setup.externalMagneticField time position =
      nonnegativeReadout UnitChoices.SI setup.magneticFieldMagnitude •
        downwardUnitVector

/-!
Rigid geometry for the point attachment visible on the rim.  With attachment
angle measured from the downward vertical, the mass height above its lowest
position is `R * (1 - cos theta)`, and its top height is the diameter `2 R`.
The coil axis has a fixed angular offset from the attachment coordinate.
-/
structure SatisfiesRigidCylinderAndCableGeometry
    (setup : MagneticLiftSetup) : Prop where
  fixedRimAttachmentHeight : ∀ units attachmentAngle,
    nonnegativeReadout units
        (setup.massHeightAtCylinderAngle attachmentAngle) =
      nonnegativeReadout units setup.cylinderRadius *
        (1 - Real.cos attachmentAngle)
  topHeightIsCylinderDiameter : ∀ units,
    nonnegativeReadout units setup.topHeight =
      2 * nonnegativeReadout units setup.cylinderRadius
  coilAxisHasFixedOffset :
    ∃ magneticMomentOffsetRadians : ℝ,
      ∀ attachmentAngle,
        setup.magneticMomentAngleFromDownward attachmentAngle =
          attachmentAngle + magneticMomentOffsetRadians

/-!
Potential-energy and torque laws for gravity and for a magnetic dipole in a
uniform field.  For a material point fixed to the rim, the gravitational
torque is `-M g R sin theta` when increasing attachment angle is the positive
axial direction.  The net torque is the sum of its two physical contributions.
-/
structure SatisfiesMagneticAndGravitationalEnergyLaws
    (setup : MagneticLiftSetup) : Prop where
  gravitationalPotentialLaw : ∀ units attachmentAngle,
    signedReadout units
        (setup.gravitationalPotentialAtAngle attachmentAngle) =
      nonnegativeReadout units setup.hangingMass *
        nonnegativeReadout units setup.gravitationalAcceleration *
        nonnegativeReadout units
          (setup.massHeightAtCylinderAngle attachmentAngle)
  magneticPotentialLaw : ∀ units attachmentAngle,
    signedReadout units
        (setup.magneticPotentialAtAngle attachmentAngle) =
      -(nonnegativeReadout units setup.magneticMomentMagnitude *
        nonnegativeReadout units setup.magneticFieldMagnitude *
        Real.cos (setup.magneticMomentAngleFromDownward attachmentAngle))
  gravitationalTorqueLaw : ∀ units attachmentAngle,
    signedReadout units (setup.gravitationalTorqueAtAngle attachmentAngle) =
      -(nonnegativeReadout units setup.hangingMass *
        nonnegativeReadout units setup.gravitationalAcceleration *
        nonnegativeReadout units setup.cylinderRadius *
        Real.sin attachmentAngle)
  magneticTorqueLaw : ∀ units attachmentAngle,
    signedReadout units (setup.magneticTorqueAtAngle attachmentAngle) =
      -(nonnegativeReadout units setup.magneticMomentMagnitude *
        nonnegativeReadout units setup.magneticFieldMagnitude *
        Real.sin (setup.magneticMomentAngleFromDownward attachmentAngle))
  netTorqueIsSum : ∀ units attachmentAngle,
    signedReadout units (setup.netTorqueAtAngle attachmentAngle) =
      signedReadout units (setup.gravitationalTorqueAtAngle attachmentAngle) +
        signedReadout units (setup.magneticTorqueAtAngle attachmentAngle)

/-!
Conservative one-dimensional rotational mechanics.  Time arguments are
coherent-SI seconds, angular position is continuous, angular velocity is its
time derivative, kinetic energy is `J omega^2 / 2`, and total mechanical
energy is conserved after release.  No reachability or energy-barrier
conclusion is stored as a law premise.
-/
structure SatisfiesConservativeRotationalDynamics
    (setup : MagneticLiftSetup) : Prop where
  angularPositionContinuous :
    Continuous setup.angularPositionRadiansAtTime
  angularVelocityIsTimeDerivative : ∀ timeSeconds,
    HasDerivAt setup.angularPositionRadiansAtTime
      (signedReadout UnitChoices.SI
        (setup.angularVelocityAtTime timeSeconds)) timeSeconds
  kineticEnergyLaw : ∀ units timeSeconds,
    signedReadout units (setup.kineticEnergyAtTime timeSeconds) =
      (1 / 2 : ℝ) *
        nonnegativeReadout units setup.effectiveRotationalInertia *
        (signedReadout units (setup.angularVelocityAtTime timeSeconds)) ^ 2
  mechanicalEnergyConserved : ∀ timeSeconds, 0 ≤ timeSeconds →
    mechanicalEnergyInJoulesAtTime setup timeSeconds =
      mechanicalEnergyInJoulesAtTime setup 0

/-! ## Displayed choices and current target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The boundary printed in choices A, B, and D. -/
def halfTurnSigmaThreshold : ℝ :=
  (1 / 2 : ℝ) * (1 + Real.pi / 2)

/-- The four propositions literally displayed beside the answer labels. -/
def displayedSigmaCondition (choice : AnswerChoice) (sigma : ℝ) : Prop :=
  match choice with
  | .A => sigma < halfTurnSigmaThreshold
  | .B => halfTurnSigmaThreshold < sigma
  | .C => (1 / 2 : ℝ) * (1 + Real.pi) < sigma
  | .D => sigma = halfTurnSigmaThreshold

/-- Dataset answer retained as metadata, not as a physical premise. -/
private def recordedDatasetAnswer : AnswerChoice := .B

/-!
Blueprint: `thm:physics:phyx_mini_0954:target`.

The source's undefined `sigma` cannot support the displayed numerical
threshold.  The strongest conclusion available from the stated apparatus and
generic conservative laws is instead this necessary symbolic energy
condition.  The loop, geometry, and energy laws first give the explicit
potential `M g R (1 - cos theta) - (N I 2 R W) B cos (theta + offset)`.
Release from rest identifies the release energy with the initial potential
energy.  If the cylinder passes a half-turn, every intermediate travel up to
`pi` is reached; its kinetic energy is the drop from that initial potential,
so the potential there cannot exceed its initial value.

The historical declaration name is retained for the existing blueprint pin;
its old sigma-threshold reading is intentionally not asserted.  Choice B and
its printed boundary remain metadata above.
-/
theorem rotatesMoreThanHalfTurn_iff_sigma_gt_threshold
    (setup : MagneticLiftSetup)
    (hStatementAndFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalMagneticLiftParameters setup)
    (hLoopAndField : SatisfiesCurrentLoopAndUniformFieldLaws setup)
    (hGeometry : SatisfiesRigidCylinderAndCableGeometry setup)
    (hEnergy : SatisfiesMagneticAndGravitationalEnergyLaws setup)
    (hDynamics : SatisfiesConservativeRotationalDynamics setup) :
    ∃ magneticMomentOffsetRadians : ℝ,
      (∀ attachmentAngle : ℝ,
        totalPotentialEnergyInJoules setup attachmentAngle =
          nonnegativeReadout UnitChoices.SI setup.hangingMass *
              nonnegativeReadout UnitChoices.SI
                setup.gravitationalAcceleration *
              nonnegativeReadout UnitChoices.SI setup.cylinderRadius *
              (1 - Real.cos attachmentAngle) -
            (setup.windingCount : ℝ) *
              nonnegativeReadout UnitChoices.SI setup.currentMagnitude *
              (2 * nonnegativeReadout UnitChoices.SI setup.cylinderRadius *
                nonnegativeReadout UnitChoices.SI setup.cylinderWidth) *
              nonnegativeReadout UnitChoices.SI
                setup.magneticFieldMagnitude *
              Real.cos
                (attachmentAngle + magneticMomentOffsetRadians)) ∧
        mechanicalEnergyInJoulesAtTime setup 0 =
          totalPotentialEnergyInJoules setup
            (initialAttachmentAngle setup) ∧
        (RotatesMoreThanHalfTurn setup →
          ∀ travelRadians : ℝ,
            travelRadians ∈ Set.Icc 0 Real.pi →
              ∃ timeSeconds : ℝ,
                0 ≤ timeSeconds ∧
                orientedAngularTravelAtTime setup timeSeconds =
                  travelRadians ∧
                energyInJoules (setup.kineticEnergyAtTime timeSeconds) =
                  totalPotentialEnergyInJoules setup
                      (initialAttachmentAngle setup) -
                    totalPotentialEnergyInJoules setup
                      (initialAttachmentAngle setup +
                        setup.releaseRotationSign * travelRadians) ∧
                totalPotentialEnergyInJoules setup
                    (initialAttachmentAngle setup +
                      setup.releaseRotationSign * travelRadians) ≤
                  totalPotentialEnergyInJoules setup
                    (initialAttachmentAngle setup)) := by
  obtain ⟨magneticMomentOffsetRadians, hOffset⟩ :=
    hGeometry.coilAxisHasFixedOffset
  refine ⟨magneticMomentOffsetRadians, ?_, ?_, ?_⟩
  · intro attachmentAngle
    rw [totalPotentialEnergyInJoules, energyInJoules, energyInJoules,
      hEnergy.gravitationalPotentialLaw,
      hEnergy.magneticPotentialLaw,
      hGeometry.fixedRimAttachmentHeight,
      hOffset,
      hLoopAndField.magneticMomentLaw,
      hLoopAndField.coilAreaLaw]
    ring
  · rw [mechanicalEnergyInJoulesAtTime, initialAttachmentAngle,
      energyInJoules, hDynamics.kineticEnergyLaw,
      hStatementAndFigure.releasedFromRest]
    norm_num
  · rintro ⟨witnessTime, hWitnessTimePositive, hWitnessTravel⟩
      travelRadians hTravelRadians
    have hTravelContinuous :
        Continuous (orientedAngularTravelAtTime setup) := by
      exact continuous_const.mul
        (hDynamics.angularPositionContinuous.sub continuous_const)
    have hTravelAtZero :
        orientedAngularTravelAtTime setup 0 = 0 := by
      simp [orientedAngularTravelAtTime, initialAttachmentAngle]
    have hTravelInEndpointInterval :
        travelRadians ∈
          Set.Icc (orientedAngularTravelAtTime setup 0)
            (orientedAngularTravelAtTime setup witnessTime) := by
      rw [hTravelAtZero]
      exact ⟨hTravelRadians.1,
        hTravelRadians.2.trans (le_of_lt hWitnessTravel)⟩
    have hWitnessTimeNonnegative : 0 ≤ witnessTime :=
      le_of_lt hWitnessTimePositive
    obtain ⟨timeSeconds, hTimeInterval, hTravelAtTime⟩ :=
      intermediate_value_Icc hWitnessTimeNonnegative
        hTravelContinuous.continuousOn hTravelInEndpointInterval
    have hPositionAtTime :
        setup.angularPositionRadiansAtTime timeSeconds =
          initialAttachmentAngle setup +
            setup.releaseRotationSign * travelRadians := by
      rw [orientedAngularTravelAtTime] at hTravelAtTime
      rcases hPhysical.releaseSenseIsSign with hSign | hSign
      · rw [hSign] at hTravelAtTime ⊢
        simp only [one_mul] at hTravelAtTime
        linarith
      · rw [hSign] at hTravelAtTime ⊢
        simp only [neg_mul, one_mul] at hTravelAtTime
        linarith
    have hInitialEnergy :
        mechanicalEnergyInJoulesAtTime setup 0 =
          totalPotentialEnergyInJoules setup
            (initialAttachmentAngle setup) := by
      rw [mechanicalEnergyInJoulesAtTime, initialAttachmentAngle,
        energyInJoules, hDynamics.kineticEnergyLaw,
        hStatementAndFigure.releasedFromRest]
      norm_num
    have hKineticEnergy :
        energyInJoules (setup.kineticEnergyAtTime timeSeconds) =
          totalPotentialEnergyInJoules setup
              (initialAttachmentAngle setup) -
            totalPotentialEnergyInJoules setup
              (initialAttachmentAngle setup +
                setup.releaseRotationSign * travelRadians) := by
      rw [← hPositionAtTime, ← hInitialEnergy,
        ← hDynamics.mechanicalEnergyConserved timeSeconds hTimeInterval.1]
      simp only [mechanicalEnergyInJoulesAtTime]
      ring
    have hKineticEnergyNonnegative :
        0 ≤ energyInJoules (setup.kineticEnergyAtTime timeSeconds) := by
      rw [energyInJoules, hDynamics.kineticEnergyLaw]
      simp only [nonnegativeReadout]
      positivity
    refine ⟨timeSeconds, hTimeInterval.1, hTravelAtTime, hKineticEnergy, ?_⟩
    linarith

end PhyXMiniProblems.ProblemPhyXMini0954
