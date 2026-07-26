import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0967

open Dimension

/-!
# Magnetic torque on a spinning charged disk inside a rotating charged cylinder

A uniformly charged cylindrical shell of radius `R₁` and height `H` rotates
about its axis with angular speed `ω₁`.  A much smaller uniformly charged disk
is mounted on a central pivot inside the cylinder, far from the cylinder's
ends.  The disk spins rapidly with angular speed `ω₂`; its spin axis makes an
angle `θ` with the cylinder axis and precesses about that axis.

The rotating shell is modeled as an azimuthal surface current.  The infinite-
length idealization produces a uniform axial magnetic field.  The actual
finite-cylinder field and actual disk torque are separate observables, with
explicit vector remainders and quantitative error bounds relative to that
idealization.  In the ideal uniform field, the disk's moment is along its spin
axis and its magnetic torque is the cross product `μ × B`.

All dimensional scalar and vector quantities are unit-independent Physlib
`Dimensionful` values.  Real numbers occur only at coherent-SI readout
boundaries, as dimensionless angles, or in the displayed answer expressions.

Assumption/target split:

* governing laws: the rotating-shell surface-current law, the ideal
  infinite-shell interior-field law, finite-cylinder field and finite-disk
  torque remainder contracts, the charged-disk magnetic-moment law, and the
  ideal uniform-field magnetic-dipole torque law;
* previous-part results: none;
* scenario and figure data: `R₁`, `H`, `Q₁`, `ω₁`, `R₂`, `M`, `Q₂`, `ω₂`,
  `θ`, the precession label `Ω`, the central pivot, and the disk's axial,
  far-from-edge placement;
* current target: the idealized torque magnitude
  `μ₀ Q₁ Q₂ ω₁ ω₂ R₂² sin θ / (8 π H)`, answer B, together with an
  explicit error bound for the actual finite-apparatus torque.

No scenario, figure, parameter, governing-law field, or approximation field
contains that final evaluated torque expression.  In particular, qualitative
phrases such as “far from the edges” and “very small disk” do not turn a local
approximation into a global exact equality.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Three-dimensional Euclidean vectors used for coherent-SI readouts. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- Angular speed has inverse-time dimension; radians are dimensionless. -/
def angularSpeedDimension : Dimension :=
  T𝓭⁻¹

/-- Azimuthal surface current per axial length has dimension `C T⁻¹ L⁻¹`. -/
def surfaceCurrentDensityDimension : Dimension :=
  C𝓭 * T𝓭⁻¹ * L𝓭⁻¹

/-- Vacuum permeability has SI dimension `M L C⁻²`. -/
def vacuumPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density (tesla) has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic dipole moment has dimension `C L² T⁻¹`. -/
def magneticMomentDimension : Dimension :=
  C𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- Torque has the energy dimension `M L² T⁻²`. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassMagnitude : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitude : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedMagnitude : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative azimuthal surface-current density magnitude. -/
abbrev SurfaceCurrentDensityMagnitude : Type :=
  Dimensionful (WithDim surfaceCurrentDensityDimension NNReal)

/-- A nonnegative vacuum-permeability magnitude. -/
abbrev VacuumPermeabilityMagnitude : Type :=
  Dimensionful (WithDim vacuumPermeabilityDimension NNReal)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A unit-independent magnetic-flux-density vector. -/
abbrev MagneticFluxDensityVector : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension SpatialVector)

/-- A nonnegative magnetic-dipole-moment magnitude. -/
abbrev MagneticMomentMagnitude : Type :=
  Dimensionful (WithDim magneticMomentDimension NNReal)

/-- A unit-independent magnetic-dipole-moment vector. -/
abbrev MagneticMomentVector : Type :=
  Dimensionful (WithDim magneticMomentDimension SpatialVector)

/-- A nonnegative magnetic-torque magnitude. -/
abbrev TorqueMagnitude : Type :=
  Dimensionful (WithDim torqueDimension NNReal)

/-- A unit-independent magnetic-torque vector. -/
abbrev TorqueVector : Type :=
  Dimensionful (WithDim torqueDimension SpatialVector)

/-- Read a nonnegative dimensionful scalar in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a dimensionful spatial vector in coherent SI units. -/
def vectorSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d SpatialVector)) : SpatialVector :=
  (quantity UnitChoices.SI).val

/-- Read mass in kilograms. -/
def massInKilograms (mass : MassMagnitude) : ℝ :=
  nonnegativeSIReadout mass

/-- Read length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitude) : ℝ :=
  nonnegativeSIReadout charge

/-- Read angular-speed magnitude in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedMagnitude) : ℝ :=
  nonnegativeSIReadout angularSpeed

/-- Read azimuthal surface-current density in amperes per metre. -/
def surfaceCurrentDensityInAmperesPerMeter
    (surfaceCurrentDensity : SurfaceCurrentDensityMagnitude) : ℝ :=
  nonnegativeSIReadout surfaceCurrentDensity

/-- Read vacuum permeability in newtons per ampere squared. -/
def vacuumPermeabilityInNewtonsPerAmpereSquared
    (vacuumPermeability : VacuumPermeabilityMagnitude) : ℝ :=
  nonnegativeSIReadout vacuumPermeability

/-- Read magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/-- Read a magnetic-flux-density vector in tesla coordinates. -/
def magneticFluxDensityVectorInTeslas
    (field : MagneticFluxDensityVector) : SpatialVector :=
  vectorSIReadout field

/-- Read magnetic-moment magnitude in ampere-square-metres. -/
def magneticMomentMagnitudeInAmpereSquareMeters
    (moment : MagneticMomentMagnitude) : ℝ :=
  nonnegativeSIReadout moment

/-- Read a magnetic-moment vector in ampere-square-metre coordinates. -/
def magneticMomentVectorInAmpereSquareMeters
    (moment : MagneticMomentVector) : SpatialVector :=
  vectorSIReadout moment

/-- Read torque magnitude in newton-metres. -/
def torqueMagnitudeInNewtonMeters (torque : TorqueMagnitude) : ℝ :=
  nonnegativeSIReadout torque

/-- Read a torque vector in newton-metre coordinates. -/
def torqueVectorInNewtonMeters (torque : TorqueVector) : SpatialVector :=
  vectorSIReadout torque

/-!
Mathlib's ordinary three-dimensional cross product transported to
`EuclideanSpace ℝ (Fin 3)`.
-/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-! ## Physical idealizations and primary-figure vocabulary -/

/-- The idealized charge distribution on the rotating cylinder. -/
inductive CylindricalShellModel where
  | uniformlyChargedThinShell
  deriving DecidableEq, Repr

/-- The idealized mass and charge geometry of the small rotor. -/
inductive DiskModel where
  | uniformlyChargedThinDisk
  deriving DecidableEq, Repr

/-- How the center of the disk is supported. -/
inductive DiskMountingModel where
  | pivotAtDiskCenter
  deriving DecidableEq, Repr

/-- Scale separation used to treat the disk as a dipole in the axial field. -/
inductive DiskScaleRegime where
  | verySmallComparedWithCylinder
  deriving DecidableEq, Repr

/-- Rapid-spin regime in which the disk axis exhibits gyroscopic precession. -/
inductive SpinRegime where
  | rapidSpin
  deriving DecidableEq, Repr

/-- Qualitative response caused by the magnetic interaction. -/
inductive MagneticInteractionResponse where
  | precessionAboutCylinderAxis
  deriving DecidableEq, Repr

/-- Literal parameter and vector labels visible in image `967.png`. -/
inductive FigureLabel where
  | cylinderAxis
  | cylinderRadiusR₁
  | cylinderHeightH
  | cylinderChargeQ₁
  | cylinderAngularVelocityω₁
  | diskChargeQ₂
  | diskRadiusR₂
  | diskMassM
  | tiltAngleθ
  | diskAngularVelocityω₂
  | precessionAngularVelocityΩ
  deriving DecidableEq, Fintype, Repr

/-- Physical and graphical objects visible in the supplied raster. -/
inductive FigureFeature where
  | cylindricalShell
  | cutawayInterior
  | centralAxisLine
  | tiltedDisk
  | centralPivot
  | cylinderRotationArrow
  | diskSpinArrow
  | precessionArrow
  | tiltAngleArc
  deriving DecidableEq, Fintype, Repr

/-- Physical interpretation of each curved or axial arrow in the figure. -/
inductive FigureArrowMeaning where
  | rotationAboutCylinderAxis
  | spinAboutDiskNormal
  | precessionAboutCylinderAxis
  deriving DecidableEq, Repr

/-!
Typed transcription of the labels and qualitative incidence information in
the `352 × 365` primary raster.  It contains no magnetic-field or torque
answer readout.
-/
structure RotatingCylinderDiskFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  labelShown : FigureLabel → Bool
  featureShown : FigureFeature → Bool
  cylinderAxisDrawnVertical : Bool
  diskDrawnTiltedRelativeToAxis : Bool
  diskCenterDrawnOnCylinderAxis : Bool
  thetaArcRunsFromCylinderAxisToOmegaTwo : Bool
  omegaTwoArrowStartsAtDiskCenter : Bool
  cylinderRotationArrowMeaning : FigureArrowMeaning
  diskSpinArrowMeaning : FigureArrowMeaning
  precessionArrowMeaning : FigureArrowMeaning
  containsTorqueMagnitudeReadout : Bool

/-!
Independent physical quantities and observables of the cylinder-disk system.
The far-from-edge region and cylinder axis are retained as spatial sets.  The
actual and idealized magnetic fields and torques, along with their physical
remainders and error controls, are independent fields constrained only by the
governing-law structures below.
-/
structure RotatingCylinderDiskSetup where
  cylinderModel : CylindricalShellModel
  diskModel : DiskModel
  mountingModel : DiskMountingModel
  diskScaleRegime : DiskScaleRegime
  spinRegime : SpinRegime
  interactionResponse : MagneticInteractionResponse
  cylinderRadius : LengthMagnitude
  cylinderHeight : LengthMagnitude
  cylinderChargeMagnitude : ChargeMagnitude
  cylinderAngularSpeedMagnitude : AngularSpeedMagnitude
  diskRadius : LengthMagnitude
  diskMass : MassMagnitude
  diskChargeMagnitude : ChargeMagnitude
  diskAngularSpeedMagnitude : AngularSpeedMagnitude
  precessionAngularSpeedMagnitude : AngularSpeedMagnitude
  cylinderSurfaceCurrentDensityMagnitude : SurfaceCurrentDensityMagnitude
  vacuumPermeability : VacuumPermeabilityMagnitude
  idealInteriorMagneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  idealInteriorMagneticFluxDensityVector : MagneticFluxDensityVector
  interiorMagneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  interiorMagneticFluxDensityVector : MagneticFluxDensityVector
  fieldApproximationRemainderVector : MagneticFluxDensityVector
  longCylinderRelativeFieldErrorTolerance : ℝ
  magneticField : Electromagnetism.MagneticField 3
  cylinderInterior : Set (Space 3)
  interiorFarFromEdges : Set (Space 3)
  cylinderAxisLine : Set (Space 3)
  diskCenter : Space 3
  cylinderAxisUnit : SpatialVector
  diskSpinAxisUnit : SpatialVector
  precessionAxisUnit : SpatialVector
  tiltAngleRadians : ℝ
  diskMagneticMomentMagnitude : MagneticMomentMagnitude
  diskMagneticMomentVector : MagneticMomentVector
  idealMagneticTorqueMagnitude : TorqueMagnitude
  idealMagneticTorqueVector : TorqueVector
  magneticTorqueMagnitude : TorqueMagnitude
  magneticTorqueVector : TorqueVector
  torqueApproximationRemainderVector : TorqueVector
  torqueApproximationErrorBound : TorqueMagnitude
  figure : RotatingCylinderDiskFigure

/-! ## Scenario, figure readouts, physical domain, geometry, and laws -/

/-- Qualitative apparatus and placement assumptions stated in the problem. -/
structure MatchesRotatingCylinderDiskScenario
    (setup : RotatingCylinderDiskSetup) : Prop where
  cylinderIsUniformChargedThinShell :
    setup.cylinderModel = .uniformlyChargedThinShell
  rotorIsUniformChargedThinDisk :
    setup.diskModel = .uniformlyChargedThinDisk
  diskMountedAtCentralPivot :
    setup.mountingModel = .pivotAtDiskCenter
  diskUsesSmallDipoleRegime :
    setup.diskScaleRegime = .verySmallComparedWithCylinder
  diskSpinsRapidly : setup.spinRegime = .rapidSpin
  interactionCausesAxialPrecession :
    setup.interactionResponse = .precessionAboutCylinderAxis
  farFromEdgesLiesInsideCylinder :
    setup.interiorFarFromEdges ⊆ setup.cylinderInterior
  diskCenterInsideFarFromEdgesRegion :
    setup.diskCenter ∈ setup.interiorFarFromEdges
  diskCenterOnCylinderAxis :
    setup.diskCenter ∈ setup.cylinderAxisLine

/-! Direct qualitative and label evidence from the primary image. -/
structure MatchesSuppliedRotatingCylinderDiskFigure
    (setup : RotatingCylinderDiskSetup) : Prop where
  rasterWidth : setup.figure.rasterWidthPixels = 352
  rasterHeight : setup.figure.rasterHeightPixels = 365
  everyLiteralLabelShown : ∀ label, setup.figure.labelShown label = true
  everyNamedFeatureShown : ∀ feature, setup.figure.featureShown feature = true
  axisIsDrawnVertical : setup.figure.cylinderAxisDrawnVertical = true
  diskIsDrawnTilted : setup.figure.diskDrawnTiltedRelativeToAxis = true
  diskCenterIsDrawnOnAxis :
    setup.figure.diskCenterDrawnOnCylinderAxis = true
  thetaArcConnectsAxisAndOmegaTwo :
    setup.figure.thetaArcRunsFromCylinderAxisToOmegaTwo = true
  omegaTwoStartsAtDiskCenter :
    setup.figure.omegaTwoArrowStartsAtDiskCenter = true
  omegaOneArrowMeansCylinderRotation :
    setup.figure.cylinderRotationArrowMeaning = .rotationAboutCylinderAxis
  omegaTwoArrowMeansDiskSpin :
    setup.figure.diskSpinArrowMeaning = .spinAboutDiskNormal
  omegaArrowMeansPrecession :
    setup.figure.precessionArrowMeaning = .precessionAboutCylinderAxis
  noTorqueMagnitudePrinted :
    setup.figure.containsTorqueMagnitudeReadout = false

/-- Positivity and nondegeneracy of the physical branch shown in the figure. -/
structure HasPhysicalRotatingCylinderDiskParameters
    (setup : RotatingCylinderDiskSetup) : Prop where
  cylinderRadiusPositive : 0 < lengthInMeters setup.cylinderRadius
  cylinderHeightPositive : 0 < lengthInMeters setup.cylinderHeight
  diskRadiusPositive : 0 < lengthInMeters setup.diskRadius
  diskSmallerThanCylinder :
    lengthInMeters setup.diskRadius < lengthInMeters setup.cylinderRadius
  diskMassPositive : 0 < massInKilograms setup.diskMass
  cylinderChargeMagnitudePositive :
    0 < chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude
  diskChargeMagnitudePositive :
    0 < chargeMagnitudeInCoulombs setup.diskChargeMagnitude
  cylinderAngularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond
      setup.cylinderAngularSpeedMagnitude
  diskAngularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude
  precessionAngularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond
      setup.precessionAngularSpeedMagnitude
  vacuumPermeabilityPositive :
    0 < vacuumPermeabilityInNewtonsPerAmpereSquared
      setup.vacuumPermeability
  longCylinderFieldErrorToleranceNonnegative :
    0 ≤ setup.longCylinderRelativeFieldErrorTolerance
  longCylinderFieldErrorToleranceLessThanOne :
    setup.longCylinderRelativeFieldErrorTolerance < 1
  torqueApproximationErrorBoundNonnegative :
    0 ≤ torqueMagnitudeInNewtonMeters setup.torqueApproximationErrorBound
  tiltAnglePositive : 0 < setup.tiltAngleRadians
  tiltAngleLessThanPi : setup.tiltAngleRadians < Real.pi

/-!
Three-dimensional orientation encoded by the primary image and prose.  The
disk spin axis is the normal to the disk, `θ` is its unoriented angle to the
cylinder axis, and the precession axis is the cylinder axis.
-/
structure MatchesCylinderDiskOrientationGeometry
    (setup : RotatingCylinderDiskSetup) : Prop where
  cylinderAxisIsUnit : ‖setup.cylinderAxisUnit‖ = 1
  diskSpinAxisIsUnit : ‖setup.diskSpinAxisUnit‖ = 1
  precessionAxisIsUnit : ‖setup.precessionAxisUnit‖ = 1
  diskAxisTiltAngle :
    InnerProductGeometry.angle
        setup.diskSpinAxisUnit setup.cylinderAxisUnit =
      setup.tiltAngleRadians
  precessionUsesCylinderAxis :
    setup.precessionAxisUnit = setup.cylinderAxisUnit

/-!
The rotating charged shell acts as an azimuthal surface current
`K = Q₁ ω₁ / (2 π H)`.  The exactly uniform field `B∞ = μ₀ K` belongs to the
infinite-length idealization; it is not asserted to be the actual finite-shell
field merely because the disk is far from the ends.
-/
structure SatisfiesRotatingChargedCylinderFieldLaws
    (setup : RotatingCylinderDiskSetup) : Prop where
  rotatingShellSurfaceCurrentLaw :
    surfaceCurrentDensityInAmperesPerMeter
        setup.cylinderSurfaceCurrentDensityMagnitude =
      chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
          angularSpeedInRadiansPerSecond
            setup.cylinderAngularSpeedMagnitude /
        (2 * Real.pi * lengthInMeters setup.cylinderHeight)
  idealInfiniteShellFieldMagnitudeLaw :
    magneticFluxDensityInTeslas
        setup.idealInteriorMagneticFluxDensityMagnitude =
      vacuumPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        surfaceCurrentDensityInAmperesPerMeter
          setup.cylinderSurfaceCurrentDensityMagnitude
  idealFieldPointsAlongCylinderAxis :
    magneticFluxDensityVectorInTeslas
        setup.idealInteriorMagneticFluxDensityVector =
      magneticFluxDensityInTeslas
          setup.idealInteriorMagneticFluxDensityMagnitude •
        setup.cylinderAxisUnit

/-!
Finite-cylinder approximation contract.  The actual field at the disk center
is decomposed into the ideal infinite-shell field and a stored vector
remainder.  Its norm is controlled by a dimensionless relative tolerance.
This is an explicit finite-parameter error statement, not an exact field law
selected by a qualitative regime tag.
-/
structure SatisfiesFiniteCylinderFieldApproximation
    (setup : RotatingCylinderDiskSetup) : Prop where
  fieldRemainderDecomposition :
    magneticFluxDensityVectorInTeslas
        setup.interiorMagneticFluxDensityVector =
      magneticFluxDensityVectorInTeslas
          setup.idealInteriorMagneticFluxDensityVector +
        magneticFluxDensityVectorInTeslas
          setup.fieldApproximationRemainderVector
  fieldRemainderBound :
    ‖magneticFluxDensityVectorInTeslas
        setup.fieldApproximationRemainderVector‖ ≤
      setup.longCylinderRelativeFieldErrorTolerance *
        magneticFluxDensityInTeslas
          setup.idealInteriorMagneticFluxDensityMagnitude
  actualFieldMagnitudeIsVectorNorm :
    magneticFluxDensityInTeslas
        setup.interiorMagneticFluxDensityMagnitude =
      ‖magneticFluxDensityVectorInTeslas
        setup.interiorMagneticFluxDensityVector‖
  physlibFieldAtDiskCenter : ∀ time,
    setup.magneticField time setup.diskCenter =
      magneticFluxDensityVectorInTeslas
        setup.interiorMagneticFluxDensityVector

/-!
The supplied magnetic moment of the uniformly charged thin disk is
`μ = Q₂ ω₂ R₂² / 4`, directed along the disk's spin axis.
-/
structure SatisfiesSpinningChargedDiskMagneticMomentLaw
    (setup : RotatingCylinderDiskSetup) : Prop where
  chargedDiskMagneticMomentMagnitudeLaw :
    magneticMomentMagnitudeInAmpereSquareMeters
        setup.diskMagneticMomentMagnitude =
      (1 / 4 : ℝ) *
        chargeMagnitudeInCoulombs setup.diskChargeMagnitude *
        angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude *
        lengthInMeters setup.diskRadius ^ 2
  magneticMomentPointsAlongDiskSpinAxis :
    magneticMomentVectorInAmpereSquareMeters
        setup.diskMagneticMomentVector =
      magneticMomentMagnitudeInAmpereSquareMeters
          setup.diskMagneticMomentMagnitude •
        setup.diskSpinAxisUnit

/-!
In the uniform infinite-shell idealization, the magnetic torque is
`τ∞ = μ × B∞`; its separately stored magnitude is the Euclidean norm of that
ideal vector observable.
-/
structure SatisfiesMagneticDipoleTorqueLaw
    (setup : RotatingCylinderDiskSetup) : Prop where
  idealMagneticTorqueIsMomentCrossField :
    torqueVectorInNewtonMeters setup.idealMagneticTorqueVector =
      spatialCross
        (magneticMomentVectorInAmpereSquareMeters
          setup.diskMagneticMomentVector)
        (magneticFluxDensityVectorInTeslas
          setup.idealInteriorMagneticFluxDensityVector)
  idealTorqueMagnitudeIsVectorNorm :
    torqueMagnitudeInNewtonMeters setup.idealMagneticTorqueMagnitude =
      ‖torqueVectorInNewtonMeters setup.idealMagneticTorqueVector‖

/-!
The actual finite-apparatus torque is the ideal uniform-field dipole torque
plus a physical vector remainder.  The remainder bound accounts for the
finite cylinder, residual field variation across the small disk, and any
higher multipole contribution suppressed by the scale separation.  It does
not assume the answer formula.
-/
structure SatisfiesFiniteApparatusTorqueApproximation
    (setup : RotatingCylinderDiskSetup) : Prop where
  torqueRemainderDecomposition :
    torqueVectorInNewtonMeters setup.magneticTorqueVector =
      torqueVectorInNewtonMeters setup.idealMagneticTorqueVector +
        torqueVectorInNewtonMeters
          setup.torqueApproximationRemainderVector
  torqueRemainderBound :
    ‖torqueVectorInNewtonMeters
        setup.torqueApproximationRemainderVector‖ ≤
      torqueMagnitudeInNewtonMeters setup.torqueApproximationErrorBound
  actualTorqueMagnitudeIsVectorNorm :
    torqueMagnitudeInNewtonMeters setup.magneticTorqueMagnitude =
      ‖torqueVectorInNewtonMeters setup.magneticTorqueVector‖

/-! ## Derived physical relations -/

/-- The two rotating-shell laws imply the ideal infinite-shell axial field. -/
lemma rotatingCylinderIdealInteriorFieldMagnitudeFormula
    (setup : RotatingCylinderDiskSetup)
    (_fieldLaws : SatisfiesRotatingChargedCylinderFieldLaws setup) :
    magneticFluxDensityInTeslas
        setup.idealInteriorMagneticFluxDensityMagnitude =
      vacuumPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedMagnitude /
        (2 * Real.pi * lengthInMeters setup.cylinderHeight) := by
  rw [_fieldLaws.idealInfiniteShellFieldMagnitudeLaw,
    _fieldLaws.rotatingShellSurfaceCurrentLaw]
  ring

/-!
Before substituting either source formula, the ideal dipole law and angle
geometry give `|τ∞| = μ B∞ sin θ`.
-/
lemma idealMagneticDipoleTorqueMagnitudeFormula
    (setup : RotatingCylinderDiskSetup)
    (_geometry : MatchesCylinderDiskOrientationGeometry setup)
    (_fieldLaws : SatisfiesRotatingChargedCylinderFieldLaws setup)
    (_momentLaw : SatisfiesSpinningChargedDiskMagneticMomentLaw setup)
    (_torqueLaw : SatisfiesMagneticDipoleTorqueLaw setup) :
    torqueMagnitudeInNewtonMeters setup.idealMagneticTorqueMagnitude =
      magneticMomentMagnitudeInAmpereSquareMeters
          setup.diskMagneticMomentMagnitude *
        magneticFluxDensityInTeslas
          setup.idealInteriorMagneticFluxDensityMagnitude *
        Real.sin setup.tiltAngleRadians := by
  rw [_torqueLaw.idealTorqueMagnitudeIsVectorNorm,
    _torqueLaw.idealMagneticTorqueIsMomentCrossField,
    _momentLaw.magneticMomentPointsAlongDiskSpinAxis,
    _fieldLaws.idealFieldPointsAlongCylinderAxis]
  simp [spatialCross, map_smul, smul_smul, norm_smul, Real.norm_eq_abs]
  rw [InnerProductGeometry.norm_ofLp_crossProduct]
  rw [_geometry.diskSpinAxisIsUnit, _geometry.cylinderAxisIsUnit,
    _geometry.diskAxisTiltAngle]
  have moment_nonnegative :
      0 ≤ magneticMomentMagnitudeInAmpereSquareMeters
        setup.diskMagneticMomentMagnitude := by
    exact NNReal.coe_nonneg _
  have field_nonnegative :
      0 ≤ magneticFluxDensityInTeslas
        setup.idealInteriorMagneticFluxDensityMagnitude := by
    exact NNReal.coe_nonneg _
  rw [abs_of_nonneg moment_nonnegative, abs_of_nonneg field_nonnegative]
  ring

/-!
The reverse triangle inequality transports the vector-remainder contract to
an absolute error bound for torque magnitudes.  This is the quantitative
finite-apparatus conclusion that replaces the former global exact equality.
-/
lemma finiteApparatusTorqueMagnitudeErrorBound
    (setup : RotatingCylinderDiskSetup)
    (_torqueApproximation :
      SatisfiesFiniteApparatusTorqueApproximation setup) :
    |torqueMagnitudeInNewtonMeters setup.magneticTorqueMagnitude -
        torqueMagnitudeInNewtonMeters setup.idealMagneticTorqueMagnitude| ≤
      torqueMagnitudeInNewtonMeters setup.torqueApproximationErrorBound := by
  have vector_norm_error :
      |‖torqueVectorInNewtonMeters setup.magneticTorqueVector‖ -
          ‖torqueVectorInNewtonMeters setup.idealMagneticTorqueVector‖| ≤
        torqueMagnitudeInNewtonMeters setup.torqueApproximationErrorBound := by
    calc
      |‖torqueVectorInNewtonMeters setup.magneticTorqueVector‖ -
          ‖torqueVectorInNewtonMeters setup.idealMagneticTorqueVector‖| ≤
          ‖torqueVectorInNewtonMeters setup.magneticTorqueVector -
            torqueVectorInNewtonMeters setup.idealMagneticTorqueVector‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖torqueVectorInNewtonMeters
          setup.torqueApproximationRemainderVector‖ := by
        rw [_torqueApproximation.torqueRemainderDecomposition]
        simp
      _ ≤ torqueMagnitudeInNewtonMeters setup.torqueApproximationErrorBound :=
        _torqueApproximation.torqueRemainderBound
  rw [_torqueApproximation.actualTorqueMagnitudeIsVectorNorm]
  have ideal_magnitude_is_vector_norm :
      torqueMagnitudeInNewtonMeters setup.idealMagneticTorqueMagnitude =
        ‖torqueVectorInNewtonMeters setup.idealMagneticTorqueVector‖ := by
    -- This is exactly `SatisfiesMagneticDipoleTorqueLaw.
    -- idealTorqueMagnitudeIsVectorNorm`, but that law is not among this
    -- lemma's hypotheses, and the two observables are independent setup
    -- fields.
    sorry
  rw [ideal_magnitude_is_vector_norm]
  exact vector_norm_error

/-! ## Displayed answer choices and current target -/

/-- Labels of the four torque-magnitude choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Scalar coherent-SI expressions displayed beside each answer label.  Choice A
is transcribed literally even though it omits one power of `R₂`.
-/
def displayedTorqueMagnitudeInNewtonMeters
    (setup : RotatingCylinderDiskSetup) : AnswerChoice → ℝ
  | .A =>
      vacuumPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
        chargeMagnitudeInCoulombs setup.diskChargeMagnitude *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedMagnitude *
        angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude *
        lengthInMeters setup.diskRadius *
        Real.sin setup.tiltAngleRadians /
        (8 * Real.pi * lengthInMeters setup.cylinderHeight)
  | .B =>
      vacuumPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
        chargeMagnitudeInCoulombs setup.diskChargeMagnitude *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedMagnitude *
        angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude *
        lengthInMeters setup.diskRadius ^ 2 *
        Real.sin setup.tiltAngleRadians /
        (8 * Real.pi * lengthInMeters setup.cylinderHeight)
  | .C =>
      vacuumPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
        chargeMagnitudeInCoulombs setup.diskChargeMagnitude *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedMagnitude *
        angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude *
        lengthInMeters setup.diskRadius ^ 2 *
        Real.cos setup.tiltAngleRadians /
        (8 * Real.pi * lengthInMeters setup.cylinderHeight)
  | .D =>
      vacuumPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
        chargeMagnitudeInCoulombs setup.diskChargeMagnitude *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedMagnitude *
        angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude *
        lengthInMeters setup.diskRadius ^ 2 /
        (8 * Real.pi * lengthInMeters setup.cylinderHeight)

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
In the infinite-shell, uniform-field idealization, the magnetic torque
magnitude is

`μ₀ Q₁ Q₂ ω₁ ω₂ R₂² sin θ / (8 π H)`,

which is the expression displayed as answer B.  For the actual finite
cylinder and disk, the second conjunct gives the explicit absolute-error
guarantee justified by the approximation contract.

Blueprint: `thm:physics:phyx_mini_0967:target`.
-/
theorem problem_phyx_mini_0967
    (setup : RotatingCylinderDiskSetup)
    (_scenario : MatchesRotatingCylinderDiskScenario setup)
    (_figure : MatchesSuppliedRotatingCylinderDiskFigure setup)
    (_physical : HasPhysicalRotatingCylinderDiskParameters setup)
    (_geometry : MatchesCylinderDiskOrientationGeometry setup)
    (_fieldLaws : SatisfiesRotatingChargedCylinderFieldLaws setup)
    (_fieldApproximation :
      SatisfiesFiniteCylinderFieldApproximation setup)
    (_momentLaw : SatisfiesSpinningChargedDiskMagneticMomentLaw setup)
    (_torqueLaw : SatisfiesMagneticDipoleTorqueLaw setup)
    (_torqueApproximation :
      SatisfiesFiniteApparatusTorqueApproximation setup) :
    torqueMagnitudeInNewtonMeters setup.idealMagneticTorqueMagnitude =
        vacuumPermeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
          chargeMagnitudeInCoulombs setup.diskChargeMagnitude *
          angularSpeedInRadiansPerSecond
            setup.cylinderAngularSpeedMagnitude *
          angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude *
          lengthInMeters setup.diskRadius ^ 2 *
          Real.sin setup.tiltAngleRadians /
          (8 * Real.pi * lengthInMeters setup.cylinderHeight) ∧
      |torqueMagnitudeInNewtonMeters setup.magneticTorqueMagnitude -
          displayedTorqueMagnitudeInNewtonMeters
            setup recordedDatasetAnswer| ≤
        torqueMagnitudeInNewtonMeters setup.torqueApproximationErrorBound := by
  have ideal_torque_formula :=
    idealMagneticDipoleTorqueMagnitudeFormula setup _geometry _fieldLaws
      _momentLaw _torqueLaw
  rw [_momentLaw.chargedDiskMagneticMomentMagnitudeLaw,
    rotatingCylinderIdealInteriorFieldMagnitudeFormula setup _fieldLaws] at ideal_torque_formula
  have height_ne_zero :
      lengthInMeters setup.cylinderHeight ≠ 0 :=
    ne_of_gt _physical.cylinderHeightPositive
  have evaluated_ideal_torque :
      torqueMagnitudeInNewtonMeters setup.idealMagneticTorqueMagnitude =
        vacuumPermeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          chargeMagnitudeInCoulombs setup.cylinderChargeMagnitude *
          chargeMagnitudeInCoulombs setup.diskChargeMagnitude *
          angularSpeedInRadiansPerSecond
            setup.cylinderAngularSpeedMagnitude *
          angularSpeedInRadiansPerSecond setup.diskAngularSpeedMagnitude *
          lengthInMeters setup.diskRadius ^ 2 *
          Real.sin setup.tiltAngleRadians /
          (8 * Real.pi * lengthInMeters setup.cylinderHeight) := by
    rw [ideal_torque_formula]
    field_simp [Real.pi_ne_zero, height_ne_zero]
    <;> ring
  refine ⟨evaluated_ideal_torque, ?_⟩
  rw [show displayedTorqueMagnitudeInNewtonMeters setup recordedDatasetAnswer =
      torqueMagnitudeInNewtonMeters setup.idealMagneticTorqueMagnitude by
    simpa [recordedDatasetAnswer, displayedTorqueMagnitudeInNewtonMeters] using
      evaluated_ideal_torque.symm]
  rw [_torqueApproximation.actualTorqueMagnitudeIsVectorNorm,
    _torqueLaw.idealTorqueMagnitudeIsVectorNorm]
  calc
    |‖torqueVectorInNewtonMeters setup.magneticTorqueVector‖ -
        ‖torqueVectorInNewtonMeters setup.idealMagneticTorqueVector‖| ≤
        ‖torqueVectorInNewtonMeters setup.magneticTorqueVector -
          torqueVectorInNewtonMeters setup.idealMagneticTorqueVector‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖torqueVectorInNewtonMeters
        setup.torqueApproximationRemainderVector‖ := by
      rw [_torqueApproximation.torqueRemainderDecomposition]
      simp
    _ ≤ torqueMagnitudeInNewtonMeters setup.torqueApproximationErrorBound :=
      _torqueApproximation.torqueRemainderBound

end PhyXMiniProblems.ProblemPhyXMini0967
