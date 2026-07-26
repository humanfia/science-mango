import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0775

open Dimension

/-!
# A falling block driving two welded disks

Two concentric metal disks are welded together and rotate about a frictionless
horizontal axle through their common center.  A light string is wrapped around
the smaller disk and supports a block.  The block is released from rest two
meters above the floor.

Physical masses, lengths, speeds, accelerations, angular speeds, and moments of
inertia are represented by Physlib's unit-independent `Dimensionful` types.
Real numbers occur only as coherent-SI readouts, coordinates in Physlib's
rigid-body interface, or dimensionless displayed data.

Assumption/target split:

* governing laws: uniform-solid-disk axial inertia, addition of the two welded
  disks' inertias, the rigid-body rotational-energy law, no-slip string
  kinematics, and conservation of mechanical energy;
* previous-part results: none;
* figure/data readouts: the `R₁` and `R₂` labels, concentric disks, common
  horizontal axle, string on the smaller disk, hanging `1.50 kg` block,
  `R₁ = 2.50 cm`, `M₁ = 0.80 kg`, `R₂ = 5.00 cm`, `M₂ = 1.60 kg`, release
  height `2.00 m`, and release from rest;
* target conclusions: the block's exact speed immediately before impact and
  its agreement, after rounding to a hundredth, with answer choice B,
  `3.40 m/s`.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension of an axial moment of inertia, `mass * length²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative axial moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Radian-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  nonnegativeSIReadout angularSpeed

/-- Kilogram-meter-squared readout of an axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (momentOfInertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout momentOfInertia

/-! ## Physical roles and primary-image vocabulary -/

/-- The two welded disks. -/
inductive Disk where
  | smaller
  | larger
  deriving DecidableEq, Fintype, Repr

/-- The two stages needed for the release-to-impact energy balance. -/
inductive MotionStage where
  | release
  | justBeforeImpact
  deriving DecidableEq, Fintype, Repr

/-- Radius labels visible in the primary image. -/
inductive RadiusLabel where
  | R1
  | R2
  deriving DecidableEq, Fintype, Repr

/-- The mass-distribution idealization used by the disk inertia law. -/
inductive DiskMassModel where
  | uniformSolid
  | other
  deriving DecidableEq, Repr

/-- Mechanical coupling between the two concentric disks. -/
inductive DiskCoupling where
  | welded
  | other
  deriving DecidableEq, Repr

/-- Location of the axle relative to the disks. -/
inductive AxleLocation where
  | throughCommonCenter
  | other
  deriving DecidableEq, Repr

/-- Orientation of the axle in the supplied image. -/
inductive AxleOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Resistive idealization of the rotation axis. -/
inductive AxleResistanceModel where
  | frictionless
  | other
  deriving DecidableEq, Repr

/-- Mass idealization justified by the description of the string as light. -/
inductive StringMassModel where
  | negligible
  | other
  deriving DecidableEq, Repr

/-- Contact condition between the string and the smaller disk. -/
inductive StringDiskContact where
  | noSlip
  | other
  deriving DecidableEq, Repr

/-!
Qualitative evidence transcribed from image `775.png`.  The image supplies
layout and labels only; no physical radius is inferred from the drawn sizes.
-/
structure WeldedDiskPulleyFigure where
  showsDisk : Disk → Bool
  showsRadiusLabel : RadiusLabel → Bool
  radiusLabelIdentifies : RadiusLabel → Disk
  showsConcentricDisks : Bool
  showsCommonHorizontalAxle : Bool
  showsStringWrappedAroundSmallerDisk : Bool
  showsStringHangingVertically : Bool
  showsBlockBelowDisks : Bool
  showsBlockMassLabelOnePointFiveKilograms : Bool

/-!
Independent physical quantities for the system.  Speeds at both stages,
angular speeds, component and total inertias, and the rigid-body realization
are stored independently.  None is defined from the displayed `3.40 m/s`
answer.
-/
structure WeldedDiskPulleySetup where
  figure : WeldedDiskPulleyFigure
  diskMass : Disk → MassQuantity
  diskRadius : Disk → LengthQuantity
  blockMass : MassQuantity
  blockHeightAboveFloor : MotionStage → LengthQuantity
  blockSpeed : MotionStage → SpeedQuantity
  disksAngularSpeed : MotionStage → AngularSpeedQuantity
  diskMomentOfInertia : Disk → MomentOfInertiaQuantity
  totalMomentOfInertia : MomentOfInertiaQuantity
  gravitationalAcceleration : AccelerationQuantity
  combinedDisksRigidBodySI : RigidBody 3
  axleAxis : Fin 3
  angularVelocityVectorRadiansPerSecond : MotionStage → Fin 3 → ℝ
  diskMassModel : Disk → DiskMassModel
  diskCoupling : DiskCoupling
  axleLocation : AxleLocation
  axleOrientation : AxleOrientation
  axleResistanceModel : AxleResistanceModel
  stringMassModel : StringMassModel
  stringDiskContact : StringDiskContact
  stringWrappedDisk : Disk
  stringIsTaut : Bool

/-! ## Figure evidence, supplied data, and admissibility -/

/-- Facts visible in the supplied primary image. -/
structure MatchesPrimaryFigure (setup : WeldedDiskPulleySetup) : Prop where
  bothDisksShown : ∀ disk, setup.figure.showsDisk disk = true
  bothRadiusLabelsShown : ∀ label, setup.figure.showsRadiusLabel label = true
  R1LabelsSmallerDisk :
    setup.figure.radiusLabelIdentifies .R1 = .smaller
  R2LabelsLargerDisk :
    setup.figure.radiusLabelIdentifies .R2 = .larger
  concentricDisksShown : setup.figure.showsConcentricDisks = true
  commonHorizontalAxleShown :
    setup.figure.showsCommonHorizontalAxle = true
  wrappedStringShown :
    setup.figure.showsStringWrappedAroundSmallerDisk = true
  verticalStringShown : setup.figure.showsStringHangingVertically = true
  hangingBlockShown : setup.figure.showsBlockBelowDisks = true
  blockMassLabelShown :
    setup.figure.showsBlockMassLabelOnePointFiveKilograms = true

/-!
Numerical and qualitative data supplied in the prose.  Uniform solid disks
and a negligible-mass taut string are the standard textbook idealizations
needed for the recorded numerical answer.
-/
structure MatchesProblemData (setup : WeldedDiskPulleySetup) : Prop where
  smallerDiskRadiusMeters :
    lengthInMeters (setup.diskRadius .smaller) = 0.025
  largerDiskRadiusMeters :
    lengthInMeters (setup.diskRadius .larger) = 0.050
  smallerDiskMassKilograms :
    massInKilograms (setup.diskMass .smaller) = 0.80
  largerDiskMassKilograms :
    massInKilograms (setup.diskMass .larger) = 1.60
  blockMassKilograms : massInKilograms setup.blockMass = 1.50
  releaseHeightMeters :
    lengthInMeters (setup.blockHeightAboveFloor .release) = 2.00
  impactHeightMeters :
    lengthInMeters (setup.blockHeightAboveFloor .justBeforeImpact) = 0
  blockReleasedFromRest :
    speedInMetersPerSecond (setup.blockSpeed .release) = 0
  disksReleasedFromRest :
    angularSpeedInRadiansPerSecond
      (setup.disksAngularSpeed .release) = 0
  bothDisksUniformSolid :
    ∀ disk, setup.diskMassModel disk = .uniformSolid
  disksAreWelded : setup.diskCoupling = .welded
  axleThroughCommonCenter : setup.axleLocation = .throughCommonCenter
  axleIsHorizontal : setup.axleOrientation = .horizontal
  axleIsFrictionless : setup.axleResistanceModel = .frictionless
  lightStringHasNegligibleMass : setup.stringMassModel = .negligible
  stringDoesNotSlip : setup.stringDiskContact = .noSlip
  stringIsWrappedAroundSmallerDisk : setup.stringWrappedDisk = .smaller
  tautString : setup.stringIsTaut = true

/-- The standard near-Earth value used to evaluate the displayed choices. -/
structure UsesStandardEarthGravity (setup : WeldedDiskPulleySetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 9.8

/-!
Positivity and nondegeneracy of the physical inputs.  In particular, no
numerical value or positivity beyond nonnegativity is imposed on the unknown
impact speed.
-/
structure HasPhysicalParameters (setup : WeldedDiskPulleySetup) : Prop where
  everyDiskMassPositive :
    ∀ disk, 0 < massInKilograms (setup.diskMass disk)
  everyDiskRadiusPositive :
    ∀ disk, 0 < lengthInMeters (setup.diskRadius disk)
  blockMassPositive : 0 < massInKilograms setup.blockMass
  releaseHeightPositive :
    0 < lengthInMeters (setup.blockHeightAboveFloor .release)
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  totalMomentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.totalMomentOfInertia

/-! ## Governing rotational, no-slip, and energy laws -/

/-!
The two uniform-solid-disk inertia formulas, their additivity after welding,
and the bridge to Physlib's three-dimensional rigid-body representation.
Angular velocity is directed along the selected axle coordinate.
-/
structure SatisfiesWeldedUniformDiskRotationalLaws
    (setup : WeldedDiskPulleySetup) : Prop where
  uniformSolidDiskMomentOfInertia :
    ∀ disk,
      momentOfInertiaInKilogramMetersSquared
          (setup.diskMomentOfInertia disk) =
        (1 / 2 : ℝ) * massInKilograms (setup.diskMass disk) *
          lengthInMeters (setup.diskRadius disk) ^ 2
  weldedMomentsAdd :
    momentOfInertiaInKilogramMetersSquared
        setup.totalMomentOfInertia =
      momentOfInertiaInKilogramMetersSquared
          (setup.diskMomentOfInertia .smaller) +
        momentOfInertiaInKilogramMetersSquared
          (setup.diskMomentOfInertia .larger)
  rigidBodyMassIsDiskMassSum :
    setup.combinedDisksRigidBodySI.mass =
      massInKilograms (setup.diskMass .smaller) +
        massInKilograms (setup.diskMass .larger)
  axleTensorEntryMatchesTotalMoment :
    setup.combinedDisksRigidBodySI.inertiaTensor
        setup.axleAxis setup.axleAxis =
      momentOfInertiaInKilogramMetersSquared
        setup.totalMomentOfInertia
  angularVelocityIsAlongAxle :
    ∀ stage component,
      setup.angularVelocityVectorRadiansPerSecond stage component =
        if component = setup.axleAxis then
          angularSpeedInRadiansPerSecond (setup.disksAngularSpeed stage)
        else 0

/-!
A taut string that does not slip has block speed equal to the tangential speed
of the smaller disk, `v = R₁ * omega`, at each modeled stage.
-/
structure SatisfiesNoSlipStringKinematics
    (setup : WeldedDiskPulleySetup) : Prop where
  tangentialSpeedCoupling :
    ∀ stage,
      speedInMetersPerSecond (setup.blockSpeed stage) =
        lengthInMeters (setup.diskRadius .smaller) *
          angularSpeedInRadiansPerSecond
            (setup.disksAngularSpeed stage)

/-!
Mechanical energy conservation between release and the instant immediately
before impact.  The three terms are block gravitational potential energy,
block translational kinetic energy, and the welded disks' rotational kinetic
energy from `RigidBody.rotationalKineticEnergy`.

This is a governing relation.  It contains the independent impact speed but
does not state its solved value or mention an answer choice.
-/
structure SatisfiesReleaseToImpactEnergyConservation
    (setup : WeldedDiskPulleySetup) : Prop where
  mechanicalEnergyConserved :
    massInKilograms setup.blockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters (setup.blockHeightAboveFloor .release) +
        (1 / 2 : ℝ) * massInKilograms setup.blockMass *
          speedInMetersPerSecond (setup.blockSpeed .release) ^ 2 +
        setup.combinedDisksRigidBodySI.rotationalKineticEnergy
          (setup.angularVelocityVectorRadiansPerSecond .release) =
      massInKilograms setup.blockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters
            (setup.blockHeightAboveFloor .justBeforeImpact) +
        (1 / 2 : ℝ) * massInKilograms setup.blockMass *
          speedInMetersPerSecond
            (setup.blockSpeed .justBeforeImpact) ^ 2 +
        setup.combinedDisksRigidBodySI.rotationalKineticEnergy
          (setup.angularVelocityVectorRadiansPerSecond .justBeforeImpact)

/-! ## Derived impact speed and displayed answers -/

/-- The two component inertias add to `0.00225 kg m² = 9/4000 kg m²`. -/
lemma totalMomentOfInertia_eq_nine_over_four_thousand
    (setup : WeldedDiskPulleySetup)
    (_data : MatchesProblemData setup)
    (_rotationalLaws : SatisfiesWeldedUniformDiskRotationalLaws setup) :
    momentOfInertiaInKilogramMetersSquared
        setup.totalMomentOfInertia = 9 / 4000 := by
  rw [_rotationalLaws.weldedMomentsAdd,
    _rotationalLaws.uniformSolidDiskMomentOfInertia .smaller,
    _rotationalLaws.uniformSolidDiskMomentOfInertia .larger,
    _data.smallerDiskMassKilograms, _data.largerDiskMassKilograms,
    _data.smallerDiskRadiusMeters, _data.largerDiskRadiusMeters]
  norm_num

/-!
Eliminating angular speed with `v = R₁ * omega` gives the standard effective-
mass formula.  It is a consequence of the governing laws, not a premise.
-/
lemma impactSpeed_squared_formula
    (setup : WeldedDiskPulleySetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_rotationalLaws : SatisfiesWeldedUniformDiskRotationalLaws setup)
    (_noSlip : SatisfiesNoSlipStringKinematics setup)
    (_energy : SatisfiesReleaseToImpactEnergyConservation setup) :
    speedInMetersPerSecond
          (setup.blockSpeed .justBeforeImpact) ^ 2 =
      (2 * massInKilograms setup.blockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (lengthInMeters (setup.blockHeightAboveFloor .release) -
            lengthInMeters
              (setup.blockHeightAboveFloor .justBeforeImpact))) /
        (massInKilograms setup.blockMass +
          momentOfInertiaInKilogramMetersSquared
              setup.totalMomentOfInertia /
            lengthInMeters (setup.diskRadius .smaller) ^ 2) := by
  have hrot (stage : MotionStage) :
      setup.combinedDisksRigidBodySI.rotationalKineticEnergy
          (setup.angularVelocityVectorRadiansPerSecond stage) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared setup.totalMomentOfInertia *
          angularSpeedInRadiansPerSecond (setup.disksAngularSpeed stage) ^ 2 := by
    rw [RigidBody.rotationalKineticEnergy]
    simp [dotProduct, Matrix.mulVec,
      _rotationalLaws.angularVelocityIsAlongAxle,
      _rotationalLaws.axleTensorEntryMatchesTotalMoment]
    ring
  have henergy := _energy.mechanicalEnergyConserved
  rw [hrot, hrot, _data.blockReleasedFromRest,
    _data.disksReleasedFromRest, _data.impactHeightMeters] at henergy
  norm_num at henergy
  have hnoslip := _noSlip.tangentialSpeedCoupling .justBeforeImpact
  rw [hnoslip] at henergy ⊢
  rw [_data.impactHeightMeters]
  norm_num
  have hr := _physical.everyDiskRadiusPositive .smaller
  have hden : 0 < massInKilograms setup.blockMass +
      momentOfInertiaInKilogramMetersSquared setup.totalMomentOfInertia /
        lengthInMeters (setup.diskRadius .smaller) ^ 2 :=
    add_pos _physical.blockMassPositive
      (div_pos _physical.totalMomentOfInertiaPositive (sq_pos_of_pos hr))
  rw [eq_div_iff hden.ne']
  field_simp [hr.ne']
  nlinarith [henergy]

/-!
For the supplied disk and block data with `g = 9.8 m/s²`, the nonnegative
impact speed is exactly `sqrt (196/17) m/s`, approximately `3.3955 m/s`.
-/
lemma impactSpeed_eq_sqrt_196_over_17
    (setup : WeldedDiskPulleySetup)
    (_data : MatchesProblemData setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_rotationalLaws : SatisfiesWeldedUniformDiskRotationalLaws setup)
    (_noSlip : SatisfiesNoSlipStringKinematics setup)
    (_energy : SatisfiesReleaseToImpactEnergyConservation setup) :
    speedInMetersPerSecond (setup.blockSpeed .justBeforeImpact) =
      Real.sqrt (196 / 17) := by
  have hsquared := impactSpeed_squared_formula setup _data _physical
    _rotationalLaws _noSlip _energy
  rw [_data.blockMassKilograms, _gravity.gravitationalAccelerationSI,
    _data.releaseHeightMeters, _data.impactHeightMeters,
    totalMomentOfInertia_eq_nine_over_four_thousand setup _data _rotationalLaws,
    _data.smallerDiskRadiusMeters] at hsquared
  norm_num at hsquared
  have hnonneg : 0 ≤ speedInMetersPerSecond
      (setup.blockSpeed .justBeforeImpact) := by
    unfold speedInMetersPerSecond
    positivity
  rw [← hsquared, Real.sqrt_sq hnonneg]

/-- Labels of the four speeds displayed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Meter-per-second value printed beside each answer label. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 3.12
  | .B => 3.40
  | .C => 3.86
  | .D => 4.86

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Agreement with a displayed hundredth means lying in its half-cent-wide
rounding interval.  This avoids the false statement that the unrounded exact
speed is literally `3.40 m/s`.
-/
def RoundsToDisplayedSpeed
    (speed : SpeedQuantity) (choice : AnswerChoice) : Prop :=
  choice.speedInMetersPerSecond - 1 / 200 ≤
      speedInMetersPerSecond speed ∧
    speedInMetersPerSecond speed <
      choice.speedInMetersPerSecond + 1 / 200

/-!
The exact modeled speed `sqrt (196/17) m/s` rounds to `3.40 m/s`.  Thus it
matches recorded answer B, and no other displayed answer satisfies the same
rounding relation.

This formalizes blueprint label `thm:physics:phyx_mini_0775:target`.
-/
theorem problem_phyx_mini_0775
    (setup : WeldedDiskPulleySetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_rotationalLaws : SatisfiesWeldedUniformDiskRotationalLaws setup)
    (_noSlip : SatisfiesNoSlipStringKinematics setup)
    (_energy : SatisfiesReleaseToImpactEnergyConservation setup) :
    speedInMetersPerSecond (setup.blockSpeed .justBeforeImpact) =
        Real.sqrt (196 / 17) ∧
      RoundsToDisplayedSpeed
        (setup.blockSpeed .justBeforeImpact) recordedDatasetAnswer ∧
      ∀ choice,
        RoundsToDisplayedSpeed
            (setup.blockSpeed .justBeforeImpact) choice →
          choice = recordedDatasetAnswer := by
  have hspeed := impactSpeed_eq_sqrt_196_over_17 setup _data _gravity
    _physical _rotationalLaws _noSlip _energy
  refine ⟨hspeed, ?_, ?_⟩
  · rw [RoundsToDisplayedSpeed, recordedDatasetAnswer,
      AnswerChoice.speedInMetersPerSecond, hspeed]
    constructor
    · exact
        (Real.le_sqrt'
          (by norm_num : (0 : ℝ) < 3.40 - 1 / 200)).2 (by norm_num)
    · exact
        (Real.sqrt_lt'
          (by norm_num : (0 : ℝ) < 3.40 + 1 / 200)).2 (by norm_num)
  · intro choice hchoice
    rw [RoundsToDisplayedSpeed, hspeed] at hchoice
    have hsqrt_sq : Real.sqrt (196 / 17) ^ 2 = (196 / 17 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (196 / 17) := Real.sqrt_nonneg _
    cases choice with
    | A =>
        change (3.12 - 1 / 200 ≤ Real.sqrt (196 / 17) ∧
          Real.sqrt (196 / 17) < 3.12 + 1 / 200) at hchoice
        norm_num [recordedDatasetAnswer]
        nlinarith [hsqrt_sq]
    | B => rfl
    | C =>
        change (3.86 - 1 / 200 ≤ Real.sqrt (196 / 17) ∧
          Real.sqrt (196 / 17) < 3.86 + 1 / 200) at hchoice
        norm_num [recordedDatasetAnswer]
        nlinarith [hsqrt_sq]
    | D =>
        change (4.86 - 1 / 200 ≤ Real.sqrt (196 / 17) ∧
          Real.sqrt (196 / 17) < 4.86 + 1 / 200) at hchoice
        norm_num [recordedDatasetAnswer]
        nlinarith [hsqrt_sq]

end PhyXMiniProblems.ProblemPhyXMini0775
