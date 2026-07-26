import Mathlib
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Kinetic energy of a three-disk machine part about axis 1

The primary figure shows three small disks `A`, `B`, and `C` joined by
lightweight struts.  Axis 1 passes through `A` perpendicular to the plane of
the triangular frame.  The labeled center-to-center strut lengths are
`AB = 0.50 m`, `BC = 0.30 m`, and `CA = 0.40 m`; the disk masses are
`m_A = 0.30 kg`, `m_B = 0.10 kg`, and `m_C = 0.20 kg`.  The requested motion
is rotation about axis 1 at `4.0 rad/s`.

Mass, length, angular speed, moment of inertia, and energy are represented by
Physlib dimensionful quantities.  Scalar real numbers occur only at coherent
SI readout boundaries, in Physlib's SI-coordinate rigid-body interface, and
in the printed multiple-choice data.

Assumption/target split:

* `MatchesPrimaryFigure` records the disk/strut labels, all printed masses and
  lengths, both depicted axes, and the axis-to-center distances implied by the
  figure.
* `MatchesProblemData` records the selected axis and angular speed, together
  with the stated small-disk and lightweight-strut idealizations.
* `SatisfiesThreeDiskRotationalLaws` records the point-mass inertia law and its
  connection to Physlib's inertia tensor and rotational kinetic energy.
* There are no previous-part results.
* The exact energy `0.456 J`, its rounding to the displayed `0.46 J`, and the
  fact that answer B is uniquely closest occur only in conclusions below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0819

open Dimension

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative scalar moment of inertia, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Rotational kinetic energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read angular speed in radians per coherent-SI second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Read an axial moment of inertia in coherent-SI `kg m²`. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules, calibrated by Physlib's joule. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Figure labels and physical setup -/

/-- The three labeled small disks in the primary figure. -/
inductive DiskLabel where
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- The three lightweight struts forming the triangular frame. -/
inductive StrutLabel where
  | AB
  | BC
  | CA
  deriving DecidableEq, Fintype, Repr

/-- The two axes explicitly labeled in the figure. -/
inductive AxisLabel where
  | axis1
  | axis2
  deriving DecidableEq, Fintype, Repr

/-- Orientation of an axis relative to the plane of the triangular frame. -/
inductive AxisOrientation where
  | perpendicularToFigurePlane
  | inFigurePlaneAlongBC
  deriving DecidableEq, Repr

/-- Idealization of each small disk when no disk radius is supplied. -/
inductive SmallDiskModel where
  | pointMassAtCenter
  deriving DecidableEq, Repr

/-- Idealization justified by the description of each strut as lightweight. -/
inductive StrutMassModel where
  | negligible
  deriving DecidableEq, Repr

/-- Literal and qualitative information transcribed from image `819.png`. -/
structure ThreeDiskFigure where
  showsDisk : DiskLabel → Bool
  showsStrut : StrutLabel → Bool
  strutEndpoints : StrutLabel → DiskLabel × DiskLabel
  printedDiskMassKilograms : DiskLabel → ℝ
  printedStrutLengthMeters : StrutLabel → ℝ
  showsAxis : AxisLabel → Bool
  axisPassesThrough : AxisLabel → DiskLabel → Bool
  axisOrientation : AxisLabel → AxisOrientation

/-!
Independent physical quantities for the machine part.  In particular,
`rotationalKineticEnergy` is not defined from any answer choice.  The
`RigidBody 3` fields expose Physlib's SI-coordinate mechanics, while the
corresponding physical scalar magnitudes remain dimensionful.
-/
structure ThreeDiskMachinePart where
  figure : ThreeDiskFigure
  diskMass : DiskLabel → MassQuantity
  strutLength : StrutLabel → LengthQuantity
  distanceFromAxis : AxisLabel → DiskLabel → LengthQuantity
  axialMomentOfInertia : AxisLabel → MomentOfInertiaQuantity
  givenAngularSpeed : AngularSpeedQuantity
  selectedAxis : AxisLabel
  rotationalKineticEnergy : AxisLabel → AngularSpeedQuantity → EnergyQuantity
  smallDiskModel : DiskLabel → SmallDiskModel
  strutMassModel : StrutLabel → StrutMassModel
  rigidBodyAboutAxis1SI : RigidBody 3
  axis1Component : Fin 3
  axis1AngularVelocityVector : AngularSpeedQuantity → Fin 3 → ℝ

/-! ## Figure/data readouts -/

/-- All metric and qualitative information read from the primary bitmap. -/
structure MatchesPrimaryFigure (setup : ThreeDiskMachinePart) : Prop where
  everyDiskIsShown :
    ∀ disk : DiskLabel, setup.figure.showsDisk disk = true
  everyStrutIsShown :
    ∀ strut : StrutLabel, setup.figure.showsStrut strut = true
  strutABEndpoints :
    setup.figure.strutEndpoints .AB = (.A, .B)
  strutBCEndpoints :
    setup.figure.strutEndpoints .BC = (.B, .C)
  strutCAEndpoints :
    setup.figure.strutEndpoints .CA = (.C, .A)
  printedMassA :
    setup.figure.printedDiskMassKilograms .A = 3 / 10
  printedMassB :
    setup.figure.printedDiskMassKilograms .B = 1 / 10
  printedMassC :
    setup.figure.printedDiskMassKilograms .C = 1 / 5
  physicalMassesMatchPrintedLabels :
    ∀ disk : DiskLabel,
      massInKilograms (setup.diskMass disk) =
        setup.figure.printedDiskMassKilograms disk
  printedLengthAB :
    setup.figure.printedStrutLengthMeters .AB = 1 / 2
  printedLengthBC :
    setup.figure.printedStrutLengthMeters .BC = 3 / 10
  printedLengthCA :
    setup.figure.printedStrutLengthMeters .CA = 2 / 5
  physicalLengthsMatchPrintedLabels :
    ∀ strut : StrutLabel,
      lengthInMeters (setup.strutLength strut) =
        setup.figure.printedStrutLengthMeters strut
  bothAxesAreShown :
    ∀ axis : AxisLabel, setup.figure.showsAxis axis = true
  axis1PassesThroughA :
    setup.figure.axisPassesThrough .axis1 .A = true
  axis2PassesThroughB :
    setup.figure.axisPassesThrough .axis2 .B = true
  axis2PassesThroughC :
    setup.figure.axisPassesThrough .axis2 .C = true
  axis1PerpendicularToFrame :
    setup.figure.axisOrientation .axis1 = .perpendicularToFigurePlane
  axis2LiesAlongBC :
    setup.figure.axisOrientation .axis2 = .inFigurePlaneAlongBC
  diskAOnAxis1 :
    lengthInMeters (setup.distanceFromAxis .axis1 .A) = 0
  diskBRadiusAboutAxis1IsAB :
    lengthInMeters (setup.distanceFromAxis .axis1 .B) =
      lengthInMeters (setup.strutLength .AB)
  diskCRadiusAboutAxis1IsCA :
    lengthInMeters (setup.distanceFromAxis .axis1 .C) =
      lengthInMeters (setup.strutLength .CA)
  diskBOnAxis2 :
    lengthInMeters (setup.distanceFromAxis .axis2 .B) = 0
  diskCOnAxis2 :
    lengthInMeters (setup.distanceFromAxis .axis2 .C) = 0

/-!
Problem-text information for the requested motion.  The point-mass model is
the standard interpretation of "small disks" when no disk radii are given;
the strut model records the explicit "lightweight" assumption.
-/
structure MatchesProblemData (setup : ThreeDiskMachinePart) : Prop where
  rotatesAboutAxis1 : setup.selectedAxis = .axis1
  angularSpeedIsFourRadiansPerSecond :
    angularSpeedInRadiansPerSecond setup.givenAngularSpeed = 4
  allDisksAreSmallPointMasses :
    ∀ disk : DiskLabel,
      setup.smallDiskModel disk = .pointMassAtCenter
  allStrutsHaveNegligibleMass :
    ∀ strut : StrutLabel,
      setup.strutMassModel strut = .negligible

/-! ## Governing rotational laws -/

/-!
The point-mass axial inertia sum and its connection to Physlib's rigid-body
mass distribution, inertia tensor, and rotational-energy definition.  These
are general physical laws for arbitrary angular speed and contain neither the
`0.456 J` derived energy nor the displayed `0.46 J` answer.
-/
structure SatisfiesThreeDiskRotationalLaws
    (setup : ThreeDiskMachinePart) : Prop where
  pointMassMomentOfInertiaAboutAxis1 :
    momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia .axis1) =
      massInKilograms (setup.diskMass .A) *
          lengthInMeters (setup.distanceFromAxis .axis1 .A) ^ 2 +
        massInKilograms (setup.diskMass .B) *
          lengthInMeters (setup.distanceFromAxis .axis1 .B) ^ 2 +
        massInKilograms (setup.diskMass .C) *
          lengthInMeters (setup.distanceFromAxis .axis1 .C) ^ 2
  rigidBodyMassIsDiskMassSum :
    setup.rigidBodyAboutAxis1SI.mass =
      massInKilograms (setup.diskMass .A) +
        massInKilograms (setup.diskMass .B) +
        massInKilograms (setup.diskMass .C)
  axis1TensorEntryMatchesScalarInertia :
    setup.rigidBodyAboutAxis1SI.inertiaTensor
        setup.axis1Component setup.axis1Component =
      momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia .axis1)
  angularVelocityIsAlongAxis1 :
    ∀ (angularSpeed : AngularSpeedQuantity) (component : Fin 3),
      setup.axis1AngularVelocityVector angularSpeed component =
        if component = setup.axis1Component then
          angularSpeedInRadiansPerSecond angularSpeed
        else 0
  rotationalEnergyUsesPhyslib :
    ∀ angularSpeed : AngularSpeedQuantity,
      energyInJoules
          (setup.rotationalKineticEnergy .axis1 angularSpeed) =
        setup.rigidBodyAboutAxis1SI.rotationalKineticEnergy
          (setup.axis1AngularVelocityVector angularSpeed)

/-! ## Derived physical quantities -/

/-- The three labeled point masses give `I₁ = 0.057 kg m²`. -/
lemma axis1MomentOfInertia_eq_57_over_1000
    (setup : ThreeDiskMachinePart)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesThreeDiskRotationalLaws setup) :
    momentOfInertiaInKilogramMetersSquared
        (setup.axialMomentOfInertia .axis1) = 57 / 1000 := by
  norm_num [_laws.pointMassMomentOfInertiaAboutAxis1,
    _figure.physicalMassesMatchPrintedLabels, _figure.printedMassA,
    _figure.printedMassB, _figure.printedMassC, _figure.diskAOnAxis1,
    _figure.diskBRadiusAboutAxis1IsAB, _figure.diskCRadiusAboutAxis1IsCA,
    _figure.physicalLengthsMatchPrintedLabels, _figure.printedLengthAB,
    _figure.printedLengthCA]

/-!
For angular velocity along the selected tensor axis, Physlib's tensor
contraction reduces to the scalar law `K = I ω² / 2`.
-/
lemma rotationalKineticEnergy_eq_half_inertia_mul_angularSpeed_sq
    (setup : ThreeDiskMachinePart)
    (_laws : SatisfiesThreeDiskRotationalLaws setup)
    (angularSpeed : AngularSpeedQuantity) :
    energyInJoules
        (setup.rotationalKineticEnergy .axis1 angularSpeed) =
      (1 / 2 : ℝ) *
        momentOfInertiaInKilogramMetersSquared
          (setup.axialMomentOfInertia .axis1) *
        angularSpeedInRadiansPerSecond angularSpeed ^ 2 := by
  rw [_laws.rotationalEnergyUsesPhyslib]
  simp only [RigidBody.rotationalKineticEnergy, dotProduct, Matrix.mulVec]
  simp_rw [_laws.angularVelocityIsAlongAxis1]
  simp [_laws.axis1TensorEntryMatchesScalarInertia]
  ring

/-- At `4 rad/s`, the exact point-mass-model energy is `0.456 J`. -/
lemma axis1KineticEnergyAtFour_eq_57_over_125
    (setup : ThreeDiskMachinePart)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesThreeDiskRotationalLaws setup) :
    energyInJoules
        (setup.rotationalKineticEnergy
          setup.selectedAxis setup.givenAngularSpeed) = 57 / 125 := by
  rw [_data.rotatesAboutAxis1]
  rw [rotationalKineticEnergy_eq_half_inertia_mul_angularSpeed_sq setup _laws]
  rw [axis1MomentOfInertia_eq_57_over_1000 setup _figure _data _laws]
  rw [_data.angularSpeedIsFourRadiansPerSecond]
  norm_num

/-! ## Multiple-choice metadata and final target -/

/-- Labels of the four energy choices displayed in the exercise. -/
inductive EnergyAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The numerical joule value printed beside each answer label. -/
def displayedEnergyJoules : EnergyAnswerChoice → ℝ
  | .A => 33 / 50
  | .B => 23 / 50
  | .C => 33 / 25
  | .D => 23 / 25

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : EnergyAnswerChoice := .B

/-- `displayed` is the nearest-hundredth rounding bin containing `exact`. -/
def RoundsToNearestHundredth (exact displayed : ℝ) : Prop :=
  displayed - 1 / 200 ≤ exact ∧ exact < displayed + 1 / 200

/-- A choice is at least as close to the exact energy as every other choice. -/
def IsClosestEnergyChoice
    (exactEnergyJoules : ℝ) (choice : EnergyAnswerChoice) : Prop :=
  ∀ other : EnergyAnswerChoice,
    |exactEnergyJoules - displayedEnergyJoules choice| ≤
      |exactEnergyJoules - displayedEnergyJoules other|

/-- A displayed answer is the unique closest energy choice. -/
def IsUniqueClosestEnergyChoice
    (exactEnergyJoules : ℝ) (choice : EnergyAnswerChoice) : Prop :=
  IsClosestEnergyChoice exactEnergyJoules choice ∧
    ∀ other : EnergyAnswerChoice,
      IsClosestEnergyChoice exactEnergyJoules other → other = choice

/-!
The exact model value is `0.456 J`, which rounds to the displayed `0.46 J`;
the latter is answer B and is uniquely closest among the four choices.
-/
theorem kineticEnergyAboutAxis1_is_answer_B
    (setup : ThreeDiskMachinePart)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesThreeDiskRotationalLaws setup) :
    energyInJoules
          (setup.rotationalKineticEnergy
            setup.selectedAxis setup.givenAngularSpeed) = 57 / 125 ∧
      RoundsToNearestHundredth
        (energyInJoules
          (setup.rotationalKineticEnergy
            setup.selectedAxis setup.givenAngularSpeed))
        (displayedEnergyJoules recordedAnswerChoice) ∧
      IsUniqueClosestEnergyChoice
        (energyInJoules
          (setup.rotationalKineticEnergy
            setup.selectedAxis setup.givenAngularSpeed))
        recordedAnswerChoice := by
  have hEnergy :=
    axis1KineticEnergyAtFour_eq_57_over_125 setup _figure _data _laws
  refine ⟨hEnergy, ?_, ?_⟩
  · rw [hEnergy]
    norm_num [RoundsToNearestHundredth, displayedEnergyJoules,
      recordedAnswerChoice]
  · rw [hEnergy]
    unfold IsUniqueClosestEnergyChoice IsClosestEnergyChoice
    constructor
    · intro other
      fin_cases other <;>
        norm_num [displayedEnergyJoules, recordedAnswerChoice]
    · intro other hOther
      fin_cases other
      · have h := hOther EnergyAnswerChoice.B
        norm_num [displayedEnergyJoules, recordedAnswerChoice] at h
      · rfl
      · have h := hOther EnergyAnswerChoice.B
        norm_num [displayedEnergyJoules, recordedAnswerChoice] at h
      · have h := hOther EnergyAnswerChoice.B
        norm_num [displayedEnergyJoules, recordedAnswerChoice] at h

end PhyXMiniProblems.ProblemPhyXMini0819
