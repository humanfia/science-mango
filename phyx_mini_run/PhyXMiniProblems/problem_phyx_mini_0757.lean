import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0757

open Dimension

/-!
# Mass of a disk in a suspended four-disk system

Four disks `A`, `B`, `C`, and `D` hang vertically in that order. A long top
cord passes over a frictionless pulley, is attached to a wall at one end, and
supports disk `A` at the other. Three shorter cords join the adjacent disk
pairs and carry the labelled tensions `T₁`, `T₂`, and `T₃`.

Masses, acceleration magnitudes, and force magnitudes are represented by
unit-independent Physlib quantities. Real numbers occur only as explicit
coherent-unit readouts and as values printed in the answer choices. In
particular, the mass of disk `C` is an independent field of the setup: it is
not defined from the recorded answer.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- The physical dimension `L T⁻²` of an acceleration magnitude. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of a force magnitude. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read force in the coherent unit induced by selected base units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  forceReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-! ## Disk, cord, and primary-figure vocabulary -/

/-- The four disks, named from top to bottom as in the supplied image. -/
inductive DiskLabel where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The three short cords whose tensions are labelled in the image. -/
inductive ShortCordLabel where
  | t1
  | t2
  | t3
  deriving DecidableEq, Fintype, Repr

/-- All tension-carrying cord segments, including the long top cord. -/
inductive CordSegment where
  | top
  | t1
  | t2
  | t3
  deriving DecidableEq, Fintype, Repr

/-- Physical objects visible in the supplied raster. -/
inductive FigureObject where
  | wall
  | pulley
  | topCord
  | diskA
  | diskB
  | diskC
  | diskD
  | shortCordT1
  | shortCordT2
  | shortCordT3
  deriving DecidableEq, Fintype, Repr

/-- Literal disk and tension labels visible in the supplied raster. -/
inductive FigureTextLabel where
  | diskA
  | diskB
  | diskC
  | diskD
  | tensionT1
  | tensionT2
  | tensionT3
  deriving DecidableEq, Fintype, Repr

/-- The motion state required for the force-balance model. -/
inductive SuspensionState where
  | heldAtRest
  | accelerating
  deriving DecidableEq, Repr

/-- Regard a labelled short cord as one of the system's cord segments. -/
def shortCordSegment : ShortCordLabel → CordSegment
  | .t1 => .t1
  | .t2 => .t2
  | .t3 => .t3

/-- Upper endpoint of each short cord, as read from the figure. -/
def expectedUpperDisk : ShortCordLabel → DiskLabel
  | .t1 => .A
  | .t2 => .B
  | .t3 => .C

/-- Lower endpoint of each short cord, as read from the figure. -/
def expectedLowerDisk : ShortCordLabel → DiskLabel
  | .t1 => .B
  | .t2 => .C
  | .t3 => .D

/-- Cord segment immediately above each disk. -/
def upperCord : DiskLabel → CordSegment
  | .A => .top
  | .B => .t1
  | .C => .t2
  | .D => .t3

/-- Cord segment immediately below a disk, if one exists. -/
def lowerCord : DiskLabel → Option CordSegment
  | .A => some .t1
  | .B => some .t2
  | .C => some .t3
  | .D => none

/-!
Typed evidence transcribed from image `757.png`. The raster records the
vertical order, cord incidence, and symbolic labels, but does not display a
numerical mass for disk `C`.
-/
structure SuppliedFourDiskFigure where
  showsObject : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  topToBottomIndex : DiskLabel → Fin 4
  shortCordUpperEndpoint : ShortCordLabel → DiskLabel
  shortCordLowerEndpoint : ShortCordLabel → DiskLabel
  topCordAttachedToWall : Bool
  topCordPassesOverPulley : Bool
  topCordSupportsDiskA : Bool
  disksAlignedVertically : Bool
  containsNumericalMassForDiskC : Bool

/-!
Independent physical quantities in the four-disk system. Disk weights and
cord tensions are fields rather than definitions made from the target mass.
-/
structure FourDiskPulleySetup where
  diskMass : DiskLabel → MassQuantity
  diskWeight : DiskLabel → ForceQuantity
  cordTension : CordSegment → ForceQuantity
  gravitationalAcceleration : AccelerationQuantity
  wallPullForce : ForceQuantity
  suspensionState : SuspensionState
  pulleyFrictionless : Bool
  figure : SuppliedFourDiskFigure

/-! ## Scenario, primary-image facts, numerical data, and governing laws -/

/-- Qualitative conditions stated or implicit in the suspended arrangement. -/
structure MatchesWrittenScenario (setup : FourDiskPulleySetup) : Prop where
  systemHeldAtRest : setup.suspensionState = .heldAtRest
  frictionlessPulley : setup.pulleyFrictionless = true

/-- Geometry and symbolic labels read from the primary image. -/
structure MatchesSuppliedFigure (setup : FourDiskPulleySetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyTextLabelShown : ∀ label, setup.figure.showsTextLabel label = true
  diskAIsTop : setup.figure.topToBottomIndex .A = 0
  diskBIsSecond : setup.figure.topToBottomIndex .B = 1
  diskCIsThird : setup.figure.topToBottomIndex .C = 2
  diskDIsBottom : setup.figure.topToBottomIndex .D = 3
  shortCordUpperEndpoints :
    ∀ cord, setup.figure.shortCordUpperEndpoint cord = expectedUpperDisk cord
  shortCordLowerEndpoints :
    ∀ cord, setup.figure.shortCordLowerEndpoint cord = expectedLowerDisk cord
  topCordAttachedToWall : setup.figure.topCordAttachedToWall = true
  topCordPassesOverPulley : setup.figure.topCordPassesOverPulley = true
  topCordSupportsDiskA : setup.figure.topCordSupportsDiskA = true
  disksAreVertical : setup.figure.disksAlignedVertically = true
  figureDoesNotContainTargetMass :
    setup.figure.containsNumericalMassForDiskC = false

/-!
Force magnitudes printed in the problem prose. The decimal values are
represented exactly: `58.8 = 294/5` and `9.8 = 49/5`.
-/
structure MatchesProblemForceReadouts (setup : FourDiskPulleySetup) : Prop where
  wallPullIs98Newtons : forceInNewtons setup.wallPullForce = 98
  tensionT1Is58Point8Newtons :
    forceInNewtons (setup.cordTension .t1) = 294 / 5
  tensionT2Is49Newtons :
    forceInNewtons (setup.cordTension .t2) = 49
  tensionT3Is9Point8Newtons :
    forceInNewtons (setup.cordTension .t3) = 49 / 5

/-!
The standard near-Earth gravitational calibration implicit in the recorded
textbook answer. It is separated from values explicitly printed in the
problem.
-/
structure UsesStandardNearEarthGravity (setup : FourDiskPulleySetup) : Prop where
  gravitationalAccelerationIs9Point8 :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 49 / 5

/-- Positivity conditions selecting a nondegenerate physical suspension. -/
structure HasPhysicalParameters (setup : FourDiskPulleySetup) : Prop where
  everyDiskMassPositive :
    ∀ disk, 0 < massInKilograms (setup.diskMass disk)
  everyDiskWeightPositive :
    ∀ disk, 0 < forceInNewtons (setup.diskWeight disk)
  everyCordTensionPositive :
    ∀ cord, 0 < forceInNewtons (setup.cordTension cord)
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  wallPullPositive : 0 < forceInNewtons setup.wallPullForce

/--
Read the force carried by the cord below a disk; the bottom disk has no lower
cord and therefore contributes zero lower-cord force to its balance equation.
-/
def lowerTensionReadout
    (setup : FourDiskPulleySetup)
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (disk : DiskLabel) : ℝ :=
  match lowerCord disk with
  | none => 0
  | some cord =>
      forceReadout massUnit lengthUnit timeUnit (setup.cordTension cord)

/-!
The governing ideal-cord, weight, and static-equilibrium laws. The final mass
of disk `C` is not a field of this structure. Instead, its value must be
derived by applying the generic balance equation to disk `C` together with
the independent `T₂`, `T₃`, and gravity readouts.
-/
structure SatisfiesSuspendedDiskStaticsLaws
    (setup : FourDiskPulleySetup) : Prop where
  topCordTransmitsWallPull :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit
          (setup.cordTension .top) =
        forceReadout massUnit lengthUnit timeUnit setup.wallPullForce
  weightFromMassAndGravity :
    ∀ (disk : DiskLabel) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit (setup.diskWeight disk) =
        massReadout massUnit (setup.diskMass disk) *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration
  verticalStaticEquilibrium :
    ∀ (disk : DiskLabel) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit
          (setup.cordTension (upperCord disk)) =
        forceReadout massUnit lengthUnit timeUnit (setup.diskWeight disk) +
          lowerTensionReadout setup massUnit lengthUnit timeUnit disk

/-! ## Answer choices and current target -/

/-- Labels of the four mass alternatives printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Mass in kilograms printed beside each answer label. -/
def displayedMassInKilograms : AnswerChoice → ℝ
  | .A => 1
  | .B => 2
  | .C => 4
  | .D => 5

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice is the unique displayed mass agreeing with disk `C`. -/
def IsUniqueMatchingDisplayedMass
    (setup : FourDiskPulleySetup) (choice : AnswerChoice) : Prop :=
  massInKilograms (setup.diskMass .C) = displayedMassInKilograms choice ∧
    ∀ other : AnswerChoice,
      massInKilograms (setup.diskMass .C) = displayedMassInKilograms other →
        other = choice

/-!
For disk `C`, static equilibrium gives `T₂ = m_C g + T₃`. With
`T₂ = 49 N`, `T₃ = 9.8 N`, and `g = 9.8 m/s²`, its mass is exactly `4 kg`,
the value displayed by choice C.

This formalizes `thm:physics:phyx_mini_0757:target`.
-/
theorem problem_phyx_mini_0757
    (setup : FourDiskPulleySetup)
    (hScenario : MatchesWrittenScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemForceReadouts setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesSuspendedDiskStaticsLaws setup) :
    massInKilograms (setup.diskMass .C) = 4 ∧
      IsUniqueMatchingDisplayedMass setup .C := by
  have hWeight :=
    hLaws.weightFromMassAndGravity .C MassUnit.kilograms
      LengthUnit.meters TimeUnit.seconds
  have hBalance :=
    hLaws.verticalStaticEquilibrium .C MassUnit.kilograms
      LengthUnit.meters TimeUnit.seconds
  have hMass : massInKilograms (setup.diskMass .C) = 4 := by
    have hT2 := hReadouts.tensionT2Is49Newtons
    have hT3 := hReadouts.tensionT3Is9Point8Newtons
    have hG := hGravity.gravitationalAccelerationIs9Point8
    unfold forceInNewtons at hT2 hT3
    unfold accelerationInMetersPerSecondSquared at hG
    unfold massInKilograms
    simp only [upperCord, lowerTensionReadout, lowerCord] at hBalance
    rw [hT2, hT3] at hBalance
    rw [hWeight, hG] at hBalance
    norm_num at hBalance ⊢
    linarith
  refine ⟨hMass, hMass, ?_⟩
  intro other hOther
  rw [hMass] at hOther
  cases other <;> norm_num [displayedMassInKilograms] at hOther
  rfl

end PhyXMiniProblems.ProblemPhyXMini0757
