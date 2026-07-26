import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0959

open Dimension

/-!
# Magnetic field of a moving electron at a moving proton

At the pictured instant, an electron is at `(0, 5.00 nm)` and moves left,
while a proton is at `(4.00 nm, 0)` and moves downward.  Both speeds are
`735 km/s`, so their paths are perpendicular.  The requested observable is
the magnetic field produced by the electron at the proton.

Physical positions, velocities, charges, speed, and vacuum permeability are
unit-independent `Dimensionful` quantities.  Real vectors and scalars occur
only as named coherent-SI readouts or as literal figure and answer data.
Physlib's spacetime-dependent `Electromagnetism.MagneticField` retains the
physical field role of the electron's field.

Assumption/target split:

* governing laws: the low-speed moving-point-charge magnetic-field law and
  the standard vacuum-permeability calibration;
* previous-part results: none;
* figure/data readouts: the particle identities and signs, their `x`- and
  `y`-axis positions, the `5.00 nm` and `4.00 nm` labels, the leftward and
  downward arrows, perpendicular paths, and the common `735 km/s` speed;
* current target conclusions: the exact into-page field, its magnitude
  rounded to `2.24 * 10^-4 T`, and unique selection of answer B.

No field value or answer choice is stored in the setup, figure, source-data
structure, permeability calibration, or moving-charge law.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Three-dimensional real vectors used only for coherent-unit readouts. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- The physical dimension `L T⁻¹` of velocity. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- Magnetic permeability has dimension `M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A unit-independent signed three-dimensional position vector. -/
abbrev PositionVectorQuantity : Type :=
  Dimensionful (WithDim L𝓭 SpatialVector)

/-- A unit-independent signed three-dimensional velocity vector. -/
abbrev VelocityVectorQuantity : Type :=
  Dimensionful (WithDim velocityDimension SpatialVector)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- Read a physical position vector in a selected coherent length unit. -/
def positionVectorReadout
    (unit : LengthUnit) (position : PositionVectorQuantity) : SpatialVector :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a physical position vector in coherent-SI metres. -/
def positionVectorInMeters (position : PositionVectorQuantity) : SpatialVector :=
  positionVectorReadout LengthUnit.meters position

/-- Read a physical position vector in nanometres, as labelled in the raster. -/
def positionVectorInNanometers
    (position : PositionVectorQuantity) : SpatialVector :=
  positionVectorReadout LengthUnit.nanometers position

/-- Read a physical velocity vector in coherent-SI metres per second. -/
def velocityVectorInMetersPerSecond
    (velocity : VelocityVectorQuantity) : SpatialVector :=
  (velocity UnitChoices.SI).val

/-- Read a signed charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a signed charge in Physlib elementary-charge units. -/
def chargeInElementaryCharges (charge : SignedChargeQuantity) : ℝ :=
  (charge ({UnitChoices.SI with
    charge := ChargeUnit.elementaryCharge} : UnitChoices)).val

/-- Read a speed in a coherent choice of length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read magnetic permeability in coherent-SI tesla-metres per ampere. -/
def permeabilityInTeslaMetersPerAmpere
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  ((permeability UnitChoices.SI).val : ℝ)

/-- Mathlib's coordinate cross product transported to Euclidean space. -/
def spatialCrossProduct
    (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-! ## Cartesian and primary-figure vocabulary -/

/-- The three coordinate axes, with `z` normal to the displayed page. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Standard positive unit vector along a coordinate axis. -/
def axisVector : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single (0 : Fin 3) 1
  | .y => EuclideanSpace.single (1 : Fin 3) 1
  | .z => EuclideanSpace.single (2 : Fin 3) 1

/-- The two particles explicitly named in the problem and raster. -/
inductive Particle where
  | electron
  | proton
  deriving DecidableEq, Fintype, Repr

/-- Charge-sign glyph drawn inside a particle marker. -/
inductive ChargeSignGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Fill colours visibly distinguishing the two particle markers. -/
inductive ParticleFillColor where
  | blue
  | red
  deriving DecidableEq, Repr

/-- Oriented Cartesian directions used by the two velocity arrows. -/
inductive AxisDirection where
  | positiveX
  | negativeX
  | positiveY
  | negativeY
  | positiveZ
  | negativeZ
  deriving DecidableEq, Fintype, Repr

/-- Coherent-SI unit vector associated with an oriented direction. -/
def directionVector : AxisDirection → SpatialVector
  | .positiveX => axisVector .x
  | .negativeX => -axisVector .x
  | .positiveY => axisVector .y
  | .negativeY => -axisVector .y
  | .positiveZ => axisVector .z
  | .negativeZ => -axisVector .z

/-- Literal content transcribed from the supplied raster `959.png`. -/
structure ElectronProtonFigure where
  axisShown : CoordinateAxis → Bool
  originOLabelShown : Bool
  particleShown : Particle → Bool
  particleTextLabel : Particle → String
  particleFillColor : Particle → ParticleFillColor
  chargeSignGlyph : Particle → ChargeSignGlyph
  particlePositionAxis : Particle → CoordinateAxis
  displayedOffsetInNanometers : Particle → ℝ
  velocityArrowShown : Particle → Bool
  velocityArrowIsGreen : Particle → Bool
  velocityArrowDirection : Particle → AxisDirection
  pathsAppearPerpendicular : Bool

/-!
Independent physical objects at the pictured instant.  In particular, the
electron's magnetic field is not defined from the displayed answer.
-/
structure MovingElectronProtonSetup where
  commonSpeed : DimSpeed
  charge : Particle → SignedChargeQuantity
  position : Particle → PositionVectorQuantity
  velocity : Particle → VelocityVectorQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  vacuumPermeability : MagneticPermeabilityQuantity
  electronMagneticField : Electromagnetism.MagneticField 3
  observationTime : Time
  figure : ElectronProtonFigure

/-- Displacement from the electron to the proton, read in metres. -/
def electronToProtonDisplacementInMeters
    (setup : MovingElectronProtonSetup) : SpatialVector :=
  positionVectorInMeters (setup.position .proton) -
    positionVectorInMeters (setup.position .electron)

/-- Interpret a coherent-SI metre vector as a Physlib spatial point. -/
def spacePointOfMeters (position : SpatialVector) : Space 3 :=
  ⟨position.ofLp⟩

/-- Electron-produced magnetic-field vector at the proton, in teslas. -/
def electronFieldAtProtonInTeslas
    (setup : MovingElectronProtonSetup) : SpatialVector :=
  setup.electronMagneticField setup.observationTime
    (spacePointOfMeters
      (positionVectorInMeters (setup.position .proton)))

/-- Magnitude of the electron-produced field at the proton, in teslas. -/
def electronFieldMagnitudeAtProtonInTeslas
    (setup : MovingElectronProtonSetup) : ℝ :=
  ‖electronFieldAtProtonInTeslas setup‖

/-! ## Problem data, primary-image evidence, and physical branch -/

/-- Written data and all literal/calibrated evidence from the primary image. -/
structure MatchesProblemStatementAndPrimaryFigure
    (setup : MovingElectronProtonSetup) : Prop where
  xAxisShown : setup.figure.axisShown .x = true
  yAxisShown : setup.figure.axisShown .y = true
  zAxisNotDrawn : setup.figure.axisShown .z = false
  originOLabelShown : setup.figure.originOLabelShown = true
  bothParticlesShown : ∀ particle,
    setup.figure.particleShown particle = true
  electronTextLabel : setup.figure.particleTextLabel .electron = "Electron"
  protonTextLabel : setup.figure.particleTextLabel .proton = "Proton"
  electronMarkerIsBlue :
    setup.figure.particleFillColor .electron = .blue
  protonMarkerIsRed :
    setup.figure.particleFillColor .proton = .red
  electronHasMinusGlyph : setup.figure.chargeSignGlyph .electron = .minus
  protonHasPlusGlyph : setup.figure.chargeSignGlyph .proton = .plus
  electronChargeIsMinusOneElementaryCharge :
    chargeInElementaryCharges (setup.charge .electron) = -1
  protonChargeIsPlusOneElementaryCharge :
    chargeInElementaryCharges (setup.charge .proton) = 1
  electronChargeInCoulombs :
    chargeInCoulombs (setup.charge .electron) = -(1.602176634e-19)
  protonChargeInCoulombs :
    chargeInCoulombs (setup.charge .proton) = 1.602176634e-19
  commonSpeedKilometersPerSecond :
    speedReadout LengthUnit.kilometers TimeUnit.seconds setup.commonSpeed = 735
  commonSpeedMetersPerSecond :
    speedReadout LengthUnit.meters TimeUnit.seconds setup.commonSpeed = 735000
  electronPositionAxisIsY :
    setup.figure.particlePositionAxis .electron = .y
  protonPositionAxisIsX :
    setup.figure.particlePositionAxis .proton = .x
  electronOffsetLabel :
    setup.figure.displayedOffsetInNanometers .electron = 5
  protonOffsetLabel :
    setup.figure.displayedOffsetInNanometers .proton = 4
  electronPositionInNanometers :
    positionVectorInNanometers (setup.position .electron) =
      5 • axisVector .y
  protonPositionInNanometers :
    positionVectorInNanometers (setup.position .proton) =
      4 • axisVector .x
  electronPositionFromOrigin :
    positionVectorInMeters (setup.position .electron) =
      (5 / 10 ^ 9 : ℝ) • axisVector .y
  protonPositionFromOrigin :
    positionVectorInMeters (setup.position .proton) =
      (4 / 10 ^ 9 : ℝ) • axisVector .x
  electronOffsetCalibratesPosition :
    setup.figure.displayedOffsetInNanometers .electron =
      ‖positionVectorInNanometers (setup.position .electron)‖
  protonOffsetCalibratesPosition :
    setup.figure.displayedOffsetInNanometers .proton =
      ‖positionVectorInNanometers (setup.position .proton)‖
  bothVelocityArrowsShown : ∀ particle,
    setup.figure.velocityArrowShown particle = true
  bothVelocityArrowsGreen : ∀ particle,
    setup.figure.velocityArrowIsGreen particle = true
  electronArrowPointsLeft :
    setup.figure.velocityArrowDirection .electron = .negativeX
  protonArrowPointsDown :
    setup.figure.velocityArrowDirection .proton = .negativeY
  electronVelocityIsLeftward :
    velocityVectorInMetersPerSecond (setup.velocity .electron) =
      735000 • directionVector .negativeX
  protonVelocityIsDownward :
    velocityVectorInMetersPerSecond (setup.velocity .proton) =
      735000 • directionVector .negativeY
  perpendicularPathsShown : setup.figure.pathsAppearPerpendicular = true
  velocityVectorsArePerpendicular :
    inner ℝ
      (velocityVectorInMetersPerSecond (setup.velocity .electron))
      (velocityVectorInMetersPerSecond (setup.velocity .proton)) = 0

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalMovingParticleParameters
    (setup : MovingElectronProtonSetup) : Prop where
  commonSpeedPositive :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds setup.commonSpeed
  electronChargeNegative : chargeInCoulombs (setup.charge .electron) < 0
  protonChargePositive : 0 < chargeInCoulombs (setup.charge .proton)
  electronVelocityNonzero :
    velocityVectorInMetersPerSecond (setup.velocity .electron) ≠ 0
  protonVelocityNonzero :
    velocityVectorInMetersPerSecond (setup.velocity .proton) ≠ 0
  particlesAreSeparated :
    0 < ‖electronToProtonDisplacementInMeters setup‖
  permeabilityPositive :
    0 < permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability

/-!
The dimensionful vacuum permeability agrees with Physlib's electromagnetic
system and has the standard SI value `4π * 10⁻⁷ T m/A`.
-/
structure UsesStandardVacuumPermeability
    (setup : MovingElectronProtonSetup) : Prop where
  agreesWithElectromagneticSystem :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      setup.electromagneticSystem.μ₀
  standardSIReadout :
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability =
      4 * Real.pi / 10 ^ 7

/-! ## Governing moving-charge magnetic-field law -/

/-!
Low-speed field of a moving point charge at the proton:

`B = μ₀ q /(4π |r|³) (v × r)`.

Here `r` points from the electron to the proton.  This is a governing law in
the independent physical quantities and contains no evaluated field or answer
choice.
-/
structure SatisfiesMovingPointChargeMagneticFieldLaw
    (setup : MovingElectronProtonSetup) : Prop where
  fieldAtProton :
    electronFieldAtProtonInTeslas setup =
      (permeabilityInTeslaMetersPerAmpere setup.vacuumPermeability *
          chargeInCoulombs (setup.charge .electron) /
          (4 * Real.pi * ‖electronToProtonDisplacementInMeters setup‖ ^ 3)) •
        spatialCrossProduct
          (velocityVectorInMetersPerSecond (setup.velocity .electron))
          (electronToProtonDisplacementInMeters setup)

/-! ## Derived field, direction, and displayed-answer target -/

/-- Exact positive field magnitude produced by the model, in teslas. -/
def exactModelFieldMagnitudeInTeslas : ℝ :=
  ((1 : ℝ) / 10 ^ 7) * 1.602176634e-19 * 735000 * (5 / 10 ^ 9) /
    (Real.sqrt 41 / 10 ^ 9) ^ 3

/-- A nonzero field vector points in a specified oriented axis direction. -/
def PointsInAxisDirection
    (field : SpatialVector) (direction : AxisDirection) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧
    field = magnitude • directionVector direction

/-!
The moving-charge law and pictured geometry give an into-page (`-z`) field
with the exact model magnitude above.
-/
lemma electronFieldAtProton_exact
    (setup : MovingElectronProtonSetup)
    (hData : MatchesProblemStatementAndPrimaryFigure setup)
    (hPhysical : HasPhysicalMovingParticleParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hMovingCharge : SatisfiesMovingPointChargeMagneticFieldLaw setup) :
    electronFieldAtProtonInTeslas setup =
      exactModelFieldMagnitudeInTeslas • directionVector .negativeZ := by
  have hNorm :
      ‖(4 / 10 ^ 9 : ℝ) • axisVector .x -
          (5 / 10 ^ 9 : ℝ) • axisVector .y‖ =
        Real.sqrt 41 / 10 ^ 9 := by
    rw [EuclideanSpace.norm_eq]
    simp [axisVector, Fin.sum_univ_succ]
    norm_num
  have hCross :
      spatialCrossProduct (735000 • directionVector .negativeX)
          ((4 / 10 ^ 9 : ℝ) • axisVector .x -
            (5 / 10 ^ 9 : ℝ) • axisVector .y) =
        (735000 * (5 / 10 ^ 9 : ℝ)) • axisVector .z := by
    ext i
    fin_cases i <;>
      simp [spatialCrossProduct, directionVector, axisVector, cross_apply]
  rw [hMovingCharge.fieldAtProton, hVacuum.standardSIReadout,
    hData.electronChargeInCoulombs, hData.electronVelocityIsLeftward]
  simp only [electronToProtonDisplacementInMeters,
    hData.protonPositionFromOrigin, hData.electronPositionFromOrigin]
  rw [hNorm, hCross]
  unfold exactModelFieldMagnitudeInTeslas directionVector
  rw [smul_smul]
  ext i
  fin_cases i <;> simp [axisVector]
  field_simp

/-- Labels of the four magnetic-field magnitudes printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-field magnitude in teslas displayed beside each choice. -/
def displayedMagneticFieldMagnitudeInTeslas : AnswerChoice → ℝ
  | .A => 112 / 10 ^ 6
  | .B => 224 / 10 ^ 6
  | .C => 224 / 10 ^ 5
  | .D => 336 / 10 ^ 6

/-- The answer label recorded by the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-! Rounding to the displayed `0.01 * 10⁻⁴ T` precision. -/
def RoundsToDisplayedPrecision (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 2000000

/-- A choice is strictly closer than every distinct displayed alternative. -/
def IsUniqueClosestDisplayedAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice, otherChoice ≠ choice →
    |actual - displayedMagneticFieldMagnitudeInTeslas choice| <
      |actual - displayedMagneticFieldMagnitudeInTeslas otherChoice|

/-!
Blueprint declaration `thm:physics:phyx_mini_0959:target`.

The electron's field at the proton points into the page.  Its magnitude is
approximately `2.242807 * 10⁻⁴ T`, which rounds to the displayed
`2.24 * 10⁻⁴ T` and uniquely selects answer B.
-/
theorem problem_phyx_mini_0959
    (setup : MovingElectronProtonSetup)
    (hData : MatchesProblemStatementAndPrimaryFigure setup)
    (hPhysical : HasPhysicalMovingParticleParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hMovingCharge : SatisfiesMovingPointChargeMagneticFieldLaw setup) :
    electronFieldMagnitudeAtProtonInTeslas setup =
        exactModelFieldMagnitudeInTeslas ∧
      PointsInAxisDirection
        (electronFieldAtProtonInTeslas setup) .negativeZ ∧
      RoundsToDisplayedPrecision
        (electronFieldMagnitudeAtProtonInTeslas setup)
        (displayedMagneticFieldMagnitudeInTeslas recordedAnswerChoice) ∧
      IsUniqueClosestDisplayedAnswer
        (electronFieldMagnitudeAtProtonInTeslas setup)
        recordedAnswerChoice := by
  have hField :=
    electronFieldAtProton_exact setup hData hPhysical hVacuum hMovingCharge
  have hExactPositive : 0 < exactModelFieldMagnitudeInTeslas := by
    unfold exactModelFieldMagnitudeInTeslas
    positivity
  have hMagnitude :
      electronFieldMagnitudeAtProtonInTeslas setup =
        exactModelFieldMagnitudeInTeslas := by
    rw [electronFieldMagnitudeAtProtonInTeslas, hField, norm_smul,
      Real.norm_eq_abs, abs_of_pos hExactPositive]
    simp [directionVector, axisVector]
  have hSqrtPositive : 0 < Real.sqrt 41 := Real.sqrt_pos.2 (by norm_num)
  have hSqrtNonnegative : 0 ≤ Real.sqrt 41 := hSqrtPositive.le
  have hSqrtSq : Real.sqrt 41 ^ 2 = 41 :=
    Real.sq_sqrt (by norm_num)
  have hSqrtCubed : Real.sqrt 41 ^ 3 = 41 * Real.sqrt 41 := by
    calc
      Real.sqrt 41 ^ 3 = Real.sqrt 41 ^ 2 * Real.sqrt 41 := by ring
      _ = 41 * Real.sqrt 41 := by rw [hSqrtSq]
  have hSqrtLower : (6403 : ℝ) / 1000 < Real.sqrt 41 := by
    nlinarith
  have hSqrtUpper : Real.sqrt 41 < (6404 : ℝ) / 1000 := by
    nlinarith
  have hExactFormula :
      exactModelFieldMagnitudeInTeslas =
        117759982599 / (82000000000000 * Real.sqrt 41) := by
    unfold exactModelFieldMagnitudeInTeslas
    rw [div_pow, hSqrtCubed]
    field_simp [ne_of_gt hSqrtPositive] <;> ring
  have hExactBounds :
      (2242 : ℝ) / 10 ^ 7 < exactModelFieldMagnitudeInTeslas ∧
        exactModelFieldMagnitudeInTeslas < (2243 : ℝ) / 10 ^ 7 := by
    rw [hExactFormula]
    constructor
    · rw [lt_div_iff₀ (mul_pos (by norm_num) hSqrtPositive)]
      nlinarith
    · rw [div_lt_iff₀ (mul_pos (by norm_num) hSqrtPositive)]
      nlinarith
  refine ⟨hMagnitude, ?_, ?_, ?_⟩
  · exact ⟨exactModelFieldMagnitudeInTeslas, hExactPositive, hField⟩
  · rw [hMagnitude]
    change
      |exactModelFieldMagnitudeInTeslas - 224 / 10 ^ 6| <
        (1 : ℝ) / 2000000
    rw [abs_lt]
    constructor <;> nlinarith [hExactBounds.1, hExactBounds.2]
  · rw [hMagnitude]
    unfold IsUniqueClosestDisplayedAnswer
    intro otherChoice hOther
    cases otherChoice with
    | A =>
        change
          |exactModelFieldMagnitudeInTeslas - 224 / 10 ^ 6| <
            |exactModelFieldMagnitudeInTeslas - 112 / 10 ^ 6|
        rw [abs_of_pos (by nlinarith [hExactBounds.1]),
          abs_of_pos (by nlinarith [hExactBounds.1])]
        nlinarith [hExactBounds.1, hExactBounds.2]
    | B => exact (hOther rfl).elim
    | C =>
        change
          |exactModelFieldMagnitudeInTeslas - 224 / 10 ^ 6| <
            |exactModelFieldMagnitudeInTeslas - 224 / 10 ^ 5|
        rw [abs_of_pos (by nlinarith [hExactBounds.1]),
          abs_of_neg (by nlinarith [hExactBounds.2])]
        nlinarith [hExactBounds.1, hExactBounds.2]
    | D =>
        change
          |exactModelFieldMagnitudeInTeslas - 224 / 10 ^ 6| <
            |exactModelFieldMagnitudeInTeslas - 336 / 10 ^ 6|
        rw [abs_of_pos (by nlinarith [hExactBounds.1]),
          abs_of_neg (by nlinarith [hExactBounds.2])]
        nlinarith [hExactBounds.1, hExactBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0959
