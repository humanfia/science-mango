import Mathlib
import Physlib.ClassicalMechanics.RigidBody.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0700

open Dimension

/-!
# Moment of inertia of a uniform circular disk

A circular lamina of total mass `M` and radius `R` rotates about the central
axis normal to its plane.  The supplied image decomposes the lamina into
narrow concentric rings: a ring at radius `r` has radial width `dr`, area
differential `dA = 2 * pi * r * dr`, and mass differential
`dm = (M / A) * dA`.

Mass, length, area, surface density, and moment of inertia are represented by
unit-independent Physlib quantities.  Real numbers occur only as coherent-SI
readouts and as the scalar radial variable used in the annular integral.
Physlib's `RigidBody` supplies the mass functional and inertia tensor; the
dimensionful scalar observable below is linked to their SI readouts by a
separate bridge hypothesis.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Physical dimension of area. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- Physical dimension of surface mass density. -/
def surfaceMassDensityDimension : Dimension := M𝓭 * L𝓭⁻¹ * L𝓭⁻¹

/-- Physical dimension of a moment of inertia, mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type := Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative, unit-independent surface mass density. -/
abbrev SurfaceMassDensityQuantity : Type :=
  Dimensionful (WithDim surfaceMassDensityDimension NNReal)

/-- A nonnegative physical moment of inertia about a specified axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Coherent-SI readout of any nonnegative dimensionful scalar quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Square-meter readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  nonnegativeSIReadout area

/-- Kilogram-per-square-meter readout of a surface mass density. -/
def surfaceMassDensityInKilogramsPerSquareMeter
    (density : SurfaceMassDensityQuantity) : ℝ :=
  nonnegativeSIReadout density

/-- Kilogram-meter-squared readout of a physical moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-! ## Disk geometry and primary-figure vocabulary -/

/-- The coordinate axes labelled in the supplied image. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index used by Physlib's three-dimensional inertia tensor. -/
def coordinateIndex : CoordinateAxis → Fin 3
  | .x => 0
  | .y => 1
  | .z => 2

/-- Coordinate planes distinguished by the three labelled axes. -/
inductive CoordinatePlane where
  | xy
  | yz
  | xz
  deriving DecidableEq, Repr

/-- Shape of the rotating body in the idealized model. -/
inductive BodyShape where
  | circularDisk
  deriving DecidableEq, Repr

/-- Mass-distribution model stated by the annular construction. -/
inductive DiskMassDistribution where
  | uniformSurfaceDensity
  deriving DecidableEq, Repr

/-- Geometry of the axis about which the requested inertia is taken. -/
inductive RotationAxisGeometry where
  | throughCenterPerpendicularToDiskPlane
  deriving DecidableEq, Repr

/-- Qualitative sense of either curved rotation arrow in the image. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Fintype, Repr

/-- Individually visible objects and annotations in image `700.png`. -/
inductive FigureFeature where
  | circularDisk
  | centerMarker
  | shadedNarrowRing
  | centralRotationAxis
  | clockwiseRotationArrow
  | counterclockwiseRotationArrow
  | ringMassFormula
  | ringAreaFormula
  deriving DecidableEq, Fintype, Repr

/-- Literal coordinate-axis labels printed in the image. -/
inductive FigureAxisLabel where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic quantity labels printed in the image. -/
inductive FigureQuantityLabel where
  | totalRadiusR
  | ringRadiusR
  | ringWidthDr
  | ringAreaDA
  | ringMassDm
  | totalMassM
  | diskAreaA
  deriving DecidableEq, Fintype, Repr

/-- Structured transcription of the primary raster's qualitative content. -/
structure CircularDiskFigure where
  showsFeature : FigureFeature → Bool
  showsAxisLabel : FigureAxisLabel → Bool
  showsQuantityLabel : FigureQuantityLabel → Bool
  depictedRotationAxis : CoordinateAxis
  axesIntersectAtDiskCenter : Bool
  shadedRingIsConcentricWithDisk : Bool
  rotationArrowShown : RotationSense → Bool
  containsNumericalParameterReadout : Bool

/-!
Independent physical quantities and scalar annular readouts for the disk.
The requested inertia is an observable constrained by the governing laws
below; it is not defined from the recorded answer.

`annularAreaRateSI r` represents `dA / dr` in square meters per meter, and
`annularMassRateSI r` represents `dm / dr` in kilograms per meter, at a radius
whose scalar argument is measured in meters.
-/
structure CircularDiskSetup where
  rigidBody : RigidBody 3
  bodyShape : BodyShape
  massDistribution : DiskMassDistribution
  diskPlane : CoordinatePlane
  rotationAxis : CoordinateAxis
  rotationAxisGeometry : RotationAxisGeometry
  totalMass : MassQuantity
  outerRadius : LengthQuantity
  diskArea : AreaQuantity
  surfaceMassDensity : SurfaceMassDensityQuantity
  momentOfInertiaAboutRotationAxis : MomentOfInertiaQuantity
  annularAreaRateSI : ℝ → ℝ
  annularMassRateSI : ℝ → ℝ
  figure : CircularDiskFigure

/-! ## Scenario, figure evidence, and governing laws -/

/-- The prose and axis geometry of the uniform disk problem. -/
structure MatchesCircularDiskScenario (setup : CircularDiskSetup) : Prop where
  bodyIsCircularDisk : setup.bodyShape = .circularDisk
  massIsUniformlySpreadOverArea :
    setup.massDistribution = .uniformSurfaceDensity
  diskLiesInXZPlane : setup.diskPlane = .xz
  rotationAxisIsY : setup.rotationAxis = .y
  requestedAxisPassesThroughCenterAndIsNormal :
    setup.rotationAxisGeometry = .throughCenterPerpendicularToDiskPlane

/-!
Literal evidence transcribed from the supplied raster.  It records the
`x`, `y`, `z`, `R`, `r`, `dr`, `dA`, `dm`, `M`, and `A` labels and the two
annular formulas, but supplies no numerical value for `M`, `R`, or the
requested moment of inertia.
-/
structure MatchesPrimaryDiskFigure (setup : CircularDiskSetup) : Prop where
  everyFeatureShown : ∀ feature, setup.figure.showsFeature feature = true
  everyAxisLabelShown : ∀ label, setup.figure.showsAxisLabel label = true
  everyQuantityLabelShown : ∀ label, setup.figure.showsQuantityLabel label = true
  displayedAxisIsY : setup.figure.depictedRotationAxis = .y
  axesMeetAtCenter : setup.figure.axesIntersectAtDiskCenter = true
  ringIsConcentric : setup.figure.shadedRingIsConcentricWithDisk = true
  bothRotationSensesShown : ∀ sense, setup.figure.rotationArrowShown sense = true
  noNumericalParameterReadout :
    setup.figure.containsNumericalParameterReadout = false

/-- Positivity and nondegeneracy conditions for the physical disk. -/
structure HasPhysicalDiskParameters (setup : CircularDiskSetup) : Prop where
  totalMassPositive : 0 < massInKilograms setup.totalMass
  outerRadiusPositive : 0 < lengthInMeters setup.outerRadius
  diskAreaPositive : 0 < areaInSquareMeters setup.diskArea
  surfaceMassDensityPositive :
    0 < surfaceMassDensityInKilogramsPerSquareMeter setup.surfaceMassDensity
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutRotationAxis

/-!
Bridge from the unit-independent scalar observables to Physlib's mass
functional and diagonal inertia-tensor component.  These equalities identify
the modeled quantities but do not prescribe their values in terms of `M` and
`R`.
-/
structure MatchesPhyslibRigidBodyReadouts (setup : CircularDiskSetup) : Prop where
  rigidBodyMassAgrees :
    setup.rigidBody.mass = massInKilograms setup.totalMass
  axialTensorComponentAgrees :
    setup.rigidBody.inertiaTensor
        (coordinateIndex setup.rotationAxis)
        (coordinateIndex setup.rotationAxis) =
      momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutRotationAxis

/-- The closed radial interval occupied by the disk, in meter readouts. -/
def radialDomainMeters (setup : CircularDiskSetup) : Set ℝ :=
  Set.Icc 0 (lengthInMeters setup.outerRadius)

/-!
Uniform-lamina and differential-annulus laws shown in the figure:

* `A = pi * R^2`;
* constant surface density is `M / A`;
* `dA / dr = 2 * pi * r`;
* `dm / dr = (M / A) * (dA / dr)`.

These are governing geometric and mass-distribution relations, not the
requested closed form for the moment of inertia.
-/
structure SatisfiesUniformAnnularMassLaws (setup : CircularDiskSetup) : Prop where
  diskAreaFormula :
    areaInSquareMeters setup.diskArea =
      Real.pi * lengthInMeters setup.outerRadius ^ 2
  uniformSurfaceDensityFormula :
    surfaceMassDensityInKilogramsPerSquareMeter setup.surfaceMassDensity =
      massInKilograms setup.totalMass / areaInSquareMeters setup.diskArea
  annularAreaDifferential : ∀ r ∈ radialDomainMeters setup,
    setup.annularAreaRateSI r = 2 * Real.pi * r
  annularMassDifferential : ∀ r ∈ radialDomainMeters setup,
    setup.annularMassRateSI r =
      surfaceMassDensityInKilogramsPerSquareMeter setup.surfaceMassDensity *
        setup.annularAreaRateSI r

/-!
General axial moment-of-inertia law `I = integral r^2 dm`, specialized only
to the annular radial decomposition.  The integrand remains independent of
the disk-specific evaluation `I = M R^2 / 2`.
-/
structure SatisfiesAnnularMomentOfInertiaLaw
    (setup : CircularDiskSetup) : Prop where
  inertiaIsRadialSecondMoment :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutRotationAxis =
      ∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius,
        r ^ 2 * setup.annularMassRateSI r

/-! ## Displayed alternatives and formal target -/

/-- Labels of the four alternatives printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Scalar expression printed beside each answer label after substituting
kilogram and meter readouts for `M` and `R`.  Choice D deliberately retains
the source's dimensionally inconsistent first power of `R`.
-/
def displayedAnswerExpression
    (choice : AnswerChoice) (massKilograms radiusMeters : ℝ) : ℝ :=
  match choice with
  | .A => (2 / 3 : ℝ) * massKilograms * radiusMeters ^ 2
  | .B => (1 / 3 : ℝ) * massKilograms * radiusMeters ^ 2
  | .C => (1 / 2 : ℝ) * massKilograms * radiusMeters ^ 2
  | .D => (1 / 2 : ℝ) * massKilograms * radiusMeters

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A displayed choice agrees with the disk's SI moment-of-inertia readout. -/
def MatchesDisplayedAnswer
    (setup : CircularDiskSetup) (choice : AnswerChoice) : Prop :=
  momentOfInertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutRotationAxis =
    displayedAnswerExpression choice
      (massInKilograms setup.totalMass)
      (lengthInMeters setup.outerRadius)

/-!
The uniform annular mass law and `I = integral r^2 dm` give

`I = (1 / 2) * M * R^2`,

so the displayed expression labelled C is the correct one.  The closed form
occurs only in this conclusion, not in any scenario, figure, bridge, or
governing-law premise.

Blueprint: `thm:physics:phyx_mini_0700:target`.
-/
theorem problem_phyx_mini_0700
    (setup : CircularDiskSetup)
    (_scenario : MatchesCircularDiskScenario setup)
    (_figure : MatchesPrimaryDiskFigure setup)
    (_physical : HasPhysicalDiskParameters setup)
    (_physlib : MatchesPhyslibRigidBodyReadouts setup)
    (_uniform : SatisfiesUniformAnnularMassLaws setup)
    (_inertiaLaw : SatisfiesAnnularMomentOfInertiaLaw setup) :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutRotationAxis =
        (1 / 2 : ℝ) * massInKilograms setup.totalMass *
          lengthInMeters setup.outerRadius ^ 2 ∧
      MatchesDisplayedAnswer setup recordedAnswerChoice := by
  have hRadiusNonnegative :
      0 ≤ lengthInMeters setup.outerRadius :=
    le_of_lt _physical.outerRadiusPositive
  have hIntegrandIntegral :
      (∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius,
          r ^ 2 * setup.annularMassRateSI r) =
        (massInKilograms setup.totalMass /
            areaInSquareMeters setup.diskArea *
            (2 * Real.pi)) *
          ∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius, r ^ 3 := by
    calc
      (∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius,
          r ^ 2 * setup.annularMassRateSI r) =
          ∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius,
            (massInKilograms setup.totalMass /
                areaInSquareMeters setup.diskArea *
                (2 * Real.pi)) * r ^ 3 := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hrDomain : r ∈ radialDomainMeters setup := by
          simpa only [radialDomainMeters, Set.uIcc_of_le hRadiusNonnegative] using hr
        change r ^ 2 * setup.annularMassRateSI r =
          (massInKilograms setup.totalMass /
              areaInSquareMeters setup.diskArea *
              (2 * Real.pi)) * r ^ 3
        rw [_uniform.annularMassDifferential r hrDomain,
          _uniform.annularAreaDifferential r hrDomain,
          _uniform.uniformSurfaceDensityFormula]
        ring
      _ = (massInKilograms setup.totalMass /
            areaInSquareMeters setup.diskArea *
            (2 * Real.pi)) *
          ∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius, r ^ 3 := by
        rw [intervalIntegral.integral_const_mul]
  have hPowerIntegral :
      (∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius, r ^ 3) =
        lengthInMeters setup.outerRadius ^ 4 / 4 := by
    convert
      (integral_pow (a := (0 : ℝ))
        (b := lengthInMeters setup.outerRadius) 3) using 1
    norm_num
  have hClosedForm :
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutRotationAxis =
        (1 / 2 : ℝ) * massInKilograms setup.totalMass *
          lengthInMeters setup.outerRadius ^ 2 := by
    calc
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutRotationAxis =
          ∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius,
            r ^ 2 * setup.annularMassRateSI r :=
        _inertiaLaw.inertiaIsRadialSecondMoment
      _ = (massInKilograms setup.totalMass /
            areaInSquareMeters setup.diskArea *
            (2 * Real.pi)) *
          ∫ r in (0 : ℝ)..lengthInMeters setup.outerRadius, r ^ 3 :=
        hIntegrandIntegral
      _ = (massInKilograms setup.totalMass /
            areaInSquareMeters setup.diskArea *
            (2 * Real.pi)) *
          (lengthInMeters setup.outerRadius ^ 4 / 4) := by
        rw [hPowerIntegral]
      _ = (1 / 2 : ℝ) * massInKilograms setup.totalMass *
          lengthInMeters setup.outerRadius ^ 2 := by
        rw [_uniform.diskAreaFormula]
        field_simp [Real.pi_ne_zero,
          ne_of_gt _physical.outerRadiusPositive]
        ring
  constructor
  · exact hClosedForm
  · simpa [MatchesDisplayedAnswer, recordedAnswerChoice,
      displayedAnswerExpression] using hClosedForm

end PhyXMiniProblems.ProblemPhyXMini0700
