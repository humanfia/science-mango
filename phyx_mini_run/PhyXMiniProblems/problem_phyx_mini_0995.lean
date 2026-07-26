import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0995

open Dimension

/-!
# Electric field on the axis of a uniformly charged conducting ring

The primary image shows a conducting ring of radius `a`, centered at `O`,
carrying total charge `Q`.  The observation point `P` lies a distance `x` from
`O` on the positive `x`-axis.  A highlighted ring element carries charge `dQ`
and arc length `ds`; its displacement to `P` is labelled
`r = √(x² + a²)`.  The element field is resolved into the displayed
components `dEₓ` and `dEᵧ`.

Basic charge and length parameters are unit-independent Physlib quantities.
Real numbers below are used only for coherent-SI readouts, angular parameters,
figure text, and components of Physlib's three-dimensional electric field.

Assumption/target split:

* governing laws: uniform angular charge and arc-length densities,
  differential Coulomb's law, and linear superposition by an angular integral;
* previous-part results: none;
* figure/data readouts: all printed point, axis, scalar, vector, and angle
  labels; the ring's `y-z` plane; `P` on the positive `x`-axis; and the
  displayed source-to-`P` distance formula;
* current target conclusion: the field at `P` equals
  `k Q x / (x² + a²)^(3/2)` in the positive `x` direction, i.e. answer B.

The closed-form field is not stored in the setup and does not occur in any
premise structure.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-!
An angular charge density has charge dimension because radians are
dimensionless.  Its SI readout has the role coulombs per radian.
-/
abbrev AngularChargeDensityQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- Read a signed charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read angular charge density in coherent-SI coulombs per radian. -/
def angularChargeDensityInCoulombsPerRadian
    (density : AngularChargeDensityQuantity) : ℝ :=
  (density UnitChoices.SI).val

/-! ## Literal vocabulary of the primary image -/

/-- Coordinate axes explicitly drawn in the supplied raster. -/
inductive FigureAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Named points or highlighted source elements in the supplied raster. -/
inductive FigurePoint where
  | O
  | P
  | chargeElement
  deriving DecidableEq, Fintype, Repr

/-- Scalar or differential labels printed in the supplied raster. -/
inductive FigureScalarLabel where
  | totalChargeQ
  | radiusA
  | axialDistanceX
  | arcElementDs
  | chargeElementDq
  deriving DecidableEq, Fintype, Repr

/-- Vector and vector-component labels printed in the supplied raster. -/
inductive FigureVectorLabel where
  | sourceDisplacementR
  | elementFieldDE
  | axialComponentDEx
  | transverseComponentDEy
  deriving DecidableEq, Fintype, Repr

/-- Angle labels printed near the source line and field-component triangle. -/
inductive FigureAngleLabel where
  | alpha
  | theta
  deriving DecidableEq, Fintype, Repr

/-- Other geometric features visible in image `995.png`. -/
inductive FigureFeature where
  | conductingRing
  | highlightedArcElement
  | highlightedChargeElement
  | dashedSourceToPLine
  | rightAngleAtCenter
  | fieldComponentTriangle
  deriving DecidableEq, Fintype, Repr

/-- Literal text expected beside each drawn coordinate axis. -/
def expectedAxisLabel : FigureAxis → String
  | .x => "x"
  | .y => "y"

/-- Literal text expected beside each named point or element. -/
def expectedPointLabel : FigurePoint → String
  | .O => "O"
  | .P => "P"
  | .chargeElement => "dQ"

/-- Literal scalar/differential text transcribed from the image. -/
def expectedScalarLabel : FigureScalarLabel → String
  | .totalChargeQ => "Q"
  | .radiusA => "a"
  | .axialDistanceX => "x"
  | .arcElementDs => "ds"
  | .chargeElementDq => "dQ"

/-- Literal vector text transcribed from the image. -/
def expectedVectorLabel : FigureVectorLabel → String
  | .sourceDisplacementR => "r"
  | .elementFieldDE => "dE"
  | .axialComponentDEx => "dEₓ"
  | .transverseComponentDEy => "dEᵧ"

/-- Literal Greek angle text transcribed from the image. -/
def expectedAngleLabel : FigureAngleLabel → String
  | .alpha => "α"
  | .theta => "θ"

/-!
Presentation data and physical label calibrations read from the primary
image.  The angle values describe the one highlighted element only; no
unwarranted equality between the visibly distinct `α` and `θ` marks is made.
-/
structure ChargedRingAxisFigure where
  axisShown : FigureAxis → Bool
  printedAxisLabel : FigureAxis → String
  pointShown : FigurePoint → Bool
  printedPointLabel : FigurePoint → String
  scalarLabelShown : FigureScalarLabel → Bool
  printedScalarLabel : FigureScalarLabel → String
  vectorArrowShown : FigureVectorLabel → Bool
  printedVectorLabel : FigureVectorLabel → String
  angleMarkShown : FigureAngleLabel → Bool
  printedAngleLabel : FigureAngleLabel → String
  featureShown : FigureFeature → Bool
  printedSourceDistanceFormula : String
  radiusLabelQuantity : LengthQuantity
  axialDistanceLabelQuantity : LengthQuantity
  totalChargeLabelQuantity : SignedChargeQuantity
  depictedAlphaRadians : ℝ
  depictedThetaRadians : ℝ

/-! ## Charged ring and independent electric-field setup -/

/-!
The source curve is parametrized by a dimensionless angle in radians.  The
two density fields represent the figure's differential elements through
`dQ = (dQ/dφ) dφ` and `ds = (ds/dφ) dφ`.
-/
structure ChargedRingSource where
  center : Space 3
  radius : LengthQuantity
  totalCharge : SignedChargeQuantity
  modeledAsConducting : Bool
  pointAtAngle : ℝ → Space 3
  chargePerRadian : ℝ → AngularChargeDensityQuantity
  arcLengthPerRadian : ℝ → LengthQuantity

/-!
The electric field and its differential angular contributions are primitive
observables.  Their relation is imposed later by Coulomb and superposition
laws; neither is defined from the requested answer.
-/
structure ChargedRingAxisSetup where
  ring : ChargedRingSource
  observationPoint : Space 3
  axialDistance : LengthQuantity
  observationTime : Time
  electromagneticSystem : Electromagnetism.EMSystem
  electricField : Electromagnetism.ElectricField 3
  fieldContributionPerRadian : ℝ → EuclideanSpace ℝ (Fin 3)
  figure : ChargedRingAxisFigure

/-- Unit vector `î` along the displayed positive `x`-axis. -/
def xAxisUnit : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Coherent-SI displacement from a ring source element to `P`. -/
def sourceToObservationDisplacementInMeters
    (setup : ChargedRingAxisSetup) (angle : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i =>
    setup.observationPoint.val i - (setup.ring.pointAtAngle angle).val i)

/-- Coherent-SI source-to-`P` distance labelled `r` in the figure. -/
def sourceToObservationDistanceInMeters
    (setup : ChargedRingAxisSetup) (angle : ℝ) : ℝ :=
  ‖sourceToObservationDisplacementInMeters setup angle‖

/-! ## Figure evidence, geometry, and physical nondegeneracy -/

/-- The physical source has the conducting-ring role stated in the scenario. -/
structure MatchesConductingRingScenario
    (setup : ChargedRingAxisSetup) : Prop where
  ringIsConducting : setup.ring.modeledAsConducting = true

/-!
Literal labels and qualitative features of the primary raster, calibrated to
the independent physical quantities.  The source-distance formula is retained
as displayed text here and derived mathematically for every source angle below.
-/
structure MatchesPrimaryChargedRingFigure
    (setup : ChargedRingAxisSetup) : Prop where
  bothAxesShown : ∀ axis, setup.figure.axisShown axis = true
  axisLabels : ∀ axis,
    setup.figure.printedAxisLabel axis = expectedAxisLabel axis
  allNamedPointsShown : ∀ point, setup.figure.pointShown point = true
  pointLabels : ∀ point,
    setup.figure.printedPointLabel point = expectedPointLabel point
  allScalarLabelsShown : ∀ label,
    setup.figure.scalarLabelShown label = true
  scalarLabels : ∀ label,
    setup.figure.printedScalarLabel label = expectedScalarLabel label
  allVectorArrowsShown : ∀ vector,
    setup.figure.vectorArrowShown vector = true
  vectorLabels : ∀ vector,
    setup.figure.printedVectorLabel vector = expectedVectorLabel vector
  bothAngleMarksShown : ∀ angle,
    setup.figure.angleMarkShown angle = true
  angleLabels : ∀ angle,
    setup.figure.printedAngleLabel angle = expectedAngleLabel angle
  allGeometricFeaturesShown : ∀ feature,
    setup.figure.featureShown feature = true
  displayedDistanceFormula :
    setup.figure.printedSourceDistanceFormula = "r = √(x² + a²)"
  radiusLabelDenotesRingRadius :
    setup.figure.radiusLabelQuantity = setup.ring.radius
  distanceLabelDenotesAxialDistance :
    setup.figure.axialDistanceLabelQuantity = setup.axialDistance
  chargeLabelDenotesTotalRingCharge :
    setup.figure.totalChargeLabelQuantity = setup.ring.totalCharge
  depictedAlphaInAngularRange :
    0 ≤ setup.figure.depictedAlphaRadians ∧
      setup.figure.depictedAlphaRadians ≤ Real.pi / 2
  depictedThetaInAngularRange :
    0 ≤ setup.figure.depictedThetaRadians ∧
      setup.figure.depictedThetaRadians ≤ Real.pi / 2

/-!
The displayed `x`-axis is coordinate `0`; the ring lies in the orthogonal
`y-z` plane and is parametrized by `(a cos φ, a sin φ)`.  Thus `O` is the
ring center and `P` is `x` metres along the positive axis.
-/
structure HasChargedRingAxisGeometry
    (setup : ChargedRingAxisSetup) : Prop where
  radiusPositive : 0 < lengthInMeters setup.ring.radius
  axialDistancePositive : 0 < lengthInMeters setup.axialDistance
  observationXCoordinate :
    setup.observationPoint.val 0 =
      setup.ring.center.val 0 + lengthInMeters setup.axialDistance
  observationYCoordinate :
    setup.observationPoint.val 1 = setup.ring.center.val 1
  observationZCoordinate :
    setup.observationPoint.val 2 = setup.ring.center.val 2
  ringXCoordinate : ∀ angle,
    (setup.ring.pointAtAngle angle).val 0 = setup.ring.center.val 0
  ringYCoordinate : ∀ angle,
    (setup.ring.pointAtAngle angle).val 1 =
      setup.ring.center.val 1 +
        lengthInMeters setup.ring.radius * Real.cos angle
  ringZCoordinate : ∀ angle,
    (setup.ring.pointAtAngle angle).val 2 =
      setup.ring.center.val 2 +
        lengthInMeters setup.ring.radius * Real.sin angle

/-- Nonzero source charge and a physically positive Coulomb constant. -/
structure HasPhysicalElectrostaticParameters
    (setup : ChargedRingAxisSetup) : Prop where
  totalChargeNonzero : chargeInCoulombs setup.ring.totalCharge ≠ 0
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Uniform charge, differential Coulomb law, and superposition -/

/-!
Uniform distribution means `dQ/dφ = Q/(2π)`.  The corresponding arc-length
density is `ds/dφ = a`; the integral clauses explicitly account for total
charge and circumference without assuming the requested electric field.
-/
structure SatisfiesUniformRingDistribution
    (setup : ChargedRingAxisSetup) : Prop where
  uniformChargePerRadian : ∀ angle,
    angularChargeDensityInCoulombsPerRadian
        (setup.ring.chargePerRadian angle) =
      chargeInCoulombs setup.ring.totalCharge / (2 * Real.pi)
  uniformArcLengthPerRadian : ∀ angle,
    lengthInMeters (setup.ring.arcLengthPerRadian angle) =
      lengthInMeters setup.ring.radius
  totalChargeAccounting :
    (∫ angle in 0..2 * Real.pi,
      angularChargeDensityInCoulombsPerRadian
        (setup.ring.chargePerRadian angle)) =
      chargeInCoulombs setup.ring.totalCharge
  circumferenceAccounting :
    (∫ angle in 0..2 * Real.pi,
      lengthInMeters (setup.ring.arcLengthPerRadian angle)) =
      2 * Real.pi * lengthInMeters setup.ring.radius

/-!
Differential Coulomb's law in coherent SI units:

`dE/dφ = k (dQ/dφ) r⃗ / ‖r⃗‖³`.

This general inverse-square vector law retains both axial and transverse
contributions and is not the closed-form field requested by the question.
-/
structure SatisfiesDifferentialCoulombFieldLaw
    (setup : ChargedRingAxisSetup) : Prop where
  contributionOfEveryElement : ∀ angle,
    setup.fieldContributionPerRadian angle =
      (setup.electromagneticSystem.coulombConstant *
          angularChargeDensityInCoulombsPerRadian
            (setup.ring.chargePerRadian angle) /
          sourceToObservationDistanceInMeters setup angle ^ 3) •
        sourceToObservationDisplacementInMeters setup angle

/-- The net electric field at `P` is the angular integral of all `dE` vectors. -/
structure SatisfiesRingFieldSuperposition
    (setup : ChargedRingAxisSetup) : Prop where
  fieldAtPIsAngularIntegral :
    setup.electricField setup.observationTime setup.observationPoint =
      ∫ angle in 0..2 * Real.pi,
        setup.fieldContributionPerRadian angle

/-! ## Symmetry consequences and multiple-choice target -/

/-!
Every point on the parametrized ring is the displayed distance
`√(x² + a²)` from `P`.
-/
lemma sourceToObservationDistance_eq
    (setup : ChargedRingAxisSetup)
    (_geometry : HasChargedRingAxisGeometry setup)
    (angle : ℝ) :
    sourceToObservationDistanceInMeters setup angle =
      Real.sqrt
        (lengthInMeters setup.axialDistance ^ 2 +
          lengthInMeters setup.ring.radius ^ 2) := by
  rw [sourceToObservationDistanceInMeters,
    sourceToObservationDisplacementInMeters, EuclideanSpace.norm_eq,
    Fin.sum_univ_three]
  simp [_geometry.observationXCoordinate,
    _geometry.observationYCoordinate, _geometry.observationZCoordinate,
    _geometry.ringXCoordinate, _geometry.ringYCoordinate,
    _geometry.ringZCoordinate]
  congr 1
  rw [mul_pow, mul_pow, sq_abs, sq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq angle]

/-!
Opposite source elements have equal-and-opposite `y` and `z` field
components, so the complete ring field has no transverse component.
-/
lemma transverseFieldComponents_cancel
    (setup : ChargedRingAxisSetup)
    (_geometry : HasChargedRingAxisGeometry setup)
    (_uniform : SatisfiesUniformRingDistribution setup)
    (_coulomb : SatisfiesDifferentialCoulombFieldLaw setup)
    (_superposition : SatisfiesRingFieldSuperposition setup) :
    (setup.electricField setup.observationTime setup.observationPoint) 1 = 0 ∧
      (setup.electricField setup.observationTime setup.observationPoint) 2 = 0 := by
  let x := lengthInMeters setup.axialDistance
  let a := lengthInMeters setup.ring.radius
  let Q := chargeInCoulombs setup.ring.totalCharge
  let k := setup.electromagneticSystem.coulombConstant
  let d := Real.sqrt (x ^ 2 + a ^ 2)
  let yAxisUnit : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single (1 : Fin 3) 1
  let zAxisUnit : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single (2 : Fin 3) 1
  have hdisp (φ : ℝ) :
      sourceToObservationDisplacementInMeters setup φ =
        x • xAxisUnit -
          ((a * Real.cos φ) • yAxisUnit +
            (a * Real.sin φ) • zAxisUnit) := by
    ext i
    fin_cases i <;>
      simp [sourceToObservationDisplacementInMeters, xAxisUnit,
        yAxisUnit, zAxisUnit, x, a,
        _geometry.observationXCoordinate,
        _geometry.observationYCoordinate,
        _geometry.observationZCoordinate,
        _geometry.ringXCoordinate, _geometry.ringYCoordinate,
        _geometry.ringZCoordinate]
  have hnorm (φ : ℝ) :
      sourceToObservationDistanceInMeters setup φ = d := by
    simpa [d, x, a] using
      sourceToObservationDistance_eq setup _geometry φ
  have hcharge (φ : ℝ) :
      angularChargeDensityInCoulombsPerRadian
          (setup.ring.chargePerRadian φ) =
        Q / (2 * Real.pi) := by
    simpa [Q] using _uniform.uniformChargePerRadian φ
  let c := k * (Q / (2 * Real.pi)) / d ^ 3
  have hdiff (φ : ℝ) :
      setup.fieldContributionPerRadian φ =
        c • (x • xAxisUnit -
          ((a * Real.cos φ) • yAxisUnit +
            (a * Real.sin φ) • zAxisUnit)) := by
    rw [_coulomb.contributionOfEveryElement, hcharge, hnorm, hdisp]
  have hDisplacementIntegral :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          x • xAxisUnit -
            ((a * Real.cos φ) • yAxisUnit +
              (a * Real.sin φ) • zAxisUnit)) =
        (2 * Real.pi * x) • xAxisUnit := by
    rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous (fun _φ : ℝ =>
          x • xAxisUnit)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun φ : ℝ =>
          (a * Real.cos φ) • yAxisUnit +
            (a * Real.sin φ) • zAxisUnit)).intervalIntegrable _ _),
      intervalIntegral.integral_add
        ((by fun_prop : Continuous (fun φ : ℝ =>
          (a * Real.cos φ) • yAxisUnit)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun φ : ℝ =>
          (a * Real.sin φ) • zAxisUnit)).intervalIntegrable _ _)]
    simp [integral_sin, integral_cos]
    simp [smul_smul, mul_comm]
  have hfield :
      setup.electricField setup.observationTime setup.observationPoint =
        (2 * Real.pi * c * x) • xAxisUnit := by
    calc
      setup.electricField setup.observationTime setup.observationPoint =
          ∫ φ in (0 : ℝ)..(2 * Real.pi),
            setup.fieldContributionPerRadian φ :=
        _superposition.fieldAtPIsAngularIntegral
      _ = ∫ φ in (0 : ℝ)..(2 * Real.pi),
          c • (x • xAxisUnit -
            ((a * Real.cos φ) • yAxisUnit +
              (a * Real.sin φ) • zAxisUnit)) := by
        apply intervalIntegral.integral_congr
        intro φ _hφ
        exact hdiff φ
      _ = c • (∫ φ in (0 : ℝ)..(2 * Real.pi),
          x • xAxisUnit -
            ((a * Real.cos φ) • yAxisUnit +
              (a * Real.sin φ) • zAxisUnit)) := by
        rw [intervalIntegral.integral_smul]
      _ = (2 * Real.pi * c * x) • xAxisUnit := by
        rw [hDisplacementIntegral, smul_smul]
        congr 1
        ring
  rw [hfield]
  constructor <;> simp [xAxisUnit]

/-!
All axial contributions have the same component.  Integrating the uniform
charge density gives the standard scalar coefficient of the ring field.
-/
lemma axialFieldComponent_eq
    (setup : ChargedRingAxisSetup)
    (_geometry : HasChargedRingAxisGeometry setup)
    (_physical : HasPhysicalElectrostaticParameters setup)
    (_uniform : SatisfiesUniformRingDistribution setup)
    (_coulomb : SatisfiesDifferentialCoulombFieldLaw setup)
    (_superposition : SatisfiesRingFieldSuperposition setup) :
    (setup.electricField setup.observationTime setup.observationPoint) 0 =
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs setup.ring.totalCharge *
        lengthInMeters setup.axialDistance /
        Real.rpow
          (lengthInMeters setup.axialDistance ^ 2 +
            lengthInMeters setup.ring.radius ^ 2)
          (3 / 2 : ℝ) := by
  let x := lengthInMeters setup.axialDistance
  let a := lengthInMeters setup.ring.radius
  let Q := chargeInCoulombs setup.ring.totalCharge
  let k := setup.electromagneticSystem.coulombConstant
  let d := Real.sqrt (x ^ 2 + a ^ 2)
  let yAxisUnit : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single (1 : Fin 3) 1
  let zAxisUnit : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single (2 : Fin 3) 1
  have hx : 0 < x := by
    simpa [x] using _geometry.axialDistancePositive
  have ha : 0 < a := by
    simpa [a] using _geometry.radiusPositive
  have hs : 0 < x ^ 2 + a ^ 2 := by
    positivity
  have hd : 0 < d := by
    exact Real.sqrt_pos.2 hs
  have hdisp (φ : ℝ) :
      sourceToObservationDisplacementInMeters setup φ =
        x • xAxisUnit -
          ((a * Real.cos φ) • yAxisUnit +
            (a * Real.sin φ) • zAxisUnit) := by
    ext i
    fin_cases i <;>
      simp [sourceToObservationDisplacementInMeters, xAxisUnit,
        yAxisUnit, zAxisUnit, x, a,
        _geometry.observationXCoordinate,
        _geometry.observationYCoordinate,
        _geometry.observationZCoordinate,
        _geometry.ringXCoordinate, _geometry.ringYCoordinate,
        _geometry.ringZCoordinate]
  have hnorm (φ : ℝ) :
      sourceToObservationDistanceInMeters setup φ = d := by
    simpa [d, x, a] using
      sourceToObservationDistance_eq setup _geometry φ
  have hcharge (φ : ℝ) :
      angularChargeDensityInCoulombsPerRadian
          (setup.ring.chargePerRadian φ) =
        Q / (2 * Real.pi) := by
    simpa [Q] using _uniform.uniformChargePerRadian φ
  let c := k * (Q / (2 * Real.pi)) / d ^ 3
  have hdiff (φ : ℝ) :
      setup.fieldContributionPerRadian φ =
        c • (x • xAxisUnit -
          ((a * Real.cos φ) • yAxisUnit +
            (a * Real.sin φ) • zAxisUnit)) := by
    rw [_coulomb.contributionOfEveryElement, hcharge, hnorm, hdisp]
  have hDisplacementIntegral :
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          x • xAxisUnit -
            ((a * Real.cos φ) • yAxisUnit +
              (a * Real.sin φ) • zAxisUnit)) =
        (2 * Real.pi * x) • xAxisUnit := by
    rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous (fun _φ : ℝ =>
          x • xAxisUnit)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun φ : ℝ =>
          (a * Real.cos φ) • yAxisUnit +
            (a * Real.sin φ) • zAxisUnit)).intervalIntegrable _ _),
      intervalIntegral.integral_add
        ((by fun_prop : Continuous (fun φ : ℝ =>
          (a * Real.cos φ) • yAxisUnit)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun φ : ℝ =>
          (a * Real.sin φ) • zAxisUnit)).intervalIntegrable _ _)]
    simp [integral_sin, integral_cos]
    simp [smul_smul, mul_comm]
  have hfield :
      setup.electricField setup.observationTime setup.observationPoint =
        (2 * Real.pi * c * x) • xAxisUnit := by
    calc
      setup.electricField setup.observationTime setup.observationPoint =
          ∫ φ in (0 : ℝ)..(2 * Real.pi),
            setup.fieldContributionPerRadian φ :=
        _superposition.fieldAtPIsAngularIntegral
      _ = ∫ φ in (0 : ℝ)..(2 * Real.pi),
          c • (x • xAxisUnit -
            ((a * Real.cos φ) • yAxisUnit +
              (a * Real.sin φ) • zAxisUnit)) := by
        apply intervalIntegral.integral_congr
        intro φ _hφ
        exact hdiff φ
      _ = c • (∫ φ in (0 : ℝ)..(2 * Real.pi),
          x • xAxisUnit -
            ((a * Real.cos φ) • yAxisUnit +
              (a * Real.sin φ) • zAxisUnit)) := by
        rw [intervalIntegral.integral_smul]
      _ = (2 * Real.pi * c * x) • xAxisUnit := by
        rw [hDisplacementIntegral, smul_smul]
        congr 1
        ring
  have hdenominator :
      d ^ 3 = Real.rpow (x ^ 2 + a ^ 2) (3 / 2 : ℝ) := by
    dsimp [d]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (le_of_lt hs)]
    norm_num
  have hCoefficient :
      2 * Real.pi * c * x =
        k * Q * x / Real.rpow (x ^ 2 + a ^ 2) (3 / 2 : ℝ) := by
    rw [show c = k * (Q / (2 * Real.pi)) / d ^ 3 by rfl,
      hdenominator]
    field_simp [Real.pi_ne_zero,
      ne_of_gt (Real.rpow_pos_of_pos hs (3 / 2 : ℝ))]
  rw [hfield]
  simpa [xAxisUnit, x, a, Q, k] using hCoefficient

/-- Labels attached to the four electric-field choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The coherent-SI scalar multiplying `î` in each printed answer.  This records
the alternatives but does not define the independent electric field.
-/
def AnswerChoice.axialCoefficient
    (setup : ChargedRingAxisSetup) : AnswerChoice → ℝ
  | .A =>
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs setup.ring.totalCharge *
        lengthInMeters setup.ring.radius /
        Real.rpow
          (lengthInMeters setup.axialDistance ^ 2 +
            lengthInMeters setup.ring.radius ^ 2)
          (3 / 2 : ℝ)
  | .B =>
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs setup.ring.totalCharge *
        lengthInMeters setup.axialDistance /
        Real.rpow
          (lengthInMeters setup.axialDistance ^ 2 +
            lengthInMeters setup.ring.radius ^ 2)
          (3 / 2 : ℝ)
  | .C =>
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs setup.ring.totalCharge *
        lengthInMeters setup.axialDistance /
        Real.rpow
          (lengthInMeters setup.axialDistance ^ 2 +
            lengthInMeters setup.ring.radius ^ 2)
          (1 / 2 : ℝ)
  | .D =>
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs setup.ring.totalCharge /
        (lengthInMeters setup.axialDistance ^ 2 +
          lengthInMeters setup.ring.radius ^ 2)

/-- The vector represented by a displayed answer choice. -/
def AnswerChoice.fieldVector
    (setup : ChargedRingAxisSetup) (choice : AnswerChoice) :
    EuclideanSpace ℝ (Fin 3) :=
  choice.axialCoefficient setup • xAxisUnit

/-- The dataset's recorded answer label, retained as unused metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
**Blueprint target** `thm:physics:phyx_mini_0995:target`.

For a uniformly charged conducting ring, transverse differential fields cancel
pairwise and the axial components add.  Therefore the field at `P` is

`(1 / (4 π ε₀)) Q x / (x² + a²)^(3/2) î`,

which is exactly displayed answer B.
-/
theorem electricFieldOnAxisOfUniformlyChargedRing
    (setup : ChargedRingAxisSetup)
    (_scenario : MatchesConductingRingScenario setup)
    (_figure : MatchesPrimaryChargedRingFigure setup)
    (_geometry : HasChargedRingAxisGeometry setup)
    (_physical : HasPhysicalElectrostaticParameters setup)
    (_uniform : SatisfiesUniformRingDistribution setup)
    (_coulomb : SatisfiesDifferentialCoulombFieldLaw setup)
    (_superposition : SatisfiesRingFieldSuperposition setup) :
    setup.electricField setup.observationTime setup.observationPoint =
      (setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs setup.ring.totalCharge *
          lengthInMeters setup.axialDistance /
          Real.rpow
            (lengthInMeters setup.axialDistance ^ 2 +
              lengthInMeters setup.ring.radius ^ 2)
            (3 / 2 : ℝ)) •
        xAxisUnit := by
  have hAxial :=
    axialFieldComponent_eq setup _geometry _physical _uniform _coulomb
      _superposition
  have hTransverse :=
    transverseFieldComponents_cancel setup _geometry _uniform _coulomb
      _superposition
  ext i
  fin_cases i
  · simpa [xAxisUnit] using hAxial
  · simpa [xAxisUnit] using hTransverse.1
  · simpa [xAxisUnit] using hTransverse.2

end PhyXMiniProblems.ProblemPhyXMini0995
