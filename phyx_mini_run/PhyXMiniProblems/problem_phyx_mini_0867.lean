import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0867

open Dimension
open scoped BigOperators

/-!
# Potential difference between two uniformly charged spheres

The primary image shows a large positively charged sphere on the left and a
small positively charged sphere on the right. Their diameters are `60 cm` and
`10 cm`, their charges are `100 nC` and `25 nC`, and the horizontal arrow
between their centers is labelled `100 cm`. Point `a` is on the right-hand
surface of the large sphere and point `b` is on the left-hand surface of the
small sphere.

The physical quantities below are unit-independent Physlib dimensionful
values. Real numbers occur only at explicitly named unit-readout boundaries,
in literal raster data, and in displayed multiple-choice values. In
particular, the potentials at `a` and `b` are independent fields of the setup;
neither is defined from the recorded answer.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Electric potential has dimension `M L^2 T^-2 C^-1`. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Coulomb's constant has dimension `M L^3 T^-2 C^-2`. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative total electric charge carried by one sphere. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A signed electric potential, with its physical dimension retained. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative dimensionful value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a positive sphere charge in coherent-SI coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read a positive sphere charge in nanocoulombs. -/
def chargeMagnitudeInNanocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  10 ^ 9 * chargeMagnitudeInCoulombs charge

/-- Read an electric potential in coherent-SI volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read Coulomb's constant in newton-metres-squared per coulomb-squared. -/
def coulombConstantInNewtonMetersSquaredPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-! ## Figure labels, physical objects, and raster vocabulary -/

/-- The two spheres distinguished by size and horizontal placement. -/
inductive SphereLabel where
  | largeLeft
  | smallRight
  deriving DecidableEq, Fintype, Repr

/-- The two surface points named in the supplied image. -/
inductive SurfacePointLabel where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- Horizontal placement of a sphere in the drawing. -/
inductive HorizontalPlacement where
  | left
  | right
  deriving DecidableEq, Repr

/-- Which horizontal side of a circle carries a labelled surface point. -/
inductive HorizontalSurfaceSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Meaning of the horizontal `100 cm` arrow in the primary raster. -/
inductive SeparationArrowRole where
  | centerToCenter
  | surfaceGap
  deriving DecidableEq, Repr

/-- Spherical charge-distribution idealization stated by the problem. -/
inductive SphereChargeDistribution where
  | uniformSpherical
  | unspecified
  deriving DecidableEq, Repr

/-- Electrostatic environmental idealization used for the calculation. -/
inductive ElectrostaticModel where
  | stationarySpheresInVacuum
  | other
  deriving DecidableEq, Repr

/-!
Literal and relational information visible in image 867. The numerical fields
are printed unit-labelled readouts, not replacements for physical lengths or
charges.
-/
structure TwoChargedSpheresFigure where
  showsSphere : SphereLabel → Bool
  showsPositiveCenterMark : SphereLabel → Bool
  spherePlacement : SphereLabel → HorizontalPlacement
  printedDiameterCentimeters : SphereLabel → ℝ
  printedChargeNanocoulombs : SphereLabel → ℝ
  showsPoint : SurfacePointLabel → Bool
  pointOnSphere : SurfacePointLabel → SphereLabel
  pointSurfaceSide : SurfacePointLabel → HorizontalSurfaceSide
  printedSeparationCentimeters : ℝ
  separationArrowRole : SeparationArrowRole

/-!
Independent physical data for the two-sphere configuration. The contribution
of each sphere and the total potential at each labelled point are stored as
physical quantities and constrained only by the governing-law assumptions
below.
-/
structure TwoUniformlyChargedSpheresSetup where
  model : ElectrostaticModel
  chargeDistribution : SphereLabel → SphereChargeDistribution
  sphereDiameter : SphereLabel → LengthQuantity
  sphereRadius : SphereLabel → LengthQuantity
  sphereCharge : SphereLabel → ChargeMagnitudeQuantity
  centerSeparation : LengthQuantity
  centerDistanceToPoint : SphereLabel → SurfacePointLabel → LengthQuantity
  coulombConstant : CoulombConstantQuantity
  potentialContribution : SphereLabel → SurfacePointLabel →
    ElectricPotentialQuantity
  potentialAt : SurfacePointLabel → ElectricPotentialQuantity
  figure : TwoChargedSpheresFigure

/-! ## Assumptions: scenario, primary-image data, geometry, and physical laws -/

/-- Qualitative electrostatic and uniform-charge assumptions from the prose. -/
structure MatchesUniformlyChargedSphereScenario
    (setup : TwoUniformlyChargedSpheresSetup) : Prop where
  stationarySpheresInVacuum : setup.model = .stationarySpheresInVacuum
  eachSphereUniformlyCharged : ∀ sphere,
    setup.chargeDistribution sphere = .uniformSpherical

/-!
The physical measurements stated by the problem. These fields contain no
potential or answer-choice information.
-/
structure MatchesReportedSphereMeasurements
    (setup : TwoUniformlyChargedSpheresSetup) : Prop where
  largeDiameterCentimeters :
    lengthInCentimeters (setup.sphereDiameter .largeLeft) = 60
  smallDiameterCentimeters :
    lengthInCentimeters (setup.sphereDiameter .smallRight) = 10
  largeChargeNanocoulombs :
    chargeMagnitudeInNanocoulombs (setup.sphereCharge .largeLeft) = 100
  smallChargeNanocoulombs :
    chargeMagnitudeInNanocoulombs (setup.sphereCharge .smallRight) = 25
  centerSeparationCentimeters :
    lengthInCentimeters setup.centerSeparation = 100

/-!
Primary-raster evidence, including the interpretation of the `100 cm` arrow
as center-to-center. This follows the bitmap itself: the arrow endpoints lie
above the two sphere centers.
-/
structure MatchesSuppliedTwoSphereFigure
    (setup : TwoUniformlyChargedSpheresSetup) : Prop where
  everySphereShown : ∀ sphere, setup.figure.showsSphere sphere = true
  everyPositiveMarkShown : ∀ sphere,
    setup.figure.showsPositiveCenterMark sphere = true
  everyPointShown : ∀ point, setup.figure.showsPoint point = true
  largeSphereIsLeft :
    setup.figure.spherePlacement .largeLeft = .left
  smallSphereIsRight :
    setup.figure.spherePlacement .smallRight = .right
  pointAOnLargeSphere :
    setup.figure.pointOnSphere .a = .largeLeft
  pointBOnSmallSphere :
    setup.figure.pointOnSphere .b = .smallRight
  pointAOnRightSurface :
    setup.figure.pointSurfaceSide .a = .right
  pointBOnLeftSurface :
    setup.figure.pointSurfaceSide .b = .left
  arrowMeasuresCenterSeparation :
    setup.figure.separationArrowRole = .centerToCenter
  printedLargeDiameter :
    setup.figure.printedDiameterCentimeters .largeLeft = 60
  printedSmallDiameter :
    setup.figure.printedDiameterCentimeters .smallRight = 10
  printedLargeCharge :
    setup.figure.printedChargeNanocoulombs .largeLeft = 100
  printedSmallCharge :
    setup.figure.printedChargeNanocoulombs .smallRight = 25
  printedCenterSeparation :
    setup.figure.printedSeparationCentimeters = 100
  diameterLabelsCalibrated : ∀ sphere,
    setup.figure.printedDiameterCentimeters sphere =
      lengthInCentimeters (setup.sphereDiameter sphere)
  chargeLabelsCalibrated : ∀ sphere,
    setup.figure.printedChargeNanocoulombs sphere =
      chargeMagnitudeInNanocoulombs (setup.sphereCharge sphere)
  separationLabelCalibrated :
    setup.figure.printedSeparationCentimeters =
      lengthInCentimeters setup.centerSeparation

/-!
Geometry derived from the spherical diameters and the two facing surface
points. In particular the four center-to-point distances are `0.30 m`,
`0.70 m`, `0.95 m`, and `0.05 m` after applying the measurement data.
-/
structure UsesFacingSurfacePointGeometry
    (setup : TwoUniformlyChargedSpheresSetup) : Prop where
  diameterIsTwiceRadius : ∀ sphere,
    lengthInMeters (setup.sphereDiameter sphere) =
      2 * lengthInMeters (setup.sphereRadius sphere)
  pointAOnLargeSurface :
    lengthInMeters (setup.centerDistanceToPoint .largeLeft .a) =
      lengthInMeters (setup.sphereRadius .largeLeft)
  pointBOnSmallSurface :
    lengthInMeters (setup.centerDistanceToPoint .smallRight .b) =
      lengthInMeters (setup.sphereRadius .smallRight)
  smallCenterToPointA :
    lengthInMeters (setup.centerDistanceToPoint .smallRight .a) =
      lengthInMeters setup.centerSeparation -
        lengthInMeters (setup.sphereRadius .largeLeft)
  largeCenterToPointB :
    lengthInMeters (setup.centerDistanceToPoint .largeLeft .b) =
      lengthInMeters setup.centerSeparation -
        lengthInMeters (setup.sphereRadius .smallRight)

/-- Positivity and exterior-point conditions needed by the potential law. -/
structure HasPhysicalTwoSphereParameters
    (setup : TwoUniformlyChargedSpheresSetup) : Prop where
  everyRadiusPositive : ∀ sphere,
    0 < lengthInMeters (setup.sphereRadius sphere)
  everyChargePositive : ∀ sphere,
    0 < chargeMagnitudeInCoulombs (setup.sphereCharge sphere)
  centerSeparationPositive : 0 < lengthInMeters setup.centerSeparation
  spheresDisjoint :
    lengthInMeters (setup.sphereRadius .largeLeft) +
        lengthInMeters (setup.sphereRadius .smallRight) <
      lengthInMeters setup.centerSeparation
  coulombConstantPositive :
    0 < coulombConstantInNewtonMetersSquaredPerCoulombSquared
      setup.coulombConstant
  everyLabelledPointExterior : ∀ source point,
    lengthInMeters (setup.sphereRadius source) ≤
      lengthInMeters (setup.centerDistanceToPoint source point)

/-!
The textbook numerical calibration of Coulomb's constant used for evaluating
the multiple-choice data. It contains no potential difference or answer.
-/
structure UsesTextbookCoulombConstant
    (setup : TwoUniformlyChargedSpheresSetup) : Prop where
  textbookCoulombConstant :
    coulombConstantInNewtonMetersSquaredPerCoulombSquared
        setup.coulombConstant =
      (899 : ℝ) / 100 * 10 ^ 9

/-!
For a uniformly charged sphere, its potential at a point on or outside the
sphere equals `k Q / r`; electrostatic potentials add linearly. This is the
general governing law used here, not the requested numerical conclusion.
-/
structure SatisfiesUniformSpherePotentialLawAndSuperposition
    (setup : TwoUniformlyChargedSpheresSetup) : Prop where
  exteriorSphereContribution : ∀ source point,
    lengthInMeters (setup.sphereRadius source) ≤
        lengthInMeters (setup.centerDistanceToPoint source point) →
      electricPotentialInVolts (setup.potentialContribution source point) =
        coulombConstantInNewtonMetersSquaredPerCoulombSquared
            setup.coulombConstant *
          chargeMagnitudeInCoulombs (setup.sphereCharge source) /
          lengthInMeters (setup.centerDistanceToPoint source point)
  potentialSuperposition : ∀ point,
    electricPotentialInVolts (setup.potentialAt point) =
      ∑ source : SphereLabel,
        electricPotentialInVolts (setup.potentialContribution source point)

/-! ## Requested potential difference and answer choices -/

/-- How much higher the potential at `b` is than the potential at `a`, in volts. -/
def potentialDifferenceBMinusAInVolts
    (setup : TwoUniformlyChargedSpheresSetup) : ℝ :=
  electricPotentialInVolts (setup.potentialAt .b) -
    electricPotentialInVolts (setup.potentialAt .a)

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Potential difference printed beside each answer choice, in volts. -/
def displayedPotentialDifferenceInVolts : AnswerChoice → ℝ
  | .A => (6 : ℝ) / 5
  | .B => 140
  | .C => 2000
  | .D => 2100

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A value rounds to a display at the stated positive resolution. -/
def RoundsToNearestResolution
    (value displayed resolution : ℝ) : Prop :=
  0 < resolution ∧ |value - displayed| ≤ resolution / 2

/-- A choice is uniquely closest to the calculated potential difference. -/
def IsUniqueClosestDisplayedAnswer
    (setup : TwoUniformlyChargedSpheresSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |potentialDifferenceBMinusAInVolts setup -
        displayedPotentialDifferenceInVolts choice| <
      |potentialDifferenceBMinusAInVolts setup -
        displayedPotentialDifferenceInVolts other|

/-!
The sphere-potential law, measurement conversions, and facing-point geometry
place `V(b) - V(a)` within the interval that rounds to `2100 V` at `100 V`
resolution. This is a derived numerical statement, not a premise.
-/
lemma potentialDifference_rounding_bounds
    (setup : TwoUniformlyChargedSpheresSetup)
    (hData : MatchesReportedSphereMeasurements setup)
    (hGeometry : UsesFacingSurfacePointGeometry setup)
    (hPhysical : HasPhysicalTwoSphereParameters setup)
    (hConstant : UsesTextbookCoulombConstant setup)
    (hPotential : SatisfiesUniformSpherePotentialLawAndSuperposition setup) :
    2050 ≤ potentialDifferenceBMinusAInVolts setup ∧
      potentialDifferenceBMinusAInVolts setup < 2150 := by
  have centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
      (length.2 UnitChoices.SI
        ({UnitChoices.SI with length := LengthUnit.centimeters} :
          UnitChoices))
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.scale,
      LengthUnit.meters, LengthUnit.div_eq_val, NNReal.smul_def] at h ⊢
    exact h
  have hLargeDiameter :
      lengthInMeters (setup.sphereDiameter .largeLeft) = (3 : ℝ) / 5 := by
    have h := centimeters_eq (setup.sphereDiameter .largeLeft)
    rw [hData.largeDiameterCentimeters] at h
    norm_num at h ⊢
    linarith
  have hSmallDiameter :
      lengthInMeters (setup.sphereDiameter .smallRight) = (1 : ℝ) / 10 := by
    have h := centimeters_eq (setup.sphereDiameter .smallRight)
    rw [hData.smallDiameterCentimeters] at h
    norm_num at h ⊢
    linarith
  have hCenterSeparation :
      lengthInMeters setup.centerSeparation = 1 := by
    have h := centimeters_eq setup.centerSeparation
    rw [hData.centerSeparationCentimeters] at h
    norm_num at h ⊢
    linarith
  have hLargeCharge :
      chargeMagnitudeInCoulombs (setup.sphereCharge .largeLeft) =
        (1 : ℝ) / 10000000 := by
    have h := hData.largeChargeNanocoulombs
    norm_num [chargeMagnitudeInNanocoulombs] at h ⊢
    linarith
  have hSmallCharge :
      chargeMagnitudeInCoulombs (setup.sphereCharge .smallRight) =
        (1 : ℝ) / 40000000 := by
    have h := hData.smallChargeNanocoulombs
    norm_num [chargeMagnitudeInNanocoulombs] at h ⊢
    linarith
  have hLargeRadius :
      lengthInMeters (setup.sphereRadius .largeLeft) = (3 : ℝ) / 10 := by
    have h := hGeometry.diameterIsTwiceRadius .largeLeft
    rw [hLargeDiameter] at h
    norm_num at h ⊢
    linarith
  have hSmallRadius :
      lengthInMeters (setup.sphereRadius .smallRight) = (1 : ℝ) / 20 := by
    have h := hGeometry.diameterIsTwiceRadius .smallRight
    rw [hSmallDiameter] at h
    norm_num at h ⊢
    linarith
  have hLargeToA :
      lengthInMeters (setup.centerDistanceToPoint .largeLeft .a) =
        (3 : ℝ) / 10 := by
    rw [hGeometry.pointAOnLargeSurface, hLargeRadius]
  have hSmallToA :
      lengthInMeters (setup.centerDistanceToPoint .smallRight .a) =
        (7 : ℝ) / 10 := by
    rw [hGeometry.smallCenterToPointA, hCenterSeparation, hLargeRadius]
    norm_num
  have hLargeToB :
      lengthInMeters (setup.centerDistanceToPoint .largeLeft .b) =
        (19 : ℝ) / 20 := by
    rw [hGeometry.largeCenterToPointB, hCenterSeparation, hSmallRadius]
    norm_num
  have hSmallToB :
      lengthInMeters (setup.centerDistanceToPoint .smallRight .b) =
        (1 : ℝ) / 20 := by
    rw [hGeometry.pointBOnSmallSurface, hSmallRadius]
  have hLargeAtA :=
    hPotential.exteriorSphereContribution .largeLeft .a
      (hPhysical.everyLabelledPointExterior .largeLeft .a)
  have hSmallAtA :=
    hPotential.exteriorSphereContribution .smallRight .a
      (hPhysical.everyLabelledPointExterior .smallRight .a)
  have hLargeAtB :=
    hPotential.exteriorSphereContribution .largeLeft .b
      (hPhysical.everyLabelledPointExterior .largeLeft .b)
  have hSmallAtB :=
    hPotential.exteriorSphereContribution .smallRight .b
      (hPhysical.everyLabelledPointExterior .smallRight .b)
  rw [hConstant.textbookCoulombConstant, hLargeCharge, hLargeToA] at hLargeAtA
  rw [hConstant.textbookCoulombConstant, hSmallCharge, hSmallToA] at hSmallAtA
  rw [hConstant.textbookCoulombConstant, hLargeCharge, hLargeToB] at hLargeAtB
  rw [hConstant.textbookCoulombConstant, hSmallCharge, hSmallToB] at hSmallAtB
  norm_num at hLargeAtA hSmallAtA hLargeAtB hSmallAtB
  have hSphereSum (f : SphereLabel → ℝ) :
      ∑ source : SphereLabel, f source =
        f .largeLeft + f .smallRight := by
    rw [show (Finset.univ : Finset SphereLabel) =
      {.largeLeft, .smallRight} by decide]
    simp
  have hPotentialAtA := hPotential.potentialSuperposition .a
  have hPotentialAtB := hPotential.potentialSuperposition .b
  rw [hSphereSum, hLargeAtA, hSmallAtA] at hPotentialAtA
  rw [hSphereSum, hLargeAtB, hSmallAtB] at hPotentialAtB
  unfold potentialDifferenceBMinusAInVolts
  rw [hPotentialAtA, hPotentialAtB]
  norm_num

/-!
Point `b` is at higher potential than point `a`; the excess rounds to
`2100 V`, uniquely selecting answer D.

This declaration formalizes `thm:physics:phyx_mini_0867:target`. No
hypothesis contains the sign, rounding interval, `2100 V`, or answer D.
-/
theorem problem_phyx_mini_0867
    (setup : TwoUniformlyChargedSpheresSetup)
    (hScenario : MatchesUniformlyChargedSphereScenario setup)
    (hData : MatchesReportedSphereMeasurements setup)
    (hFigure : MatchesSuppliedTwoSphereFigure setup)
    (hGeometry : UsesFacingSurfacePointGeometry setup)
    (hPhysical : HasPhysicalTwoSphereParameters setup)
    (hConstant : UsesTextbookCoulombConstant setup)
    (hPotential : SatisfiesUniformSpherePotentialLawAndSuperposition setup) :
    electricPotentialInVolts (setup.potentialAt .a) <
        electricPotentialInVolts (setup.potentialAt .b) ∧
      RoundsToNearestResolution
        (potentialDifferenceBMinusAInVolts setup) 2100 100 ∧
      IsUniqueClosestDisplayedAnswer setup recordedDatasetAnswer := by
  have hBounds := potentialDifference_rounding_bounds
    setup hData hGeometry hPhysical hConstant hPotential
  have hStrict :
      2050 < potentialDifferenceBMinusAInVolts setup := by
    have centimeters_eq (length : LengthQuantity) :
        lengthInCentimeters length = 100 * lengthInMeters length := by
      have h := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
        (length.2 UnitChoices.SI
          ({UnitChoices.SI with length := LengthUnit.centimeters} :
            UnitChoices))
      norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
        UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.scale,
        LengthUnit.meters, LengthUnit.div_eq_val, NNReal.smul_def] at h ⊢
      exact h
    have hLargeDiameter :
        lengthInMeters (setup.sphereDiameter .largeLeft) = (3 : ℝ) / 5 := by
      have h := centimeters_eq (setup.sphereDiameter .largeLeft)
      rw [hData.largeDiameterCentimeters] at h
      norm_num at h ⊢
      linarith
    have hSmallDiameter :
        lengthInMeters (setup.sphereDiameter .smallRight) = (1 : ℝ) / 10 := by
      have h := centimeters_eq (setup.sphereDiameter .smallRight)
      rw [hData.smallDiameterCentimeters] at h
      norm_num at h ⊢
      linarith
    have hCenterSeparation :
        lengthInMeters setup.centerSeparation = 1 := by
      have h := centimeters_eq setup.centerSeparation
      rw [hData.centerSeparationCentimeters] at h
      norm_num at h ⊢
      linarith
    have hLargeCharge :
        chargeMagnitudeInCoulombs (setup.sphereCharge .largeLeft) =
          (1 : ℝ) / 10000000 := by
      have h := hData.largeChargeNanocoulombs
      norm_num [chargeMagnitudeInNanocoulombs] at h ⊢
      linarith
    have hSmallCharge :
        chargeMagnitudeInCoulombs (setup.sphereCharge .smallRight) =
          (1 : ℝ) / 40000000 := by
      have h := hData.smallChargeNanocoulombs
      norm_num [chargeMagnitudeInNanocoulombs] at h ⊢
      linarith
    have hLargeRadius :
        lengthInMeters (setup.sphereRadius .largeLeft) = (3 : ℝ) / 10 := by
      have h := hGeometry.diameterIsTwiceRadius .largeLeft
      rw [hLargeDiameter] at h
      norm_num at h ⊢
      linarith
    have hSmallRadius :
        lengthInMeters (setup.sphereRadius .smallRight) = (1 : ℝ) / 20 := by
      have h := hGeometry.diameterIsTwiceRadius .smallRight
      rw [hSmallDiameter] at h
      norm_num at h ⊢
      linarith
    have hLargeToA :
        lengthInMeters (setup.centerDistanceToPoint .largeLeft .a) =
          (3 : ℝ) / 10 := by
      rw [hGeometry.pointAOnLargeSurface, hLargeRadius]
    have hSmallToA :
        lengthInMeters (setup.centerDistanceToPoint .smallRight .a) =
          (7 : ℝ) / 10 := by
      rw [hGeometry.smallCenterToPointA, hCenterSeparation, hLargeRadius]
      norm_num
    have hLargeToB :
        lengthInMeters (setup.centerDistanceToPoint .largeLeft .b) =
          (19 : ℝ) / 20 := by
      rw [hGeometry.largeCenterToPointB, hCenterSeparation, hSmallRadius]
      norm_num
    have hSmallToB :
        lengthInMeters (setup.centerDistanceToPoint .smallRight .b) =
          (1 : ℝ) / 20 := by
      rw [hGeometry.pointBOnSmallSurface, hSmallRadius]
    have hLargeAtA :=
      hPotential.exteriorSphereContribution .largeLeft .a
        (hPhysical.everyLabelledPointExterior .largeLeft .a)
    have hSmallAtA :=
      hPotential.exteriorSphereContribution .smallRight .a
        (hPhysical.everyLabelledPointExterior .smallRight .a)
    have hLargeAtB :=
      hPotential.exteriorSphereContribution .largeLeft .b
        (hPhysical.everyLabelledPointExterior .largeLeft .b)
    have hSmallAtB :=
      hPotential.exteriorSphereContribution .smallRight .b
        (hPhysical.everyLabelledPointExterior .smallRight .b)
    rw [hConstant.textbookCoulombConstant, hLargeCharge, hLargeToA] at hLargeAtA
    rw [hConstant.textbookCoulombConstant, hSmallCharge, hSmallToA] at hSmallAtA
    rw [hConstant.textbookCoulombConstant, hLargeCharge, hLargeToB] at hLargeAtB
    rw [hConstant.textbookCoulombConstant, hSmallCharge, hSmallToB] at hSmallAtB
    norm_num at hLargeAtA hSmallAtA hLargeAtB hSmallAtB
    have hSphereSum (f : SphereLabel → ℝ) :
        ∑ source : SphereLabel, f source =
          f .largeLeft + f .smallRight := by
      rw [show (Finset.univ : Finset SphereLabel) =
        {.largeLeft, .smallRight} by decide]
      simp
    have hPotentialAtA := hPotential.potentialSuperposition .a
    have hPotentialAtB := hPotential.potentialSuperposition .b
    rw [hSphereSum, hLargeAtA, hSmallAtA] at hPotentialAtA
    rw [hSphereSum, hLargeAtB, hSmallAtB] at hPotentialAtB
    unfold potentialDifferenceBMinusAInVolts
    rw [hPotentialAtA, hPotentialAtB]
    norm_num
  constructor
  · unfold potentialDifferenceBMinusAInVolts at hStrict
    linarith
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [abs_le]
    constructor <;> linarith [hBounds.1, hBounds.2]
  · unfold IsUniqueClosestDisplayedAnswer
    dsimp only [recordedDatasetAnswer]
    intro other hOther
    have hChosenError :
        |potentialDifferenceBMinusAInVolts setup - 2100| < 50 := by
      rw [abs_lt]
      constructor <;> linarith [hBounds.2, hStrict]
    cases other with
    | A =>
        simp only [displayedPotentialDifferenceInVolts]
        calc
          |potentialDifferenceBMinusAInVolts setup - 2100| < 50 :=
            hChosenError
          _ < |potentialDifferenceBMinusAInVolts setup - (6 : ℝ) / 5| := by
            rw [abs_of_pos (by linarith [hStrict])]
            linarith
    | B =>
        simp only [displayedPotentialDifferenceInVolts]
        calc
          |potentialDifferenceBMinusAInVolts setup - 2100| < 50 :=
            hChosenError
          _ < |potentialDifferenceBMinusAInVolts setup - 140| := by
            rw [abs_of_pos (by linarith [hStrict])]
            linarith
    | C =>
        simp only [displayedPotentialDifferenceInVolts]
        calc
          |potentialDifferenceBMinusAInVolts setup - 2100| < 50 :=
            hChosenError
          _ < |potentialDifferenceBMinusAInVolts setup - 2000| := by
            rw [abs_of_pos (by linarith [hStrict])]
            linarith
    | D => exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0867
