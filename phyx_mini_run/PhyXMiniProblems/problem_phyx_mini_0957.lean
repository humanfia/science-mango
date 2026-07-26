import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0957

open Dimension

/-!
# Deflection of a charged particle by a finite magnetic-field region

A positive particle enters at the origin with velocity in the displayed `+y`
direction.  A uniform magnetic field points into the page in the strip from
`y = 0` to `y = d`.  The Lorentz force bends the particle toward the displayed
`+x` direction, which points left in the supplied raster.  At `y = d` the
particle leaves its circular arc and follows the tangent through a field-free
region until it strikes the wall at `y = D`.

Physical magnitudes use Physlib's unit-independent
`Dimensionful (WithDim _ NNReal)` representation.  Real numbers occur only at
explicit unit-readout boundaries, for the dimensionless exit angle, and in
displayed answer values.

Assumption/target split:

* governing laws: uniform field magnitude, zero field in the field-free
  region, the perpendicular magnetic-orbit radius law `q B R = m v`, uniform
  circular arc length `v t₁ = R θ`, the exit coordinates of that arc, and
  straight tangent motion after exit;
* previous-part results: none;
* figure/data readouts: positive charge, initial `+y` velocity, into-page
  field, left-pointing displayed `+x` direction, `q = 2.15 μC`,
  `m = 3.20e-11 kg`, `v₀ = 1.45e5 m/s`, `B = 0.420 T`, `d = 25.0 cm`,
  `D = 75.0 cm`, and field-free length `50.0 cm`;
* current target conclusions: the total-deflection circle-and-tangent formula
  and the fact that its numerical value uniquely selects displayed choice B,
  `0.0305 m`.

Neither the total-deflection formula nor the answer selection occurs in a
premise structure or governing-law field.
-/

/-! ## Dimensions, dimensionful quantities, and named-unit readouts -/

/-- Magnetic flux density has coherent-SI dimension `M T⁻¹ C⁻¹` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a duration in coherent-SI seconds. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read an electric-charge magnitude in coherent-SI coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read a speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a magnetic-flux-density magnitude in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityQuantity) : ℝ :=
  ((fieldMagnitude UnitChoices.SI).val : ℝ)

/-! ## Physical and primary-raster vocabulary -/

/-- Sign of the particle's electric charge. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Named directions in the plane of image `957.png`. -/
inductive PlanarDirection where
  | positiveX
  | negativeX
  | positiveY
  | negativeY
  deriving DecidableEq, Repr

/-- Literal arrow directions on the two-dimensional page. -/
inductive PageDirection where
  | left
  | right
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Directions normal to the page, represented by dots or crosses. -/
inductive PageNormalDirection where
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Relative directions needed by the perpendicular magnetic-motion model. -/
inductive RelativeOrientation where
  | perpendicular
  | parallel
  | other
  deriving DecidableEq, Repr

/-- Idealized spatial models for the applied field. -/
inductive MagneticFieldModel where
  | uniformInFiniteStripAndZeroAbove
  | other
  deriving DecidableEq, Repr

/-- Symbolic physical-quantity labels visible in the supplied raster. -/
inductive FigureQuantityLabel where
  | initialSpeed
  | magneticField
  | fieldDepth
  | wallDistance
  | curvatureRadius
  | fieldExitDeflection
  | totalDeflection
  deriving DecidableEq, Fintype, Repr

/-- Expected printed symbol for each physical-quantity label. -/
def expectedPrintedSymbol : FigureQuantityLabel → String
  | .initialSpeed => "v₀"
  | .magneticField => "B"
  | .fieldDepth => "d"
  | .wallDistance => "D"
  | .curvatureRadius => "R"
  | .fieldExitDeflection => "Δx₁"
  | .totalDeflection => "Δx"

/-!
Literal presentation data from the primary raster `957.png`.  The two printed
numerical length labels remain physical quantities rather than bare scalars.
-/
structure MagneticDeflectionFigure where
  wallShown : Bool
  positiveChargeGlyphShown : Bool
  magneticFieldCrossesShown : Bool
  circularArcShown : Bool
  straightTangentSegmentShown : Bool
  radiusSegmentShown : Bool
  initialVelocityArrowShown : Bool
  xAxisArrowDirectionOnPage : PageDirection
  yAxisArrowDirectionOnPage : PageDirection
  initialVelocityArrowDirectionOnPage : PageDirection
  magneticFieldGlyphDirection : PageNormalDirection
  trajectoryBendDirectionOnPage : PageDirection
  quantityLabelShown : FigureQuantityLabel → Bool
  printedSymbol : FigureQuantityLabel → String
  printedFieldDepth : LengthQuantity
  printedWallDistance : LengthQuantity

/-!
Independent physical quantities and observables in the experiment.  In
particular, `totalHorizontalDeflection` is not defined from the target formula
or from an answer choice.
-/
structure ChargedParticleDeflectionSetup where
  particleChargeSign : ChargeSign
  particleChargeMagnitude : ChargeMagnitudeQuantity
  particleMass : MassQuantity
  initialSpeed : SpeedQuantity
  magneticFluxDensityMagnitude : MagneticFluxDensityQuantity
  fieldDepth : LengthQuantity
  wallDistance : LengthQuantity
  fieldFreeLength : LengthQuantity
  curvatureRadius : LengthQuantity
  timeInMagneticField : TimeQuantity
  exitSweepAngleInRadians : ℝ
  fieldExitDeflection : LengthQuantity
  totalHorizontalDeflection : LengthQuantity
  initialVelocityDirection : PlanarDirection
  magneticFieldDirection : PageNormalDirection
  velocityFieldOrientation : RelativeOrientation
  initialLorentzForceDirection : PlanarDirection
  magneticFieldModel : MagneticFieldModel
  magneticField : Electromagnetism.MagneticField 3
  magneticFieldRegion : Set (Time × Space 3)
  fieldFreeRegion : Set (Time × Space 3)
  figure : MagneticDeflectionFigure

/-! ## Written data, primary-image evidence, and governing laws -/

/-- Numerical and qualitative data explicitly stated in the problem prose. -/
structure MatchesWrittenProblemData
    (setup : ChargedParticleDeflectionSetup) : Prop where
  chargeIsPositive : setup.particleChargeSign = .positive
  chargeMagnitudeIsTwoPointFifteenMicrocoulombs :
    chargeMagnitudeInCoulombs setup.particleChargeMagnitude = 2.15e-6
  massIsThreePointTwoTimesTenToMinusElevenKilograms :
    massInKilograms setup.particleMass = 3.20e-11
  initialSpeedIsOnePointFourFiveTimesTenToFiveMetersPerSecond :
    speedInMetersPerSecond setup.initialSpeed = 1.45e5
  fieldMagnitudeIsZeroPointFourTwoZeroTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 0.420
  fieldDepthIsTwentyFiveCentimeters :
    lengthInCentimeters setup.fieldDepth = 25.0
  wallDistanceIsSeventyFiveCentimeters :
    lengthInCentimeters setup.wallDistance = 75.0
  fieldFreeLengthIsFiftyCentimeters :
    lengthInCentimeters setup.fieldFreeLength = 50.0
  initialMotionIsPositiveY : setup.initialVelocityDirection = .positiveY
  fieldPointsIntoPage : setup.magneticFieldDirection = .intoPage
  velocityIsPerpendicularToField :
    setup.velocityFieldOrientation = .perpendicular
  finiteUniformFieldModel :
    setup.magneticFieldModel = .uniformInFiniteStripAndZeroAbove

/-!
Primary-raster evidence.  The image places positive `x` to the left, positive
`y` upward, shows crosses for an into-page field, and depicts the circular arc
joining a straight tangent at the field boundary.
-/
structure MatchesSuppliedMagneticDeflectionFigure
    (setup : ChargedParticleDeflectionSetup) : Prop where
  wallIsShown : setup.figure.wallShown = true
  positiveChargeIsShown : setup.figure.positiveChargeGlyphShown = true
  magneticCrossesAreShown : setup.figure.magneticFieldCrossesShown = true
  circularArcIsShown : setup.figure.circularArcShown = true
  straightTangentIsShown : setup.figure.straightTangentSegmentShown = true
  radiusIsShown : setup.figure.radiusSegmentShown = true
  initialVelocityArrowIsShown : setup.figure.initialVelocityArrowShown = true
  displayedPositiveXPointsLeft :
    setup.figure.xAxisArrowDirectionOnPage = .left
  displayedPositiveYPointsUp :
    setup.figure.yAxisArrowDirectionOnPage = .upward
  velocityArrowPointsPositiveY :
    setup.figure.initialVelocityArrowDirectionOnPage = .upward
  crossesMeanIntoPage :
    setup.figure.magneticFieldGlyphDirection = .intoPage
  displayedTrajectoryBendsPositiveX :
    setup.figure.trajectoryBendDirectionOnPage = .left
  lorentzForceFollowsDisplayedBend :
    setup.initialLorentzForceDirection = .positiveX
  allQuantityLabelsAreShown : ∀ label,
    setup.figure.quantityLabelShown label = true
  printedQuantitySymbols : ∀ label,
    setup.figure.printedSymbol label = expectedPrintedSymbol label
  depthLabelNamesPhysicalDepth :
    setup.figure.printedFieldDepth = setup.fieldDepth
  wallLabelNamesPhysicalWallDistance :
    setup.figure.printedWallDistance = setup.wallDistance

/-- Positivity and nondegeneracy conditions for the depicted orbit. -/
structure HasPhysicalDeflectionParameters
    (setup : ChargedParticleDeflectionSetup) : Prop where
  chargeMagnitudePositive :
    0 < chargeMagnitudeInCoulombs setup.particleChargeMagnitude
  massPositive : 0 < massInKilograms setup.particleMass
  speedPositive : 0 < speedInMetersPerSecond setup.initialSpeed
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  fieldDepthPositive : 0 < lengthInMeters setup.fieldDepth
  wallLiesBeyondField :
    lengthInMeters setup.fieldDepth < lengthInMeters setup.wallDistance
  fieldFreeLengthPositive : 0 < lengthInMeters setup.fieldFreeLength
  radiusExceedsFieldDepth :
    lengthInMeters setup.fieldDepth < lengthInMeters setup.curvatureRadius
  timeInFieldPositive : 0 < timeInSeconds setup.timeInMagneticField
  exitAnglePositive : 0 < setup.exitSweepAngleInRadians
  exitAngleAcute : setup.exitSweepAngleInRadians < Real.pi / 2
  exitDeflectionNonnegative :
    0 ≤ lengthInMeters setup.fieldExitDeflection
  exitPointBeforeCircleCenter :
    lengthInMeters setup.fieldExitDeflection <
      lengthInMeters setup.curvatureRadius
  totalDeflectionNonnegative :
    0 ≤ lengthInMeters setup.totalHorizontalDeflection
  magneticFieldRegionNonempty : setup.magneticFieldRegion.Nonempty
  fieldFreeRegionNonempty : setup.fieldFreeRegion.Nonempty

/-! The vertical distance from the field exit to the wall is `D - d`. -/
structure SatisfiesFieldAndWallGeometry
    (setup : ChargedParticleDeflectionSetup) : Prop where
  fieldFreeLengthIsDifference :
    lengthInMeters setup.fieldFreeLength =
      lengthInMeters setup.wallDistance - lengthInMeters setup.fieldDepth

/-!
The scalar flux-density magnitude calibrates Physlib's magnetic vector field
throughout the field strip, while the named field-free region has zero field.
-/
structure HasUniformFiniteMagneticField
    (setup : ChargedParticleDeflectionSetup) : Prop where
  uniformMagnitude : ∀ time position,
    (time, position) ∈ setup.magneticFieldRegion →
      ‖setup.magneticField time position‖ =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  zeroInFieldFreeRegion : ∀ time position,
    (time, position) ∈ setup.fieldFreeRegion →
      setup.magneticField time position = 0

/-!
School-physics laws for the positively charged particle while its velocity is
perpendicular to the uniform magnetic field.  The angle `θ` is measured from
the initial `+y` direction toward displayed `+x`.
-/
structure SatisfiesPerpendicularMagneticCircularMotion
    (setup : ChargedParticleDeflectionSetup) : Prop where
  magneticOrbitRadiusLaw :
    chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthInMeters setup.curvatureRadius =
      massInKilograms setup.particleMass *
        speedInMetersPerSecond setup.initialSpeed
  uniformCircularArcLengthLaw :
    speedInMetersPerSecond setup.initialSpeed *
        timeInSeconds setup.timeInMagneticField =
      lengthInMeters setup.curvatureRadius *
        setup.exitSweepAngleInRadians
  exitVerticalCoordinateLaw :
    lengthInMeters setup.fieldDepth =
      lengthInMeters setup.curvatureRadius *
        Real.sin setup.exitSweepAngleInRadians
  exitHorizontalCoordinateLaw :
    lengthInMeters setup.fieldExitDeflection =
      lengthInMeters setup.curvatureRadius *
        (1 - Real.cos setup.exitSweepAngleInRadians)

/-!
After leaving the field, the particle retains the velocity tangent to the
circular arc.  Consequently its extra horizontal displacement across the
field-free vertical distance is `ℓ tan θ`.  This is a governing motion law,
not the requested eliminated formula or a numerical answer.
-/
structure SatisfiesFieldFreeTangentMotion
    (setup : ChargedParticleDeflectionSetup) : Prop where
  tangentDriftLaw :
    lengthInMeters setup.totalHorizontalDeflection -
        lengthInMeters setup.fieldExitDeflection =
      lengthInMeters setup.fieldFreeLength *
        Real.tan setup.exitSweepAngleInRadians

/-! ## Derived relations and displayed answer -/

/-- The four answer labels printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Horizontal deflection printed beside each choice, in metres. -/
def AnswerChoice.displayedDeflectionInMeters : AnswerChoice → ℝ
  | .A => 0.0245
  | .B => 0.0305
  | .C => 0.035
  | .D => 0.0172

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Absolute discrepancy between a physical deflection and a displayed choice. -/
def displayedDeflectionError
    (setup : ChargedParticleDeflectionSetup)
    (choice : AnswerChoice) : ℝ :=
  |lengthInMeters setup.totalHorizontalDeflection -
    choice.displayedDeflectionInMeters|

/-!
A choice is the unique nearest displayed value to the physical deflection.
This comparison is appropriate for the source's multiple-choice decimal
approximations and does not assert that a rounded display is an exact length.
-/
def IsUniqueClosestDisplayedDeflection
    (setup : ChargedParticleDeflectionSetup)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    other ≠ choice →
      displayedDeflectionError setup choice <
        displayedDeflectionError setup other

/-!
The perpendicular magnetic-orbit law gives `R = m v₀ / (q B)`.  This is an
intermediate derived relation, not a premise field.
-/
lemma curvatureRadius_eq_mass_mul_speed_div_charge_mul_field
    (setup : ChargedParticleDeflectionSetup)
    (hPhysical : HasPhysicalDeflectionParameters setup)
    (hCircular : SatisfiesPerpendicularMagneticCircularMotion setup) :
    lengthInMeters setup.curvatureRadius =
      massInKilograms setup.particleMass *
          speedInMetersPerSecond setup.initialSpeed /
        (chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude) := by
  have hDenominatorPositive :
      0 <
        chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude :=
    mul_pos hPhysical.chargeMagnitudePositive hPhysical.fieldMagnitudePositive
  apply (eq_div_iff hDenominatorPositive.ne').2
  nlinarith only [hCircular.magneticOrbitRadiusLaw]

/-!
Eliminating the exit angle and the intermediate deflection from the circle
and tangent laws gives the total horizontal displacement.  The square root is
the positive horizontal radius component at the field exit.
-/
lemma totalHorizontalDeflection_eq_circle_tangent_formula
    (setup : ChargedParticleDeflectionSetup)
    (hPhysical : HasPhysicalDeflectionParameters setup)
    (hGeometry : SatisfiesFieldAndWallGeometry setup)
    (hCircular : SatisfiesPerpendicularMagneticCircularMotion setup)
    (hTangent : SatisfiesFieldFreeTangentMotion setup) :
    lengthInMeters setup.totalHorizontalDeflection =
      lengthInMeters setup.curvatureRadius -
          Real.sqrt
            (lengthInMeters setup.curvatureRadius ^ 2 -
              lengthInMeters setup.fieldDepth ^ 2) +
        (lengthInMeters setup.wallDistance -
            lengthInMeters setup.fieldDepth) *
          lengthInMeters setup.fieldDepth /
          Real.sqrt
            (lengthInMeters setup.curvatureRadius ^ 2 -
              lengthInMeters setup.fieldDepth ^ 2) := by
  let R : ℝ := lengthInMeters setup.curvatureRadius
  let d : ℝ := lengthInMeters setup.fieldDepth
  let D : ℝ := lengthInMeters setup.wallDistance
  let ℓ : ℝ := lengthInMeters setup.fieldFreeLength
  let θ : ℝ := setup.exitSweepAngleInRadians
  let x₁ : ℝ := lengthInMeters setup.fieldExitDeflection
  let x : ℝ := lengthInMeters setup.totalHorizontalDeflection
  change
    x =
      R - Real.sqrt (R ^ 2 - d ^ 2) +
        (D - d) * d / Real.sqrt (R ^ 2 - d ^ 2)
  have hRPositive : 0 < R := by
    exact lt_trans hPhysical.fieldDepthPositive
      hPhysical.radiusExceedsFieldDepth
  have hThetaPositive : 0 < θ := hPhysical.exitAnglePositive
  have hThetaAcute : θ < Real.pi / 2 := hPhysical.exitAngleAcute
  have hCosPositive : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith only [hThetaPositive, Real.pi_pos]
    · exact hThetaAcute
  have hVertical : d = R * Real.sin θ :=
    hCircular.exitVerticalCoordinateLaw
  have hHorizontal : x₁ = R * (1 - Real.cos θ) :=
    hCircular.exitHorizontalCoordinateLaw
  have hFieldFree : ℓ = D - d :=
    hGeometry.fieldFreeLengthIsDifference
  have hTangent :
      x - x₁ = ℓ * Real.tan θ :=
    hTangent.tangentDriftLaw
  have hRadicand :
      R ^ 2 - d ^ 2 = (R * Real.cos θ) ^ 2 := by
    rw [hVertical]
    nlinarith only [Real.sin_sq_add_cos_sq θ]
  have hSqrt :
      Real.sqrt (R ^ 2 - d ^ 2) = R * Real.cos θ := by
    rw [hRadicand, Real.sqrt_sq]
    exact (mul_pos hRPositive hCosPositive).le
  have hDriftFraction :
      (D - d) * d / (R * Real.cos θ) =
        (D - d) * Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos, hVertical]
    field_simp [hRPositive.ne', hCosPositive.ne']
  rw [hSqrt, hDriftFraction]
  rw [hHorizontal, hFieldFree] at hTangent
  nlinarith only [hTangent]

/-!
The stated numerical data make the physical result approximately
`0.03044 m`, whose unique nearest displayed value is choice B, `0.0305 m`.
-/
lemma totalHorizontalDeflection_uniquely_matches_answerB
    (setup : ChargedParticleDeflectionSetup)
    (hData : MatchesWrittenProblemData setup)
    (hPhysical : HasPhysicalDeflectionParameters setup)
    (hGeometry : SatisfiesFieldAndWallGeometry setup)
    (hCircular : SatisfiesPerpendicularMagneticCircularMotion setup)
    (hTangent : SatisfiesFieldFreeTangentMotion setup) :
    IsUniqueClosestDisplayedDeflection setup .B := by
  have lengthInCentimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hRadiusFormula :=
    curvatureRadius_eq_mass_mul_speed_div_charge_mul_field
      setup hPhysical hCircular
  have hRadius :
      lengthInMeters setup.curvatureRadius = (4640 : ℝ) / 903 := by
    calc
      lengthInMeters setup.curvatureRadius =
          massInKilograms setup.particleMass *
              speedInMetersPerSecond setup.initialSpeed /
            (chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
              magneticFluxDensityInTeslas
                setup.magneticFluxDensityMagnitude) :=
        hRadiusFormula
      _ = (4640 : ℝ) / 903 := by
        rw [hData.massIsThreePointTwoTimesTenToMinusElevenKilograms,
          hData.initialSpeedIsOnePointFourFiveTimesTenToFiveMetersPerSecond,
          hData.chargeMagnitudeIsTwoPointFifteenMicrocoulombs,
          hData.fieldMagnitudeIsZeroPointFourTwoZeroTeslas]
        norm_num
  have hDepth :
      lengthInMeters setup.fieldDepth = (1 : ℝ) / 4 := by
    have h := hData.fieldDepthIsTwentyFiveCentimeters
    rw [lengthInCentimeters_eq] at h
    norm_num at h ⊢
    linarith only [h]
  have hWall :
      lengthInMeters setup.wallDistance = (3 : ℝ) / 4 := by
    have h := hData.wallDistanceIsSeventyFiveCentimeters
    rw [lengthInCentimeters_eq] at h
    norm_num at h ⊢
    linarith only [h]
  have hTotalFormula :=
    totalHorizontalDeflection_eq_circle_tangent_formula
      setup hPhysical hGeometry hCircular hTangent
  rw [hRadius, hDepth, hWall] at hTotalFormula
  let x : ℝ := lengthInMeters setup.totalHorizontalDeflection
  let s : ℝ :=
    Real.sqrt (((4640 : ℝ) / 903) ^ 2 - ((1 : ℝ) / 4) ^ 2)
  have hTotal :
      x = (4640 : ℝ) / 903 - s + 1 / (8 * s) := by
    dsimp only [x, s]
    rw [hTotalFormula]
    have hSqrtNonzero :
        Real.sqrt
            (((4640 : ℝ) / 903) ^ 2 - ((1 : ℝ) / 4) ^ 2) ≠ 0 := by
      positivity
    field_simp [hSqrtNonzero]
    <;> ring
  have hRadicandPositive :
      0 < ((4640 : ℝ) / 903) ^ 2 - ((1 : ℝ) / 4) ^ 2 := by
    norm_num
  have hsPositive : 0 < s := by
    exact Real.sqrt_pos.2 hRadicandPositive
  have hsNonnegative : 0 ≤ s := hsPositive.le
  have hsSquare :
      s ^ 2 =
        ((4640 : ℝ) / 903) ^ 2 - ((1 : ℝ) / 4) ^ 2 := by
    exact Real.sq_sqrt hRadicandPositive.le
  have hsLower : (5132 : ℝ) / 1000 < s := by
    by_contra h
    have hsUpper' : s ≤ (5132 : ℝ) / 1000 := le_of_not_gt h
    have hProduct :
        0 ≤ ((5132 : ℝ) / 1000 - s) *
          ((5132 : ℝ) / 1000 + s) :=
      mul_nonneg (sub_nonneg.mpr hsUpper') (by positivity)
    nlinarith only [hProduct, hsSquare]
  have hsUpper : s < (5133 : ℝ) / 1000 := by
    by_contra h
    have hsLower' : (5133 : ℝ) / 1000 ≤ s := le_of_not_gt h
    have hProduct :
        0 ≤ (s - (5133 : ℝ) / 1000) *
          (s + (5133 : ℝ) / 1000) :=
      mul_nonneg (sub_nonneg.mpr hsLower') (by positivity)
    nlinarith only [hProduct, hsSquare]
  have hTotalCleared :
      x * (8 * s) =
        (((4640 : ℝ) / 903 - s) * (8 * s) + 1) := by
    calc
      x * (8 * s) =
          ((4640 : ℝ) / 903 - s + 1 / (8 * s)) * (8 * s) := by
        rw [hTotal]
      _ = ((4640 : ℝ) / 903 - s) * (8 * s) + 1 := by
        field_simp [hsPositive.ne']
  have hxLower : (11 : ℝ) / 400 < x := by
    by_contra h
    have hxUpper' : x ≤ (11 : ℝ) / 400 := le_of_not_gt h
    have hProduct :
        x * (8 * s) ≤ ((11 : ℝ) / 400) * (8 * s) :=
      mul_le_mul_of_nonneg_right hxUpper' (by positivity)
    nlinarith only [hProduct, hTotalCleared, hsSquare, hsLower]
  have hxUpper : x < (131 : ℝ) / 4000 := by
    by_contra h
    have hxLower' : (131 : ℝ) / 4000 ≤ x := le_of_not_gt h
    have hProduct :
        ((131 : ℝ) / 4000) * (8 * s) ≤ x * (8 * s) :=
      mul_le_mul_of_nonneg_right hxLower' (by positivity)
    nlinarith only [hProduct, hTotalCleared, hsSquare, hsUpper]
  unfold IsUniqueClosestDisplayedDeflection
  intro other hOther
  cases other with
  | A =>
      change |x - 0.0305| < |x - 0.0245|
      rw [← sq_lt_sq]
      norm_num at hxLower ⊢
      nlinarith only [hxLower]
  | B =>
      exact (hOther rfl).elim
  | C =>
      change |x - 0.0305| < |x - 0.035|
      rw [← sq_lt_sq]
      norm_num at hxUpper ⊢
      nlinarith only [hxUpper]
  | D =>
      change |x - 0.0305| < |x - 0.0172|
      rw [← sq_lt_sq]
      norm_num at hxLower ⊢
      nlinarith only [hxLower]

/-!
The total horizontal deflection is the circle sagitta accumulated inside the
field plus the tangent drift through the field-free region.  With the supplied
particle and apparatus data, this uniquely selects recorded choice B.

This declaration formalizes
`thm:physics:phyx_mini_0957:target`.  Neither the eliminated deflection formula
nor the answer match occurs in any premise.
-/
theorem problem_phyx_mini_0957
    (setup : ChargedParticleDeflectionSetup)
    (hData : MatchesWrittenProblemData setup)
    (hFigure : MatchesSuppliedMagneticDeflectionFigure setup)
    (hPhysical : HasPhysicalDeflectionParameters setup)
    (hGeometry : SatisfiesFieldAndWallGeometry setup)
    (hField : HasUniformFiniteMagneticField setup)
    (hCircular : SatisfiesPerpendicularMagneticCircularMotion setup)
    (hTangent : SatisfiesFieldFreeTangentMotion setup) :
    lengthInMeters setup.curvatureRadius =
        massInKilograms setup.particleMass *
            speedInMetersPerSecond setup.initialSpeed /
          (chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
            magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude) ∧
      lengthInMeters setup.totalHorizontalDeflection =
        lengthInMeters setup.curvatureRadius -
            Real.sqrt
              (lengthInMeters setup.curvatureRadius ^ 2 -
                lengthInMeters setup.fieldDepth ^ 2) +
          (lengthInMeters setup.wallDistance -
              lengthInMeters setup.fieldDepth) *
            lengthInMeters setup.fieldDepth /
            Real.sqrt
              (lengthInMeters setup.curvatureRadius ^ 2 -
                lengthInMeters setup.fieldDepth ^ 2) ∧
      IsUniqueClosestDisplayedDeflection setup recordedDatasetAnswer := by
  constructor
  · exact curvatureRadius_eq_mass_mul_speed_div_charge_mul_field
      setup hPhysical hCircular
  constructor
  · exact totalHorizontalDeflection_eq_circle_tangent_formula
      setup hPhysical hGeometry hCircular hTangent
  · change IsUniqueClosestDisplayedDeflection setup .B
    exact totalHorizontalDeflection_uniquely_matches_answerB
      setup hData hPhysical hGeometry hCircular hTangent

end PhyXMiniProblems.ProblemPhyXMini0957
