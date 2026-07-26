import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0972

open Dimension

/-!
# Motional emf across a blood vessel

The primary image `972.png` models conducting blood as horizontal slabs moving
right through a magnetic field directed into the page.  Charge separation is
measured across the vessel diameter `d`.

Physical magnitudes are represented by Physlib `Dimensionful` quantities.
Real numbers occur only at explicit unit-readout boundaries and in literal
source metadata.  In particular, the magnetic-field strength is an independent
observable constrained by the motional-emf law; it is not defined from the
recorded answer.
-/

/-! ## Physical dimensions, quantities, and unit readouts -/

/-- Magnetic-flux density, measured in teslas in coherent SI, has dimension
`M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric potential difference has dimension `B · velocity · length`. -/
def potentialDifferenceDimension : Dimension :=
  magneticFluxDensityDimension * (L𝓭 * T𝓭⁻¹) * L𝓭

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitudeQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedMagnitudeQuantity : Type := DimSpeed

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative electric-potential-difference magnitude. -/
abbrev PotentialDifferenceMagnitudeQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthMagnitudeQuantity) : ℝ :=
  coherentSIReadout length

/-- Read a length in millimetres. -/
def lengthInMillimeters (length : LengthMagnitudeQuantity) : ℝ :=
  ((length {UnitChoices.SI with
    length := LengthUnit.millimeters}).val : ℝ)

/-- Read a speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitudeQuantity) : ℝ :=
  coherentSIReadout speed

/-- Read a speed in centimetres per second. -/
def speedInCentimetersPerSecond (speed : SpeedMagnitudeQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := LengthUnit.centimeters
    time := TimeUnit.seconds}).val : ℝ)

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (fieldStrength : MagneticFluxDensityMagnitudeQuantity) : ℝ :=
  coherentSIReadout fieldStrength

/-- Read a potential-difference magnitude in volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceMagnitudeQuantity) : ℝ :=
  coherentSIReadout potentialDifference

/-- Read a potential-difference magnitude in millivolts. -/
def potentialDifferenceInMillivolts
    (potentialDifference : PotentialDifferenceMagnitudeQuantity) : ℝ :=
  1000 * potentialDifferenceInVolts potentialDifference

/-! ## Conducting blood and primary-figure vocabulary -/

/-- The two signs of mobile ionic charge carriers mentioned in the scenario. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-!
An abstract conducting-blood model retaining mobile positive and negative ion
species without reducing either charge or conductivity to a scalar alias.
-/
structure ConductingBlood where
  IonSpecies : Type
  chargeSign : IonSpecies → ChargeSign
  mobile : IonSpecies → Prop
  hasMobilePositiveIon :
    ∃ ion, mobile ion ∧ chargeSign ion = .positive
  hasMobileNegativeIon :
    ∃ ion, mobile ion ∧ chargeSign ion = .negative

/-- Electrical idealization assigned to the vessel and its contents. -/
inductive VesselElectricalModel where
  | conductingWire
  | insulatingTube
  deriving DecidableEq, Repr

/-- Kinematic idealization used for the flowing blood. -/
inductive BloodFlowIdealization where
  | parallelConductingSlabs
  | continuousInsulator
  deriving DecidableEq, Repr

/-- Directions distinguished in the plane of the supplied image. -/
inductive PlanarDirection where
  | left
  | right
  | up
  | down
  deriving DecidableEq, Repr

/-- Axes distinguished in the plane of the supplied image. -/
inductive PlanarAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Directions normal to the page of the supplied image. -/
inductive PageNormalDirection where
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Glyph convention for a magnetic field normal to the page. -/
inductive MagneticFieldGlyph where
  | crosses
  | dots
  deriving DecidableEq, Repr

/-- Relative orientation of two physical directions. -/
inductive RelativeOrientation where
  | parallel
  | perpendicular
  | oblique
  deriving DecidableEq, Repr

/-- Literal presentation data transcribed from the primary raster. -/
structure BloodVesselFigure where
  redCylinderShown : Bool
  magneticFieldVectorLabelShown : Bool
  velocityArrowShown : Bool
  diameterLabelShown : Bool
  cylinderAxis : PlanarAxis
  diameterAxis : PlanarAxis
  velocityArrowDirection : PlanarDirection
  fieldGlyph : MagneticFieldGlyph

/-!
Independent physical observables for the vessel experiment.  The slab
thickness and vessel diameter are kept distinct until the written model equates
them.  Likewise, the requested field strength is not computed by this record.
-/
structure BloodVesselMotionalEmfSetup where
  blood : ConductingBlood
  vesselModel : VesselElectricalModel
  flowIdealization : BloodFlowIdealization
  vesselDiameter : LengthMagnitudeQuantity
  slabThickness : LengthMagnitudeQuantity
  flowSpeed : SpeedMagnitudeQuantity
  magneticFieldStrength : MagneticFluxDensityMagnitudeQuantity
  producedPotentialDifference : PotentialDifferenceMagnitudeQuantity
  flowDirection : PlanarDirection
  magneticFieldDirection : PageNormalDirection
  diameterAxis : PlanarAxis
  fieldFlowOrientation : RelativeOrientation
  diameterFlowOrientation : RelativeOrientation
  figure : BloodVesselFigure

/-! ## Scenario, figure evidence, measurements, and governing law -/

/-- The conductor-and-moving-slab idealization stated in the written scenario. -/
structure MatchesWrittenBloodVesselScenario
    (setup : BloodVesselMotionalEmfSetup) : Prop where
  vesselActsAsWire : setup.vesselModel = .conductingWire
  bloodActsAsSlabs :
    setup.flowIdealization = .parallelConductingSlabs
  slabThicknessIsVesselDiameter :
    setup.slabThickness = setup.vesselDiameter
  magneticFieldPerpendicularToFlow :
    setup.fieldFlowOrientation = .perpendicular
  diameterPerpendicularToFlow :
    setup.diameterFlowOrientation = .perpendicular

/-!
Literal figure evidence and its calibration to the physical setup.  The
standard cross-glyph convention is recorded explicitly as “into the page.”
-/
structure MatchesSuppliedBloodVesselFigure
    (setup : BloodVesselMotionalEmfSetup) : Prop where
  cylinderShown : setup.figure.redCylinderShown = true
  magneticFieldLabelShown :
    setup.figure.magneticFieldVectorLabelShown = true
  velocityArrowShown : setup.figure.velocityArrowShown = true
  diameterLabelShown : setup.figure.diameterLabelShown = true
  cylinderHorizontal : setup.figure.cylinderAxis = .horizontal
  diameterVertical : setup.figure.diameterAxis = .vertical
  arrowPointsRight :
    setup.figure.velocityArrowDirection = .right
  fieldDrawnWithCrosses : setup.figure.fieldGlyph = .crosses
  crossesMeanIntoPage :
    setup.magneticFieldDirection = .intoPage
  physicalFlowMatchesArrow :
    setup.flowDirection = setup.figure.velocityArrowDirection
  physicalDiameterMatchesFigure :
    setup.diameterAxis = setup.figure.diameterAxis

/-!
The three nominal measurements printed in the question.  No magnetic-field
value occurs here: it remains the quantity requested by the problem.
-/
structure HasGivenBloodVesselMeasurements
    (setup : BloodVesselMotionalEmfSetup) : Prop where
  speedReadout :
    speedInCentimetersPerSecond setup.flowSpeed = 15
  diameterReadout :
    lengthInMillimeters setup.vesselDiameter = 5
  potentialDifferenceReadout :
    potentialDifferenceInMillivolts
      setup.producedPotentialDifference = 1

/-!
For mutually perpendicular `B`, `v`, and charge-separation direction, the
motional-emf magnitude law is `ΔV = B v d`.  This premise is a governing law,
not the requested numerical field strength.
-/
structure SatisfiesPerpendicularMotionalEmfLaw
    (setup : BloodVesselMotionalEmfSetup) : Prop where
  potentialDifferenceFromMovingConductor :
    potentialDifferenceInVolts
        setup.producedPotentialDifference =
      magneticFluxDensityInTeslas setup.magneticFieldStrength *
        speedInMetersPerSecond setup.flowSpeed *
        lengthInMeters setup.slabThickness

/-! ## Derived relation, answer metadata, and requested result -/

/-- Solving the motional-emf law for a nondegenerate magnetic field strength. -/
lemma magneticFieldStrength_eq_potentialDifference_div_speed_mul_thickness
    (setup : BloodVesselMotionalEmfSetup)
    (hSpeed : speedInMetersPerSecond setup.flowSpeed ≠ 0)
    (hThickness : lengthInMeters setup.slabThickness ≠ 0)
    (hLaw : SatisfiesPerpendicularMotionalEmfLaw setup) :
    magneticFluxDensityInTeslas setup.magneticFieldStrength =
      potentialDifferenceInVolts setup.producedPotentialDifference /
        (speedInMetersPerSecond setup.flowSpeed *
          lengthInMeters setup.slabThickness) := by
  apply (eq_div_iff (mul_ne_zero hSpeed hThickness)).2
  simpa [mul_assoc] using
    hLaw.potentialDifferenceFromMovingConductor.symm

/-- Labels of the four field strengths displayed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-field strength in teslas displayed beside an answer label. -/
def AnswerChoice.displayedFieldStrengthInTeslas : AnswerChoice → ℝ
  | .A => 66 / 5
  | .B => 33 / 25
  | .C => 13 / 1000
  | .D => 13 / 100000

/-- The dataset records answer label B. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A choice is strictly closer than every alternative to the required field. -/
def IsClosestDisplayedFieldStrength
    (setup : BloodVesselMotionalEmfSetup)
    (candidate : AnswerChoice) : Prop :=
  ∀ other, other ≠ candidate →
    |magneticFluxDensityInTeslas setup.magneticFieldStrength -
        candidate.displayedFieldStrengthInTeslas| <
      |magneticFluxDensityInTeslas setup.magneticFieldStrength -
        other.displayedFieldStrengthInTeslas|

/-!
The nominal SI values give
`B = (1/1000) / ((15/100) * (5/1000)) = 4/3 T`.  Thus the displayed
`1.32 T` value (answer B) is the closest offered choice, though it is not
exactly equal to the nominal calculation.

This declaration formalizes `thm:physics:phyx_mini_0972:target`.
-/
theorem problem_phyx_mini_0972
    (setup : BloodVesselMotionalEmfSetup)
    (hScenario : MatchesWrittenBloodVesselScenario setup)
    (hFigure : MatchesSuppliedBloodVesselFigure setup)
    (hMeasurements : HasGivenBloodVesselMeasurements setup)
    (hLaw : SatisfiesPerpendicularMotionalEmfLaw setup) :
    magneticFluxDensityInTeslas setup.magneticFieldStrength = 4 / 3 ∧
      IsClosestDisplayedFieldStrength setup recordedDatasetAnswer := by
  have hSpeedConversion :
      speedInCentimetersPerSecond setup.flowSpeed =
        100 * speedInMetersPerSecond setup.flowSpeed := by
    have h := congrArg
      (fun x : WithDim (L𝓭 * T𝓭⁻¹) NNReal => (x.val : ℝ))
      (setup.flowSpeed.property UnitChoices.SI
        ({UnitChoices.SI with
          length := LengthUnit.centimeters
          time := TimeUnit.seconds} : UnitChoices))
    norm_num [speedInCentimetersPerSecond, speedInMetersPerSecond,
      coherentSIReadout, UnitChoices.dimScale, LengthUnit.centimeters] at h ⊢
    exact h
  have hLengthConversion :
      lengthInMillimeters setup.vesselDiameter =
        1000 * lengthInMeters setup.vesselDiameter := by
    have h := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
      (setup.vesselDiameter.property UnitChoices.SI
        ({UnitChoices.SI with
          length := LengthUnit.millimeters} : UnitChoices))
    norm_num [lengthInMillimeters, lengthInMeters, coherentSIReadout,
      UnitChoices.dimScale, LengthUnit.millimeters] at h ⊢
    exact h
  have hSpeedSI :
      speedInMetersPerSecond setup.flowSpeed = 3 / 20 := by
    nlinarith [hMeasurements.speedReadout, hSpeedConversion]
  have hDiameterSI :
      lengthInMeters setup.vesselDiameter = 1 / 200 := by
    nlinarith [hMeasurements.diameterReadout, hLengthConversion]
  have hThicknessSI :
      lengthInMeters setup.slabThickness = 1 / 200 := by
    rw [hScenario.slabThicknessIsVesselDiameter]
    exact hDiameterSI
  have hPotentialSI :
      potentialDifferenceInVolts setup.producedPotentialDifference =
        1 / 1000 := by
    have h := hMeasurements.potentialDifferenceReadout
    change
      1000 *
          potentialDifferenceInVolts setup.producedPotentialDifference =
        1 at h
    norm_num at h ⊢
    linarith
  have hField :
      magneticFluxDensityInTeslas setup.magneticFieldStrength = 4 / 3 := by
    have h := hLaw.potentialDifferenceFromMovingConductor
    rw [hPotentialSI, hSpeedSI, hThicknessSI] at h
    norm_num at h ⊢
    linarith
  refine ⟨hField, ?_⟩
  intro other hOther
  rw [hField]
  cases other with
  | A =>
      norm_num [recordedDatasetAnswer,
        AnswerChoice.displayedFieldStrengthInTeslas]
  | B => exact (hOther rfl).elim
  | C =>
      norm_num [recordedDatasetAnswer,
        AnswerChoice.displayedFieldStrengthInTeslas]
  | D =>
      norm_num [recordedDatasetAnswer,
        AnswerChoice.displayedFieldStrengthInTeslas]

end PhyXMiniProblems.ProblemPhyXMini0972
