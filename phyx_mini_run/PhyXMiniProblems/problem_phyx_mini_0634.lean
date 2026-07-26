import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Electron velocity selector from a magnetic-deflection measurement

An electron crosses a `3.0 cm` region between parallel plates.  With zero
plate voltage, a `1.0 mT` magnetic field bends its path through a circular arc
whose endpoint is displaced by `2.0 mm`.  The arc geometry determines its
radius, magnetic circular motion determines the electron speed, and a
perpendicular electric field can then cancel the magnetic force.

Physical lengths, mass, charge, speed, field strengths, and potential
differences are represented by Physlib dimensionful quantities.  Real numbers
occur only as coherent SI readouts, primary-figure labels, and displayed
multiple-choice values.  In particular, the required potential difference is
an independent field of the setup and is not defined to equal the recorded
answer.

Assumption/target boundary:

* `MatchesProblemAndFigureData` contains only prose measurements and primary-
  figure readouts.
* `UsesStandardElectronReferenceData` supplies the textbook electron
  charge-to-mass ratio; it does not mention a voltage.
* `SatisfiesCircularArcGeometry`, `IsUniformCrossedFieldArrangement`, and
  `SatisfiesElectronSelectorPhysics` state geometry and governing laws.
* There are no previous-part results.
* The derived `198.88 V` value, its `2 V` proximity to `200 V`, and answer B
  occur only in conclusions and in the table of displayed choices.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0634

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The dimension `M T⁻¹ C⁻¹` of magnetic flux density (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² T⁻² C⁻¹` of an electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative electric-field-strength magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative potential-difference magnitude. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed real-valued dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  signedSIReadout charge

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Tesla readout of a magnetic-flux-density magnitude. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityQuantity) : ℝ :=
  nonnegativeSIReadout field

/-- Volt-per-meter readout of an electric-field-strength magnitude. -/
def electricFieldStrengthInVoltsPerMeter
    (field : ElectricFieldStrengthQuantity) : ℝ :=
  nonnegativeSIReadout field

/-- Volt readout of a potential-difference magnitude. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  nonnegativeSIReadout potentialDifference

/-! ## Spatial directions and primary-figure vocabulary -/

/-- Unit vector in the incoming electron's rightward direction. -/
def rightDirection : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Unit vector toward the bottom of the page. -/
def downwardDirection : EuclideanSpace ℝ (Fin 3) :=
  -EuclideanSpace.single (1 : Fin 3) 1

/-- Unit vector into the page, represented by the crosses in the figure. -/
def intoPageDirection : EuclideanSpace ℝ (Fin 3) :=
  -EuclideanSpace.single (2 : Fin 3) 1

/-- Qualitative directions used by the primary diagram and force arrows. -/
inductive SpatialDirection where
  | right
  | upward
  | downward
  | intoPage
  deriving DecidableEq, Fintype, Repr

/-- The four length expressions explicitly marked on the circular-arc figure. -/
inductive FigureLengthLabel where
  | L
  | deltaY
  | radius
  | radiusMinusDeltaY
  deriving DecidableEq, Fintype, Repr

/-- The electric and magnetic contributions to the force in the final trial. -/
inductive FieldForce where
  | electric
  | magnetic
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and printed information transcribed from image 634.  The image
prints `L = 3.0 cm` but leaves `Δy` symbolic; the numerical `2.0 mm` deflection
therefore remains a prose datum in `MatchesProblemAndFigureData`.
-/
structure MagneticDeflectionFigure where
  particleCarriesMinusSign : Bool
  incomingParticleDirection : SpatialDirection
  magneticFieldDirection : SpatialDirection
  deflectedPathDirection : SpatialDirection
  magneticFieldShownByCrosses : Bool
  parallelPlatePairShown : Bool
  circularArcLabelShown : Bool
  lengthLabelShown : FigureLengthLabel → Bool
  printedLInCentimeters : ℝ
  centerOfCircleMarked : Bool
  centerBelowEntryPath : Bool

/-! ## Physical setup -/

/-!
The physical quantities for the deflection trial and the final balancing
trial.  The actual electric and magnetic fields retain Physlib's spacetime-
dependent field types; the separately stored dimensionful magnitudes are their
coherent SI calibrations.  `requiredPotentialDifference` is independent data
until the governing laws constrain it.
-/
structure ElectronVelocitySelectorSetup where
  figure : MagneticDeflectionFigure
  plateSeparation : LengthQuantity
  plateLength : LengthQuantity
  magneticRegionWidth : LengthQuantity
  magneticRegionOverlapsElectrodes : Bool
  magneticFluxDensityMagnitude : MagneticFluxDensityQuantity
  deflectionTrialPotentialDifference : PotentialDifferenceQuantity
  zeroVoltageVerticalDeflection : LengthQuantity
  circularArcRadius : LengthQuantity
  electronMass : MassQuantity
  electronCharge : SignedChargeQuantity
  electronSpeed : DimSpeed
  balancingElectricFieldStrength : ElectricFieldStrengthQuantity
  requiredPotentialDifference : PotentialDifferenceQuantity
  appliedMagneticField : Electromagnetism.MagneticField 3
  balancingElectricField : Electromagnetism.ElectricField 3
  balancingForceDirection : FieldForce → SpatialDirection

/-! ## Source data, figure readouts, and standard electron data -/

/-!
All numerical measurements stated in the prose and all qualitative labels read
from the primary image.  Neither the final potential difference nor an answer
choice appears here.
-/
structure MatchesProblemAndFigureData
    (setup : ElectronVelocitySelectorSetup) : Prop where
  plateSeparationMeters : lengthInMeters setup.plateSeparation = 5 / 1000
  plateLengthMeters : lengthInMeters setup.plateLength = 3 / 100
  magneticRegionWidthMeters :
    lengthInMeters setup.magneticRegionWidth = 3 / 100
  fieldOverlapsElectrodes : setup.magneticRegionOverlapsElectrodes = true
  magneticFluxDensityTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 1 / 1000
  deflectionTrialUsesZeroVolts :
    potentialDifferenceInVolts
        setup.deflectionTrialPotentialDifference = 0
  observedVerticalDeflectionMeters :
    lengthInMeters setup.zeroVoltageVerticalDeflection = 2 / 1000
  electronShownWithMinusSign : setup.figure.particleCarriesMinusSign = true
  incomingElectronPointsRight :
    setup.figure.incomingParticleDirection = .right
  magneticFieldPointsIntoPage :
    setup.figure.magneticFieldDirection = .intoPage
  circularArcDeflectsDownward :
    setup.figure.deflectedPathDirection = .downward
  fieldIsDepictedByCrosses :
    setup.figure.magneticFieldShownByCrosses = true
  bothParallelPlatesAreShown : setup.figure.parallelPlatePairShown = true
  pathIsLabeledCircularArc : setup.figure.circularArcLabelShown = true
  allFourGeometricLengthsAreLabeled :
    ∀ label, setup.figure.lengthLabelShown label = true
  printedHorizontalLengthCentimeters :
    setup.figure.printedLInCentimeters = 3
  centerOfCircleIsMarked : setup.figure.centerOfCircleMarked = true
  centerLiesBelowEntryPath : setup.figure.centerBelowEntryPath = true

/-!
The standard textbook magnitude-to-mass ratio `|qₑ|/mₑ = 1.76 × 10¹¹ C/kg`
and the electron's negative sign.  This external reference datum does not
mention the balancing field or voltage.
-/
structure UsesStandardElectronReferenceData
    (setup : ElectronVelocitySelectorSetup) : Prop where
  electronChargeIsNegative : chargeInCoulombs setup.electronCharge < 0
  chargeMagnitudeToMassRatio :
    |chargeInCoulombs setup.electronCharge| /
        massInKilograms setup.electronMass = 1.76 * 10 ^ 11

/-- Positivity and nondegeneracy conditions for the physical magnitudes. -/
structure HasPhysicalElectronSelectorParameters
    (setup : ElectronVelocitySelectorSetup) : Prop where
  positivePlateSeparation : 0 < lengthInMeters setup.plateSeparation
  positiveMagneticRegionWidth :
    0 < lengthInMeters setup.magneticRegionWidth
  positiveObservedDeflection :
    0 < lengthInMeters setup.zeroVoltageVerticalDeflection
  positiveCircularRadius : 0 < lengthInMeters setup.circularArcRadius
  deflectionSmallerThanRadius :
    lengthInMeters setup.zeroVoltageVerticalDeflection <
      lengthInMeters setup.circularArcRadius
  positiveElectronMass : 0 < massInKilograms setup.electronMass
  nonzeroElectronCharge : chargeInCoulombs setup.electronCharge ≠ 0
  positiveElectronSpeed : 0 < speedInMetersPerSecond setup.electronSpeed
  positiveMagneticFluxDensity :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude

/-! ## Geometry and governing physical laws -/

/-!
The Pythagorean relation visible in the figure: the horizontal leg is `L`, the
vertical leg is `r - Δy`, and the hypotenuse is the circular radius `r`.
-/
structure SatisfiesCircularArcGeometry
    (setup : ElectronVelocitySelectorSetup) : Prop where
  pythagoreanRadiusRelation :
    lengthInMeters setup.circularArcRadius ^ 2 =
      lengthInMeters setup.magneticRegionWidth ^ 2 +
        (lengthInMeters setup.circularArcRadius -
          lengthInMeters setup.zeroVoltageVerticalDeflection) ^ 2

/-!
The uniform crossed-field arrangement.  Physlib field vectors are interpreted
as tesla and volt-per-meter coordinate readouts, while the dimensionful scalar
quantities supply their physical magnitudes.
-/
structure IsUniformCrossedFieldArrangement
    (setup : ElectronVelocitySelectorSetup) : Prop where
  magneticFieldUniformAndIntoPage :
    ∀ spacetimeTime position,
      setup.appliedMagneticField spacetimeTime position =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude •
          intoPageDirection
  electricFieldUniformAndDownward :
    ∀ spacetimeTime position,
      setup.balancingElectricField spacetimeTime position =
        electricFieldStrengthInVoltsPerMeter
            setup.balancingElectricFieldStrength • downwardDirection
  fieldsArePerpendicular :
    inner ℝ downwardDirection intoPageDirection = 0

/-!
Magnitude forms of the governing relations:

* magnetic Lorentz force supplies the centripetal force,
  `m v²/r = |q| v B`;
* a uniform parallel-plate field obeys `E = ΔV/d`;
* no deflection requires equal electric and magnetic force magnitudes,
  `|q|E = |q|vB`, with opposite directions.

These are general physical laws applied to independent setup quantities, not a
substituted numerical answer.
-/
structure SatisfiesElectronSelectorPhysics
    (setup : ElectronVelocitySelectorSetup) : Prop where
  magneticCircularMotionLaw :
    massInKilograms setup.electronMass *
          speedInMetersPerSecond setup.electronSpeed ^ 2 /
        lengthInMeters setup.circularArcRadius =
      |chargeInCoulombs setup.electronCharge| *
        speedInMetersPerSecond setup.electronSpeed *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  parallelPlateFieldLaw :
    electricFieldStrengthInVoltsPerMeter
        setup.balancingElectricFieldStrength =
      potentialDifferenceInVolts setup.requiredPotentialDifference /
        lengthInMeters setup.plateSeparation
  noDeflectionForceBalance :
    |chargeInCoulombs setup.electronCharge| *
        electricFieldStrengthInVoltsPerMeter
          setup.balancingElectricFieldStrength =
      |chargeInCoulombs setup.electronCharge| *
        speedInMetersPerSecond setup.electronSpeed *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  magneticForcePointsDownward :
    setup.balancingForceDirection .magnetic = .downward
  electricForcePointsUpward :
    setup.balancingForceDirection .electric = .upward

/-! ## Displayed choices and derived target -/

/-- Labels of the four potential-difference choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Voltage printed beside each answer label. -/
def displayedPotentialDifferenceInVolts : AnswerChoice → ℝ
  | .A => 150
  | .B => 200
  | .C => 250
  | .D => 300

/-!
A displayed choice is closest when its printed voltage is at least as close to
the computed physical voltage as every alternative.
-/
def IsClosestDisplayedPotentialDifference
    (potentialDifference : PotentialDifferenceQuantity)
    (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |potentialDifferenceInVolts potentialDifference -
        displayedPotentialDifferenceInVolts choice| ≤
      |potentialDifferenceInVolts potentialDifference -
        displayedPotentialDifferenceInVolts alternative|

/-!
The circle geometry gives `r = (L² + Δy²)/(2 Δy)`.  This is a derived
intermediate relation and is not present in any premise structure.
-/
lemma circularArcRadius_from_observedDeflection
    (setup : ElectronVelocitySelectorSetup)
    (hPhysical : HasPhysicalElectronSelectorParameters setup)
    (hGeometry : SatisfiesCircularArcGeometry setup) :
    lengthInMeters setup.circularArcRadius =
      (lengthInMeters setup.magneticRegionWidth ^ 2 +
          lengthInMeters setup.zeroVoltageVerticalDeflection ^ 2) /
        (2 * lengthInMeters setup.zeroVoltageVerticalDeflection) := by
  have hDenominator :
      2 * lengthInMeters setup.zeroVoltageVerticalDeflection ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (ne_of_gt hPhysical.positiveObservedDeflection)
  apply (eq_div_iff hDenominator).2
  nlinarith [hGeometry.pythagoreanRadiusRelation]

/-!
Combining magnetic circular motion, force balance, and the plate-field law
gives `ΔV = (|q|/m) B² r d`.  This symbolic voltage relation is derived rather
than assumed.
-/
lemma requiredPotentialDifference_formula
    (setup : ElectronVelocitySelectorSetup)
    (hPhysical : HasPhysicalElectronSelectorParameters setup)
    (hPhysics : SatisfiesElectronSelectorPhysics setup) :
    potentialDifferenceInVolts setup.requiredPotentialDifference =
      (|chargeInCoulombs setup.electronCharge| /
          massInKilograms setup.electronMass) *
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude ^ 2 *
          lengthInMeters setup.circularArcRadius *
            lengthInMeters setup.plateSeparation := by
  have hRadiusNe : lengthInMeters setup.circularArcRadius ≠ 0 :=
    ne_of_gt hPhysical.positiveCircularRadius
  have hSpeedNe : speedInMetersPerSecond setup.electronSpeed ≠ 0 :=
    ne_of_gt hPhysical.positiveElectronSpeed
  have hMassNe : massInKilograms setup.electronMass ≠ 0 :=
    ne_of_gt hPhysical.positiveElectronMass
  have hSeparationNe : lengthInMeters setup.plateSeparation ≠ 0 :=
    ne_of_gt hPhysical.positivePlateSeparation
  have hChargeMagnitudeNe :
      |chargeInCoulombs setup.electronCharge| ≠ 0 :=
    abs_ne_zero.mpr hPhysical.nonzeroElectronCharge
  have hMagneticMotion :
      massInKilograms setup.electronMass *
          speedInMetersPerSecond setup.electronSpeed ^ 2 =
        |chargeInCoulombs setup.electronCharge| *
            speedInMetersPerSecond setup.electronSpeed *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
            lengthInMeters setup.circularArcRadius :=
    (div_eq_iff hRadiusNe).mp hPhysics.magneticCircularMotionLaw
  have hMagneticMotionFactored :
      speedInMetersPerSecond setup.electronSpeed *
          (massInKilograms setup.electronMass *
            speedInMetersPerSecond setup.electronSpeed) =
        speedInMetersPerSecond setup.electronSpeed *
          (|chargeInCoulombs setup.electronCharge| *
            magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
              lengthInMeters setup.circularArcRadius) := by
    calc
      speedInMetersPerSecond setup.electronSpeed *
            (massInKilograms setup.electronMass *
              speedInMetersPerSecond setup.electronSpeed) =
          massInKilograms setup.electronMass *
            speedInMetersPerSecond setup.electronSpeed ^ 2 := by ring
      _ = |chargeInCoulombs setup.electronCharge| *
              speedInMetersPerSecond setup.electronSpeed *
            magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
              lengthInMeters setup.circularArcRadius :=
        hMagneticMotion
      _ = speedInMetersPerSecond setup.electronSpeed *
          (|chargeInCoulombs setup.electronCharge| *
            magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
              lengthInMeters setup.circularArcRadius) := by ring
  have hSpeedRelation :
      massInKilograms setup.electronMass *
          speedInMetersPerSecond setup.electronSpeed =
        |chargeInCoulombs setup.electronCharge| *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
            lengthInMeters setup.circularArcRadius :=
    mul_left_cancel₀ hSpeedNe hMagneticMotionFactored
  have hSpeedFormula :
      speedInMetersPerSecond setup.electronSpeed =
        (|chargeInCoulombs setup.electronCharge| *
            magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthInMeters setup.circularArcRadius) /
            massInKilograms setup.electronMass := by
    apply (eq_div_iff hMassNe).2
    simpa [mul_comm] using hSpeedRelation
  have hForceBalanceFactored :
      |chargeInCoulombs setup.electronCharge| *
          electricFieldStrengthInVoltsPerMeter
            setup.balancingElectricFieldStrength =
        |chargeInCoulombs setup.electronCharge| *
          (speedInMetersPerSecond setup.electronSpeed *
            magneticFluxDensityInTeslas
              setup.magneticFluxDensityMagnitude) := by
    simpa [mul_assoc] using hPhysics.noDeflectionForceBalance
  have hFieldStrength :
      electricFieldStrengthInVoltsPerMeter
          setup.balancingElectricFieldStrength =
        speedInMetersPerSecond setup.electronSpeed *
          magneticFluxDensityInTeslas
            setup.magneticFluxDensityMagnitude :=
    mul_left_cancel₀ hChargeMagnitudeNe hForceBalanceFactored
  have hPlateField :
      electricFieldStrengthInVoltsPerMeter
            setup.balancingElectricFieldStrength *
          lengthInMeters setup.plateSeparation =
        potentialDifferenceInVolts setup.requiredPotentialDifference :=
    (eq_div_iff hSeparationNe).mp hPhysics.parallelPlateFieldLaw
  calc
    potentialDifferenceInVolts setup.requiredPotentialDifference =
        electricFieldStrengthInVoltsPerMeter
            setup.balancingElectricFieldStrength *
          lengthInMeters setup.plateSeparation := hPlateField.symm
    _ = (speedInMetersPerSecond setup.electronSpeed *
          magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude) *
        lengthInMeters setup.plateSeparation := by rw [hFieldStrength]
    _ = (|chargeInCoulombs setup.electronCharge| /
          massInKilograms setup.electronMass) *
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude ^ 2 *
          lengthInMeters setup.circularArcRadius *
            lengthInMeters setup.plateSeparation := by
      rw [hSpeedFormula]
      ring

/-!
Blueprint: `thm:physics:phyx_mini_0634:target`.

The measured arc gives `r = 0.226 m`; using the textbook electron
charge-to-mass ratio then gives `ΔV = 198.88 V`.  This is within `2 V` of the
displayed `200 V` and is closer to choice B than to every other choice.
-/
theorem requiredPotentialDifference_matches_choiceB
    (setup : ElectronVelocitySelectorSetup)
    (hData : MatchesProblemAndFigureData setup)
    (hElectron : UsesStandardElectronReferenceData setup)
    (hPhysical : HasPhysicalElectronSelectorParameters setup)
    (hGeometry : SatisfiesCircularArcGeometry setup)
    (hFields : IsUniformCrossedFieldArrangement setup)
    (hPhysics : SatisfiesElectronSelectorPhysics setup) :
    lengthInMeters setup.circularArcRadius = 113 / 500 ∧
      potentialDifferenceInVolts setup.requiredPotentialDifference =
        4972 / 25 ∧
      |potentialDifferenceInVolts setup.requiredPotentialDifference -
          displayedPotentialDifferenceInVolts .B| ≤ 2 ∧
      displayedPotentialDifferenceInVolts .B = 200 ∧
      IsClosestDisplayedPotentialDifference
        setup.requiredPotentialDifference .B := by
  have hRadius :=
    circularArcRadius_from_observedDeflection setup hPhysical hGeometry
  rw [hData.magneticRegionWidthMeters,
    hData.observedVerticalDeflectionMeters] at hRadius
  norm_num at hRadius
  have hVoltage :=
    requiredPotentialDifference_formula setup hPhysical hPhysics
  rw [hElectron.chargeMagnitudeToMassRatio,
    hData.magneticFluxDensityTeslas, hRadius,
    hData.plateSeparationMeters] at hVoltage
  norm_num at hVoltage
  refine ⟨hRadius, hVoltage, ?_, rfl, ?_⟩
  · rw [hVoltage]
    norm_num [displayedPotentialDifferenceInVolts]
  · intro alternative
    rw [hVoltage]
    cases alternative <;> norm_num [displayedPotentialDifferenceInVolts]

end PhyXMiniProblems.ProblemPhyXMini0634
