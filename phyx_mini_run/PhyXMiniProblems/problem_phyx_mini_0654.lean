import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0654

open Dimension

/-!
# Quantum escape estimate for a dust speck in a frictionless trough

A dust speck of mass `1.0 * 10^-13 g` appears at rest at the bottom of the
smooth trough in the supplied raster.  The trough is `10 μm` wide, and the
particular illustrated depth is `1.0 μm`.  The question asks for the deepest
trough of that width from which quantum localization gives the speck a good
chance to escape.

The physical model below keeps mass, length, momentum, action, acceleration,
and energy dimensionful.  Scalar real numbers occur only at named-unit or
coherent-SI readout boundaries and as dimensionless probabilities.  The
deepest good-chance depth is an independent field, not a definition involving
the recorded answer.

The customary order-of-magnitude estimate models the width as the position
uncertainty, saturates `Δx * Δp = ℏ / 2`, converts the momentum spread to
kinetic energy, and balances it against `m g h`.  With the literal data this
predicts a depth near `1.42 * 10^-28 m`, whereas every displayed option has
exponent `10^-27 m`.  Following the project retry protocol, choice C is kept
only as dataset metadata.  The main theorem states the physically supported
depth interval and records that A, although still an order of magnitude too
large, is the uniquely nearest displayed choice.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- Momentum has physical dimension mass times length per time. -/
def momentumDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹

/-- Action has physical dimension mass times length squared per time. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- Acceleration has physical dimension length per time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent momentum-spread magnitude. -/
abbrev MomentumMagnitude : Type :=
  Dimensionful (WithDim momentumDimension NNReal)

/-- A signed, unit-independent mean momentum along the trough. -/
abbrev SignedMomentumQuantity : Type :=
  Dimensionful (WithDim momentumDimension ℝ)

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout
    (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in micrometres. -/
def lengthInMicrometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.micrometers length

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Read a physical mass in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Read a momentum-spread magnitude in kilogram-metres per second. -/
def momentumMagnitudeInKilogramMetersPerSecond
    (momentum : MomentumMagnitude) : ℝ :=
  nonnegativeSIReadout momentum

/-- Read a signed mean momentum in kilogram-metres per second. -/
def signedMomentumInKilogramMetersPerSecond
    (momentum : SignedMomentumQuantity) : ℝ :=
  (momentum UnitChoices.SI).val

/-- Read a physical action in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  nonnegativeSIReadout action

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Read a physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Scenario, figure vocabulary, and independent physical setup -/

/-- The kind of object shown by the dot in the trough. -/
inductive ObjectKind where
  | dustSpeck
  | other
  deriving DecidableEq, Repr

/-- Cross-sectional shape of the hole in the supplied image. -/
inductive HoleCrossSectionShape where
  | smoothSymmetricTrough
  | other
  deriving DecidableEq, Repr

/-- Location of the particle marker in the trough cross-section. -/
inductive MarkerLocation where
  | bottomCenter
  | other
  deriving DecidableEq, Repr

/-- Length unit printed after a scalar in the raster. -/
inductive FigureLengthUnit where
  | micrometer
  | other
  deriving DecidableEq, Repr

/-!
Primary-raster evidence.  The printed depth is the depth of the illustrated
trough, not the much smaller threshold depth asked for in the question.
-/
structure SuppliedDustHoleFigure where
  crossSectionShape : HoleCrossSectionShape
  particleMarkerLocation : MarkerLocation
  smoothWallsShown : Bool
  widthDoubleArrowShown : Bool
  depthDoubleArrowShown : Bool
  frictionlessSurfaceLabelShown : Bool
  printedWidthValue : ℝ
  printedWidthUnit : FigureLengthUnit
  printedIllustratedDepthValue : ℝ
  printedIllustratedDepthUnit : FigureLengthUnit

/-!
Independent physical data for the confinement-and-escape estimate.  In
particular, neither `deepestGoodChanceEscapeDepth` nor `escapeProbability` is
defined from the answer choices or from a closed-form expression.
-/
structure DustHoleEscapeSetup where
  objectKind : ObjectKind
  dustMass : MassQuantity
  holeWidth : LengthQuantity
  illustratedHoleDepth : LengthQuantity
  deepestGoodChanceEscapeDepth : LengthQuantity
  appearsAtRest : Bool
  meanMomentumAlongTrough : SignedMomentumQuantity
  positionUncertaintyAlongTrough : LengthQuantity
  momentumUncertaintyAlongTrough : MomentumMagnitude
  reducedPlanckAction : ActionQuantity
  confinementKineticEnergy : DimEnergy
  localGravitationalAcceleration : AccelerationQuantity
  gravitationalPotentialEnergy : LengthQuantity → DimEnergy
  escapeProbability : LengthQuantity → Set.Icc (0 : ℝ) 1
  figure : SuppliedDustHoleFigure

/-! ## Source readouts, figure evidence, and physical laws -/

/-- Qualitative facts stated in the problem prose. -/
structure MatchesDustSpeckScenario
    (setup : DustHoleEscapeSetup) : Prop where
  objectIsDustSpeck : setup.objectKind = .dustSpeck
  speckAppearsAtRest : setup.appearsAtRest = true
  vanishingObservedMeanMomentum :
    signedMomentumInKilogramMetersPerSecond
      setup.meanMomentumAlongTrough = 0

/-- The mass and width stated by the problem, plus the image's illustrated depth. -/
structure MatchesProblemReadouts
    (setup : DustHoleEscapeSetup) : Prop where
  dustMassIsOneTimesTenToMinusThirteenGrams :
    massInGrams setup.dustMass = 1 / (10 : ℝ) ^ 13
  holeWidthIsTenMicrometers :
    lengthInMicrometers setup.holeWidth = 10
  illustratedDepthIsOneMicrometer :
    lengthInMicrometers setup.illustratedHoleDepth = 1

/-- Labels, arrows, geometry, and marker placement verified in image 654. -/
structure MatchesSuppliedDustHoleFigure
    (setup : DustHoleEscapeSetup) : Prop where
  crossSectionIsSmoothSymmetricTrough :
    setup.figure.crossSectionShape = .smoothSymmetricTrough
  markerIsAtBottomCenter :
    setup.figure.particleMarkerLocation = .bottomCenter
  smoothWallsAreShown : setup.figure.smoothWallsShown = true
  widthArrowIsShown : setup.figure.widthDoubleArrowShown = true
  depthArrowIsShown : setup.figure.depthDoubleArrowShown = true
  frictionlessLabelIsShown :
    setup.figure.frictionlessSurfaceLabelShown = true
  printedWidthIsTenMicrometers :
    setup.figure.printedWidthValue = 10 ∧
      setup.figure.printedWidthUnit = .micrometer
  printedDepthIsOneMicrometer :
    setup.figure.printedIllustratedDepthValue = 1 ∧
      setup.figure.printedIllustratedDepthUnit = .micrometer
  printedWidthMatchesPhysicalWidth :
    setup.figure.printedWidthValue =
      lengthInMicrometers setup.holeWidth
  printedDepthMatchesIllustratedDepth :
    setup.figure.printedIllustratedDepthValue =
      lengthInMicrometers setup.illustratedHoleDepth

/-- Standard coherent-SI reference data used by the estimate. -/
structure UsesStandardQuantumAndGravityData
    (setup : DustHoleEscapeSetup) : Prop where
  reducedPlanckConstantCalibration :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)
  standardGravitationalAcceleration :
    accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration = 9.80665

/-- Positivity and probability conditions selecting a physical setup. -/
structure HasPhysicalDustHoleParameters
    (setup : DustHoleEscapeSetup) : Prop where
  positiveDustMass : 0 < massInKilograms setup.dustMass
  positiveHoleWidth : 0 < lengthInMeters setup.holeWidth
  positiveIllustratedDepth :
    0 < lengthInMeters setup.illustratedHoleDepth
  positiveDeepestGoodChanceDepth :
    0 < lengthInMeters setup.deepestGoodChanceEscapeDepth
  positivePositionUncertainty :
    0 < lengthInMeters setup.positionUncertaintyAlongTrough
  positiveMomentumUncertainty :
    0 < momentumMagnitudeInKilogramMetersPerSecond
      setup.momentumUncertaintyAlongTrough
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  positiveGravitationalAcceleration :
    0 < accelerationInMetersPerSecondSquared
      setup.localGravitationalAcceleration
  nonnegativeConfinementKineticEnergy :
    0 ≤ energyInJoules setup.confinementKineticEnergy

/-!
The characteristic good-chance estimate treats the hole width as the
position-localization scale and saturates the Heisenberg lower bound.
This is a general relation among independently stored physical quantities;
it contains no depth or answer-choice numeral.
-/
structure SatisfiesMinimumUncertaintyLocalizationEstimate
    (setup : DustHoleEscapeSetup) : Prop where
  positionUncertaintyIsHoleWidth :
    lengthInMeters setup.positionUncertaintyAlongTrough =
      lengthInMeters setup.holeWidth
  saturatedPositionMomentumRelation :
    lengthInMeters setup.positionUncertaintyAlongTrough *
        momentumMagnitudeInKilogramMetersPerSecond
          setup.momentumUncertaintyAlongTrough =
      actionInJouleSeconds setup.reducedPlanckAction / 2

/-!
The momentum spread supplies kinetic energy `Δp² / (2m)`, while climbing a
vertical height `h` costs gravitational potential energy `m g h`.
-/
structure SatisfiesKineticAndGravitationalEnergyLaws
    (setup : DustHoleEscapeSetup) : Prop where
  momentumSpreadKineticEnergy :
    energyInJoules setup.confinementKineticEnergy =
      momentumMagnitudeInKilogramMetersPerSecond
          setup.momentumUncertaintyAlongTrough ^ 2 /
        (2 * massInKilograms setup.dustMass)
  gravitationalPotentialEnergyLaw : ∀ depth : LengthQuantity,
    energyInJoules (setup.gravitationalPotentialEnergy depth) =
      massInKilograms setup.dustMass *
        accelerationInMetersPerSecondSquared
          setup.localGravitationalAcceleration *
        lengthInMeters depth

/-- The dimensionless probability threshold used to mean “a good chance.” -/
def goodChanceProbabilityThreshold : ℝ := 1 / 2

/-!
At the deepest good-chance boundary the confinement kinetic-energy scale
equals the gravitational barrier energy.  The independent probability
observable is at least one half there, and is below one half for every deeper
trough.  Thus maximality is stated physically rather than defined by the
requested answer.
-/
structure SatisfiesGoodChanceEscapeBoundary
    (setup : DustHoleEscapeSetup) : Prop where
  boundaryEnergyBalance :
    setup.confinementKineticEnergy =
      setup.gravitationalPotentialEnergy
        setup.deepestGoodChanceEscapeDepth
  goodChanceAtBoundary :
    goodChanceProbabilityThreshold ≤
      (setup.escapeProbability setup.deepestGoodChanceEscapeDepth : ℝ)
  everyDeeperHoleIsBelowThreshold : ∀ depth : LengthQuantity,
    lengthInMeters setup.deepestGoodChanceEscapeDepth <
        lengthInMeters depth →
      (setup.escapeProbability depth : ℝ) <
        goodChanceProbabilityThreshold

/-! ## Derived estimate, answer metadata, and physically supported target -/

/-- Labels of the four depth choices printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal metre values printed beside the answer choices. -/
def displayedDepthInMeters : AnswerChoice → ℝ
  | .A => 1 / (10 : ℝ) ^ 27
  | .B => 12 / (10 : ℝ) ^ 28
  | .C => 14 / (10 : ℝ) ^ 28
  | .D => 16 / (10 : ℝ) ^ 28

/-- Dataset answer label retained as metadata, never used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice is strictly nearer to the modeled depth than every other choice. -/
def IsUniqueNearestDisplayedDepth
    (depth : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters depth - displayedDepthInMeters choice| <
      |lengthInMeters depth - displayedDepthInMeters other|

/-!
The general localization, kinetic-energy, gravitational-energy, and boundary
laws imply the coherent-SI estimate

`h = ℏ² / (8 m² g w²)`.

This helper conclusion contains no problem-specific mass, width, or answer
value.
-/
lemma deepestGoodChanceEscapeDepth_formula
    (setup : DustHoleEscapeSetup)
    (h_physical : HasPhysicalDustHoleParameters setup)
    (h_localization :
      SatisfiesMinimumUncertaintyLocalizationEstimate setup)
    (h_energy : SatisfiesKineticAndGravitationalEnergyLaws setup)
    (h_boundary : SatisfiesGoodChanceEscapeBoundary setup) :
    lengthInMeters setup.deepestGoodChanceEscapeDepth =
      actionInJouleSeconds setup.reducedPlanckAction ^ 2 /
        (8 * massInKilograms setup.dustMass ^ 2 *
          accelerationInMetersPerSecondSquared
            setup.localGravitationalAcceleration *
          lengthInMeters setup.holeWidth ^ 2) := by
  have h_balance :=
    congrArg energyInJoules h_boundary.boundaryEnergyBalance
  rw [h_energy.momentumSpreadKineticEnergy,
    h_energy.gravitationalPotentialEnergyLaw] at h_balance
  have h_uncertainty :=
    h_localization.saturatedPositionMomentumRelation
  rw [h_localization.positionUncertaintyIsHoleWidth] at h_uncertainty
  have h_mass_ne :
      massInKilograms setup.dustMass ≠ 0 :=
    ne_of_gt h_physical.positiveDustMass
  have h_gravity_ne :
      accelerationInMetersPerSecondSquared
          setup.localGravitationalAcceleration ≠ 0 :=
    ne_of_gt h_physical.positiveGravitationalAcceleration
  have h_width_ne :
      lengthInMeters setup.holeWidth ≠ 0 :=
    ne_of_gt h_physical.positiveHoleWidth
  have h_uncertainty_twice :
      2 * (lengthInMeters setup.holeWidth *
        momentumMagnitudeInKilogramMetersPerSecond
          setup.momentumUncertaintyAlongTrough) =
        actionInJouleSeconds setup.reducedPlanckAction := by
    linarith
  have h_uncertainty_sq :=
    congrArg (fun z : ℝ => z ^ 2) h_uncertainty_twice
  field_simp [h_mass_ne] at h_balance
  field_simp [h_mass_ne, h_gravity_ne, h_width_ne]
  nlinarith

/-!
This is the physically supported conclusion for
`thm:physics:phyx_mini_0654:target`.  With the literal mass, width, calibrated
`ℏ`, standard gravity, and the governing laws above, the deepest good-chance
depth lies between `1.41 * 10^-28 m` and `1.42 * 10^-28 m`.  Since all printed
choices are of order `10^-27 m`, A is merely the uniquely nearest displayed
choice; the recorded C label is not asserted by the theorem and is not used as
a premise.
-/
theorem problem_phyx_mini_0654
    (setup : DustHoleEscapeSetup)
    (h_scenario : MatchesDustSpeckScenario setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedDustHoleFigure setup)
    (h_reference : UsesStandardQuantumAndGravityData setup)
    (h_physical : HasPhysicalDustHoleParameters setup)
    (h_localization :
      SatisfiesMinimumUncertaintyLocalizationEstimate setup)
    (h_energy : SatisfiesKineticAndGravitationalEnergyLaws setup)
    (h_boundary : SatisfiesGoodChanceEscapeBoundary setup) :
    lengthInMeters setup.deepestGoodChanceEscapeDepth ∈
        Set.Icc (141 / (10 : ℝ) ^ 30) (142 / (10 : ℝ) ^ 30) ∧
      IsUniqueNearestDisplayedDepth
        setup.deepestGoodChanceEscapeDepth .A := by
  have h_mass_conversion :
      massInGrams setup.dustMass =
        1000 * massInKilograms setup.dustMass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.dustMass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, massReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have h_mass_readout :=
    h_readouts.dustMassIsOneTimesTenToMinusThirteenGrams
  rw [h_mass_conversion] at h_mass_readout
  have h_mass :
      massInKilograms setup.dustMass = 1 / (10 : ℝ) ^ 16 := by
    norm_num at h_mass_readout ⊢
    linarith
  have h_length_conversion (length : LengthQuantity) :
      lengthInMicrometers length =
        1000000 * lengthInMeters length := by
    change
      ((length
          {UnitChoices.SI with length := LengthUnit.micrometers}).val : ℝ) =
        1000000 * ((length UnitChoices.SI).val : ℝ)
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.micrometers}]
    change
      (↑(UnitChoices.dimScale UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.micrometers} L𝓭) : ℝ) *
          ((length UnitChoices.SI).val : ℝ) =
        1000000 * ((length UnitChoices.SI).val : ℝ)
    congr 1
    norm_num [UnitChoices.dimScale, UnitChoices.SI,
      LengthUnit.micrometers, LengthUnit.scale,
      LengthUnit.div_eq_val, LengthUnit.meters]
    rfl
  have h_width_readout := h_readouts.holeWidthIsTenMicrometers
  rw [h_length_conversion] at h_width_readout
  have h_width :
      lengthInMeters setup.holeWidth = 1 / (10 : ℝ) ^ 5 := by
    norm_num at h_width_readout ⊢
    linarith
  have h_depth :=
    deepestGoodChanceEscapeDepth_formula setup h_physical
      h_localization h_energy h_boundary
  rw [h_reference.reducedPlanckConstantCalibration, h_mass,
    h_reference.standardGravitationalAcceleration, h_width] at h_depth
  norm_num [Constants.ℏ] at h_depth
  refine ⟨?_, ?_⟩
  · constructor
    · rw [h_depth]
      norm_num
    · rw [h_depth]
      norm_num
  · rw [IsUniqueNearestDisplayedDepth]
    intro other h_other
    rw [h_depth]
    cases other with
    | A => exact (h_other rfl).elim
    | B => norm_num [displayedDepthInMeters]
    | C => norm_num [displayedDepthInMeters]
    | D => norm_num [displayedDepthInMeters]

end PhyXMiniProblems.ProblemPhyXMini0654
