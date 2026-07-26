import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0711

open Dimension
open scoped BigOperators

/-!
# Rotation frequency of two masses on an expanding rod

Two equal endpoint masses rotate on a massless rod about an axis through the
rod's midpoint.  Compressed gas changes the rod length from `50 cm` to
`160 cm`; the initial rotation frequency is `2 rev/s`.  With no external
torque about the axis, angular momentum is conserved.

Physical mass, length, rotation frequency, moment of inertia, and angular
momentum are unit-independent Physlib `Dimensionful` quantities.  Real
numbers occur only as named-unit readouts, schematic pixel data, and displayed
multiple-choice values.  In particular, the unknown final frequency is an
independent field constrained by the governing laws rather than defined from
the answer.

Assumption/target split:

* governing laws: centered endpoint geometry, point-mass moment of inertia,
  `L = I (2 pi f)`, endpoint decomposition, and angular-momentum conservation
  in the absence of external torque;
* previous-part results: none;
* figure/data readouts: the two equal masses, massless rod, midpoint axis,
  gas-driven expansion, `50 cm`, `160 cm`, `2 rev/s`, and the labels and
  arrows in the before/after raster;
* target conclusions: the exact final frequency `25 / 128 rev/s`, agreement
  to two decimal places with `0.20 rev/s`, and selection of choice C.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- Rotation frequency has inverse-time dimension; one cycle is one revolution. -/
def rotationFrequencyDimension : Dimension := T𝓭⁻¹

/-- A moment of inertia has dimension mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- Angular momentum has dimension mass times length squared per time. -/
def angularMomentumDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative ordinary rotation frequency, measured in revolutions per time. -/
abbrev RotationFrequencyQuantity : Type :=
  Dimensionful (WithDim rotationFrequencyDimension NNReal)

/-- A nonnegative scalar moment of inertia about the displayed rotation axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative angular-momentum magnitude along the displayed upward axis. -/
abbrev AngularMomentumMagnitude : Type :=
  Dimensionful (WithDim angularMomentumDimension NNReal)

/-- Read a physical mass in the selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/--
Read ordinary rotation frequency in revolutions per selected time unit.  The
dimensionless cycle counted by this readout is fixed to mean one revolution.
-/
def rotationFrequencyReadout
    (timeUnit : TimeUnit) (frequency : RotationFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read a moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read angular momentum in coherent selected mechanical units. -/
def angularMomentumReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (angularMomentum : AngularMomentumMagnitude) : ℝ :=
  ((angularMomentum {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Centimetre readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Revolutions-per-second readout of an ordinary rotation frequency. -/
def frequencyInRevolutionsPerSecond
    (frequency : RotationFrequencyQuantity) : ℝ :=
  rotationFrequencyReadout TimeUnit.seconds frequency

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two configurations shown in the panels labelled `Before` and `After`. -/
inductive Configuration where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- The two material spheres labelled `1` and `2` in both panels. -/
inductive EndpointMass where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- The idealized contribution of the connecting rod to the mass distribution. -/
inductive RodMassModel where
  | massless
  | massive
  deriving DecidableEq, Repr

/-- The mechanism stated to change the rod length. -/
inductive ExpansionMechanism where
  | compressedGas
  | other
  deriving DecidableEq, Repr

/-- Relation of the fixed rotation axis to the straight rod. -/
inductive RotationAxisGeometry where
  | throughRodMidpointPerpendicularToRotationPlane
  | other
  deriving DecidableEq, Repr

/-- Literal labels visible in image `711.png`. -/
inductive FigureLabel where
  | beforePanel
  | afterPanel
  | endpointOne
  | endpointTwo
  | initialOmega
  | finalOmega
  | initialLengthLi
  | finalLengthLf
  | initialMomentumP1i
  | initialMomentumP2i
  | finalMomentumP1f
  | finalMomentumP2f
  | initialTotalAngularMomentumLi
  | initialEndpointAngularMomentumL1i
  | initialEndpointAngularMomentumL2i
  | finalTotalAngularMomentumLf
  | rotationAxis
  deriving DecidableEq, Fintype, Repr

/-!
Literal and qualitative information transcribed from the supplied raster.
Pixel radii describe only the perspective drawing; they are not physical
length measurements.  The final omega label contains no numerical answer.
-/
structure ExpandingRodFigure where
  labelShown : FigureLabel → Bool
  endpointSphereShown : Configuration → EndpointMass → Bool
  connectingRodShown : Configuration → Bool
  rotationAxisShown : Configuration → Bool
  circularOrbitShown : Configuration → Bool
  directedRotationShown : Configuration → Bool
  endpointLinearMomentumArrowShown : Configuration → EndpointMass → Bool
  endpointMomentumArrowTangentToOrbit : Configuration → EndpointMass → Bool
  totalAngularMomentumArrowShown : Configuration → Bool
  totalAngularMomentumArrowPointsUpward : Configuration → Bool
  rodCrossesAxisAtMidpoint : Configuration → Bool
  orbitRadiusPixels : Configuration → ℝ
  printedRodLengthCentimeters : Configuration → ℝ
  printedRotationFrequencyRevPerSecond : Configuration → Option ℝ
  initialAngularMomentumSumTextShown : Bool

/-! ## Independent physical setup -/

/-!
The final rotation frequency, both moments of inertia, and both total angular
momenta are independent observables.  Subsequent predicates relate them by
general geometry and mechanics laws; no field contains the requested result.
-/
structure ExpandingTwoMassRodSetup where
  endpointMass : EndpointMass → MassQuantity
  rodLength : Configuration → LengthQuantity
  orbitRadius : Configuration → EndpointMass → LengthQuantity
  rotationFrequency : Configuration → RotationFrequencyQuantity
  momentOfInertiaAboutMidpointAxis : Configuration → MomentOfInertiaQuantity
  endpointAngularMomentumAboutAxis :
    Configuration → EndpointMass → AngularMomentumMagnitude
  totalAngularMomentumAboutAxis : Configuration → AngularMomentumMagnitude
  rodMassModel : RodMassModel
  expansionMechanism : ExpansionMechanism
  axisGeometry : RotationAxisGeometry
  rotatesAboutDisplayedAxis : Configuration → Bool
  endpointMassesRemainAttached : Bool
  externalTorqueAboutAxisIsZeroDuringExpansion : Bool
  figure : ExpandingRodFigure

/-! ## Scenario, numerical data, and figure evidence -/

/-- The prose-level two-equal-mass, massless, gas-expanding rod scenario. -/
structure MatchesExpandingTwoMassRodScenario
    (setup : ExpandingTwoMassRodSetup) : Prop where
  equalEndpointMasses : setup.endpointMass .one = setup.endpointMass .two
  rodIsMassless : setup.rodMassModel = .massless
  gasDrivesExpansion : setup.expansionMechanism = .compressedGas
  midpointAxis :
    setup.axisGeometry = .throughRodMidpointPerpendicularToRotationPlane
  rotatingBeforeAndAfter :
    ∀ configuration, setup.rotatesAboutDisplayedAxis configuration = true
  massesStayAttached : setup.endpointMassesRemainAttached = true

/-!
Numerical physical readouts stated in the problem.  There is deliberately no
field for the final rotation frequency.
-/
structure MatchesProblemReadouts
    (setup : ExpandingTwoMassRodSetup) : Prop where
  initialRodLengthCentimeters :
    lengthInCentimeters (setup.rodLength .before) = 50
  finalRodLengthCentimeters :
    lengthInCentimeters (setup.rodLength .after) = 160
  initialFrequencyRevolutionsPerSecond :
    frequencyInRevolutionsPerSecond (setup.rotationFrequency .before) = 2

/-!
Evidence read directly from image `711.png`: labels, rods, spheres, circular
paths, tangential linear-momentum arrows, upward total-angular-momentum arrows,
and the printed before/after data.  The post-expansion frequency is shown only
as the unknown symbol omega-f.
-/
structure MatchesSuppliedExpandingRodFigure
    (setup : ExpandingTwoMassRodSetup) : Prop where
  everyLiteralLabelShown : ∀ label, setup.figure.labelShown label = true
  bothEndpointSpheresShown :
    ∀ configuration endpoint,
      setup.figure.endpointSphereShown configuration endpoint = true
  connectingRodVisible :
    ∀ configuration, setup.figure.connectingRodShown configuration = true
  rotationAxisVisible :
    ∀ configuration, setup.figure.rotationAxisShown configuration = true
  circularOrbitVisible :
    ∀ configuration, setup.figure.circularOrbitShown configuration = true
  directedRotationVisible :
    ∀ configuration, setup.figure.directedRotationShown configuration = true
  everyEndpointMomentumArrowShown :
    ∀ configuration endpoint,
      setup.figure.endpointLinearMomentumArrowShown configuration endpoint = true
  endpointMomentumArrowsAreTangential :
    ∀ configuration endpoint,
      setup.figure.endpointMomentumArrowTangentToOrbit configuration endpoint = true
  totalAngularMomentumArrowsShown :
    ∀ configuration,
      setup.figure.totalAngularMomentumArrowShown configuration = true
  totalAngularMomentumArrowsPointUpward :
    ∀ configuration,
      setup.figure.totalAngularMomentumArrowPointsUpward configuration = true
  axisIntersectsRodAtMidpoint :
    ∀ configuration, setup.figure.rodCrossesAxisAtMidpoint configuration = true
  largerOrbitDrawnAfterExpansion :
    setup.figure.orbitRadiusPixels .before <
      setup.figure.orbitRadiusPixels .after
  initialPrintedLength :
    setup.figure.printedRodLengthCentimeters .before = 50
  finalPrintedLength :
    setup.figure.printedRodLengthCentimeters .after = 160
  initialPrintedFrequency :
    setup.figure.printedRotationFrequencyRevPerSecond .before = some 2
  finalFrequencyHasNoPrintedValue :
    setup.figure.printedRotationFrequencyRevPerSecond .after = none
  initialAngularMomentumDecompositionPrinted :
    setup.figure.initialAngularMomentumSumTextShown = true

/-- Positivity and nondegeneracy conditions for the rotating physical branch. -/
structure HasPhysicalExpandingRodParameters
    (setup : ExpandingTwoMassRodSetup) : Prop where
  endpointMassPositive : ∀ endpoint massUnit,
    0 < massReadout massUnit (setup.endpointMass endpoint)
  rodLengthPositive : ∀ configuration lengthUnit,
    0 < lengthReadout lengthUnit (setup.rodLength configuration)
  orbitRadiusPositive : ∀ configuration endpoint lengthUnit,
    0 < lengthReadout lengthUnit (setup.orbitRadius configuration endpoint)
  rotationFrequencyPositive : ∀ configuration timeUnit,
    0 < rotationFrequencyReadout timeUnit
      (setup.rotationFrequency configuration)
  momentOfInertiaPositive : ∀ configuration massUnit lengthUnit,
    0 < momentOfInertiaReadout massUnit lengthUnit
      (setup.momentOfInertiaAboutMidpointAxis configuration)
  totalAngularMomentumPositive : ∀ configuration massUnit lengthUnit timeUnit,
    0 < angularMomentumReadout massUnit lengthUnit timeUnit
      (setup.totalAngularMomentumAboutAxis configuration)

/-! ## Geometry and governing mechanics -/

/-- Each endpoint mass lies half a rod length from the midpoint axis. -/
structure SatisfiesCenteredEndpointGeometry
    (setup : ExpandingTwoMassRodSetup) : Prop where
  endpointRadiusIsHalfRodLength : ∀ configuration endpoint lengthUnit,
    lengthReadout lengthUnit (setup.orbitRadius configuration endpoint) =
      lengthReadout lengthUnit (setup.rodLength configuration) / 2

/-!
General rigid-rotation laws for two point masses on a massless rod.  The
factor `2 * pi` converts ordinary rotation frequency in revolutions per unit
time to angular speed in radians per unit time.  These laws are uniform in
configuration and contain no specialized final-frequency value.
-/
structure SatisfiesTwoPointMassRigidRotationLaws
    (setup : ExpandingTwoMassRodSetup) : Prop where
  pointMassMomentOfInertia : ∀ configuration massUnit lengthUnit,
    momentOfInertiaReadout massUnit lengthUnit
        (setup.momentOfInertiaAboutMidpointAxis configuration) =
      ∑ endpoint : EndpointMass,
        massReadout massUnit (setup.endpointMass endpoint) *
          lengthReadout lengthUnit
            (setup.orbitRadius configuration endpoint) ^ 2
  endpointAngularMomentumLaw :
    ∀ configuration endpoint massUnit lengthUnit timeUnit,
      angularMomentumReadout massUnit lengthUnit timeUnit
          (setup.endpointAngularMomentumAboutAxis configuration endpoint) =
        massReadout massUnit (setup.endpointMass endpoint) *
          lengthReadout lengthUnit
              (setup.orbitRadius configuration endpoint) ^ 2 *
            (2 * Real.pi *
              rotationFrequencyReadout timeUnit
                (setup.rotationFrequency configuration))
  totalAngularMomentumIsEndpointSum :
    ∀ configuration massUnit lengthUnit timeUnit,
      angularMomentumReadout massUnit lengthUnit timeUnit
          (setup.totalAngularMomentumAboutAxis configuration) =
        ∑ endpoint : EndpointMass,
          angularMomentumReadout massUnit lengthUnit timeUnit
            (setup.endpointAngularMomentumAboutAxis configuration endpoint)
  totalAngularMomentumLaw :
    ∀ configuration massUnit lengthUnit timeUnit,
      angularMomentumReadout massUnit lengthUnit timeUnit
          (setup.totalAngularMomentumAboutAxis configuration) =
        momentOfInertiaReadout massUnit lengthUnit
            (setup.momentOfInertiaAboutMidpointAxis configuration) *
          (2 * Real.pi *
            rotationFrequencyReadout timeUnit
              (setup.rotationFrequency configuration))

/-!
With zero external torque about the fixed midpoint axis, total angular
momentum is the same before and after the gas-driven expansion.  This premise
does not specify the final frequency.
-/
structure SatisfiesAngularMomentumConservationDuringExpansion
    (setup : ExpandingTwoMassRodSetup) : Prop where
  noExternalTorque :
    setup.externalTorqueAboutAxisIsZeroDuringExpansion = true
  angularMomentumConserved : ∀ massUnit lengthUnit timeUnit,
    angularMomentumReadout massUnit lengthUnit timeUnit
        (setup.totalAngularMomentumAboutAxis .before) =
      angularMomentumReadout massUnit lengthUnit timeUnit
        (setup.totalAngularMomentumAboutAxis .after)

/-! ## Derived rotation-frequency relations -/

/-- Two equal endpoint masses at radius `l/2` have `I = m l^2 / 2`. -/
lemma midpointMomentOfInertia_readout
    (setup : ExpandingTwoMassRodSetup)
    (_scenario : MatchesExpandingTwoMassRodScenario setup)
    (_geometry : SatisfiesCenteredEndpointGeometry setup)
    (_rotation : SatisfiesTwoPointMassRigidRotationLaws setup) :
    ∀ configuration massUnit lengthUnit,
      momentOfInertiaReadout massUnit lengthUnit
          (setup.momentOfInertiaAboutMidpointAxis configuration) =
        massReadout massUnit (setup.endpointMass .one) *
          lengthReadout lengthUnit (setup.rodLength configuration) ^ 2 / 2 := by
  intro configuration massUnit lengthUnit
  rw [_rotation.pointMassMomentOfInertia]
  have huniv : (Finset.univ : Finset EndpointMass) =
      {EndpointMass.one, EndpointMass.two} := by
    decide
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_singleton]
  simp_rw [_geometry.endpointRadiusIsHalfRodLength]
  rw [← _scenario.equalEndpointMasses]
  ring

/-!
Conservation of angular momentum cancels the common mass and `2 pi` factors,
leaving `l_i^2 f_i = l_f^2 f_f` in centimetre/second readouts.
-/
lemma rodLengthSquared_mul_frequency_conserved
    (setup : ExpandingTwoMassRodSetup)
    (_scenario : MatchesExpandingTwoMassRodScenario setup)
    (_physical : HasPhysicalExpandingRodParameters setup)
    (_geometry : SatisfiesCenteredEndpointGeometry setup)
    (_rotation : SatisfiesTwoPointMassRigidRotationLaws setup)
    (_conservation :
      SatisfiesAngularMomentumConservationDuringExpansion setup) :
    lengthInCentimeters (setup.rodLength .before) ^ 2 *
        frequencyInRevolutionsPerSecond (setup.rotationFrequency .before) =
      lengthInCentimeters (setup.rodLength .after) ^ 2 *
        frequencyInRevolutionsPerSecond
          (setup.rotationFrequency .after) := by
  have hconservation := _conservation.angularMomentumConserved
    MassUnit.kilograms LengthUnit.centimeters TimeUnit.seconds
  rw [_rotation.totalAngularMomentumLaw .before,
    _rotation.totalAngularMomentumLaw .after,
    midpointMomentOfInertia_readout setup _scenario _geometry _rotation .before,
    midpointMomentOfInertia_readout setup _scenario _geometry _rotation .after]
    at hconservation
  have hmass :=
    _physical.endpointMassPositive EndpointMass.one MassUnit.kilograms
  have hpi := Real.pi_pos
  simp only [lengthInCentimeters, frequencyInRevolutionsPerSecond]
  apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt hmass) (ne_of_gt hpi))
  linear_combination hconservation

/-!
Using the stated lengths and initial frequency gives the exact physical
readout `2 * (50 / 160)^2 = 25 / 128 rev/s`.
-/
lemma finalRotationFrequency_exact
    (setup : ExpandingTwoMassRodSetup)
    (_scenario : MatchesExpandingTwoMassRodScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_physical : HasPhysicalExpandingRodParameters setup)
    (_geometry : SatisfiesCenteredEndpointGeometry setup)
    (_rotation : SatisfiesTwoPointMassRigidRotationLaws setup)
    (_conservation :
      SatisfiesAngularMomentumConservationDuringExpansion setup) :
    frequencyInRevolutionsPerSecond (setup.rotationFrequency .after) =
      (25 : ℝ) / 128 := by
  have hconserved := rodLengthSquared_mul_frequency_conserved setup _scenario
    _physical _geometry _rotation _conservation
  rw [_readouts.initialRodLengthCentimeters,
    _readouts.finalRodLengthCentimeters,
    _readouts.initialFrequencyRevolutionsPerSecond] at hconserved
  norm_num at hconserved ⊢
  linarith

/-! ## Displayed choices and formalization target -/

/-- Labels of the four rotation-frequency choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Revolutions-per-second value printed beside each answer label. -/
def AnswerChoice.revolutionsPerSecond : AnswerChoice → ℝ
  | .A => 4 / 5
  | .B => 1 / 2
  | .C => 1 / 5
  | .D => 11 / 10

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
Agreement with a value printed to two decimal places: the exact physical
readout differs from the displayed value by less than half of `0.01 rev/s`.
-/
def MatchesDisplayedRotationFrequency
    (setup : ExpandingTwoMassRodSetup) (choice : AnswerChoice) : Prop :=
  |frequencyInRevolutionsPerSecond (setup.rotationFrequency .after) -
      choice.revolutionsPerSecond| < (1 : ℝ) / 200

/-- A displayed choice is strictly closer than every other displayed value. -/
def IsUniqueClosestDisplayedRotationFrequency
    (setup : ExpandingTwoMassRodSetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice, otherChoice ≠ choice →
    |frequencyInRevolutionsPerSecond (setup.rotationFrequency .after) -
        choice.revolutionsPerSecond| <
      |frequencyInRevolutionsPerSecond (setup.rotationFrequency .after) -
        otherChoice.revolutionsPerSecond|

/-!
The expanded rod rotates at exactly `25/128 rev/s`, which rounds to
`0.20 rev/s` and uniquely selects recorded choice C.

This formalizes `thm:physics:phyx_mini_0711:target`.
-/
theorem finalRotationFrequency_matches_recordedChoiceC
    (setup : ExpandingTwoMassRodSetup)
    (_scenario : MatchesExpandingTwoMassRodScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedExpandingRodFigure setup)
    (_physical : HasPhysicalExpandingRodParameters setup)
    (_geometry : SatisfiesCenteredEndpointGeometry setup)
    (_rotation : SatisfiesTwoPointMassRigidRotationLaws setup)
    (_conservation :
      SatisfiesAngularMomentumConservationDuringExpansion setup) :
    frequencyInRevolutionsPerSecond (setup.rotationFrequency .after) =
        (25 : ℝ) / 128 ∧
      MatchesDisplayedRotationFrequency setup recordedDatasetAnswer ∧
      IsUniqueClosestDisplayedRotationFrequency
        setup recordedDatasetAnswer := by
  have hfrequency := finalRotationFrequency_exact setup _scenario _readouts
    _physical _geometry _rotation _conservation
  refine ⟨hfrequency, ?_, ?_⟩
  · norm_num [MatchesDisplayedRotationFrequency, recordedDatasetAnswer,
      AnswerChoice.revolutionsPerSecond, hfrequency, abs_of_nonpos,
      abs_of_nonneg]
  · rw [IsUniqueClosestDisplayedRotationFrequency, hfrequency]
    intro otherChoice hne
    fin_cases otherChoice
    · norm_num [recordedDatasetAnswer, AnswerChoice.revolutionsPerSecond,
        abs_of_nonpos, abs_of_nonneg]
    · norm_num [recordedDatasetAnswer, AnswerChoice.revolutionsPerSecond,
        abs_of_nonpos, abs_of_nonneg]
    · exact (hne rfl).elim
    · norm_num [recordedDatasetAnswer, AnswerChoice.revolutionsPerSecond,
        abs_of_nonpos, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0711
