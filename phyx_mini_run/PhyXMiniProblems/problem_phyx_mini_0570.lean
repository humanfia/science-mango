import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0570

open Dimension

/-!
# Probability-density penetration into an upward potential step

An electron approaches from the left a one-dimensional potential step at
`x = 0`.  The potential is zero on the left and is the constant `V₀` on the
right.  Its energy `E = K = 5 eV` lies below the `10 eV` step, so the wave in
the right-hand region is evanescent.

Here "penetration distance" means the distance over which the probability
density, rather than the wave-function amplitude, falls by a factor `exp (-1)`.
Thus a density proportional to `exp (-2 κ x)` has penetration distance
`1 / (2 κ)`.  This convention is essential: the amplitude e-folding length
would be twice the recorded answer.

Energy, mass, action, position, length, and inverse length are represented by
unit-independent Physlib quantities.  Real scalars are used only at explicit
unit-readout boundaries, for normalized density ratios, and for displayed
answer values.  The penetration distance is an independent physical field;
no premise sets it to `0.044 nm` or selects answer C.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent coordinate along the scattering axis. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative inverse length, used for the evanescent decay constant. -/
abbrev InverseLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- The physical dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an energy in electron volts using Physlib's calibrated electron volt. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Read a mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read an action in coherent SI units, joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read a signed position in metres. -/
def positionInMeters (position : SignedLengthQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Read an inverse-length quantity in inverse metres. -/
def inverseLengthInInverseMeters
    (inverseLength : InverseLengthQuantity) : ℝ :=
  ((inverseLength UnitChoices.SI).val : ℝ)

/-! ## Physical setup and primary-figure vocabulary -/

/-- Particle species distinguished by the problem statement. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- The two constant-potential regions separated by `x = 0`. -/
inductive PotentialRegion where
  | leftOfStep
  | rightOfStep
  deriving DecidableEq, Fintype, Repr

/-- Horizontal propagation directions in the one-dimensional diagram. -/
inductive HorizontalDirection where
  | towardNegativeX
  | towardPositiveX
  deriving DecidableEq, Repr

/-- Physical roles of the two plotted axes. -/
inductive FigureAxisRole where
  | position
  | potentialEnergy
  deriving DecidableEq, Repr

/-- Literal quantity/text labels visible in image `570.png`. -/
inductive FigureTextLabel where
  | horizontalX
  | verticalVOfX
  | stepHeightV₀
  | totalEnergyE
  | boundaryZero
  | position
  | particle
  deriving DecidableEq, Fintype, Repr

/--
Qualitative evidence read from the primary raster: axes and labels, a zero
left plateau, a jump at the origin, the `V₀` right plateau, the lower `E`
level, and a particle directed toward positive `x`.
-/
structure PotentialStepFigure where
  horizontalAxisRole : FigureAxisRole
  verticalAxisRole : FigureAxisRole
  labelShown : FigureTextLabel → Bool
  leftZeroPotentialSegmentShown : Bool
  verticalJumpAtOriginShown : Bool
  rightV₀PlateauShown : Bool
  energyLevelBelowV₀Shown : Bool
  incomingParticleShown : Bool
  dashedApproachPathShown : Bool
  approachArrowDirection : HorizontalDirection

/--
Independent quantities in the under-step scattering experiment.  In
particular, the probability-density penetration distance is stored rather
than defined from the source's recorded numerical answer.
-/
structure ElectronPotentialStepSetup where
  particleSpecies : ParticleSpecies
  incidentDirection : HorizontalDirection
  incidentKineticEnergy : DimEnergy
  totalEnergy : DimEnergy
  stepHeight : DimEnergy
  potentialEnergyAt : PotentialRegion → DimEnergy
  stepBoundaryPosition : SignedLengthQuantity
  particleRestMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  amplitudeDecayConstant : InverseLengthQuantity
  relativeProbabilityDensityAtMeters : ℝ → ℝ
  probabilityDensityPenetrationDistance : LengthQuantity
  figure : PotentialStepFigure

/-! ## Scenario, data readouts, figure evidence, and governing laws -/

/-- The prose describes an electron incident from the left toward positive `x`. -/
structure MatchesElectronStepScenario
    (setup : ElectronPotentialStepSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  electronMovesTowardPositiveX :
    setup.incidentDirection = .towardPositiveX

/-- The numerical input data stated in the question. -/
structure MatchesProblemNumericalReadouts
    (setup : ElectronPotentialStepSetup) : Prop where
  kineticEnergyElectronVolts :
    energyInElectronVolts setup.incidentKineticEnergy = 5
  stepHeightElectronVolts :
    energyInElectronVolts setup.stepHeight = 10

/--
The sharp step is at the origin, with zero potential on the left and `V₀` on
the right.  The incident total energy equals kinetic plus potential energy.
-/
structure MatchesUpwardPotentialStepProfile
    (setup : ElectronPotentialStepSetup) : Prop where
  boundaryAtOrigin : positionInMeters setup.stepBoundaryPosition = 0
  leftPotentialZero :
    energyInJoules (setup.potentialEnergyAt .leftOfStep) = 0
  rightPotentialIsStepHeight :
    energyInJoules (setup.potentialEnergyAt .rightOfStep) =
      energyInJoules setup.stepHeight
  incidentTotalEnergyRelation :
    energyInJoules setup.totalEnergy =
      energyInJoules setup.incidentKineticEnergy +
        energyInJoules (setup.potentialEnergyAt .leftOfStep)

/--
Primary-image evidence from `570.png`.  This contains no penetration-distance
readout and no answer-choice label.
-/
structure MatchesSuppliedPotentialStepFigure
    (figure : PotentialStepFigure) : Prop where
  horizontalAxisIsPosition : figure.horizontalAxisRole = .position
  verticalAxisIsPotentialEnergy :
    figure.verticalAxisRole = .potentialEnergy
  allPrintedLabelsVisible : ∀ label, figure.labelShown label = true
  zeroPotentialLeftSegmentVisible :
    figure.leftZeroPotentialSegmentShown = true
  verticalStepAtZeroVisible : figure.verticalJumpAtOriginShown = true
  constantV₀RightSegmentVisible : figure.rightV₀PlateauShown = true
  energyEIsDrawnBelowV₀ : figure.energyLevelBelowV₀Shown = true
  particleVisible : figure.incomingParticleShown = true
  dashedPathVisible : figure.dashedApproachPathShown = true
  arrowPointsTowardStep :
    figure.approachArrowDirection = .towardPositiveX

/-- Standard electron mass and Physlib reduced-Planck-constant calibrations. -/
structure UsesStandardElectronReferenceData
    (setup : ElectronPotentialStepSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.particleRestMass = 9.1093837015e-31
  reducedPlanckJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/-- Positivity and `E < V₀` select the classically forbidden branch. -/
structure HasPhysicalUnderStepParameters
    (setup : ElectronPotentialStepSetup) : Prop where
  positiveIncidentEnergy :
    0 < energyInJoules setup.incidentKineticEnergy
  positiveStepHeight : 0 < energyInJoules setup.stepHeight
  totalEnergyBelowStep :
    energyInJoules setup.totalEnergy < energyInJoules setup.stepHeight
  positiveElectronMass : 0 < massInKilograms setup.particleRestMass
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  positiveDecayConstant :
    0 < inverseLengthInInverseMeters setup.amplitudeDecayConstant
  positivePenetrationDistance :
    0 < lengthInMeters setup.probabilityDensityPenetrationDistance

/--
For a constant region with `E < V₀`, the amplitude decay constant obeys

`κ = sqrt (2 m (V₀ - E)) / ℏ`,

and the probability density relative to its boundary value obeys
`ρ(x) / ρ(0) = exp (-2 κ x)` for `x ≥ 0`.  These are general governing laws,
not a numerical penetration-distance answer.
-/
structure SatisfiesEvanescentProbabilityDensityLaw
    (setup : ElectronPotentialStepSetup) : Prop where
  amplitudeDecayConstantLaw :
    inverseLengthInInverseMeters setup.amplitudeDecayConstant =
      Real.sqrt
          (2 * massInKilograms setup.particleRestMass *
            (energyInJoules setup.stepHeight -
              energyInJoules setup.totalEnergy)) /
        actionInJouleSeconds setup.reducedPlanckAction
  probabilityDensityDecayLaw : ∀ xMeters : ℝ, 0 ≤ xMeters →
    setup.relativeProbabilityDensityAtMeters xMeters =
      Real.exp
        (-2 * inverseLengthInInverseMeters setup.amplitudeDecayConstant *
          xMeters)

/--
The requested observable is the positive distance at which the normalized
probability density has fallen to `exp (-1)`.  This fixes the physical meaning
of "penetration distance" without assuming its numerical value.
-/
structure IsProbabilityDensityEfoldingDistance
    (setup : ElectronPotentialStepSetup) : Prop where
  densityAtPenetrationDistance :
    setup.relativeProbabilityDensityAtMeters
        (lengthInMeters setup.probabilityDensityPenetrationDistance) =
      Real.exp (-1)

/-! ## Derived penetration relation and displayed-answer semantics -/

/--
The two governing decay laws imply the coherent-SI closed form for the
probability-density penetration distance.  This is a derived conclusion, not
a field of any premise structure.
-/
lemma probabilityDensityPenetrationDistance_closedForm
    (setup : ElectronPotentialStepSetup)
    (_physical : HasPhysicalUnderStepParameters setup)
    (_decay : SatisfiesEvanescentProbabilityDensityLaw setup)
    (_definition : IsProbabilityDensityEfoldingDistance setup) :
    lengthInMeters setup.probabilityDensityPenetrationDistance =
      actionInJouleSeconds setup.reducedPlanckAction /
        (2 * Real.sqrt
          (2 * massInKilograms setup.particleRestMass *
            (energyInJoules setup.stepHeight -
              energyInJoules setup.totalEnergy))) := by
  have hρ := _decay.probabilityDensityDecayLaw
    (lengthInMeters setup.probabilityDensityPenetrationDistance)
    (le_of_lt _physical.positivePenetrationDistance)
  rw [_definition.densityAtPenetrationDistance] at hρ
  have hExponent :
      -2 * inverseLengthInInverseMeters setup.amplitudeDecayConstant *
            lengthInMeters setup.probabilityDensityPenetrationDistance = -1 :=
    Real.exp_injective (Eq.symm hρ)
  have hProduct :
      2 * inverseLengthInInverseMeters setup.amplitudeDecayConstant *
            lengthInMeters setup.probabilityDensityPenetrationDistance = 1 := by
    linarith
  have hActionNe : actionInJouleSeconds setup.reducedPlanckAction ≠ 0 :=
    ne_of_gt _physical.positiveReducedPlanckAction
  have hDecaySqrt :
      inverseLengthInInverseMeters setup.amplitudeDecayConstant *
          actionInJouleSeconds setup.reducedPlanckAction =
        Real.sqrt
          (2 * massInKilograms setup.particleRestMass *
            (energyInJoules setup.stepHeight -
              energyInJoules setup.totalEnergy)) :=
    (eq_div_iff hActionNe).mp _decay.amplitudeDecayConstantLaw
  have hSqrtPos :
      0 < Real.sqrt
        (2 * massInKilograms setup.particleRestMass *
          (energyInJoules setup.stepHeight -
            energyInJoules setup.totalEnergy)) := by
    rw [← hDecaySqrt]
    exact mul_pos _physical.positiveDecayConstant
      _physical.positiveReducedPlanckAction
  apply (eq_div_iff
    (mul_ne_zero (by norm_num) (ne_of_gt hSqrtPos))).2
  calc
    lengthInMeters setup.probabilityDensityPenetrationDistance *
        (2 * Real.sqrt
          (2 * massInKilograms setup.particleRestMass *
            (energyInJoules setup.stepHeight -
              energyInJoules setup.totalEnergy))) =
        (2 * inverseLengthInInverseMeters setup.amplitudeDecayConstant *
          lengthInMeters setup.probabilityDensityPenetrationDistance) *
            actionInJouleSeconds setup.reducedPlanckAction := by
              rw [← hDecaySqrt]
              ring
    _ = actionInJouleSeconds setup.reducedPlanckAction := by
      rw [hProduct]
      ring

/-- Labels of the four penetration-distance choices in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The penetration distance printed beside each label, measured in nanometres. -/
def displayedPenetrationDistanceNanometers : AnswerChoice → ℝ
  | .A => 55 / 100
  | .B => 95 / 100
  | .C => 44 / 1000
  | .D => 102 / 10

/-- Dataset metadata recording answer C; it is deliberately not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a value displayed to three decimal places in nanometres. -/
def AgreesWhenRoundedToThreeDecimalNanometers
    (setup : ElectronPotentialStepSetup) (choice : AnswerChoice) : Prop :=
  |lengthInNanometers setup.probabilityDensityPenetrationDistance -
      displayedPenetrationDistanceNanometers choice| < (1 / 2000 : ℝ)

/-- The selected value is strictly nearer than each other displayed distance. -/
def IsUniqueNearestPenetrationDistanceChoice
    (setup : ElectronPotentialStepSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInNanometers setup.probabilityDensityPenetrationDistance -
        displayedPenetrationDistanceNanometers choice| <
      |lengthInNanometers setup.probabilityDensityPenetrationDistance -
        displayedPenetrationDistanceNanometers other|

/--
For a `5 eV` electron incident on the `10 eV` step shown in image 570, the
probability-density e-folding distance rounds to `0.044 nm`, uniquely selecting
answer C.

This formalizes `thm:physics:phyx_mini_0570:target`.  Neither `0.044 nm` nor
choice C occurs in any theorem premise.
-/
theorem problem_phyx_mini_0570
    (setup : ElectronPotentialStepSetup)
    (_scenario : MatchesElectronStepScenario setup)
    (_readouts : MatchesProblemNumericalReadouts setup)
    (_profile : MatchesUpwardPotentialStepProfile setup)
    (_figure : MatchesSuppliedPotentialStepFigure setup.figure)
    (_reference : UsesStandardElectronReferenceData setup)
    (_physical : HasPhysicalUnderStepParameters setup)
    (_decay : SatisfiesEvanescentProbabilityDensityLaw setup)
    (_definition : IsProbabilityDensityEfoldingDistance setup) :
    AgreesWhenRoundedToThreeDecimalNanometers setup .C ∧
      IsUniqueNearestPenetrationDistanceChoice setup .C := by
  have hTotal := _profile.incidentTotalEnergyRelation
  rw [_profile.leftPotentialZero, add_zero] at hTotal
  have hKinetic := _readouts.kineticEnergyElectronVolts
  have hStep := _readouts.stepHeightElectronVolts
  norm_num [energyInElectronVolts, energyInJoules, DimEnergy.electronVolt,
    CarriesDimension.toDimensionful_apply_apply] at hKinetic hStep
  have hDifference :
      energyInJoules setup.stepHeight - energyInJoules setup.totalEnergy =
        5 * 1.602176634e-19 := by
    norm_num at hKinetic hStep ⊢
    dsimp [energyInJoules] at hTotal ⊢
    linarith
  have hRadicand :
      2 * massInKilograms setup.particleRestMass *
          (energyInJoules setup.stepHeight - energyInJoules setup.totalEnergy) =
        2 * 9.1093837015e-31 * (5 * 1.602176634e-19) := by
    rw [_reference.electronMassKilograms, hDifference]
  have hSqrtLower :
      1.20e-24 < Real.sqrt
        (2 * massInKilograms setup.particleRestMass *
          (energyInJoules setup.stepHeight -
            energyInJoules setup.totalEnergy)) := by
    rw [hRadicand]
    have hsquare := Real.sq_sqrt
      (show 0 ≤
        (2 * 9.1093837015e-31 * (5 * 1.602176634e-19) : ℝ) by
          norm_num)
    have hsqrt := Real.sqrt_nonneg
      (2 * 9.1093837015e-31 * (5 * 1.602176634e-19) : ℝ)
    nlinarith
  have hSqrtUpper :
      Real.sqrt
        (2 * massInKilograms setup.particleRestMass *
          (energyInJoules setup.stepHeight -
            energyInJoules setup.totalEnergy)) <
        1.21e-24 := by
    rw [hRadicand]
    have hsquare := Real.sq_sqrt
      (show 0 ≤
        (2 * 9.1093837015e-31 * (5 * 1.602176634e-19) : ℝ) by
          norm_num)
    have hsqrt := Real.sqrt_nonneg
      (2 * 9.1093837015e-31 * (5 * 1.602176634e-19) : ℝ)
    nlinarith
  have hUnits :
      lengthInNanometers setup.probabilityDensityPenetrationDistance =
        1000000000 *
          lengthInMeters setup.probabilityDensityPenetrationDistance := by
    have h := congrArg
      (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
      (setup.probabilityDensityPenetrationDistance.2
        UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.nanometers})
    norm_num [lengthInNanometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, NNReal.smul_def] at h ⊢
    exact h
  have hClosed := probabilityDensityPenetrationDistance_closedForm setup
    _physical _decay _definition
  have hNmValue :
      lengthInNanometers setup.probabilityDensityPenetrationDistance =
        (1000000000 *
          actionInJouleSeconds setup.reducedPlanckAction) /
          (2 * Real.sqrt
            (2 * massInKilograms setup.particleRestMass *
              (energyInJoules setup.stepHeight -
                energyInJoules setup.totalEnergy))) := by
    rw [hUnits, hClosed]
    ring
  have hAction := _reference.reducedPlanckJouleSeconds
  norm_num [Constants.ℏ] at hAction
  have hDenominatorPositive :
      0 < 2 * Real.sqrt
        (2 * massInKilograms setup.particleRestMass *
          (energyInJoules setup.stepHeight -
            energyInJoules setup.totalEnergy)) := by
    positivity
  have hInterval :
      (0.0435 : ℝ) <
          lengthInNanometers setup.probabilityDensityPenetrationDistance ∧
        lengthInNanometers setup.probabilityDensityPenetrationDistance <
          0.0445 := by
    rw [hNmValue, hAction]
    constructor
    · rw [lt_div_iff₀ hDenominatorPositive]
      norm_num at hSqrtUpper ⊢
      nlinarith
    · rw [div_lt_iff₀ hDenominatorPositive]
      norm_num at hSqrtLower ⊢
      nlinarith
  have hAgreement :
      AgreesWhenRoundedToThreeDecimalNanometers setup .C := by
    rw [AgreesWhenRoundedToThreeDecimalNanometers,
      displayedPenetrationDistanceNanometers, abs_lt]
    constructor <;> norm_num <;> nlinarith [hInterval.1, hInterval.2]
  constructor
  · exact hAgreement
  · intro other hOther
    fin_cases other
    · calc
        |lengthInNanometers setup.probabilityDensityPenetrationDistance -
            displayedPenetrationDistanceNanometers .C| < (1 / 2000 : ℝ) :=
          hAgreement
        _ < |lengthInNanometers setup.probabilityDensityPenetrationDistance -
            displayedPenetrationDistanceNanometers .A| := by
          rw [abs_of_neg]
          · norm_num [displayedPenetrationDistanceNanometers]
            nlinarith [hInterval.2]
          · norm_num [displayedPenetrationDistanceNanometers]
            nlinarith [hInterval.2]
    · calc
        |lengthInNanometers setup.probabilityDensityPenetrationDistance -
            displayedPenetrationDistanceNanometers .C| < (1 / 2000 : ℝ) :=
          hAgreement
        _ < |lengthInNanometers setup.probabilityDensityPenetrationDistance -
            displayedPenetrationDistanceNanometers .B| := by
          rw [abs_of_neg]
          · norm_num [displayedPenetrationDistanceNanometers]
            nlinarith [hInterval.2]
          · norm_num [displayedPenetrationDistanceNanometers]
            nlinarith [hInterval.2]
    · exact (hOther rfl).elim
    · calc
        |lengthInNanometers setup.probabilityDensityPenetrationDistance -
            displayedPenetrationDistanceNanometers .C| < (1 / 2000 : ℝ) :=
          hAgreement
        _ < |lengthInNanometers setup.probabilityDensityPenetrationDistance -
            displayedPenetrationDistanceNanometers .D| := by
          rw [abs_of_neg]
          · norm_num [displayedPenetrationDistanceNanometers]
            nlinarith [hInterval.2]
          · norm_num [displayedPenetrationDistanceNanometers]
            nlinarith [hInterval.2]

end PhyXMiniProblems.ProblemPhyXMini0570
