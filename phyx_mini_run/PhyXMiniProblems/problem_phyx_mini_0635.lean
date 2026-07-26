import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0635

open Dimension

/-!
# Closest approach of an alpha particle to a gold nucleus

An alpha particle approaches a fixed gold nucleus head-on with initial speed
`2.0 * 10^7 m/s`.  The primary figure labels the nuclear charges as `2e` and
`79e`, treats the initial separation as effectively infinite, and shows the
alpha particle momentarily at rest at the closest separation `r_min`.

Mass, charge, length, speed, and energy are represented by unit-independent
Physlib quantities.  Real numbers occur only at explicitly named unit-readout
boundaries and in the printed answer values.

Assumption/target boundary:

* `MatchesProblemScenarioAndData` records the head-on fixed-target model,
  effectively infinite initial separation, and stated initial speed;
* `MatchesPrimaryFigure` records literal diagram evidence, the charge labels,
  and the zero speed at closest approach;
* `UsesReferenceAlphaGoldConstants` supplies the independent alpha-mass and
  free-space Coulomb-constant calibrations;
* the governing-law structures state classical kinetic energy, repulsive
  Coulomb potential energy, and conservation of mechanical energy; and
* neither the closest-approach formula, its numerical interval, nor answer B
  occurs in any premise.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Femtometre readout of a nuclear-scale physical length. -/
def lengthInFemtometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.femtometers length

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read a charge magnitude in a selected Physlib charge unit. -/
def chargeReadout
    (unit : ChargeUnit) (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge {UnitChoices.SI with charge := unit}).val : ℝ)

/-- SI coulomb readout of a physical charge magnitude. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeReadout ChargeUnit.coulombs charge

/-- Read a charge magnitude as a multiple of the elementary charge. -/
def chargeInElementaryCharges (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeReadout ChargeUnit.elementaryCharge charge

/-- SI metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Coherent-SI joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Physlib's exact elementary-charge unit, expressed as a scalar number of
coulombs.  Charges in the setup remain dimensionful quantities.
-/
def physlibElementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two charged bodies shown in the alpha--gold diagram. -/
inductive FigureBody where
  | alphaParticle
  | goldNucleus
  deriving DecidableEq, Fintype, Repr

/-- The two snapshots displayed in the supplied diagram. -/
inductive InteractionStage where
  | beforeInteraction
  | closestApproach
  deriving DecidableEq, Fintype, Repr

/-- Radial direction relative to the gold nucleus. -/
inductive RadialDirection where
  | towardGoldNucleus
  | awayFromGoldNucleus
  deriving DecidableEq, Repr

/-- Qualitative model for the initial alpha--gold separation. -/
inductive SeparationRegime where
  | effectivelyInfinite
  | finite
  deriving DecidableEq, Repr

/-- Interaction retained by the textbook closest-approach model. -/
inductive InteractionModel where
  | electrostaticCoulombRepulsion
  | other
  deriving DecidableEq, Repr

/-- Literal symbolic labels visible in the primary image. -/
inductive FigureLabel where
  | before
  | after
  | alphaChargeTwoE
  | goldChargeSeventyNineE
  | goldNucleus
  | initialVelocityVi
  | initialSeparationApproximatelyInfinite
  | finalVelocityZero
  | closestSeparationRMin
  deriving DecidableEq, Fintype, Repr

/-!
Presentation facts transcribed from image 635.  It contains no numerical
value for `r_min`.
-/
structure AlphaGoldClosestApproachFigure where
  bodyShown : InteractionStage → FigureBody → Bool
  labelShown : FigureLabel → Bool
  positiveChargeMarksShown : InteractionStage → FigureBody → Bool
  alphaDrawnLeftOfGold : InteractionStage → Bool
  initialVelocityArrowPointsTowardGold : Bool
  closestSeparationArrowBetweenBodies : Bool
  zeroSpeedExplanationPrinted : Bool

/-!
Independent physical quantities for the two snapshots.  The closest-approach
distance is an unknown observable, not a definition made from an answer.
-/
structure AlphaGoldClosestApproachSetup where
  alphaMass : MassQuantity
  chargeMagnitude : FigureBody → ChargeMagnitudeQuantity
  speedAt : InteractionStage → DimSpeed
  closestApproachDistance : LengthQuantity
  kineticEnergyAt : InteractionStage → DimEnergy
  electrostaticPotentialEnergyAt : InteractionStage → DimEnergy
  electromagneticSystem : Electromagnetism.EMSystem
  interactionModel : InteractionModel
  initialSeparationRegime : SeparationRegime
  incidentRadialDirection : RadialDirection
  trajectoryIsHeadOn : Bool
  goldNucleusHeldFixed : Bool
  figure : AlphaGoldClosestApproachFigure

/-! ## Scenario, figure/data readouts, and reference constants -/

/-- The qualitative model and the incident speed stated by the problem. -/
structure MatchesProblemScenarioAndData
    (setup : AlphaGoldClosestApproachSetup) : Prop where
  coulombRepulsionModel :
    setup.interactionModel = .electrostaticCoulombRepulsion
  headOnTrajectory : setup.trajectoryIsHeadOn = true
  alphaMovesTowardGold :
    setup.incidentRadialDirection = .towardGoldNucleus
  goldTreatedAsFixed : setup.goldNucleusHeldFixed = true
  startsEffectivelyAtInfinity :
    setup.initialSeparationRegime = .effectivelyInfinite
  statedInitialSpeed :
    speedInMetersPerSecond (setup.speedAt .beforeInteraction) =
      2 * (10 : ℝ) ^ 7

/-!
Literal figure evidence and its association with the dimensionful physical
charges and speeds.  In particular, the image gives `v_f = 0` but does not
give the value of `r_min`.
-/
structure MatchesPrimaryFigure
    (setup : AlphaGoldClosestApproachSetup) : Prop where
  everyBodyShown : ∀ stage body,
    setup.figure.bodyShown stage body = true
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  positiveChargeMarksShown : ∀ stage body,
    setup.figure.positiveChargeMarksShown stage body = true
  alphaIsLeftOfGold : ∀ stage,
    setup.figure.alphaDrawnLeftOfGold stage = true
  incidentArrowPointsTowardGold :
    setup.figure.initialVelocityArrowPointsTowardGold = true
  closestSeparationArrowShown :
    setup.figure.closestSeparationArrowBetweenBodies = true
  zeroSpeedExplanationShown :
    setup.figure.zeroSpeedExplanationPrinted = true
  alphaChargeLabelAgrees :
    chargeInElementaryCharges
        (setup.chargeMagnitude .alphaParticle) = 2
  goldChargeLabelAgrees :
    chargeInElementaryCharges
        (setup.chargeMagnitude .goldNucleus) = 79
  speedAtClosestApproachIsZero :
    speedInMetersPerSecond (setup.speedAt .closestApproach) = 0

/-!
Independent reference constants used to evaluate the multiple-choice result.
The alpha-particle mass is in kilograms and Physlib's electromagnetic system
method is calibrated to the free-space Coulomb constant in SI units.
-/
structure UsesReferenceAlphaGoldConstants
    (setup : AlphaGoldClosestApproachSetup) : Prop where
  alphaMassCalibration :
    massInKilograms setup.alphaMass = 6.6446573357e-27
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity conditions selecting a nondegenerate physical encounter. -/
structure HasPhysicalAlphaGoldParameters
    (setup : AlphaGoldClosestApproachSetup) : Prop where
  alphaMassPositive : 0 < massInKilograms setup.alphaMass
  alphaChargePositive :
    0 < chargeInCoulombs (setup.chargeMagnitude .alphaParticle)
  goldChargePositive :
    0 < chargeInCoulombs (setup.chargeMagnitude .goldNucleus)
  initialSpeedPositive :
    0 < speedInMetersPerSecond (setup.speedAt .beforeInteraction)
  closestDistancePositive :
    0 < lengthInMeters setup.closestApproachDistance
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Governing physical laws -/

/-- Classical translational kinetic energy, `K = (1/2) m v²`. -/
structure SatisfiesClassicalKineticEnergyLaw
    (setup : AlphaGoldClosestApproachSetup) : Prop where
  kineticEnergyAtEachStage : ∀ stage,
    energyInJoules (setup.kineticEnergyAt stage) =
      (1 / 2 : ℝ) * massInKilograms setup.alphaMass *
        speedInMetersPerSecond (setup.speedAt stage) ^ 2

/-!
The electrostatic energy vanishes at the effectively infinite initial
separation and equals `k q_alpha q_Au / r_min` at closest approach.  This is
the general Coulomb potential-energy law at the unknown separation, not the
requested solution for that separation.
-/
structure SatisfiesRepulsiveCoulombPotentialLaw
    (setup : AlphaGoldClosestApproachSetup) : Prop where
  initialPotentialAtInfinity :
    energyInJoules
        (setup.electrostaticPotentialEnergyAt .beforeInteraction) = 0
  closestApproachPotential :
    energyInJoules
        (setup.electrostaticPotentialEnergyAt .closestApproach) =
      setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.chargeMagnitude .alphaParticle) *
          chargeInCoulombs (setup.chargeMagnitude .goldNucleus) /
        lengthInMeters setup.closestApproachDistance

/-- Conservation of mechanical energy between the two displayed snapshots. -/
structure SatisfiesMechanicalEnergyConservation
    (setup : AlphaGoldClosestApproachSetup) : Prop where
  energyBalance :
    energyInJoules (setup.kineticEnergyAt .beforeInteraction) +
        energyInJoules
          (setup.electrostaticPotentialEnergyAt .beforeInteraction) =
      energyInJoules (setup.kineticEnergyAt .closestApproach) +
        energyInJoules
          (setup.electrostaticPotentialEnergyAt .closestApproach)

/-! ## Derived closest approach and displayed answer -/

/-!
Unit covariance converts an elementary-charge readout to the corresponding
coulomb readout.  This is a unit-conversion fact, independent of the
closest-approach dynamics.
-/
lemma chargeInCoulombs_eq_elementaryChargeMultiple
    (charge : ChargeMagnitudeQuantity) :
    chargeInCoulombs charge =
      chargeInElementaryCharges charge *
        physlibElementaryChargeInCoulombs := by
  let uElementary : UnitChoices :=
    {UnitChoices.SI with charge := ChargeUnit.elementaryCharge}
  let uCoulomb : UnitChoices :=
    {UnitChoices.SI with charge := ChargeUnit.coulombs}
  have hCovariance := charge.property uElementary uCoulomb
  change charge uCoulomb =
    (UnitChoices.dimScale uElementary uCoulomb C𝓭) •
      charge uElementary at hCovariance
  have hScaled : charge uCoulomb =
      (ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) •
        charge uElementary := by
    simpa [uElementary, uCoulomb, UnitChoices.dimScale, C𝓭] using
      hCovariance
  have hReadout :=
    congrArg (fun x => ((x.val : NNReal) : ℝ)) hScaled
  simpa [uElementary, uCoulomb, chargeInCoulombs,
    chargeInElementaryCharges, chargeReadout,
    physlibElementaryChargeInCoulombs, WithDim.smul_val,
    NNReal.smul_def, mul_comm] using hReadout

/-!
Energy conservation gives the exact closest-approach relation

`r_min = 2 k q_alpha q_Au / (m_alpha v_i^2)`.

No numerical answer choice is used in this derivation.
-/
lemma closestApproachDistance_exact
    (setup : AlphaGoldClosestApproachSetup)
    (_scenario : MatchesProblemScenarioAndData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalAlphaGoldParameters setup)
    (_kinetic : SatisfiesClassicalKineticEnergyLaw setup)
    (_coulomb : SatisfiesRepulsiveCoulombPotentialLaw setup)
    (_conservation : SatisfiesMechanicalEnergyConservation setup) :
    lengthInMeters setup.closestApproachDistance =
      2 * setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.chargeMagnitude .alphaParticle) *
          chargeInCoulombs (setup.chargeMagnitude .goldNucleus) /
        (massInKilograms setup.alphaMass *
          speedInMetersPerSecond (setup.speedAt .beforeInteraction) ^ 2) := by
  have hEnergy := _conservation.energyBalance
  rw [_kinetic.kineticEnergyAtEachStage .beforeInteraction,
    _coulomb.initialPotentialAtInfinity,
    _kinetic.kineticEnergyAtEachStage .closestApproach,
    _coulomb.closestApproachPotential,
    _figure.speedAtClosestApproachIsZero] at hEnergy
  norm_num at hEnergy
  have hDistance :
      lengthInMeters setup.closestApproachDistance ≠ 0 :=
    ne_of_gt _physical.closestDistancePositive
  have hMass : massInKilograms setup.alphaMass ≠ 0 :=
    ne_of_gt _physical.alphaMassPositive
  have hSpeed :
      speedInMetersPerSecond (setup.speedAt .beforeInteraction) ≠ 0 :=
    ne_of_gt _physical.initialSpeedPositive
  have hDenominator :
      massInKilograms setup.alphaMass *
          speedInMetersPerSecond (setup.speedAt .beforeInteraction) ^ 2 ≠ 0 :=
    mul_ne_zero hMass (pow_ne_zero 2 hSpeed)
  field_simp [hDistance] at hEnergy
  field_simp [hDenominator]
  nlinarith [hEnergy]

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The closest-approach distance printed for each choice, in metres. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 22 / (10 : ℝ) ^ 15
  | .B => 27 / (10 : ℝ) ^ 15
  | .C => 31 / (10 : ℝ) ^ 15
  | .D => 34 / (10 : ℝ) ^ 15

/-- The answer label recorded in the source dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Agreement at the precision of a value printed to the nearest
`0.1 * 10^-14 m`; half a displayed unit is `5 * 10^-16 m`.
-/
def MatchesDisplayedClosestApproach
    (setup : AlphaGoldClosestApproachSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.closestApproachDistance -
      choice.distanceInMeters| < 5 / (10 : ℝ) ^ 16

/-- Exactly one displayed choice agrees with the physical distance. -/
def IsUniqueMatchingDisplayedClosestApproach
    (setup : AlphaGoldClosestApproachSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedClosestApproach setup choice ∧
    ∀ other : AnswerChoice, other ≠ choice →
      ¬ MatchesDisplayedClosestApproach setup other

/-!
With the reference alpha mass, exact elementary charge, and free-space
Coulomb constant, the physical result lies strictly between
`2.65 * 10^-14 m` and `2.75 * 10^-14 m`.
-/
lemma closestApproachDistance_numericalBounds
    (setup : AlphaGoldClosestApproachSetup)
    (_scenario : MatchesProblemScenarioAndData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_constants : UsesReferenceAlphaGoldConstants setup)
    (_physical : HasPhysicalAlphaGoldParameters setup)
    (_kinetic : SatisfiesClassicalKineticEnergyLaw setup)
    (_coulomb : SatisfiesRepulsiveCoulombPotentialLaw setup)
    (_conservation : SatisfiesMechanicalEnergyConservation setup) :
    265 / (10 : ℝ) ^ 16 <
        lengthInMeters setup.closestApproachDistance ∧
      lengthInMeters setup.closestApproachDistance <
        275 / (10 : ℝ) ^ 16 := by
  have hExact := closestApproachDistance_exact setup _scenario _figure
    _physical _kinetic _coulomb _conservation
  have hAlphaCharge :=
    chargeInCoulombs_eq_elementaryChargeMultiple
      (setup.chargeMagnitude .alphaParticle)
  have hGoldCharge :=
    chargeInCoulombs_eq_elementaryChargeMultiple
      (setup.chargeMagnitude .goldNucleus)
  rw [_figure.alphaChargeLabelAgrees] at hAlphaCharge
  rw [_figure.goldChargeLabelAgrees] at hGoldCharge
  rw [hExact, _constants.coulombConstantCalibration, hAlphaCharge,
    hGoldCharge, _constants.alphaMassCalibration,
    _scenario.statedInitialSpeed]
  norm_num [physlibElementaryChargeInCoulombs,
    ChargeUnit.elementaryCharge, ChargeUnit.scale,
    ChargeUnit.coulombs, ChargeUnit.div_eq_val, NNReal.toReal]

/-!
The closest approach is determined by Coulomb repulsion and energy
conservation.  Its SI readout is about `2.7 * 10^-14 m`, making B the unique
matching displayed choice.

This formalizes `thm:physics:phyx_mini_0635:target`.
-/
theorem problem_phyx_mini_0635
    (setup : AlphaGoldClosestApproachSetup)
    (hScenario : MatchesProblemScenarioAndData setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hConstants : UsesReferenceAlphaGoldConstants setup)
    (hPhysical : HasPhysicalAlphaGoldParameters setup)
    (hKinetic : SatisfiesClassicalKineticEnergyLaw setup)
    (hCoulomb : SatisfiesRepulsiveCoulombPotentialLaw setup)
    (hConservation : SatisfiesMechanicalEnergyConservation setup) :
    lengthInMeters setup.closestApproachDistance =
        2 * setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.chargeMagnitude .alphaParticle) *
            chargeInCoulombs (setup.chargeMagnitude .goldNucleus) /
          (massInKilograms setup.alphaMass *
            speedInMetersPerSecond (setup.speedAt .beforeInteraction) ^ 2) ∧
      IsUniqueMatchingDisplayedClosestApproach setup
        recordedDatasetAnswer := by
  constructor
  · exact closestApproachDistance_exact setup hScenario hFigure hPhysical
      hKinetic hCoulomb hConservation
  · have hBounds := closestApproachDistance_numericalBounds setup
      hScenario hFigure hConstants hPhysical hKinetic hCoulomb hConservation
    rcases hBounds with ⟨hLower, hUpper⟩
    unfold IsUniqueMatchingDisplayedClosestApproach
    constructor
    · unfold MatchesDisplayedClosestApproach
      simp only [recordedDatasetAnswer, AnswerChoice.distanceInMeters]
      rw [abs_lt]
      constructor <;> norm_num at hLower hUpper ⊢ <;> linarith
    · intro other hOther hMatches
      cases other <;>
        simp_all [recordedDatasetAnswer, MatchesDisplayedClosestApproach,
          AnswerChoice.distanceInMeters, abs_lt] <;>
        norm_num at * <;>
        linarith

end PhyXMiniProblems.ProblemPhyXMini0635
