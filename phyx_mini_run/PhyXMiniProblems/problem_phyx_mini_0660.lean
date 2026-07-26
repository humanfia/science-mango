import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.QuantumMechanics.RectangularBarrier.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0660

open Dimension

/-!
# Alpha decay through a rectangular Coulomb barrier

The supplied graph is a one-dimensional approximation to the nuclear
potential for a nucleus with mass number approximately `235`.  A `15 fm`
central well of depth `-60 MeV` is flanked by two `20 fm` rectangular Coulomb
barriers whose tops are at `30 MeV`; the alpha-particle energy line is at
`5.0 MeV`.

Lengths, mass, energies, action, and attenuation wave number are represented
by unit-independent Physlib quantities.  Real numbers occur only at named-unit
readouts, for the dimensionless mass-number estimate and tunneling
probability, and for displayed answer values.  Physlib's
`QuantumMechanics.RectangularBarrier` represents each rectangular barrier;
because that API does not expose a transmission coefficient, the standard
opaque-barrier law is an explicit governing-law premise.

Assumption/target split:

* governing laws: the evanescent decay relation and opaque rectangular-barrier
  transmission law, together with calibration of Physlib's barrier objects;
* previous-part results: none;
* figure/data readouts: `A ≈ 235`, the `15 fm` nuclear diameter, both `20 fm`
  barriers, the `30 MeV` barrier top, `-60 MeV` well bottom, `5.0 MeV` energy
  line, graph labels, and standard alpha/Planck reference data;
* current conclusions: the `25 MeV` forbidden-region energy difference and
  the tunneling probability rounding to `9.9 × 10⁻³⁹`, so none of the four
  displayed source choices matches the stated model with standard constants.

The dataset's recorded choice C is retained below only as answer metadata.
It is not a physical premise and is not asserted by the target theorem.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent physical energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- The physical dimension `mass * length² / time` of action. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative inverse length used for under-barrier attenuation. -/
abbrev InverseLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Read a physical length in a selected named unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in femtometres. -/
def lengthInFemtometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.femtometers length

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read an energy in coherent SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read an energy in electron-volts using Physlib's calibrated unit. -/
def energyInElectronVolts (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.electronVolt UnitChoices.SI).val

/-- Read an energy in mega-electron-volts. -/
def energyInMegaElectronVolts (energy : EnergyQuantity) : ℝ :=
  energyInElectronVolts energy / 1_000_000

/-- Read an action in coherent SI joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read an attenuation wave number in inverse metres. -/
def inverseLengthInInverseMeters
    (inverseLength : InverseLengthQuantity) : ℝ :=
  ((inverseLength UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure vocabulary -/

/-- Particle species represented by the energy line. -/
inductive ParticleSpecies where
  | alphaParticle
  | other
  deriving DecidableEq, Repr

/-- Physical origin assigned to the modeled barriers. -/
inductive BarrierOrigin where
  | coulombRepulsion
  | other
  deriving DecidableEq, Repr

/-- The two barriers flanking the nuclear well in the one-dimensional graph. -/
inductive BarrierSide where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The three finite-width regions drawn in the graph. -/
inductive PotentialRegion where
  | leftBarrier
  | nuclearWell
  | rightBarrier
  deriving DecidableEq, Fintype, Repr

/-- The two axes of the supplied potential-energy plot. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical role assigned to each plot axis. -/
inductive PlotAxisQuantity where
  | position
  | potentialEnergy
  deriving DecidableEq, Repr

/-- Qualitative shape of the plotted potential. -/
inductive PotentialProfileShape where
  | symmetricRectangularBarriersAndWell
  | other
  deriving DecidableEq, Repr

/-- Region of the primary figure corresponding to a barrier side. -/
def BarrierSide.figureRegion : BarrierSide → PotentialRegion
  | .left => .leftBarrier
  | .right => .rightBarrier

/-!
Typed geometric and energy information carried by the supplied graph.
No tunneling probability or answer choice is stored in the figure.
-/
structure NuclearPotentialFigure where
  axisQuantity : PlotAxis → PlotAxisQuantity
  axisLabel : PlotAxis → String
  profileShape : PotentialProfileShape
  regionWidth : PotentialRegion → LengthQuantity
  regionPotentialEnergy : PotentialRegion → EnergyQuantity
  exteriorPotentialEnergy : EnergyQuantity
  alphaEnergyLine : EnergyQuantity

/-!
Independent physical quantities in the alpha-decay model.  In particular,
the attenuation wave number and tunneling probability are fields constrained
only by the general laws below, not definitions of the recorded answer.
-/
structure AlphaDecayBarrierSetup where
  particleSpecies : ParticleSpecies
  parentNucleusMassNumber : ℕ
  barrierOrigin : BarrierOrigin
  alphaInitiallyInsideNucleus : Bool
  usesOneDimensionalModel : Bool
  nucleusDiameter : LengthQuantity
  barrierWidth : BarrierSide → LengthQuantity
  barrierHeight : EnergyQuantity
  nuclearWellBottom : EnergyQuantity
  alphaEnergy : EnergyQuantity
  alphaMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  attenuationWaveNumber : InverseLengthQuantity
  outgoingBarrierSide : BarrierSide
  tunnelingProbability : ℝ
  scalarBarrierModel : BarrierSide → QuantumMechanics.RectangularBarrier
  figure : NuclearPotentialFigure

/-! ## Scenario, figure/data readouts, reference data, and governing laws -/

/-- Qualitative physical model stated in the problem. -/
structure MatchesAlphaDecayScenario
    (setup : AlphaDecayBarrierSetup) : Prop where
  particleIsAlpha : setup.particleSpecies = .alphaParticle
  barrierIsCoulombic : setup.barrierOrigin = .coulombRepulsion
  alphaStartsInsideNucleus : setup.alphaInitiallyInsideNucleus = true
  oneDimensionalApproximation : setup.usesOneDimensionalModel = true

/-!
Numerical information stated in the prose.  The interval formalizes the
source's approximate mass-number description `A ≈ 235`.  This premise has no
tunneling-probability field.
-/
structure MatchesProblemProseReadouts
    (setup : AlphaDecayBarrierSetup) : Prop where
  massNumberApproximately235 :
    setup.parentNucleusMassNumber ∈ Set.Icc 234 236
  nucleusDiameterFemtometers :
    lengthInFemtometers setup.nucleusDiameter = 15
  eachBarrierWidthFemtometers :
    ∀ side, lengthInFemtometers (setup.barrierWidth side) = 20
  rectangularBarrierHeightMegaElectronVolts :
    energyInMegaElectronVolts setup.barrierHeight = 30

/-!
Labels, geometry, and energy levels read directly from image `660.png`.
The graph shows two equal rectangular barriers, a central well whose width is
the nuclear diameter, the exterior zero level, and the alpha energy line.
-/
structure MatchesSuppliedNuclearPotentialFigure
    (setup : AlphaDecayBarrierSetup) : Prop where
  horizontalAxisRole :
    setup.figure.axisQuantity .horizontal = .position
  verticalAxisRole :
    setup.figure.axisQuantity .vertical = .potentialEnergy
  horizontalAxisLabel : setup.figure.axisLabel .horizontal = "x"
  verticalAxisLabel : setup.figure.axisLabel .vertical = "U (MeV)"
  plottedShape :
    setup.figure.profileShape = .symmetricRectangularBarriersAndWell
  leftBarrierWidthIsPhysicalWidth :
    setup.figure.regionWidth .leftBarrier = setup.barrierWidth .left
  wellWidthIsNuclearDiameter :
    setup.figure.regionWidth .nuclearWell = setup.nucleusDiameter
  rightBarrierWidthIsPhysicalWidth :
    setup.figure.regionWidth .rightBarrier = setup.barrierWidth .right
  shownBarrierWidthsFemtometers :
    ∀ side : BarrierSide,
      lengthInFemtometers
          (setup.figure.regionWidth (BarrierSide.figureRegion side)) = 20
  shownWellWidthFemtometers :
    lengthInFemtometers (setup.figure.regionWidth .nuclearWell) = 15
  leftBarrierAtPhysicalHeight :
    setup.figure.regionPotentialEnergy .leftBarrier = setup.barrierHeight
  rightBarrierAtPhysicalHeight :
    setup.figure.regionPotentialEnergy .rightBarrier = setup.barrierHeight
  wellAtPhysicalBottom :
    setup.figure.regionPotentialEnergy .nuclearWell = setup.nuclearWellBottom
  shownBarrierTopMegaElectronVolts :
    energyInMegaElectronVolts setup.barrierHeight = 30
  shownWellBottomMegaElectronVolts :
    energyInMegaElectronVolts setup.nuclearWellBottom = -60
  shownExteriorLevelMegaElectronVolts :
    energyInMegaElectronVolts setup.figure.exteriorPotentialEnergy = 0
  shownAlphaEnergyIsPhysicalEnergy :
    setup.figure.alphaEnergyLine = setup.alphaEnergy
  shownAlphaEnergyMegaElectronVolts :
    energyInMegaElectronVolts setup.figure.alphaEnergyLine = 5

/-!
Standard alpha-particle and reduced-Planck reference data needed for the
textbook estimate.  These calibrations do not contain a transmission result.
-/
structure UsesStandardAlphaReferenceData
    (setup : AlphaDecayBarrierSetup) : Prop where
  alphaMassKilograms :
    massInKilograms setup.alphaMass = 6.6446573357e-27
  reducedPlanckJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/-!
Calibrate each Physlib scalar rectangular barrier against the dimensionful
alpha mass, width, and barrier energy.  Absolute face coordinates are not
fixed because only the widths are relevant to the tunneling calculation.
-/
structure MatchesPhyslibRectangularBarriers
    (setup : AlphaDecayBarrierSetup) : Prop where
  scalarMassIsKilogramReadout : ∀ side,
    (setup.scalarBarrierModel side).m = massInKilograms setup.alphaMass
  scalarWidthIsMeterReadout : ∀ side,
    (setup.scalarBarrierModel side).upper -
        (setup.scalarBarrierModel side).lower =
      lengthInMeters (setup.barrierWidth side)
  scalarHeightIsJouleReadout : ∀ side,
    (setup.scalarBarrierModel side).V₀ =
      energyInJoules setup.barrierHeight

/-- Positivity and branch conditions selecting a physical tunneling setup. -/
structure HasPhysicalAlphaTunnelingParameters
    (setup : AlphaDecayBarrierSetup) : Prop where
  positiveNucleusDiameter : 0 < lengthInMeters setup.nucleusDiameter
  positiveBarrierWidth :
    ∀ side, 0 < lengthInMeters (setup.barrierWidth side)
  positiveBarrierHeight : 0 < energyInJoules setup.barrierHeight
  positiveAlphaEnergy : 0 < energyInJoules setup.alphaEnergy
  alphaEnergyBelowBarrier :
    energyInJoules setup.alphaEnergy < energyInJoules setup.barrierHeight
  negativeWellBottom : energyInJoules setup.nuclearWellBottom < 0
  positiveAlphaMass : 0 < massInKilograms setup.alphaMass
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  positiveAttenuationWaveNumber :
    0 < inverseLengthInInverseMeters setup.attenuationWaveNumber
  opaqueBarrierRegime :
    1 < inverseLengthInInverseMeters setup.attenuationWaveNumber *
      lengthInMeters (setup.barrierWidth setup.outgoingBarrierSide)
  probabilityInUnitInterval : setup.tunnelingProbability ∈ Set.Icc 0 1

/-!
For `E < U`, the classically forbidden wave number satisfies
`κ = sqrt (2 m (U - E)) / ℏ`.  Both sides are coherent-SI inverse-metre
readouts.  No numerical transmission probability appears in this law.
-/
structure SatisfiesAlphaBarrierDecayRelation
    (setup : AlphaDecayBarrierSetup) : Prop where
  attenuationWaveNumberLaw :
    inverseLengthInInverseMeters setup.attenuationWaveNumber =
      Real.sqrt
          (2 * massInKilograms setup.alphaMass *
            (energyInJoules setup.barrierHeight -
              energyInJoules setup.alphaEnergy)) /
        actionInJouleSeconds setup.reducedPlanckAction

/-!
The opaque rectangular-barrier estimate `T = exp (-2 κ L)` for the barrier
encountered by the outgoing alpha particle.  This is a governing relation
among independent quantities, not the requested numerical specialization.
-/
structure SatisfiesOpaqueAlphaTransmissionLaw
    (setup : AlphaDecayBarrierSetup) : Prop where
  transmissionProbabilityLaw :
    setup.tunnelingProbability =
      Real.exp
        (-2 * inverseLengthInInverseMeters setup.attenuationWaveNumber *
          lengthInMeters (setup.barrierWidth setup.outgoingBarrierSide))

/-! ## Displayed answers and current conclusions -/

/-- Labels of the four dimensionless probability choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Probability printed beside each answer label, represented exactly. -/
def displayedTunnelingProbability : AnswerChoice → ℝ
  | .A => 62 / 10 ^ 40
  | .B => 64 / 10 ^ 40
  | .C => 66 / 10 ^ 40
  | .D => 68 / 10 ^ 40

/-- Answer metadata recorded by the source dataset; not a physics premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
`value` rounds to the probability `reportedValue`, where the rounding quantum
is `0.1 × 10⁻³⁹ = 10⁻⁴⁰`.  The half-open interval resolves the upper tie.
-/
def RoundsToDisplayedScientificNotation
    (value reportedValue : ℝ) : Prop :=
  reportedValue - 1 / (2 * 10 ^ 40) ≤ value ∧
    value < reportedValue + 1 / (2 * 10 ^ 40)

/-- A displayed choice is the rounded value of the modeled probability. -/
def MatchesDisplayedTunnelingProbability
    (setup : AlphaDecayBarrierSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedScientificNotation setup.tunnelingProbability
    (displayedTunnelingProbability choice)

/-!
For the `A ≈ 235` one-dimensional model in image `660.png`, an alpha at
`5.0 MeV` encounters a `20 fm`, `30 MeV` rectangular Coulomb barrier.  The
standard alpha mass, exact Physlib electron-volt conversion, Physlib's reduced
Planck constant, and opaque-barrier law give approximately
`9.8778 × 10⁻³⁹`, hence `9.9 × 10⁻³⁹` at the answer choices' displayed
precision.  This lies outside all four displayed choices, whose values range
from `6.2 × 10⁻³⁹` to `6.8 × 10⁻³⁹`.

This formalizes `thm:physics:phyx_mini_0660:target`.  Neither the supported
rounded probability nor the conclusion that no choice matches occurs in any
scenario, readout, reference-data, calibration, positivity, or governing-law
premise.  Recorded choice C occurs only in `recordedDatasetAnswer`, which is
not an assumption of this theorem.
-/
theorem problem_phyx_mini_0660
    (setup : AlphaDecayBarrierSetup)
    (_scenario : MatchesAlphaDecayScenario setup)
    (_prose : MatchesProblemProseReadouts setup)
    (_figure : MatchesSuppliedNuclearPotentialFigure setup)
    (_reference : UsesStandardAlphaReferenceData setup)
    (_barriers : MatchesPhyslibRectangularBarriers setup)
    (_physical : HasPhysicalAlphaTunnelingParameters setup)
    (_decay : SatisfiesAlphaBarrierDecayRelation setup)
    (_transmission : SatisfiesOpaqueAlphaTransmissionLaw setup) :
    energyInMegaElectronVolts setup.barrierHeight -
          energyInMegaElectronVolts setup.alphaEnergy = 25 ∧
      RoundsToDisplayedScientificNotation setup.tunnelingProbability
          (99 / 10 ^ 40) ∧
      (∀ choice : AnswerChoice,
        ¬ MatchesDisplayedTunnelingProbability setup choice) := by
  have energyInJoules_eq
      (energy : EnergyQuantity) :
      energyInJoules energy =
        (1602176634 / 10 ^ 22 : ℝ) *
          energyInMegaElectronVolts energy := by
    simp [energyInJoules, energyInMegaElectronVolts,
      energyInElectronVolts, DimEnergy.joule, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
    ring
  have alphaEnergyMegaElectronVolts :
      energyInMegaElectronVolts setup.alphaEnergy = 5 := by
    rw [← _figure.shownAlphaEnergyIsPhysicalEnergy]
    exact _figure.shownAlphaEnergyMegaElectronVolts
  have energyDifferenceMegaElectronVolts :
      energyInMegaElectronVolts setup.barrierHeight -
          energyInMegaElectronVolts setup.alphaEnergy = 25 := by
    rw [_prose.rectangularBarrierHeightMegaElectronVolts,
      alphaEnergyMegaElectronVolts]
    norm_num
  refine ⟨energyDifferenceMegaElectronVolts, ?_⟩
  have barrierEnergyJoules :
      energyInJoules setup.barrierHeight =
        (1602176634 / 10 ^ 22 : ℝ) * 30 := by
    rw [energyInJoules_eq,
      _prose.rectangularBarrierHeightMegaElectronVolts]
  have alphaEnergyJoules :
      energyInJoules setup.alphaEnergy =
        (1602176634 / 10 ^ 22 : ℝ) * 5 := by
    rw [energyInJoules_eq, alphaEnergyMegaElectronVolts]
  have energyDifferenceJoules :
      energyInJoules setup.barrierHeight -
          energyInJoules setup.alphaEnergy =
        (4005441585 / 10 ^ 21 : ℝ) := by
    rw [barrierEnergyJoules, alphaEnergyJoules]
    norm_num
  have alphaMassKilograms :
      massInKilograms setup.alphaMass =
        (66446573357 / 10 ^ 37 : ℝ) := by
    rw [_reference.alphaMassKilograms]
    norm_num
  have reducedPlanckJouleSeconds :
      actionInJouleSeconds setup.reducedPlanckAction =
        (1054571817 / 10 ^ 43 : ℝ) := by
    rw [_reference.reducedPlanckJouleSeconds]
    norm_num [Constants.ℏ]
  have lengthInMeters_eq
      (length : LengthQuantity) :
      lengthInMeters length =
        (1 / 10 ^ 15 : ℝ) * lengthInFemtometers length := by
    have unitScale :
        NNReal.toReal
            ({UnitChoices.SI with
                length := LengthUnit.femtometers}.dimScale
              UnitChoices.SI L𝓭) =
          (1 / 10 ^ 15 : ℝ) := by
      rw [UnitChoices.dimScale_apply]
      simp only [Dimension.L𝓭, Rat.cast_one, Rat.cast_zero,
        NNReal.rpow_one, NNReal.rpow_zero, mul_one]
      rw [UnitChoices.SI_length, LengthUnit.femtometers,
        LengthUnit.scale_div_self LengthUnit.meters
          ((1 / 10 : ℝ) ^ 15) (by positivity)]
      change (1 / 10 : ℝ) ^ 15 = 1 / 10 ^ 15
      ring
    have dimensionScaling := length.property
      {UnitChoices.SI with length := LengthUnit.femtometers}
      UnitChoices.SI
    have scalarScaling := congrArg
      (fun x : WithDim L𝓭 NNReal => NNReal.toReal x.val)
      dimensionScaling
    change NNReal.toReal (length UnitChoices.SI).val =
      NNReal.toReal
          ({UnitChoices.SI with
              length := LengthUnit.femtometers}.dimScale
            UnitChoices.SI L𝓭) *
        NNReal.toReal
          (length
            {UnitChoices.SI with
              length := LengthUnit.femtometers}).val at scalarScaling
    rw [unitScale] at scalarScaling
    rw [lengthInMeters, lengthInFemtometers, lengthReadout]
    exact scalarScaling
  have outgoingBarrierWidthMeters :
      lengthInMeters
          (setup.barrierWidth setup.outgoingBarrierSide) =
        (20 / 10 ^ 15 : ℝ) := by
    rw [lengthInMeters_eq,
      _prose.eachBarrierWidthFemtometers]
    ring
  have attenuationWaveNumber :
      inverseLengthInInverseMeters setup.attenuationWaveNumber =
        Real.sqrt
            (2 * (66446573357 / 10 ^ 37 : ℝ) *
              (4005441585 / 10 ^ 21 : ℝ)) /
          (1054571817 / 10 ^ 43 : ℝ) := by
    rw [_decay.attenuationWaveNumberLaw,
      alphaMassKilograms, energyDifferenceJoules,
      reducedPlanckJouleSeconds]
  have tunnelingProbability :
      setup.tunnelingProbability =
        Real.exp
          (-2 *
            (Real.sqrt
                (2 * (66446573357 / 10 ^ 37 : ℝ) *
                  (4005441585 / 10 ^ 21 : ℝ)) /
              (1054571817 / 10 ^ 43 : ℝ)) *
            (20 / 10 ^ 15 : ℝ)) := by
    rw [_transmission.transmissionProbabilityLaw,
      attenuationWaveNumber, outgoingBarrierWidthMeters]
  let radicand : ℝ :=
    2 * (66446573357 / 10 ^ 37 : ℝ) *
      (4005441585 / 10 ^ 21 : ℝ)
  let planckAction : ℝ := 1054571817 / 10 ^ 43
  let barrierWidth : ℝ := 20 / 10 ^ 15
  let exponentMagnitude : ℝ :=
    2 * (Real.sqrt radicand / planckAction) * barrierWidth
  have exponentIdentity :
      -2 *
            (Real.sqrt
                (2 * (66446573357 / 10 ^ 37 : ℝ) *
                  (4005441585 / 10 ^ 21 : ℝ)) /
              (1054571817 / 10 ^ 43 : ℝ)) *
            (20 / 10 ^ 15 : ℝ) =
        -exponentMagnitude := by
    dsimp [exponentMagnitude, radicand, planckAction, barrierWidth]
    ring
  rw [exponentIdentity] at tunnelingProbability
  have radicandNonnegative : 0 ≤ radicand := by
    positivity
  have lowerSquare :
      ((87510 / 1000 : ℝ) * planckAction /
          (2 * barrierWidth)) ^ 2 < radicand := by
    norm_num [radicand, planckAction, barrierWidth]
  have upperSquare :
      radicand <
        ((87511 / 1000 : ℝ) * planckAction /
          (2 * barrierWidth)) ^ 2 := by
    norm_num [radicand, planckAction, barrierWidth]
  have lowerRootArgumentNonnegative :
      0 ≤
        (87510 / 1000 : ℝ) * planckAction /
          (2 * barrierWidth) := by
    positivity
  have upperRootArgumentPositive :
      0 <
        (87511 / 1000 : ℝ) * planckAction /
          (2 * barrierWidth) := by
    positivity
  have lowerRoot :
      (87510 / 1000 : ℝ) * planckAction /
          (2 * barrierWidth) <
        Real.sqrt radicand :=
    (Real.lt_sqrt lowerRootArgumentNonnegative).2 lowerSquare
  have upperRoot :
      Real.sqrt radicand <
        (87511 / 1000 : ℝ) * planckAction /
          (2 * barrierWidth) :=
    (Real.sqrt_lt' upperRootArgumentPositive).2 upperSquare
  have exponentMagnitudeBounds :
      (87510 / 1000 : ℝ) < exponentMagnitude ∧
        exponentMagnitude < (87511 / 1000 : ℝ) := by
    dsimp [exponentMagnitude, radicand, planckAction, barrierWidth]
      at lowerRoot upperRoot ⊢
    constructor <;>
      norm_num at lowerRoot upperRoot ⊢ <;>
      nlinarith
  have exponentBounds :
      (-87511 / 1000 : ℝ) < -exponentMagnitude ∧
        -exponentMagnitude < (-87510 / 1000 : ℝ) := by
    constructor <;> linarith [exponentMagnitudeBounds.1,
      exponentMagnitudeBounds.2]
  let lowerSeries : ℝ :=
    ∑ i ∈ Finset.range 4,
      (489 / 1000 : ℝ) ^ i / i.factorial
  let upperSeries : ℝ :=
    (∑ i ∈ Finset.range 4,
      (490 / 1000 : ℝ) ^ i / i.factorial) +
      (490 / 1000 : ℝ) ^ 4 * (4 + 1) /
        (Nat.factorial 4 * 4)
  have lowerSeriesPositive : 0 < lowerSeries := by
    norm_num [lowerSeries, Finset.sum_range_succ, Nat.factorial]
  have upperSeriesPositive : 0 < upperSeries := by
    norm_num [upperSeries, Finset.sum_range_succ, Nat.factorial]
  have expNeg88 :
      Real.exp (-88 : ℝ) = Real.exp (-1) ^ 88 := by
    rw [show (-88 : ℝ) = (88 : ℕ) * (-1 : ℝ) by
      norm_num, Real.exp_nat_mul]
  have expNeg88Lower :
      (0.36787944116 : ℝ) ^ 88 < Real.exp (-88) := by
    rw [expNeg88]
    exact pow_lt_pow_left₀ Real.exp_neg_one_gt_d9
      (by norm_num) (by norm_num)
  have expNeg88Upper :
      Real.exp (-88) < (0.3678794412 : ℝ) ^ 88 := by
    rw [expNeg88]
    exact pow_lt_pow_left₀ Real.exp_neg_one_lt_d9
      (Real.exp_nonneg _) (by norm_num)
  have expSmallLower :
      lowerSeries ≤ Real.exp (489 / 1000 : ℝ) := by
    exact Real.sum_le_exp_of_nonneg (by norm_num) 4
  have expSmallUpper :
      Real.exp (490 / 1000 : ℝ) ≤ upperSeries := by
    exact Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
  have exponentialBounds :
      (99 / 10 ^ 40 : ℝ) - 1 / (2 * 10 ^ 40) ≤
          Real.exp (-exponentMagnitude) ∧
        Real.exp (-exponentMagnitude) <
          (99 / 10 ^ 40 : ℝ) + 1 / (2 * 10 ^ 40) := by
    constructor
    · refine le_of_lt
        (lt_trans ?_ (Real.exp_lt_exp.mpr exponentBounds.1))
      rw [show (-87511 / 1000 : ℝ) =
          -88 + 489 / 1000 by norm_num, Real.exp_add]
      calc
        (99 / 10 ^ 40 : ℝ) - 1 / (2 * 10 ^ 40) <
            (0.36787944116 : ℝ) ^ 88 * lowerSeries := by
          norm_num [lowerSeries, Finset.sum_range_succ,
            Nat.factorial]
        _ < Real.exp (-88) * lowerSeries :=
          mul_lt_mul_of_pos_right expNeg88Lower
            lowerSeriesPositive
        _ ≤ Real.exp (-88) * Real.exp (489 / 1000 : ℝ) :=
          mul_le_mul_of_nonneg_left expSmallLower
            (Real.exp_nonneg _)
    · refine lt_trans
        (Real.exp_lt_exp.mpr exponentBounds.2) ?_
      rw [show (-87510 / 1000 : ℝ) =
          -88 + 490 / 1000 by norm_num, Real.exp_add]
      calc
        Real.exp (-88) * Real.exp (490 / 1000 : ℝ) ≤
            Real.exp (-88) * upperSeries :=
          mul_le_mul_of_nonneg_left expSmallUpper
            (Real.exp_nonneg _)
        _ < (0.3678794412 : ℝ) ^ 88 * upperSeries :=
          mul_lt_mul_of_pos_right expNeg88Upper
            upperSeriesPositive
        _ < (99 / 10 ^ 40 : ℝ) + 1 / (2 * 10 ^ 40) := by
          norm_num [upperSeries, Finset.sum_range_succ,
            Nat.factorial]
  have probabilityRounding :
      RoundsToDisplayedScientificNotation setup.tunnelingProbability
        (99 / 10 ^ 40) := by
    unfold RoundsToDisplayedScientificNotation
    rw [tunnelingProbability]
    exact exponentialBounds
  refine ⟨probabilityRounding, ?_⟩
  intro choice matchingChoice
  have modeledProbabilityLower :
      (197 / (2 * 10 ^ 40) : ℝ) ≤
        setup.tunnelingProbability := by
    have lowerBound := probabilityRounding.1
    norm_num at lowerBound ⊢
    exact lowerBound
  unfold MatchesDisplayedTunnelingProbability
    RoundsToDisplayedScientificNotation at matchingChoice
  cases choice
  all_goals
    norm_num [displayedTunnelingProbability] at matchingChoice modeledProbabilityLower
  all_goals linarith

end PhyXMiniProblems.ProblemPhyXMini0660
