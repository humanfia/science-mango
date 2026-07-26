import Mathlib
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0866

open Dimension

/-!
# Proton reversing between parallel capacitor plates

A proton starts midway between parallel capacitor plates with speed
`200000 m/s`, initially moving toward the right-hand positive plate.  The
left-hand plate is labelled `0 V` and the right-hand plate `500 V`.  The
proton turns before reaching the positive plate and subsequently collides
with the negative plate.

Mass, charge magnitude, speed, electric potential, and energy are represented
by unit-independent Physlib quantities.  Real numbers appear only as named SI
readouts, literal diagram coordinates, and displayed answer values.  In
particular, the collision speed is an independent physical observable and is
not defined from answer choice D.

Assumption/target split:

* `MatchesCapacitorProtonScenario` records the particle, plate, midpoint,
  direction, turning-point, and collision roles;
* `MatchesSuppliedCapacitorFigureAndData` records the literal `0 V`, `500 V`,
  and `200,000 m/s` readouts and the visible marks and arrows;
* `HasStandardProtonCalibration` supplies the standard proton mass and
  elementary-charge calibrations;
* `SatisfiesUniformParallelPlatePotentialLaw` and
  `SatisfiesElectrostaticEnergyLaws` state the governing potential and energy
  relations; and
* the numerical collision-speed window and selection of answer D occur only
  in lemma or theorem conclusions.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- The physical dimension `L T⁻¹` of speed. -/
def speedDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- The dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent physical electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- SI mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- SI charge-magnitude readout in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- SI speed readout in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- SI electric-potential readout in volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- SI energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
The exact elementary-charge magnitude in coulombs, grounded in Physlib's
`ChargeUnit.elementaryCharge` rather than introduced as an untyped decimal.
-/
def elementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-- CODATA proton mass readout used by the problem's nonrelativistic model. -/
def standardProtonMassInKilograms : ℝ :=
  167262192595 / (10 : ℝ) ^ 38

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two capacitor plates as placed in the primary bitmap. -/
inductive PlateLabel where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The electrostatic role of a capacitor plate. -/
inductive PlatePolarity where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-- Particle species distinguished by this model. -/
inductive ParticleSpecies where
  | proton
  | other
  deriving DecidableEq, Fintype, Repr

/-- Sign of a particle's electric charge. -/
inductive ChargeSign where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-- Arrangement of the two long capacitor plates. -/
inductive PlateArrangement where
  | parallel
  | nonparallel
  deriving DecidableEq, Fintype, Repr

/-- Horizontal directions named by the side-view diagram. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Fintype, Repr

/-- Named instants in the proton's one-dimensional motion. -/
inductive MotionEvent where
  | launch
  | turningPoint
  | collision
  deriving DecidableEq, Fintype, Repr

/-- Qualitative locations across the gap between the plates. -/
inductive AcrossGapLocation where
  | leftPlate
  | midpoint
  | betweenMidpointAndRightPlate
  | rightPlate
  deriving DecidableEq, Fintype, Repr

/-- The charge marks drawn repeatedly inside a plate. -/
inductive DrawnPlateMark where
  | minus
  | plus
  deriving DecidableEq, Fintype, Repr

/-!
Literal features of `phyx_data/test_image/866.png`.  The real-valued horizontal
coordinates are diagram coordinates only; they are not physical lengths.
-/
structure CapacitorProtonFigure where
  plateHorizontalCoordinate : PlateLabel → ℝ
  printedPotentialLabel : PlateLabel → String
  repeatedMark : PlateLabel → DrawnPlateMark
  repeatedMarkCount : PlateLabel → ℕ
  protonDrawnAsRedCircle : Bool
  protonContainsPlusSign : Bool
  printedSpeedText : String
  shortVelocityArrowDirection : HorizontalDirection
  trajectoryTerminalArrowDirection : HorizontalDirection
  trajectoryTurnsBack : Bool

/-!
Independent physical observables for the capacitor experiment.  Neither the
collision speed nor any displayed answer is fixed by this structure.
-/
structure CapacitorProtonSetup where
  particleSpecies : ParticleSpecies
  particleChargeSign : ChargeSign
  plateArrangement : PlateArrangement
  platePolarity : PlateLabel → PlatePolarity
  platePotential : PlateLabel → ElectricPotentialQuantity
  particleMass : MassQuantity
  particleChargeMagnitude : ChargeMagnitudeQuantity
  locationAt : MotionEvent → AcrossGapLocation
  speedAt : MotionEvent → SpeedQuantity
  electricPotentialAt : MotionEvent → ElectricPotentialQuantity
  kineticEnergyAt : MotionEvent → DimEnergy
  electricPotentialEnergyAt : MotionEvent → DimEnergy
  launchDirection : HorizontalDirection
  collisionDirection : HorizontalDirection
  electricFieldDirection : HorizontalDirection
  collisionPlate : PlateLabel
  figure : CapacitorProtonFigure

/-! ## Scenario and figure/data readouts -/

/-!
Qualitative physical roles stated in the prose and represented by the curved
trajectory.  The zero speed at the turning point expresses reversal of this
one-dimensional motion; it does not constrain the requested collision speed.
-/
structure MatchesCapacitorProtonScenario
    (setup : CapacitorProtonSetup) : Prop where
  particleIsProton : setup.particleSpecies = .proton
  protonChargeIsPositive : setup.particleChargeSign = .positive
  platesAreParallel : setup.plateArrangement = .parallel
  leftPlateIsNegative : setup.platePolarity .left = .negative
  rightPlateIsPositive : setup.platePolarity .right = .positive
  protonStartsAtMidpoint : setup.locationAt .launch = .midpoint
  protonTurnsTowardPositivePlate :
    setup.locationAt .turningPoint = .betweenMidpointAndRightPlate
  protonReversesAtRest :
    speedInMetersPerSecond (setup.speedAt .turningPoint) = 0
  protonCollidesWithLeftPlate : setup.locationAt .collision = .leftPlate
  collisionPlateIsNegative : setup.collisionPlate = .left
  initiallyMovesTowardPositivePlate : setup.launchDirection = .rightward
  movesLeftAtCollision : setup.collisionDirection = .leftward
  electricFieldPointsFromPositiveToNegative :
    setup.electricFieldDirection = .leftward

/-!
Readouts and visual facts transcribed from the primary bitmap.  The bitmap has
five cyan minus marks on the left plate and five red plus marks on the right.
No collision-speed number occurs here.
-/
structure MatchesSuppliedCapacitorFigureAndData
    (setup : CapacitorProtonSetup) : Prop where
  leftPlateIsDrawnLeftOfRightPlate :
    setup.figure.plateHorizontalCoordinate .left <
      setup.figure.plateHorizontalCoordinate .right
  leftPotentialText : setup.figure.printedPotentialLabel .left = "0 V"
  rightPotentialText : setup.figure.printedPotentialLabel .right = "500 V"
  leftPlateHasMinusMarks : setup.figure.repeatedMark .left = .minus
  rightPlateHasPlusMarks : setup.figure.repeatedMark .right = .plus
  fiveLeftMarks : setup.figure.repeatedMarkCount .left = 5
  fiveRightMarks : setup.figure.repeatedMarkCount .right = 5
  protonIsRedCircle : setup.figure.protonDrawnAsRedCircle = true
  protonHasVisiblePlusSign : setup.figure.protonContainsPlusSign = true
  displayedInitialSpeedText :
    setup.figure.printedSpeedText = "200,000 m/s"
  shortArrowPointsRight :
    setup.figure.shortVelocityArrowDirection = .rightward
  terminalArrowPointsLeft :
    setup.figure.trajectoryTerminalArrowDirection = .leftward
  trajectoryTurnsBack : setup.figure.trajectoryTurnsBack = true
  leftPlatePotentialReadout :
    electricPotentialInVolts (setup.platePotential .left) = 0
  rightPlatePotentialReadout :
    electricPotentialInVolts (setup.platePotential .right) = 500
  launchSpeedReadout :
    speedInMetersPerSecond (setup.speedAt .launch) = 200000

/-!
Standard physical calibration of the proton mass and positive elementary
charge.  These data do not mention the unknown collision speed.
-/
structure HasStandardProtonCalibration
    (setup : CapacitorProtonSetup) : Prop where
  protonMassReadout :
    massInKilograms setup.particleMass = standardProtonMassInKilograms
  protonChargeReadout :
    chargeMagnitudeInCoulombs setup.particleChargeMagnitude =
      elementaryChargeInCoulombs

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalCapacitorProtonParameters
    (setup : CapacitorProtonSetup) : Prop where
  protonMassPositive : 0 < massInKilograms setup.particleMass
  protonChargeMagnitudePositive :
    0 < chargeMagnitudeInCoulombs setup.particleChargeMagnitude
  launchSpeedPositive :
    0 < speedInMetersPerSecond (setup.speedAt .launch)

/-! ## Governing electrostatic and mechanical laws -/

/-!
For ideal parallel plates, electric potential varies affinely across the gap.
Thus the geometric midpoint has the average plate potential, and collision at
a plate has that plate's potential.  The turning-point inequalities encode
that the shown reversal occurs strictly inside the gap.
-/
structure SatisfiesUniformParallelPlatePotentialLaw
    (setup : CapacitorProtonSetup) : Prop where
  launchPotentialAtMidpoint :
    electricPotentialInVolts (setup.electricPotentialAt .launch) =
      (electricPotentialInVolts (setup.platePotential .left) +
          electricPotentialInVolts (setup.platePotential .right)) / 2
  collisionPotentialAtCollisionPlate :
    electricPotentialInVolts (setup.electricPotentialAt .collision) =
      electricPotentialInVolts (setup.platePotential setup.collisionPlate)
  turningPotentialAboveLaunchPotential :
    electricPotentialInVolts (setup.electricPotentialAt .launch) <
      electricPotentialInVolts (setup.electricPotentialAt .turningPoint)
  turningPotentialBelowPositivePlate :
    electricPotentialInVolts (setup.electricPotentialAt .turningPoint) <
      electricPotentialInVolts (setup.platePotential .right)

/-!
The nonrelativistic kinetic-energy law `K = m v² / 2`, electrostatic
potential energy `U = q V` for a positive proton, and conservation of `K + U`
throughout the ideal field.  These are general laws over all three named
events, not a specialization to the numerical answer.
-/
structure SatisfiesElectrostaticEnergyLaws
    (setup : CapacitorProtonSetup) : Prop where
  nonrelativisticKineticEnergy : ∀ event : MotionEvent,
    energyInJoules (setup.kineticEnergyAt event) =
      massInKilograms setup.particleMass *
        speedInMetersPerSecond (setup.speedAt event) ^ 2 / 2
  positiveChargePotentialEnergy : ∀ event : MotionEvent,
    energyInJoules (setup.electricPotentialEnergyAt event) =
      chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
        electricPotentialInVolts (setup.electricPotentialAt event)
  mechanicalEnergyConservedFromLaunch : ∀ event : MotionEvent,
    energyInJoules (setup.kineticEnergyAt event) +
        energyInJoules (setup.electricPotentialEnergyAt event) =
      energyInJoules (setup.kineticEnergyAt .launch) +
        energyInJoules (setup.electricPotentialEnergyAt .launch)

/-! ## Displayed choices and current target -/

/-- Labels of the four displayed speed choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in metres per second printed beside an answer label. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 159000
  | .B => 149000
  | .C => 219000
  | .D => 296000

/-!
The printed values have three significant figures, so a speed agrees with a
choice when it lies within half of the last displayed `1000 m/s` increment.
-/
def RoundsToDisplayedSpeed
    (setup : CapacitorProtonSetup) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond (setup.speedAt .collision) -
      displayedSpeedInMetersPerSecond choice| ≤ 500

/-- A choice is at least as close to the physical collision speed as any other. -/
def IsClosestDisplayedSpeed
    (setup : CapacitorProtonSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |speedInMetersPerSecond (setup.speedAt .collision) -
        displayedSpeedInMetersPerSecond choice| ≤
      |speedInMetersPerSecond (setup.speedAt .collision) -
        displayedSpeedInMetersPerSecond alternative|

/-!
The uniform-potential law places the launch midpoint at `250 V` and the
negative collision plate at `0 V`.  Both are derived relations.
-/
lemma launch_and_collision_potential_readouts
    (setup : CapacitorProtonSetup)
    (hScenario : MatchesCapacitorProtonScenario setup)
    (hData : MatchesSuppliedCapacitorFigureAndData setup)
    (hPotential : SatisfiesUniformParallelPlatePotentialLaw setup) :
    electricPotentialInVolts (setup.electricPotentialAt .launch) = 250 ∧
      electricPotentialInVolts (setup.electricPotentialAt .collision) = 0 := by
  constructor
  · rw [hPotential.launchPotentialAtMidpoint,
      hData.leftPlatePotentialReadout, hData.rightPlatePotentialReadout]
    norm_num
  · rw [hPotential.collisionPotentialAtCollisionPlate,
      hScenario.collisionPlateIsNegative, hData.leftPlatePotentialReadout]

/-!
Energy conservation determines the collision speed squared before any decimal
rounding or comparison with the answer choices.
-/
lemma collision_speed_squared_from_energy_conservation
    (setup : CapacitorProtonSetup)
    (hPhysical : HasPhysicalCapacitorProtonParameters setup)
    (hLaws : SatisfiesElectrostaticEnergyLaws setup) :
    speedInMetersPerSecond (setup.speedAt .collision) ^ 2 =
      speedInMetersPerSecond (setup.speedAt .launch) ^ 2 +
        2 * chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
            (electricPotentialInVolts (setup.electricPotentialAt .launch) -
              electricPotentialInVolts
                (setup.electricPotentialAt .collision)) /
          massInKilograms setup.particleMass := by
  have hMassNe :
      massInKilograms setup.particleMass ≠ 0 :=
    ne_of_gt hPhysical.protonMassPositive
  have hConservation :=
    hLaws.mechanicalEnergyConservedFromLaunch .collision
  rw [hLaws.nonrelativisticKineticEnergy,
    hLaws.positiveChargePotentialEnergy,
    hLaws.nonrelativisticKineticEnergy,
    hLaws.positiveChargePotentialEnergy] at hConservation
  field_simp [hMassNe]
  nlinarith

/-!
With the standard proton calibration and the supplied readouts, the positive
collision speed is within `500 m/s` of `296000 m/s = 2.96 × 10⁵ m/s`.
-/
lemma collision_speed_rounds_to_choice_D
    (setup : CapacitorProtonSetup)
    (hScenario : MatchesCapacitorProtonScenario setup)
    (hData : MatchesSuppliedCapacitorFigureAndData setup)
    (hCalibration : HasStandardProtonCalibration setup)
    (hPhysical : HasPhysicalCapacitorProtonParameters setup)
    (hPotential : SatisfiesUniformParallelPlatePotentialLaw setup)
    (hLaws : SatisfiesElectrostaticEnergyLaws setup) :
    RoundsToDisplayedSpeed setup .D := by
  obtain ⟨hLaunchPotential, hCollisionPotential⟩ :=
    launch_and_collision_potential_readouts setup hScenario hData hPotential
  have hSpeedSq :=
    collision_speed_squared_from_energy_conservation setup hPhysical hLaws
  rw [hData.launchSpeedReadout, hCalibration.protonChargeReadout,
    hLaunchPotential, hCollisionPotential,
    hCalibration.protonMassReadout] at hSpeedSq
  norm_num [elementaryChargeInCoulombs, ChargeUnit.elementaryCharge,
    standardProtonMassInKilograms] at hSpeedSq
  unfold RoundsToDisplayedSpeed displayedSpeedInMetersPerSecond
  change speedInMetersPerSecond (setup.speedAt .collision) ^ 2 =
    40000000000 +
      2 * (801088317 / 5000000000000000000000000000 : ℝ) * 250 /
        (33452438519 /
          20000000000000000000000000000000000000 : ℝ) at hSpeedSq
  norm_num at hSpeedSq ⊢
  have hSpeedNonnegative :
      0 ≤ speedInMetersPerSecond (setup.speedAt .collision) :=
    NNReal.coe_nonneg _
  rw [abs_le]
  constructor <;> nlinarith [hSpeedSq]

/-!
The proton therefore collides with the negative plate at the speed represented
by choice D.  The exact squared-speed relation is retained alongside the
three-significant-figure numerical conclusion.
-/
theorem proton_collision_speed_matches_choice_D
    (setup : CapacitorProtonSetup)
    (hScenario : MatchesCapacitorProtonScenario setup)
    (hData : MatchesSuppliedCapacitorFigureAndData setup)
    (hCalibration : HasStandardProtonCalibration setup)
    (hPhysical : HasPhysicalCapacitorProtonParameters setup)
    (hPotential : SatisfiesUniformParallelPlatePotentialLaw setup)
    (hLaws : SatisfiesElectrostaticEnergyLaws setup) :
    speedInMetersPerSecond (setup.speedAt .collision) ^ 2 =
        speedInMetersPerSecond (setup.speedAt .launch) ^ 2 +
          2 * chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
              (electricPotentialInVolts
                  (setup.electricPotentialAt .launch) -
                electricPotentialInVolts
                  (setup.electricPotentialAt .collision)) /
            massInKilograms setup.particleMass ∧
      RoundsToDisplayedSpeed setup .D ∧
      displayedSpeedInMetersPerSecond .D = 296000 ∧
      IsClosestDisplayedSpeed setup .D := by
  refine ⟨collision_speed_squared_from_energy_conservation setup hPhysical hLaws,
    collision_speed_rounds_to_choice_D setup hScenario hData hCalibration
      hPhysical hPotential hLaws,
    by norm_num [displayedSpeedInMetersPerSecond], ?_⟩
  have hRound :=
    collision_speed_rounds_to_choice_D setup hScenario hData hCalibration
      hPhysical hPotential hLaws
  have hRound' :
      |speedInMetersPerSecond (setup.speedAt .collision) - 296000| ≤ 500 := by
    simpa [RoundsToDisplayedSpeed, displayedSpeedInMetersPerSecond] using hRound
  have hLower :
      295500 ≤ speedInMetersPerSecond (setup.speedAt .collision) := by
    have := (abs_le.mp hRound').1
    linarith
  intro alternative
  fin_cases alternative <;> simp only [displayedSpeedInMetersPerSecond]
  · exact hRound'.trans (by rw [abs_of_nonneg] <;> linarith)
  · exact hRound'.trans (by rw [abs_of_nonneg] <;> linarith)
  · exact hRound'.trans (by rw [abs_of_nonneg] <;> linarith)
  · exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0866
