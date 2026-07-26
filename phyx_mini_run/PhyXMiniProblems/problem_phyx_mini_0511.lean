import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0511

open Dimension

/-!
# Threshold production of a neutral pion in a proton--proton collision

The supplied figure shows two protons of equal rest mass approaching one
another with equal speed `v`.  After the collision the two protons remain and
a neutral pion has been produced between them.  The prose states that all
three outgoing particles are at rest, so this is the production threshold in
the center-of-momentum frame.

Physical masses, speeds, signed one-dimensional velocity components, and
energies are represented by unit-independent Physlib quantities.  Real
numbers are used only for unit readouts, dimensionless speed ratios, and the
values printed in the multiple-choice list.
-/

/-! ## Dimensionful quantities and readouts -/

/-- A nonnegative physical rest mass, independent of a choice of units. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical speed, using Physlib's dimensionful speed type. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed velocity component along the horizontal collision axis. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical mass in coherent SI units, hence in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a nonnegative speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed velocity component in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Meter-per-second readout of a signed velocity component. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-!
Physlib's speed of light has a real-valued dimensionful carrier.  Its readout
is therefore kept separate from the nonnegative `speedReadout` above.
-/
def vacuumLightSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  signedVelocityReadout lengthUnit timeUnit DimSpeed.speedOfLight

/-- The coherent SI value of the physical speed of light. -/
def vacuumLightSpeedInMetersPerSecond : ℝ :=
  vacuumLightSpeedReadout LengthUnit.meters TimeUnit.seconds

/-- Read a physical energy in coherent SI units, hence in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Particle, stage, and figure labels -/

/-- The three individually tracked particles in the reaction diagram. -/
inductive ParticleLabel where
  | leftProton
  | rightProton
  | neutralPion
  deriving DecidableEq, Fintype, Repr

/-- The two particle species occurring in the reaction. -/
inductive ParticleSpecies where
  | proton
  | neutralPion
  deriving DecidableEq, Repr

/-- Species attached to each individual particle label. -/
def particleSpecies : ParticleLabel → ParticleSpecies
  | .leftProton => .proton
  | .rightProton => .proton
  | .neutralPion => .neutralPion

/-- Coarse electric-charge information supplied by the `+` signs and prose. -/
inductive ElectricChargeClass where
  | positive
  | neutral
  deriving DecidableEq, Repr

/-- Charge class of the two protons and the neutral pion. -/
def particleChargeClass : ParticleLabel → ElectricChargeClass
  | .leftProton => .positive
  | .rightProton => .positive
  | .neutralPion => .neutral

/-- State immediately before or immediately after the collision. -/
inductive CollisionStage where
  | beforeCollision
  | afterCollision
  deriving DecidableEq, Fintype, Repr

/-- Left, center, and right locations in a row of the supplied diagram. -/
inductive FigureSlot where
  | left
  | center
  | right
  deriving DecidableEq, Fintype, Repr

/-- Horizontal direction of an incoming velocity arrow. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- The red and green particle colors used by the supplied figure. -/
inductive FigureColor where
  | red
  | green
  deriving DecidableEq, Repr

/-!
The label and geometry content of the primary image.  It stores particle
placement, inward arrows, colors, labels, signs, and printed mass readouts,
but deliberately contains no numerical value for the unknown speed `v`.
-/
structure ProtonPionCollisionFigure where
  particleAtSlot : CollisionStage → FigureSlot → Option ParticleLabel
  incomingArrowDirection : ParticleLabel → Option HorizontalDirection
  incomingArrowText : ParticleLabel → Option String
  printedSpeciesName : ParticleSpecies → String
  displayedColor : ParticleSpecies → FigureColor
  printedRestMassKilograms : ParticleSpecies → ℝ
  showsPositiveChargeSign : ParticleLabel → Bool
  showsDownwardReactionArrow : Bool

/-!
All unknown physical quantities in the collision.  Particle energies and
total energies are independent dimensionful fields constrained by the laws
below.  In particular, `initialProtonSpeed` is not defined from an answer
choice or from the desired closed form.
-/
structure ProtonPionCollisionSetup where
  protonRestMass : MassQuantity
  neutralPionRestMass : MassQuantity
  initialProtonSpeed : SpeedQuantity
  particlePresentAt : CollisionStage → ParticleLabel → Bool
  velocityComponentAt :
    CollisionStage → ParticleLabel → SignedVelocityQuantity
  particleEnergyAt : CollisionStage → ParticleLabel → DimEnergy
  totalEnergyAt : CollisionStage → DimEnergy
  figure : ProtonPionCollisionFigure

/-- Rest mass of a labelled particle in a collision setup. -/
def particleRestMass
    (setup : ProtonPionCollisionSetup) : ParticleLabel → MassQuantity
  | .leftProton => setup.protonRestMass
  | .rightProton => setup.protonRestMass
  | .neutralPion => setup.neutralPionRestMass

/-! ## Scenario, primary-image evidence, and numerical data -/

/-!
The particle-content and kinematic facts from the prose.  Initially only the
two protons are present and their velocity components are equal and opposite.
Afterward both protons still exist, the pion has been produced, and all three
particles are at rest.  None of these facts fixes the magnitude of the
initial speed.
-/
structure MatchesHeadOnThresholdScenario
    (setup : ProtonPionCollisionSetup) : Prop where
  leftProtonInitiallyPresent :
    setup.particlePresentAt .beforeCollision .leftProton = true
  rightProtonInitiallyPresent :
    setup.particlePresentAt .beforeCollision .rightProton = true
  pionInitiallyAbsent :
    setup.particlePresentAt .beforeCollision .neutralPion = false
  allThreeParticlesFinallyPresent :
    ∀ particle : ParticleLabel,
      setup.particlePresentAt .afterCollision particle = true
  leftProtonMovesRightAtInitialSpeed :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedVelocityReadout lengthUnit timeUnit
          (setup.velocityComponentAt .beforeCollision .leftProton) =
        speedReadout lengthUnit timeUnit setup.initialProtonSpeed
  rightProtonMovesLeftAtInitialSpeed :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedVelocityReadout lengthUnit timeUnit
          (setup.velocityComponentAt .beforeCollision .rightProton) =
        -speedReadout lengthUnit timeUnit setup.initialProtonSpeed
  allThreeParticlesFinallyAtRest :
    ∀ (particle : ParticleLabel) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      signedVelocityReadout lengthUnit timeUnit
          (setup.velocityComponentAt .afterCollision particle) = 0

/-!
Primary-image evidence: the two inward arrows labelled `v`, red proton labels
and `+` signs, the downward reaction arrow, and a final green pion between the
surviving protons.  Printed masses are linked to physical masses separately
by `MatchesProblemMassReadouts`.
-/
structure MatchesSuppliedProtonPionFigure
    (setup : ProtonPionCollisionSetup) : Prop where
  beforeLeftSlot :
    setup.figure.particleAtSlot .beforeCollision .left =
      some .leftProton
  beforeCenterSlot :
    setup.figure.particleAtSlot .beforeCollision .center = none
  beforeRightSlot :
    setup.figure.particleAtSlot .beforeCollision .right =
      some .rightProton
  afterLeftSlot :
    setup.figure.particleAtSlot .afterCollision .left =
      some .leftProton
  afterCenterSlot :
    setup.figure.particleAtSlot .afterCollision .center =
      some .neutralPion
  afterRightSlot :
    setup.figure.particleAtSlot .afterCollision .right =
      some .rightProton
  leftIncomingArrowPointsRight :
    setup.figure.incomingArrowDirection .leftProton = some .rightward
  rightIncomingArrowPointsLeft :
    setup.figure.incomingArrowDirection .rightProton = some .leftward
  leftIncomingArrowLabel :
    setup.figure.incomingArrowText .leftProton = some "v"
  rightIncomingArrowLabel :
    setup.figure.incomingArrowText .rightProton = some "v"
  protonPrintedName :
    setup.figure.printedSpeciesName .proton = "Proton"
  pionPrintedName :
    setup.figure.printedSpeciesName .neutralPion = "Pion"
  protonDisplayedRed : setup.figure.displayedColor .proton = .red
  pionDisplayedGreen : setup.figure.displayedColor .neutralPion = .green
  protonChargeSigns :
    setup.figure.showsPositiveChargeSign .leftProton = true ∧
      setup.figure.showsPositiveChargeSign .rightProton = true
  noPionChargeSign :
    setup.figure.showsPositiveChargeSign .neutralPion = false
  reactionArrowShown : setup.figure.showsDownwardReactionArrow = true

/-!
The rest-mass data stated in the problem and printed in the image, expressed
as exact rational SI readouts:

* `1.67 × 10⁻²⁷ kg = 167 / 10²⁹ kg` for either proton;
* `2.40 × 10⁻²⁸ kg = 24 / 10²⁹ kg` for the neutral pion.

No speed or answer choice occurs in these data.
-/
structure MatchesProblemMassReadouts
    (setup : ProtonPionCollisionSetup) : Prop where
  protonMassKilograms :
    massInKilograms setup.protonRestMass = 167 / (10 : ℝ) ^ 29
  neutralPionMassKilograms :
    massInKilograms setup.neutralPionRestMass = 24 / (10 : ℝ) ^ 29
  figureProtonMassKilograms :
    setup.figure.printedRestMassKilograms .proton =
      167 / (10 : ℝ) ^ 29
  figureNeutralPionMassKilograms :
    setup.figure.printedRestMassKilograms .neutralPion =
      24 / (10 : ℝ) ^ 29

/-! ## Dimensionless ratios and physical regime -/

/-- The unknown initial proton speed as a dimensionless fraction of `c`. -/
def initialSpeedFractionOfLight (setup : ProtonPionCollisionSetup) : ℝ :=
  speedInMetersPerSecond setup.initialProtonSpeed /
    vacuumLightSpeedInMetersPerSecond

/-- Absolute speed fraction associated with a signed velocity component. -/
def velocityFractionOfLight (velocity : SignedVelocityQuantity) : ℝ :=
  |signedVelocityInMetersPerSecond velocity| /
    vacuumLightSpeedInMetersPerSecond

/-!
Positivity, subluminality, and nondegeneracy assumptions for the physical
collision.  They constrain the domain of the relativistic square root but do
not specify the requested speed.
-/
structure HasPhysicalCollisionParameters
    (setup : ProtonPionCollisionSetup) : Prop where
  protonMassPositive : 0 < massInKilograms setup.protonRestMass
  pionMassPositive : 0 < massInKilograms setup.neutralPionRestMass
  lightSpeedPositive : 0 < vacuumLightSpeedInMetersPerSecond
  initialSpeedPositive :
    0 < speedInMetersPerSecond setup.initialProtonSpeed
  initialSpeedSubluminal : initialSpeedFractionOfLight setup < 1
  presentParticleEnergiesPositive :
    ∀ (stage : CollisionStage) (particle : ParticleLabel),
      setup.particlePresentAt stage particle = true →
        0 < energyInJoules (setup.particleEnergyAt stage particle)
  totalEnergiesPositive :
    ∀ stage : CollisionStage,
      0 < energyInJoules (setup.totalEnergyAt stage)

/-! ## Governing relativistic-energy and conservation laws -/

/-!
The standard relativistic particle-energy law `E = γ(β) m c²`, additivity of
particle energies in each state, and conservation of total energy through the
collision.  The particle-energy law applies uniformly to every present
particle; it neither singles out an answer choice nor contains a solved value
of the initial speed.
-/
structure SatisfiesRelativisticCollisionEnergyLaws
    (setup : ProtonPionCollisionSetup) : Prop where
  relativisticParticleEnergy :
    ∀ (stage : CollisionStage) (particle : ParticleLabel),
      setup.particlePresentAt stage particle = true →
        energyInJoules (setup.particleEnergyAt stage particle) =
          LorentzGroup.γ
              (velocityFractionOfLight
                (setup.velocityComponentAt stage particle)) *
            massInKilograms (particleRestMass setup particle) *
              vacuumLightSpeedInMetersPerSecond ^ 2
  initialEnergyIsSumOfTwoProtonEnergies :
    energyInJoules (setup.totalEnergyAt .beforeCollision) =
      energyInJoules
          (setup.particleEnergyAt .beforeCollision .leftProton) +
        energyInJoules
          (setup.particleEnergyAt .beforeCollision .rightProton)
  finalEnergyIsSumOfThreeRestEnergies :
    energyInJoules (setup.totalEnergyAt .afterCollision) =
      energyInJoules
          (setup.particleEnergyAt .afterCollision .leftProton) +
        energyInJoules
          (setup.particleEnergyAt .afterCollision .rightProton) +
        energyInJoules
          (setup.particleEnergyAt .afterCollision .neutralPion)
  totalEnergyConserved :
    setup.totalEnergyAt .beforeCollision =
      setup.totalEnergyAt .afterCollision

/-! ## Answer choices and current target -/

/-- Labels of the four speed fractions printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The coefficient of `c` printed beside each answer label. -/
def displayedSpeedFractionOfLight : AnswerChoice → ℝ
  | .A => 21 / 50
  | .B => 9 / 20
  | .C => 27 / 100
  | .D => 9 / 25

/-!
A speed ratio agrees with a value displayed to three decimal places when its
absolute error is less than half of `0.001`.
-/
def MatchesDisplayedSpeedChoice
    (setup : ProtonPionCollisionSetup) (choice : AnswerChoice) : Prop :=
  |initialSpeedFractionOfLight setup -
      displayedSpeedFractionOfLight choice| < 1 / 2000

/-!
At threshold, energy conservation first yields

`γ = (2 M_p + M_π) / (2 M_p) = 179 / 167`.

This is an intermediate consequence of the governing laws and mass data, not
an assumed field of the collision setup.
-/
lemma initialProtonLorentzFactor_eq_179_div_167
    (setup : ProtonPionCollisionSetup)
    (hScenario : MatchesHeadOnThresholdScenario setup)
    (hMasses : MatchesProblemMassReadouts setup)
    (hPhysical : HasPhysicalCollisionParameters setup)
    (hEnergy : SatisfiesRelativisticCollisionEnergyLaws setup) :
    LorentzGroup.γ (initialSpeedFractionOfLight setup) = 179 / 167 := by
  have hLeftVelocity :
      velocityFractionOfLight
          (setup.velocityComponentAt .beforeCollision .leftProton) =
        initialSpeedFractionOfLight setup := by
    rw [velocityFractionOfLight, initialSpeedFractionOfLight]
    rw [show signedVelocityInMetersPerSecond
          (setup.velocityComponentAt .beforeCollision .leftProton) =
        speedInMetersPerSecond setup.initialProtonSpeed by
          exact hScenario.leftProtonMovesRightAtInitialSpeed
            LengthUnit.meters TimeUnit.seconds]
    rw [abs_of_nonneg]
    exact NNReal.coe_nonneg _
  have hRightVelocity :
      velocityFractionOfLight
          (setup.velocityComponentAt .beforeCollision .rightProton) =
        initialSpeedFractionOfLight setup := by
    rw [velocityFractionOfLight, initialSpeedFractionOfLight]
    rw [show signedVelocityInMetersPerSecond
          (setup.velocityComponentAt .beforeCollision .rightProton) =
        -speedInMetersPerSecond setup.initialProtonSpeed by
          exact hScenario.rightProtonMovesLeftAtInitialSpeed
            LengthUnit.meters TimeUnit.seconds]
    rw [abs_neg, abs_of_nonneg]
    exact NNReal.coe_nonneg _
  have hFinalVelocity (particle : ParticleLabel) :
      velocityFractionOfLight
          (setup.velocityComponentAt .afterCollision particle) = 0 := by
    rw [velocityFractionOfLight]
    rw [show signedVelocityInMetersPerSecond
          (setup.velocityComponentAt .afterCollision particle) = 0 by
          exact hScenario.allThreeParticlesFinallyAtRest particle
            LengthUnit.meters TimeUnit.seconds]
    simp
  have hLeftEnergy := hEnergy.relativisticParticleEnergy
    .beforeCollision .leftProton hScenario.leftProtonInitiallyPresent
  have hRightEnergy := hEnergy.relativisticParticleEnergy
    .beforeCollision .rightProton hScenario.rightProtonInitiallyPresent
  have hFinalLeftEnergy := hEnergy.relativisticParticleEnergy
    .afterCollision .leftProton
      (hScenario.allThreeParticlesFinallyPresent .leftProton)
  have hFinalRightEnergy := hEnergy.relativisticParticleEnergy
    .afterCollision .rightProton
      (hScenario.allThreeParticlesFinallyPresent .rightProton)
  have hFinalPionEnergy := hEnergy.relativisticParticleEnergy
    .afterCollision .neutralPion
      (hScenario.allThreeParticlesFinallyPresent .neutralPion)
  simp [hLeftVelocity, particleRestMass, hMasses.protonMassKilograms] at hLeftEnergy
  simp [hRightVelocity, particleRestMass, hMasses.protonMassKilograms] at hRightEnergy
  simp [hFinalVelocity, particleRestMass, hMasses.protonMassKilograms] at hFinalLeftEnergy
  simp [hFinalVelocity, particleRestMass, hMasses.protonMassKilograms] at hFinalRightEnergy
  simp [hFinalVelocity, particleRestMass, hMasses.neutralPionMassKilograms] at hFinalPionEnergy
  have hConservation :=
    congrArg energyInJoules hEnergy.totalEnergyConserved
  rw [hEnergy.initialEnergyIsSumOfTwoProtonEnergies,
    hEnergy.finalEnergyIsSumOfThreeRestEnergies,
    hLeftEnergy, hRightEnergy, hFinalLeftEnergy, hFinalRightEnergy,
    hFinalPionEnergy] at hConservation
  norm_num at hConservation ⊢
  nlinarith [sq_pos_of_pos hPhysical.lightSpeedPositive]

/-!
Solving the Lorentz-factor relation in the positive subluminal regime gives

`v / c = sqrt (1 - (167 / 179)^2) ≈ 0.3599777`.

Thus the physical speed is approximately `0.360 c`, the value printed as
choice D.  The exact ratio, its dimensionful readout relation, and the unique
selection of D are conclusions and occur in no premise above.

This formalizes `thm:physics:phyx_mini_0511:target`.
-/
theorem problem_phyx_mini_0511
    (setup : ProtonPionCollisionSetup)
    (hScenario : MatchesHeadOnThresholdScenario setup)
    (hFigure : MatchesSuppliedProtonPionFigure setup)
    (hMasses : MatchesProblemMassReadouts setup)
    (hPhysical : HasPhysicalCollisionParameters setup)
    (hEnergy : SatisfiesRelativisticCollisionEnergyLaws setup) :
    initialSpeedFractionOfLight setup =
        Real.sqrt (1 - ((167 : ℝ) / 179) ^ 2) ∧
      (∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
        speedReadout lengthUnit timeUnit setup.initialProtonSpeed =
          Real.sqrt (1 - ((167 : ℝ) / 179) ^ 2) *
            vacuumLightSpeedReadout lengthUnit timeUnit) ∧
      MatchesDisplayedSpeedChoice setup .D ∧
      ∀ choice : AnswerChoice,
        MatchesDisplayedSpeedChoice setup choice → choice = .D := by
  have hBetaPositive : 0 < initialSpeedFractionOfLight setup := by
    exact div_pos hPhysical.initialSpeedPositive hPhysical.lightSpeedPositive
  have hBetaAbs : |initialSpeedFractionOfLight setup| < 1 := by
    rw [abs_of_pos hBetaPositive]
    exact hPhysical.initialSpeedSubluminal
  have hGamma :=
    initialProtonLorentzFactor_eq_179_div_167
      setup hScenario hMasses hPhysical hEnergy
  have hGammaSq :=
    LorentzGroup.γ_sq (initialSpeedFractionOfLight setup) hBetaAbs
  rw [hGamma] at hGammaSq
  have hOneSubBetaSqPositive :
      0 < 1 - initialSpeedFractionOfLight setup ^ 2 := by
    have hProductPositive :
        0 < initialSpeedFractionOfLight setup *
          (1 - initialSpeedFractionOfLight setup) :=
      mul_pos hBetaPositive (sub_pos.mpr hPhysical.initialSpeedSubluminal)
    nlinarith
  have hBetaSq :
      initialSpeedFractionOfLight setup ^ 2 =
        1 - ((167 : ℝ) / 179) ^ 2 := by
    field_simp [ne_of_gt hOneSubBetaSqPositive] at hGammaSq
    norm_num at hGammaSq ⊢
    nlinarith
  have hBetaExact :
      initialSpeedFractionOfLight setup =
        Real.sqrt (1 - ((167 : ℝ) / 179) ^ 2) := by
    rw [← Real.sqrt_sq (le_of_lt hBetaPositive), hBetaSq]
  have hReadoutRelation :
      ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
        speedReadout lengthUnit timeUnit setup.initialProtonSpeed =
          Real.sqrt (1 - ((167 : ℝ) / 179) ^ 2) *
            vacuumLightSpeedReadout lengthUnit timeUnit := by
    intro lengthUnit timeUnit
    let units : UnitChoices :=
      {UnitChoices.SI with length := lengthUnit, time := timeUnit}
    have hVelocityScale :=
      (setup.velocityComponentAt .beforeCollision .leftProton).2
        UnitChoices.SI units
    have hLightScale :=
      DimSpeed.speedOfLight.2 UnitChoices.SI units
    have hSpeedScale :
        speedReadout lengthUnit timeUnit setup.initialProtonSpeed =
          (UnitChoices.SI.dimScale units (L𝓭 * T𝓭⁻¹) : ℝ) *
            speedInMetersPerSecond setup.initialProtonSpeed := by
      rw [← hScenario.leftProtonMovesRightAtInitialSpeed
        lengthUnit timeUnit]
      rw [show speedInMetersPerSecond setup.initialProtonSpeed =
          signedVelocityInMetersPerSecond
            (setup.velocityComponentAt .beforeCollision .leftProton) by
        exact (hScenario.leftProtonMovesRightAtInitialSpeed
          LengthUnit.meters TimeUnit.seconds).symm]
      simpa [signedVelocityReadout, signedVelocityInMetersPerSecond, units,
        UnitChoices.SI, NNReal.smul_def, smul_eq_mul]
        using congrArg WithDim.val hVelocityScale
    have hLightReadoutScale :
        vacuumLightSpeedReadout lengthUnit timeUnit =
          (UnitChoices.SI.dimScale units (L𝓭 * T𝓭⁻¹) : ℝ) *
            vacuumLightSpeedInMetersPerSecond := by
      simpa [vacuumLightSpeedReadout,
        vacuumLightSpeedInMetersPerSecond, signedVelocityReadout, units,
        UnitChoices.SI, NNReal.smul_def, smul_eq_mul]
        using congrArg WithDim.val hLightScale
    have hSpeedSI :
        speedInMetersPerSecond setup.initialProtonSpeed =
          initialSpeedFractionOfLight setup *
            vacuumLightSpeedInMetersPerSecond := by
      rw [initialSpeedFractionOfLight]
      field_simp [ne_of_gt hPhysical.lightSpeedPositive]
    rw [hSpeedScale, hLightReadoutScale, hSpeedSI, hBetaExact]
    ring
  have hRadicandNonnegative :
      0 ≤ 1 - ((167 : ℝ) / 179) ^ 2 := by
    norm_num
  have hSqrtSq :
      (Real.sqrt (1 - ((167 : ℝ) / 179) ^ 2)) ^ 2 =
        1 - ((167 : ℝ) / 179) ^ 2 :=
    Real.sq_sqrt hRadicandNonnegative
  have hSqrtLower :
      (719 : ℝ) / 2000 <
        Real.sqrt (1 - ((167 : ℝ) / 179) ^ 2) := by
    have hSqrtNonnegative :=
      Real.sqrt_nonneg (1 - ((167 : ℝ) / 179) ^ 2)
    norm_num at hSqrtSq hSqrtNonnegative ⊢
    nlinarith
  have hSqrtUpper :
      Real.sqrt (1 - ((167 : ℝ) / 179) ^ 2) <
        (721 : ℝ) / 2000 := by
    have hSqrtNonnegative :=
      Real.sqrt_nonneg (1 - ((167 : ℝ) / 179) ^ 2)
    norm_num at hSqrtSq hSqrtNonnegative ⊢
    nlinarith
  norm_num at hSqrtLower hSqrtUpper
  refine ⟨hBetaExact, hReadoutRelation, ?_, ?_⟩
  · rw [MatchesDisplayedSpeedChoice, hBetaExact, displayedSpeedFractionOfLight,
      abs_lt]
    constructor <;> norm_num <;> nlinarith
  · intro choice hChoice
    cases choice with
    | A =>
        rw [MatchesDisplayedSpeedChoice, hBetaExact,
          displayedSpeedFractionOfLight, abs_lt] at hChoice
        norm_num at hChoice
        nlinarith
    | B =>
        rw [MatchesDisplayedSpeedChoice, hBetaExact,
          displayedSpeedFractionOfLight, abs_lt] at hChoice
        norm_num at hChoice
        nlinarith
    | C =>
        rw [MatchesDisplayedSpeedChoice, hBetaExact,
          displayedSpeedFractionOfLight, abs_lt] at hChoice
        norm_num at hChoice
        nlinarith
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0511
