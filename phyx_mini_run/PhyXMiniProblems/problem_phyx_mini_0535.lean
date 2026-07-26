import Mathlib.Algebra.Order.Round
import Mathlib.Order.Filter.Extr
import Physlib.Electromagnetism.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0535

open Dimension
open scoped BigOperators

/-!
# Minimum-energy separation in a four-particle model crystal

The primary image shows four collinear objects in the alternating order
electron--ion--electron--ion.  Each of the three adjacent gaps is marked by a
double-headed arrow labelled `d`.  The two ions have charge `+e` and are fixed;
the two electrons have charge `-e`.

The textbook quantum model treats the electrons as opposite-spin particles in
the common ground spatial mode of a one-dimensional rigid box spanning the
outermost particles.  Its length is therefore `3d`.  The total energy is the
sum of the two rigid-box kinetic energies and all six pairwise Coulomb
energies.  The governing laws below are stated separately from the requested
minimum and from the displayed answer choices.

Basic lengths, positions, masses, charges, actions, and energies are genuine
dimensionful Physlib quantities.  Real numbers occur only as explicitly named
unit readouts, dimensionless mode/charge data, and displayed numerical values.

Assumption/target split:

* governing laws: the one-dimensional rigid-box ground-state energy,
  pairwise Coulomb energy, and additive total-energy accounting;
* previous-part results: none;
* figure/data readouts: two fixed `+e` ions, two `-e` electrons, the alternating
  collinear order, three equal gaps labelled `d`, and reference constants;
* target conclusions: existence and uniqueness (by length readout) of the
  positive energy-minimizing separation, its analytic value, its proximity to
  `49.9 pm`, and unique selection of answer D.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent one-dimensional position. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A signed physical electric charge. -/
abbrev ChargeQuantity : Type := Dimensionful (WithDim C𝓭 ℝ)

/-- The physical dimension `M L² T⁻¹` of action. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical action, used for the reduced Planck constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a nonnegative physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed one-dimensional position in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (position : SignedLengthQuantity) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Picometre readout used by the displayed answers. -/
def lengthInPicometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.picometers length

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a charge in a selected Physlib charge unit. -/
def chargeReadout (unit : ChargeUnit) (charge : ChargeQuantity) : ℝ :=
  (charge {UnitChoices.SI with charge := unit}).val

/-- SI coulomb readout of a physical charge. -/
def chargeInCoulombs (charge : ChargeQuantity) : ℝ :=
  chargeReadout ChargeUnit.coulombs charge

/-- Read a charge as a signed multiple of the elementary charge. -/
def chargeInElementaryCharges (charge : ChargeQuantity) : ℝ :=
  chargeReadout ChargeUnit.elementaryCharge charge

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a Physlib energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Particles, pairs, quantum state, and primary-image vocabulary -/

/-- The four particles, named in their left-to-right order in the image. -/
inductive CrystalParticle where
  | leftElectron
  | leftIon
  | rightElectron
  | rightIon
  deriving DecidableEq, Fintype, Repr

/-- The two indistinguishable electrons, distinguished only by image position. -/
inductive ElectronLabel where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Regard a labelled electron as one of the four pictured particles. -/
def ElectronLabel.particle : ElectronLabel → CrystalParticle
  | .left => .leftElectron
  | .right => .rightElectron

/-- The particle species stated in the prose. -/
inductive ParticleSpecies where
  | electron
  | positiveIon
  deriving DecidableEq, Repr

/-- Opposite spin states allow the two electrons to share one spatial mode. -/
inductive ElectronSpin where
  | up
  | down
  deriving DecidableEq, Repr

/-- The confinement idealization used for the quantum kinetic energy. -/
inductive ConfinementModel where
  | oneDimensionalInfiniteRigidBox
  | other
  deriving DecidableEq, Repr

/-- The six unordered pairs among the four pictured particles. -/
inductive ParticlePair where
  | leftElectron_leftIon
  | leftElectron_rightElectron
  | leftElectron_rightIon
  | leftIon_rightElectron
  | leftIon_rightIon
  | rightElectron_rightIon
  deriving DecidableEq, Fintype, Repr

/-- First endpoint of each unordered particle pair. -/
def ParticlePair.first : ParticlePair → CrystalParticle
  | .leftElectron_leftIon => .leftElectron
  | .leftElectron_rightElectron => .leftElectron
  | .leftElectron_rightIon => .leftElectron
  | .leftIon_rightElectron => .leftIon
  | .leftIon_rightIon => .leftIon
  | .rightElectron_rightIon => .rightElectron

/-- Second endpoint of each unordered particle pair. -/
def ParticlePair.second : ParticlePair → CrystalParticle
  | .leftElectron_leftIon => .leftIon
  | .leftElectron_rightElectron => .rightElectron
  | .leftElectron_rightIon => .rightIon
  | .leftIon_rightElectron => .rightElectron
  | .leftIon_rightIon => .rightIon
  | .rightElectron_rightIon => .rightIon

/-- Number of adjacent `d`-gaps separating the endpoints of a pair. -/
def ParticlePair.gapCount : ParticlePair → ℕ
  | .leftElectron_leftIon => 1
  | .leftElectron_rightElectron => 2
  | .leftElectron_rightIon => 3
  | .leftIon_rightElectron => 1
  | .leftIon_rightIon => 2
  | .rightElectron_rightIon => 1

/-- The three adjacent gaps explicitly marked in the image. -/
inductive AdjacentGap where
  | first
  | second
  | third
  deriving DecidableEq, Fintype, Repr

/-- Relative size and colour of a sphere in the supplied raster. -/
inductive SphereStyle where
  | smallBlue
  | largeRed
  deriving DecidableEq, Repr

/-- The sole symbolic length label visible in the supplied raster. -/
inductive FigureLabel where
  | d
  deriving DecidableEq, Fintype, Repr

/-- The image marks each adjacent gap in both horizontal directions. -/
inductive SeparationMarker where
  | doubleHeadedHorizontalArrow
  deriving DecidableEq, Repr

/-- Qualitative information transcribed from the primary bitmap. -/
structure FourParticleCrystalFigure where
  sphereStyle : CrystalParticle → SphereStyle
  verticalGuideLineShown : CrystalParticle → Bool
  gapMarker : AdjacentGap → SeparationMarker
  gapLabel : AdjacentGap → FigureLabel
  allCentersCollinear : Bool

/-! ## Independent crystal model -/

/-!
The physical state and the energy observables for every trial separation.
None of these fields defines a minimizing distance or mentions an answer
choice.
-/
structure FourParticleCrystalSetup where
  species : CrystalParticle → ParticleSpecies
  isFixed : CrystalParticle → Bool
  particleCharge : CrystalParticle → ChargeQuantity
  electronSpin : ElectronLabel → ElectronSpin
  electronMass : MassQuantity
  reducedPlanckConstant : ActionQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  confinementModel : ConfinementModel
  electronSpatialMode : ElectronLabel → ℕ
  positionAtSpacing : LengthQuantity → CrystalParticle → SignedLengthQuantity
  pairDistanceAtSpacing : ParticlePair → LengthQuantity → LengthQuantity
  boxLengthAtSpacing : LengthQuantity → LengthQuantity
  electronKineticEnergyAtSpacing : ElectronLabel → LengthQuantity → DimEnergy
  pairPotentialEnergyAtSpacing : ParticlePair → LengthQuantity → DimEnergy
  totalEnergyAtSpacing : LengthQuantity → DimEnergy
  figure : FourParticleCrystalFigure

/-! ## Scenario, figure/data readouts, and reference constants -/

/-- The two-fixed-ion, two-electron scenario stated in the problem. -/
structure MatchesTwoIonTwoElectronScenario
    (setup : FourParticleCrystalSetup) : Prop where
  leftParticleIsElectron : setup.species .leftElectron = .electron
  firstIonIsPositive : setup.species .leftIon = .positiveIon
  thirdParticleIsElectron : setup.species .rightElectron = .electron
  finalIonIsPositive : setup.species .rightIon = .positiveIon
  leftIonFixed : setup.isFixed .leftIon = true
  rightIonFixed : setup.isFixed .rightIon = true
  leftElectronMobile : setup.isFixed .leftElectron = false
  rightElectronMobile : setup.isFixed .rightElectron = false
  electronCharges : ∀ electron : ElectronLabel,
    chargeInElementaryCharges (setup.particleCharge electron.particle) = -1
  ionCharges :
    chargeInElementaryCharges (setup.particleCharge .leftIon) = 1 ∧
      chargeInElementaryCharges (setup.particleCharge .rightIon) = 1
  oppositeElectronSpins :
    setup.electronSpin .left = .up ∧ setup.electronSpin .right = .down
  rigidBoxModel :
    setup.confinementModel = .oneDimensionalInfiniteRigidBox

/-!
Evidence from the primary image.  It fixes the alternating styles, the three
`d` labels, and the linear coordinates for an arbitrary trial `d`; it does not
select any numerical value of `d`.
-/
structure MatchesPrimaryCrystalFigure
    (setup : FourParticleCrystalSetup) : Prop where
  leftElectronStyle : setup.figure.sphereStyle .leftElectron = .smallBlue
  leftIonStyle : setup.figure.sphereStyle .leftIon = .largeRed
  rightElectronStyle : setup.figure.sphereStyle .rightElectron = .smallBlue
  rightIonStyle : setup.figure.sphereStyle .rightIon = .largeRed
  allVerticalGuidesShown : ∀ particle,
    setup.figure.verticalGuideLineShown particle = true
  everyGapHasDoubleArrow : ∀ gap,
    setup.figure.gapMarker gap = .doubleHeadedHorizontalArrow
  everyGapLabelIsD : ∀ gap, setup.figure.gapLabel gap = .d
  centersAreCollinear : setup.figure.allCentersCollinear = true
  leftElectronAtOrigin : ∀ (d : LengthQuantity) (unit : LengthUnit),
    signedLengthReadout unit (setup.positionAtSpacing d .leftElectron) = 0
  leftIonAtD : ∀ (d : LengthQuantity) (unit : LengthUnit),
    signedLengthReadout unit (setup.positionAtSpacing d .leftIon) =
      lengthReadout unit d
  rightElectronAtTwoD : ∀ (d : LengthQuantity) (unit : LengthUnit),
    signedLengthReadout unit (setup.positionAtSpacing d .rightElectron) =
      2 * lengthReadout unit d
  rightIonAtThreeD : ∀ (d : LengthQuantity) (unit : LengthUnit),
    signedLengthReadout unit (setup.positionAtSpacing d .rightIon) =
      3 * lengthReadout unit d
  pairDistancesFollowFigure :
    ∀ (pair : ParticlePair) (d : LengthQuantity) (unit : LengthUnit),
      lengthReadout unit (setup.pairDistanceAtSpacing pair d) =
        (pair.gapCount : ℝ) * lengthReadout unit d
  boxSpansOutermostParticles : ∀ (d : LengthQuantity) (unit : LengthUnit),
    lengthReadout unit (setup.boxLengthAtSpacing d) =
      3 * lengthReadout unit d

/-!
Reference constants used for the numerical comparison.  Physlib supplies
`Constants.ℏ`, `ChargeUnit.elementaryCharge`, and Coulomb's constant as the
method `Electromagnetism.EMSystem.coulombConstant`.  The electron mass and the
free-space electromagnetic-system calibration are explicit SI data.
-/
structure UsesReferenceCrystalConstants
    (setup : FourParticleCrystalSetup) : Prop where
  reducedPlanckConstantCalibration :
    actionInJouleSeconds setup.reducedPlanckConstant = (Constants.ℏ : ℝ)
  electronMassCalibration :
    massInKilograms setup.electronMass = 9.1093837139e-31
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity conditions selecting a nondegenerate physical model. -/
structure HasPhysicalCrystalParameters
    (setup : FourParticleCrystalSetup) : Prop where
  electronMassPositive : 0 < massInKilograms setup.electronMass
  reducedPlanckConstantPositive :
    0 < actionInJouleSeconds setup.reducedPlanckConstant
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  elementaryPositiveIonCharge :
    0 < chargeInCoulombs (setup.particleCharge .leftIon)
  trialDistancesPositive :
    ∀ (pair : ParticlePair) (d : LengthQuantity),
      0 < lengthInMeters d →
        0 < lengthInMeters (setup.pairDistanceAtSpacing pair d)
  trialBoxLengthPositive : ∀ d : LengthQuantity,
    0 < lengthInMeters d → 0 < lengthInMeters (setup.boxLengthAtSpacing d)

/-! ## Governing quantum and electrostatic laws -/

/-!
Both opposite-spin electrons occupy the `n = 1` spatial mode.  In a
one-dimensional infinite well of length `L`, each then has kinetic energy
`(pi*hbar)^2/(2*m*L^2)`.  This all-separations law contains no minimizing
distance.
-/
structure SatisfiesRigidBoxGroundStateLaw
    (setup : FourParticleCrystalSetup) : Prop where
  bothElectronsInGroundSpatialMode :
    ∀ electron : ElectronLabel, setup.electronSpatialMode electron = 1
  groundStateKineticEnergy :
    ∀ (electron : ElectronLabel) (d : LengthQuantity),
      0 < lengthInMeters d →
        energyInJoules (setup.electronKineticEnergyAtSpacing electron d) =
          (Real.pi * actionInJouleSeconds setup.reducedPlanckConstant) ^ 2 /
            (2 * massInKilograms setup.electronMass *
              lengthInMeters (setup.boxLengthAtSpacing d) ^ 2)

/-!
Every pair contributes `k q₁ q₂/r`, and the total energy is the sum of the two
electron kinetic energies and all six pair energies.  These are general
governing laws over positive trial separations, not equilibrium conditions.
-/
structure SatisfiesCoulombAndTotalEnergyLaws
    (setup : FourParticleCrystalSetup) : Prop where
  pairwiseCoulombEnergy :
    ∀ (pair : ParticlePair) (d : LengthQuantity),
      0 < lengthInMeters d →
        energyInJoules (setup.pairPotentialEnergyAtSpacing pair d) =
          setup.electromagneticSystem.coulombConstant *
              chargeInCoulombs (setup.particleCharge pair.first) *
              chargeInCoulombs (setup.particleCharge pair.second) /
            lengthInMeters (setup.pairDistanceAtSpacing pair d)
  additiveTotalEnergy :
    ∀ d : LengthQuantity,
      0 < lengthInMeters d →
        energyInJoules (setup.totalEnergyAtSpacing d) =
          (∑ electron : ElectronLabel,
            energyInJoules (setup.electronKineticEnergyAtSpacing electron d)) +
          ∑ pair : ParticlePair,
            energyInJoules (setup.pairPotentialEnergyAtSpacing pair d)

/-! ## Energy minimization and displayed answer choices -/

/-- The scalar total-energy curve obtained by reading a trial energy in joules. -/
def totalEnergyInJoulesAtSpacing
    (setup : FourParticleCrystalSetup) (d : LengthQuantity) : ℝ :=
  energyInJoules (setup.totalEnergyAtSpacing d)

/-- A positive separation at which the energy is globally minimal. -/
def IsEnergyMinimizingSeparation
    (setup : FourParticleCrystalSetup) (d : LengthQuantity) : Prop :=
  0 < lengthInMeters d ∧
    IsMinOn (totalEnergyInJoulesAtSpacing setup)
      {trial | 0 < lengthInMeters trial} d

/-- Global minimality together with uniqueness of the physical length readout. -/
def IsUniqueEnergyMinimizingSeparation
    (setup : FourParticleCrystalSetup) (d : LengthQuantity) : Prop :=
  IsEnergyMinimizingSeparation setup d ∧
    ∀ other : LengthQuantity,
      IsEnergyMinimizingSeparation setup other →
        lengthInMeters other = lengthInMeters d

/-- Labels of the four separation choices printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Picometre value printed beside each answer label. -/
def AnswerChoice.separationInPicometers : AnswerChoice → ℝ
  | .A => 621 / 10
  | .B => 544 / 10
  | .C => 218 / 10
  | .D => 499 / 10

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed answer is uniquely closest to a derived physical separation. -/
def IsUniqueClosestDisplayedSeparation
    (d : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInPicometers d - choice.separationInPicometers| <
      |lengthInPicometers d - other.separationInPicometers|

/-!
The stationary positive length obtained by balancing the inverse-square
rigid-box kinetic term with the attractive inverse-distance Coulomb term.
This is an analytic candidate built from independent physical constants; its
minimality and numerical answer-choice consequences are proved below rather
than built into the definition.
-/
def stationarySeparationInMeters (setup : FourParticleCrystalSetup) : ℝ :=
  2 * Real.pi ^ 2 *
      actionInJouleSeconds setup.reducedPlanckConstant ^ 2 /
    (21 * setup.electromagneticSystem.coulombConstant *
      massInKilograms setup.electronMass *
      chargeInCoulombs (setup.particleCharge .leftIon) ^ 2)

/-!
The two ground-state kinetic terms and six Coulomb pairs reduce to

`E(d) = pi^2 hbar^2/(9 m d^2) - 7 k e^2/(3 d)`.

This is derived from the all-pairs laws and figure geometry, not assumed.
-/
lemma totalEnergyCurve_eq
    (setup : FourParticleCrystalSetup)
    (h_scenario : MatchesTwoIonTwoElectronScenario setup)
    (h_figure : MatchesPrimaryCrystalFigure setup)
    (h_quantum : SatisfiesRigidBoxGroundStateLaw setup)
    (h_energy : SatisfiesCoulombAndTotalEnergyLaws setup) :
    ∀ d : LengthQuantity,
      0 < lengthInMeters d →
        totalEnergyInJoulesAtSpacing setup d =
          Real.pi ^ 2 *
                actionInJouleSeconds setup.reducedPlanckConstant ^ 2 /
              (9 * massInKilograms setup.electronMass *
                lengthInMeters d ^ 2) -
            7 * setup.electromagneticSystem.coulombConstant *
                chargeInCoulombs (setup.particleCharge .leftIon) ^ 2 /
              (3 * lengthInMeters d) := by
  intro d hd
  have charge_conversion (charge : ChargeQuantity) :
      chargeInCoulombs charge =
        1.602176634e-19 * chargeInElementaryCharges charge := by
    have h := congrArg WithDim.val
      (charge.property
        {UnitChoices.SI with charge := ChargeUnit.elementaryCharge}
        UnitChoices.SI)
    change chargeInCoulombs charge = _ at h
    rw [h]
    unfold chargeInElementaryCharges chargeReadout
    simp only [WithDim.smul_val, NNReal.smul_def]
    congr 1
    norm_num [UnitChoices.dimScale_apply, ChargeUnit.elementaryCharge,
      ChargeUnit.coulombs, ChargeUnit.scale, ChargeUnit.div_eq_val,
      WithDim.dim_apply, C𝓭]
    rfl
  have h_leftElectron :
      chargeInCoulombs (setup.particleCharge .leftElectron) =
        -chargeInCoulombs (setup.particleCharge .leftIon) := by
    rw [charge_conversion, charge_conversion]
    have h_electron := h_scenario.electronCharges .left
    simp only [ElectronLabel.particle] at h_electron
    rw [h_electron, h_scenario.ionCharges.1]
    ring
  have h_rightElectron :
      chargeInCoulombs (setup.particleCharge .rightElectron) =
        -chargeInCoulombs (setup.particleCharge .leftIon) := by
    rw [charge_conversion, charge_conversion]
    have h_electron := h_scenario.electronCharges .right
    simp only [ElectronLabel.particle] at h_electron
    rw [h_electron, h_scenario.ionCharges.1]
    ring
  have h_rightIon :
      chargeInCoulombs (setup.particleCharge .rightIon) =
        chargeInCoulombs (setup.particleCharge .leftIon) := by
    rw [charge_conversion, charge_conversion,
      h_scenario.ionCharges.2, h_scenario.ionCharges.1]
  have h_box :
      lengthInMeters (setup.boxLengthAtSpacing d) =
        3 * lengthInMeters d := by
    simpa [lengthInMeters] using
      h_figure.boxSpansOutermostParticles d LengthUnit.meters
  have h_distance (pair : ParticlePair) :
      lengthInMeters (setup.pairDistanceAtSpacing pair d) =
        (pair.gapCount : ℝ) * lengthInMeters d := by
    simpa [lengthInMeters] using
      h_figure.pairDistancesFollowFigure pair d LengthUnit.meters
  have h_electron_sum :
      (∑ electron : ElectronLabel,
          energyInJoules
            (setup.electronKineticEnergyAtSpacing electron d)) =
        energyInJoules (setup.electronKineticEnergyAtSpacing .left d) +
          energyInJoules
            (setup.electronKineticEnergyAtSpacing .right d) := by
    rw [show (Finset.univ : Finset ElectronLabel) = {.left, .right} by
      decide]
    simp
  have h_pair_sum :
      (∑ pair : ParticlePair,
          energyInJoules (setup.pairPotentialEnergyAtSpacing pair d)) =
        energyInJoules
            (setup.pairPotentialEnergyAtSpacing
              .leftElectron_leftIon d) +
          energyInJoules
            (setup.pairPotentialEnergyAtSpacing
              .leftElectron_rightElectron d) +
          energyInJoules
            (setup.pairPotentialEnergyAtSpacing
              .leftElectron_rightIon d) +
          energyInJoules
            (setup.pairPotentialEnergyAtSpacing
              .leftIon_rightElectron d) +
          energyInJoules
            (setup.pairPotentialEnergyAtSpacing .leftIon_rightIon d) +
          energyInJoules
            (setup.pairPotentialEnergyAtSpacing
              .rightElectron_rightIon d) := by
    rw [show (Finset.univ : Finset ParticlePair) =
        {.leftElectron_leftIon, .leftElectron_rightElectron,
          .leftElectron_rightIon, .leftIon_rightElectron,
          .leftIon_rightIon, .rightElectron_rightIon} by
      decide]
    simp
    ring
  change energyInJoules (setup.totalEnergyAtSpacing d) = _
  rw [h_energy.additiveTotalEnergy d hd, h_electron_sum, h_pair_sum]
  rw [h_quantum.groundStateKineticEnergy .left d hd,
    h_quantum.groundStateKineticEnergy .right d hd]
  rw [h_energy.pairwiseCoulombEnergy .leftElectron_leftIon d hd,
    h_energy.pairwiseCoulombEnergy .leftElectron_rightElectron d hd,
    h_energy.pairwiseCoulombEnergy .leftElectron_rightIon d hd,
    h_energy.pairwiseCoulombEnergy .leftIon_rightElectron d hd,
    h_energy.pairwiseCoulombEnergy .leftIon_rightIon d hd,
    h_energy.pairwiseCoulombEnergy .rightElectron_rightIon d hd]
  rw [h_box]
  simp only [ParticlePair.first, ParticlePair.second]
  rw [h_leftElectron, h_rightElectron, h_rightIon]
  simp only [h_distance, ParticlePair.gapCount, Nat.cast_one,
    Nat.cast_ofNat]
  ring

/-!
For positive constants the curve above has its unique positive minimum at
`2*pi^2*hbar^2/(21*k*m*e^2)`.  This lemma does not use any displayed answer.
-/
lemma exists_unique_minimizing_separation
    (setup : FourParticleCrystalSetup)
    (h_scenario : MatchesTwoIonTwoElectronScenario setup)
    (h_figure : MatchesPrimaryCrystalFigure setup)
    (h_physical : HasPhysicalCrystalParameters setup)
    (h_quantum : SatisfiesRigidBoxGroundStateLaw setup)
    (h_energy : SatisfiesCoulombAndTotalEnergyLaws setup) :
    ∃ d : LengthQuantity,
      lengthInMeters d = stationarySeparationInMeters setup ∧
        IsUniqueEnergyMinimizingSeparation setup d := by
  let A : ℝ :=
    Real.pi ^ 2 *
        actionInJouleSeconds setup.reducedPlanckConstant ^ 2 /
      (9 * massInKilograms setup.electronMass)
  let B : ℝ :=
    7 * setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs (setup.particleCharge .leftIon) ^ 2 /
      3
  let s : ℝ := stationarySeparationInMeters setup
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos
      (mul_pos (sq_pos_of_pos Real.pi_pos)
        (sq_pos_of_pos h_physical.reducedPlanckConstantPositive))
      (mul_pos (by norm_num) h_physical.electronMassPositive)
  have hB : 0 < B := by
    dsimp [B]
    exact div_pos
      (mul_pos
        (mul_pos (by norm_num) h_physical.coulombConstantPositive)
        (sq_pos_of_pos h_physical.elementaryPositiveIonCharge))
      (by norm_num)
  have hstation : B * s = 2 * A := by
    dsimp [A, B, s, stationarySeparationInMeters]
    field_simp [ne_of_gt h_physical.electronMassPositive,
      ne_of_gt h_physical.coulombConstantPositive,
      ne_of_gt h_physical.elementaryPositiveIonCharge]
    ring
  have hs : 0 < s := by
    nlinarith
  let d : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨⟨s, le_of_lt hs⟩⟩ : WithDim L𝓭 NNReal)
  have hd_readout : lengthInMeters d = s := by
    norm_num [d, lengthInMeters, lengthReadout,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_apply, L𝓭, LengthUnit.meters,
      LengthUnit.div_eq_val]
    rfl
  have hd_positive : 0 < lengthInMeters d := by
    rw [hd_readout]
    exact hs
  have h_curve (trial : LengthQuantity)
      (htrial : 0 < lengthInMeters trial) :
      totalEnergyInJoulesAtSpacing setup trial =
        A / lengthInMeters trial ^ 2 -
          B / lengthInMeters trial := by
    rw [totalEnergyCurve_eq setup h_scenario h_figure h_quantum h_energy
      trial htrial]
    dsimp [A, B]
    ring
  have h_minimum (x : ℝ) (hx : 0 < x) :
      A / s ^ 2 - B / s ≤ A / x ^ 2 - B / x := by
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h_difference :
        (A / x ^ 2 - B / x) - (A / s ^ 2 - B / s) =
          A * (x - s) ^ 2 / (x ^ 2 * s ^ 2) := by
      field_simp
      nlinarith [hstation]
    rw [sub_eq_iff_eq_add] at h_difference
    rw [h_difference]
    have h_nonnegative :
        0 ≤ A * (x - s) ^ 2 / (x ^ 2 * s ^ 2) := by
      positivity
    linarith
  have h_unique (x : ℝ) (hx : 0 < x)
      (h_equal :
        A / s ^ 2 - B / s = A / x ^ 2 - B / x) :
      x = s := by
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h_difference :
        (A / x ^ 2 - B / x) - (A / s ^ 2 - B / s) =
          A * (x - s) ^ 2 / (x ^ 2 * s ^ 2) := by
      field_simp
      nlinarith [hstation]
    have h_fraction :
        A * (x - s) ^ 2 / (x ^ 2 * s ^ 2) = 0 := by
      rw [← h_difference, ← h_equal, sub_self]
    have h_denominator : x ^ 2 * s ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hs0)
    have h_numerator : A * (x - s) ^ 2 = 0 :=
      (div_eq_zero_iff.mp h_fraction).resolve_right h_denominator
    rcases mul_eq_zero.mp h_numerator with hA_zero | h_square
    · exact False.elim ((ne_of_gt hA) hA_zero)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h_square)
  refine ⟨d, ?_, ?_⟩
  · exact hd_readout.trans rfl
  · constructor
    · constructor
      · exact hd_positive
      · change ∀ trial : LengthQuantity,
          trial ∈ {trial | 0 < lengthInMeters trial} →
            totalEnergyInJoulesAtSpacing setup d ≤
              totalEnergyInJoulesAtSpacing setup trial
        intro trial htrial
        rw [h_curve d hd_positive, h_curve trial htrial, hd_readout]
        exact h_minimum (lengthInMeters trial) htrial
    · intro other h_other
      have h_other_positive := h_other.1
      have h_d_le_other := h_minimum (lengthInMeters other)
        h_other_positive
      have h_other_le_d :
          totalEnergyInJoulesAtSpacing setup other ≤
            totalEnergyInJoulesAtSpacing setup d := by
        apply h_other.2
        exact hd_positive
      rw [h_curve other h_other_positive, h_curve d hd_positive,
        hd_readout] at h_other_le_d
      have h_equal :
          A / s ^ 2 - B / s =
            A / lengthInMeters other ^ 2 -
              B / lengthInMeters other := by
        exact le_antisymm h_d_le_other h_other_le_d
      exact (h_unique (lengthInMeters other) h_other_positive h_equal).trans
        hd_readout.symm

/-!
The unique minimum is the analytic stationary separation above.  With the
reference constants it lies within `0.2 pm` of the source's `49.9 pm` and is
uniquely closest to displayed choice D.

This formalizes `thm:physics:phyx_mini_0535:target`.  Neither the stationary
length, `49.9 pm`, nor answer D occurs in a scenario, figure, reference-data,
or governing-law premise.
-/
theorem problem_phyx_mini_0535
    (setup : FourParticleCrystalSetup)
    (h_scenario : MatchesTwoIonTwoElectronScenario setup)
    (h_figure : MatchesPrimaryCrystalFigure setup)
    (h_constants : UsesReferenceCrystalConstants setup)
    (h_physical : HasPhysicalCrystalParameters setup)
    (h_quantum : SatisfiesRigidBoxGroundStateLaw setup)
    (h_energy : SatisfiesCoulombAndTotalEnergyLaws setup) :
    ∃ d : LengthQuantity,
      lengthInMeters d = stationarySeparationInMeters setup ∧
        IsUniqueEnergyMinimizingSeparation setup d ∧
        |lengthInPicometers d - 499 / 10| < 1 / 5 ∧
        IsUniqueClosestDisplayedSeparation d recordedDatasetAnswer := by
  obtain ⟨d, hd_meter, hd_minimum⟩ :=
    exists_unique_minimizing_separation setup h_scenario h_figure
      h_physical h_quantum h_energy
  have charge_conversion (charge : ChargeQuantity) :
      chargeInCoulombs charge =
        1.602176634e-19 * chargeInElementaryCharges charge := by
    have h := congrArg WithDim.val
      (charge.property
        {UnitChoices.SI with charge := ChargeUnit.elementaryCharge}
        UnitChoices.SI)
    change chargeInCoulombs charge = _ at h
    rw [h]
    unfold chargeInElementaryCharges chargeReadout
    simp only [WithDim.smul_val, NNReal.smul_def]
    congr 1
    norm_num [UnitChoices.dimScale_apply, ChargeUnit.elementaryCharge,
      ChargeUnit.coulombs, ChargeUnit.scale, ChargeUnit.div_eq_val,
      WithDim.dim_apply, C𝓭]
    rfl
  have h_ion_charge :
      chargeInCoulombs (setup.particleCharge .leftIon) =
        1.602176634e-19 := by
    rw [charge_conversion, h_scenario.ionCharges.1]
    norm_num
  have length_conversion (length : LengthQuantity) :
      lengthInPicometers length = 1e12 * lengthInMeters length := by
    have h := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
      (length.property UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.picometers})
    change lengthInPicometers length = _ at h
    rw [h]
    unfold lengthInMeters lengthReadout
    simp only [WithDim.smul_val]
    change
      (↑(UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.picometers} L𝓭) : ℝ) *
          (length UnitChoices.SI).val =
        1e12 * (length UnitChoices.SI).val
    congr 1
    norm_num [UnitChoices.dimScale_apply, LengthUnit.picometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      WithDim.dim_apply, L𝓭]
    rfl
  have h_numeric_length :
      lengthInPicometers d =
        1e12 *
          (2 * Real.pi ^ 2 * (1.054571817e-34 : ℝ) ^ 2 /
            (21 * 8.9875517923e9 * 9.1093837139e-31 *
              (1.602176634e-19 : ℝ) ^ 2)) := by
    rw [length_conversion, hd_meter]
    dsimp [stationarySeparationInMeters]
    rw [h_constants.reducedPlanckConstantCalibration,
      h_constants.electronMassCalibration,
      h_constants.coulombConstantCalibration, h_ion_charge]
    norm_num [Constants.ℏ]
  have pi_gt_sqrt_series (n : ℕ) :
      2 ^ (n + 1) *
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) <
        Real.pi := by
    have h :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 *
            2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply Real.sin_lt
        apply div_pos Real.pi_pos
      all_goals
        apply pow_pos
        norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) h
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have pi_lower_bound_start (n : ℕ) {a : ℝ}
      (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
        (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
      a < Real.pi := by
    refine lt_of_le_of_lt ?_ (pi_gt_sqrt_series n)
    rw [mul_comm]
    refine (div_le_iff₀ (pow_pos (by simp) _)).mp
      (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm,
      show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
        rw [Nat.cast_zero, zero_div]]
  have sqrt_series_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ}
      (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
      (hb : 0 < b) (hd : 0 < d)
      (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
      Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
    refine le_trans ?_ hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
      div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
      div_le_div_iff₀ hb' (pow_pos hd' _)]
    exact_mod_cast h
  have h_pi_lower : (3.1415 : ℝ) < Real.pi := by
    apply pi_lower_bound_start 6
    refine sqrt_series_step_up 1970 1393 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrt_series_step_up 3010 1629 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrt_series_step_up 11689 5959 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrt_series_step_up 10127 5088 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrt_series_step_up 33997 17019 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrt_series_step_up 23235 11621 ?_
      (by norm_num) (by norm_num) (by norm_num)
    simp [Real.sqrtTwoAddSeries]
    norm_num
  have pi_lt_sqrt_series (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) *
            Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have h :
        Real.pi <
          (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 +
              1 / (2 ^ n) ^ 3 / 4) *
            (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by simp), ← Real.sin_pi_over_two_pow_succ,
        ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <| Real.sin_gt_sub_cube (by positivity) <|
            div_le_one_of_le₀ (by
              calc
                Real.pi ≤ 4 := Real.pi_le_four
                _ = 2 ^ (0 + 2) := by norm_num
                _ ≤ 2 ^ (n + 2) := by
                  gcongr <;> norm_num) (by positivity)
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le h (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      div_div, ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n,
        add_assoc, mul_comm n]
    all_goals norm_num
  have pi_upper_bound_start (n : ℕ) {a : ℝ}
      (h : (2 : ℝ) -
          ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
      (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
      Real.pi < a := by
    refine lt_of_lt_of_le (pi_lt_sqrt_series n) ?_
    rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left,
      sub_le_comm]
    · rwa [Nat.cast_zero, zero_div] at h
    · exact div_nonneg (sub_nonneg.2 h₂)
        (pow_nonneg (le_of_lt zero_lt_two) _)
    · exact pow_pos zero_lt_two _
  have sqrt_series_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
      (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
      (hb : 0 < b) (hd : 0 < d)
      (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
      z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
    apply le_trans hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    apply Real.le_sqrt_of_sq_le
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
      div_le_div_iff₀ (pow_pos hb' _) hd']
    exact_mod_cast h
  have h_pi_upper : Real.pi < (3.15 : ℝ) := by
    apply pi_upper_bound_start 4
    · refine sqrt_series_step_down 41 29 ?_
        (by norm_num) (by norm_num) (by norm_num)
      refine sqrt_series_step_down 109 59 ?_
        (by norm_num) (by norm_num) (by norm_num)
      refine sqrt_series_step_down 865 441 ?_
        (by norm_num) (by norm_num) (by norm_num)
      refine sqrt_series_step_down 412 207 ?_
        (by norm_num) (by norm_num) (by norm_num)
      simp [Real.sqrtTwoAddSeries]
      norm_num
    · norm_num
  let C : ℝ :=
    1e12 * (2 * (1.054571817e-34 : ℝ) ^ 2 /
      (21 * 8.9875517923e9 * 9.1093837139e-31 *
        (1.602176634e-19 : ℝ) ^ 2))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have h_pi_lower_sq : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [Real.pi_pos]
  have h_pi_upper_sq : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by
    nlinarith [Real.pi_pos]
  have h_numeric_lower :
      (499 / 10 - 1 / 5 : ℝ) < C * (3.1415 : ℝ) ^ 2 := by
    norm_num [C, div_eq_mul_inv]
  have h_numeric_upper :
      C * (3.15 : ℝ) ^ 2 < (499 / 10 + 1 / 5 : ℝ) := by
    norm_num [C, div_eq_mul_inv]
  have h_close :
      |lengthInPicometers d - 499 / 10| < 1 / 5 := by
    rw [h_numeric_length]
    rw [show
        1e12 *
            (2 * Real.pi ^ 2 * (1.054571817e-34 : ℝ) ^ 2 /
              (21 * 8.9875517923e9 * 9.1093837139e-31 *
                (1.602176634e-19 : ℝ) ^ 2)) =
          C * Real.pi ^ 2 by
      dsimp [C]
      ring]
    rw [abs_lt]
    constructor
    · have h := h_numeric_lower.trans
        (mul_lt_mul_of_pos_left h_pi_lower_sq hC)
      linarith
    · have h := (mul_lt_mul_of_pos_left h_pi_upper_sq hC).trans
        h_numeric_upper
      linarith
  refine ⟨d, hd_meter, hd_minimum, h_close, ?_⟩
  intro other h_other
  have h_close_bounds := (abs_lt.mp h_close)
  fin_cases other
  · change
      |lengthInPicometers d - 499 / 10| <
        |lengthInPicometers d - 621 / 10|
    have h_negative :
        lengthInPicometers d - 621 / 10 < 0 := by
      linarith
    rw [abs_of_neg h_negative]
    exact h_close.trans (by linarith)
  · change
      |lengthInPicometers d - 499 / 10| <
        |lengthInPicometers d - 544 / 10|
    have h_negative :
        lengthInPicometers d - 544 / 10 < 0 := by
      linarith
    rw [abs_of_neg h_negative]
    exact h_close.trans (by linarith)
  · change
      |lengthInPicometers d - 499 / 10| <
        |lengthInPicometers d - 218 / 10|
    have h_positive :
        0 < lengthInPicometers d - 218 / 10 := by
      linarith
    rw [abs_of_pos h_positive]
    exact h_close.trans (by linarith)
  · exact False.elim (h_other rfl)

end PhyXMiniProblems.ProblemPhyXMini0535
