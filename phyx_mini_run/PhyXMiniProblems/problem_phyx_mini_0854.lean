import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0854

open Dimension

/-!
# Electric potential energy of a proton near two fixed electrons

The primary figure places two electrons on one vertical line.  They lie
respectively `0.50 nm` above and below a dashed horizontal midline.  A proton
lies on that midline, `2.0 nm` to the right of the electron line.  The
electrons are fixed, and the requested observable is the proton's electric
potential energy with the usual zero at infinite separation.

Lengths, signed charges, Coulomb's constant, and energy are dimensionful.
Real numbers occur at named-unit readout boundaries, in Cartesian coordinate
readouts, and in literal labels from the raster.  The proton's potential
energy is an independent setup field; neither the figure predicates nor the
physical-law predicate gives it the numerical answer requested in the
problem.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, used for the three labeled separations. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length, used for Cartesian position coordinates. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The dimension of Coulomb's constant, equivalently `J m / C²`. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, dimensionful value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Read a nonnegative physical length in a selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed physical coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (coordinate : SignedLengthQuantity) : ℝ :=
  (coordinate {UnitChoices.SI with length := unit}).val

/-- Read a nonnegative physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a nonnegative physical length in nanometres. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Read a signed physical coordinate in coherent-SI metres. -/
def signedLengthInMeters (coordinate : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters coordinate

/-- Read a signed physical charge in coherent-SI coulombs. -/
def signedChargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read Coulomb's constant in coherent `J m / C²` units. -/
def coulombConstantInJouleMetersPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Read a signed physical energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Physlib's positive elementary-charge unit expressed in coulombs. -/
def elementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Particle, coordinate, and primary-figure vocabulary -/

/-- The two electrons and proton distinguished in the supplied image. -/
inductive ParticleLabel where
  | upperElectron
  | lowerElectron
  | proton
  deriving DecidableEq, Fintype, Repr

/-- Particle species relevant to this three-particle electrostatic model. -/
inductive ParticleSpecies where
  | electron
  | proton
  deriving DecidableEq, Fintype, Repr

/-- Charge signs that can be printed inside a particle marker. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

/-- Marker colors visible in the primary raster. -/
inductive FigureColor where
  | blue
  | red
  deriving DecidableEq, Fintype, Repr

/-- A dimensionful point in the plane of the diagram. -/
structure PlanePoint where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-- Literal presentation data read from image 854. -/
structure FixedElectronsProtonFigure where
  shownSpecies : ParticleLabel → ParticleSpecies
  shownSign : ParticleLabel → Option ChargeSign
  markerColor : ParticleLabel → FigureColor
  electronTextLabel : String
  protonTextLabel : String
  dashedVerticalElectronGuideShown : Bool
  dashedHorizontalProtonGuideShown : Bool
  upperVerticalOffsetLabelNanometers : ℝ
  lowerVerticalOffsetLabelNanometers : ℝ
  horizontalOffsetLabelNanometers : ℝ

/-!
The physical three-particle setup.  The time argument is explicitly an SI
seconds readout.  It is retained so that the prose assertion that both
electrons cannot move can be stated as constancy of their worldlines.
-/
structure FixedElectronsProtonSetup where
  species : ParticleLabel → ParticleSpecies
  charge : ParticleLabel → SignedChargeQuantity
  positionAtTimeInSeconds : ParticleLabel → ℝ → PlanePoint
  observationTimeInSeconds : ℝ
  upperElectronVerticalOffset : LengthQuantity
  lowerElectronVerticalOffset : LengthQuantity
  protonHorizontalOffset : LengthQuantity
  coulombConstant : CoulombConstantQuantity
  vacuumElectromagneticSystem : Electromagnetism.EMSystem
  protonElectricPotentialEnergy : DimEnergy
  figure : FixedElectronsProtonFigure

/-! ## Static scenario and primary-figure evidence -/

/-- The setup contains precisely the particle species named by the problem. -/
structure MatchesThreeParticleScenario
    (setup : FixedElectronsProtonSetup) : Prop where
  upperParticleIsElectron : setup.species .upperElectron = .electron
  lowerParticleIsElectron : setup.species .lowerElectron = .electron
  rightParticleIsProton : setup.species .proton = .proton

/-- The statement that the two electrons are fixed and cannot move. -/
structure ElectronsAreFixed
    (setup : FixedElectronsProtonSetup) : Prop where
  upperElectronWorldlineConstant :
    ∀ timeInSeconds : ℝ,
      setup.positionAtTimeInSeconds .upperElectron timeInSeconds =
        setup.positionAtTimeInSeconds .upperElectron
          setup.observationTimeInSeconds
  lowerElectronWorldlineConstant :
    ∀ timeInSeconds : ℝ,
      setup.positionAtTimeInSeconds .lowerElectron timeInSeconds =
        setup.positionAtTimeInSeconds .lowerElectron
          setup.observationTimeInSeconds

/-- All unambiguous words, colors, signs, guides, and numbers in image 854. -/
structure MatchesSuppliedElectrostaticFigure
    (setup : FixedElectronsProtonSetup) : Prop where
  upperShownAsElectron : setup.figure.shownSpecies .upperElectron = .electron
  lowerShownAsElectron : setup.figure.shownSpecies .lowerElectron = .electron
  rightShownAsProton : setup.figure.shownSpecies .proton = .proton
  upperNegativeSignShown :
    setup.figure.shownSign .upperElectron = some .negative
  lowerNegativeSignShown :
    setup.figure.shownSign .lowerElectron = some .negative
  protonHasNoPrintedSign : setup.figure.shownSign .proton = none
  upperElectronBlue : setup.figure.markerColor .upperElectron = .blue
  lowerElectronBlue : setup.figure.markerColor .lowerElectron = .blue
  protonRed : setup.figure.markerColor .proton = .red
  electronsLabel : setup.figure.electronTextLabel = "Electrons"
  protonLabel : setup.figure.protonTextLabel = "Proton"
  verticalGuideShown : setup.figure.dashedVerticalElectronGuideShown = true
  horizontalGuideShown : setup.figure.dashedHorizontalProtonGuideShown = true
  upperOffsetReadout :
    setup.figure.upperVerticalOffsetLabelNanometers = 1 / 2
  lowerOffsetReadout :
    setup.figure.lowerVerticalOffsetLabelNanometers = 1 / 2
  horizontalOffsetReadout :
    setup.figure.horizontalOffsetLabelNanometers = 2

/-- Vertical coordinate of the midpoint between the two electrons, in metres. -/
def electronMidlineVerticalCoordinateInMeters
    (setup : FixedElectronsProtonSetup) : ℝ :=
  (signedLengthInMeters
        (setup.positionAtTimeInSeconds .upperElectron
          setup.observationTimeInSeconds).vertical +
      signedLengthInMeters
        (setup.positionAtTimeInSeconds .lowerElectron
          setup.observationTimeInSeconds).vertical) / 2

/-!
Calibration of the three printed distance labels to physical lengths and to
the relative Cartesian geometry at the observation time.  The two `0.50 nm`
labels are separate offsets from the dashed horizontal midline; they are not
a claim that the full electron-to-electron separation is `0.50 nm`.
-/
structure UsesSuppliedFigureGeometry
    (setup : FixedElectronsProtonSetup) : Prop where
  upperOffsetCalibration :
    lengthInNanometers setup.upperElectronVerticalOffset =
      setup.figure.upperVerticalOffsetLabelNanometers
  lowerOffsetCalibration :
    lengthInNanometers setup.lowerElectronVerticalOffset =
      setup.figure.lowerVerticalOffsetLabelNanometers
  horizontalOffsetCalibration :
    lengthInNanometers setup.protonHorizontalOffset =
      setup.figure.horizontalOffsetLabelNanometers
  electronsShareVerticalLine :
    signedLengthInMeters
        (setup.positionAtTimeInSeconds .upperElectron
          setup.observationTimeInSeconds).horizontal =
      signedLengthInMeters
        (setup.positionAtTimeInSeconds .lowerElectron
          setup.observationTimeInSeconds).horizontal
  protonOnHorizontalMidline :
    signedLengthInMeters
        (setup.positionAtTimeInSeconds .proton
          setup.observationTimeInSeconds).vertical =
      electronMidlineVerticalCoordinateInMeters setup
  upperElectronAboveMidline :
    signedLengthInMeters
          (setup.positionAtTimeInSeconds .upperElectron
            setup.observationTimeInSeconds).vertical -
        electronMidlineVerticalCoordinateInMeters setup =
      lengthInMeters setup.upperElectronVerticalOffset
  lowerElectronBelowMidline :
    electronMidlineVerticalCoordinateInMeters setup -
        signedLengthInMeters
          (setup.positionAtTimeInSeconds .lowerElectron
            setup.observationTimeInSeconds).vertical =
      lengthInMeters setup.lowerElectronVerticalOffset
  protonRightOfElectronLine :
    signedLengthInMeters
          (setup.positionAtTimeInSeconds .proton
            setup.observationTimeInSeconds).horizontal -
        signedLengthInMeters
          (setup.positionAtTimeInSeconds .upperElectron
            setup.observationTimeInSeconds).horizontal =
      lengthInMeters setup.protonHorizontalOffset

/-- The particles carry one negative or positive elementary charge as usual. -/
structure UsesElectronAndProtonCharges
    (setup : FixedElectronsProtonSetup) : Prop where
  upperElectronCharge :
    signedChargeInCoulombs (setup.charge .upperElectron) =
      -elementaryChargeInCoulombs
  lowerElectronCharge :
    signedChargeInCoulombs (setup.charge .lowerElectron) =
      -elementaryChargeInCoulombs
  protonCharge :
    signedChargeInCoulombs (setup.charge .proton) =
      elementaryChargeInCoulombs

/-- Positivity conditions for the physical parameters used in Coulomb's law. -/
structure HasPhysicalElectrostaticParameters
    (setup : FixedElectronsProtonSetup) : Prop where
  elementaryChargePositive : 0 < elementaryChargeInCoulombs
  upperOffsetPositive : 0 < lengthInMeters setup.upperElectronVerticalOffset
  lowerOffsetPositive : 0 < lengthInMeters setup.lowerElectronVerticalOffset
  horizontalOffsetPositive : 0 < lengthInMeters setup.protonHorizontalOffset
  coulombConstantPositive :
    0 < coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant

/-!
The dimensionful Coulomb constant agrees with Physlib's electromagnetic
system and with the standard vacuum SI readout.  This calibrates a universal
constant and does not supply the requested proton energy.
-/
structure UsesVacuumCoulombConstant
    (setup : FixedElectronsProtonSetup) : Prop where
  agreesWithElectromagneticSystem :
    coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant =
      setup.vacuumElectromagneticSystem.coulombConstant
  vacuumSIReadout :
    setup.vacuumElectromagneticSystem.coulombConstant =
      89875517923 / 10

/-! ## Geometry and governing electrostatic law -/

/-- Euclidean separation of two particle centers at the observation time. -/
def particleSeparationInMeters
    (setup : FixedElectronsProtonSetup)
    (first second : ParticleLabel) : ℝ :=
  let firstPoint :=
    setup.positionAtTimeInSeconds first setup.observationTimeInSeconds
  let secondPoint :=
    setup.positionAtTimeInSeconds second setup.observationTimeInSeconds
  Real.sqrt
    ((signedLengthInMeters firstPoint.horizontal -
          signedLengthInMeters secondPoint.horizontal) ^ 2 +
      (signedLengthInMeters firstPoint.vertical -
          signedLengthInMeters secondPoint.vertical) ^ 2)

/-- One point-charge contribution `k q₁ q₂ / r`, read in joules. -/
def pointChargeCoulombEnergyInJoules
    (setup : FixedElectronsProtonSetup)
    (first second : ParticleLabel) : ℝ :=
  coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant *
      signedChargeInCoulombs (setup.charge first) *
      signedChargeInCoulombs (setup.charge second) /
    particleSeparationInMeters setup first second

/-!
The proton's potential energy, with zero at infinite separation, is the sum
of its pairwise Coulomb interactions with the two fixed electrons.  This is
the governing law, not the numerical answer to the current question.
-/
structure SatisfiesPointChargeCoulombPotentialEnergyLaw
    (setup : FixedElectronsProtonSetup) : Prop where
  protonEnergyIsSumOfElectronContributions :
    energyInJoules setup.protonElectricPotentialEnergy =
      pointChargeCoulombEnergyInJoules setup .proton .upperElectron +
        pointChargeCoulombEnergyInJoules setup .proton .lowerElectron

/-! ## Derived geometry, displayed choices, and current target -/

/-- The two electron-proton distances derived from the figure geometry. -/
lemma electronProtonDistances_fromFigure
    (setup : FixedElectronsProtonSetup)
    (hGeometry : UsesSuppliedFigureGeometry setup) :
    particleSeparationInMeters setup .proton .upperElectron =
        Real.sqrt
          (lengthInMeters setup.protonHorizontalOffset ^ 2 +
            lengthInMeters setup.upperElectronVerticalOffset ^ 2) ∧
      particleSeparationInMeters setup .proton .lowerElectron =
        Real.sqrt
          (lengthInMeters setup.protonHorizontalOffset ^ 2 +
            lengthInMeters setup.lowerElectronVerticalOffset ^ 2) := by
  constructor
  · simp only [particleSeparationInMeters]
    apply congrArg Real.sqrt
    have hVertical :
        signedLengthInMeters
              (setup.positionAtTimeInSeconds .proton
                setup.observationTimeInSeconds).vertical -
            signedLengthInMeters
              (setup.positionAtTimeInSeconds .upperElectron
                setup.observationTimeInSeconds).vertical =
          -lengthInMeters setup.upperElectronVerticalOffset := by
      rw [hGeometry.protonOnHorizontalMidline]
      linarith [hGeometry.upperElectronAboveMidline]
    rw [hGeometry.protonRightOfElectronLine, hVertical]
    ring
  · simp only [particleSeparationInMeters]
    apply congrArg Real.sqrt
    have hHorizontal :
        signedLengthInMeters
              (setup.positionAtTimeInSeconds .proton
                setup.observationTimeInSeconds).horizontal -
            signedLengthInMeters
              (setup.positionAtTimeInSeconds .lowerElectron
                setup.observationTimeInSeconds).horizontal =
          lengthInMeters setup.protonHorizontalOffset := by
      linarith [hGeometry.electronsShareVerticalLine,
        hGeometry.protonRightOfElectronLine]
    have hVertical :
        signedLengthInMeters
              (setup.positionAtTimeInSeconds .proton
                setup.observationTimeInSeconds).vertical -
            signedLengthInMeters
              (setup.positionAtTimeInSeconds .lowerElectron
                setup.observationTimeInSeconds).vertical =
          lengthInMeters setup.lowerElectronVerticalOffset := by
      rw [hGeometry.protonOnHorizontalMidline]
      exact hGeometry.lowerElectronBelowMidline
    rw [hHorizontal, hVertical]

/-!
Before rounding to a displayed choice, Coulomb's law and the elementary
charges give this exact SI expression for the proton energy.
-/
lemma protonPotentialEnergy_coulombFormula
    (setup : FixedElectronsProtonSetup)
    (hGeometry : UsesSuppliedFigureGeometry setup)
    (hCharges : UsesElectronAndProtonCharges setup)
    (hLaws : SatisfiesPointChargeCoulombPotentialEnergyLaw setup) :
    energyInJoules setup.protonElectricPotentialEnergy =
      -coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant *
        elementaryChargeInCoulombs ^ 2 *
        (1 / Real.sqrt
              (lengthInMeters setup.protonHorizontalOffset ^ 2 +
                lengthInMeters setup.upperElectronVerticalOffset ^ 2) +
          1 / Real.sqrt
              (lengthInMeters setup.protonHorizontalOffset ^ 2 +
                lengthInMeters setup.lowerElectronVerticalOffset ^ 2)) := by
  rw [hLaws.protonEnergyIsSumOfElectronContributions]
  unfold pointChargeCoulombEnergyInJoules
  rw [hCharges.protonCharge, hCharges.upperElectronCharge,
    hCharges.lowerElectronCharge]
  obtain ⟨hUpperDistance, hLowerDistance⟩ :=
    electronProtonDistances_fromFigure setup hGeometry
  rw [hUpperDistance, hLowerDistance]
  ring

/-- Labels of the four answer choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Potential energies displayed by the four choices, in joules.  The nanometre
geometry and elementary charge make the physically meaningful exponent
`10⁻¹⁹`; the source transcription's missing exponent minus is documented in
the task result.
-/
def AnswerChoice.displayedPotentialEnergyInJoules : AnswerChoice → ℝ
  | .A => (6 / 5) / (10 : ℝ) ^ 19
  | .B => -(6 / 5) / (10 : ℝ) ^ 19
  | .C => (11 / 5) / (10 : ℝ) ^ 19
  | .D => -(11 / 5) / (10 : ℝ) ^ 19

/-- Half a displayed `0.1 × 10⁻¹⁹ J` unit. -/
def displayedEnergyRoundingToleranceInJoules : ℝ :=
  (1 / 20) / (10 : ℝ) ^ 19

/-- A modeled energy agrees with a choice at the displayed precision. -/
def MatchesDisplayedPotentialEnergy
    (setup : FixedElectronsProtonSetup) (choice : AnswerChoice) : Prop :=
  |energyInJoules setup.protonElectricPotentialEnergy -
      choice.displayedPotentialEnergyInJoules| <
    displayedEnergyRoundingToleranceInJoules

/-- Exactly one displayed choice agrees with the modeled energy. -/
def IsUniqueMatchingDisplayedPotentialEnergy
    (setup : FixedElectronsProtonSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPotentialEnergy setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedPotentialEnergy setup other → other = choice

/-- The source dataset's recorded answer label, retained as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The two attractive interactions give approximately `-2.24 × 10⁻¹⁹ J`.
At the precision of the choices this is `-2.2 × 10⁻¹⁹ J`, uniquely selecting
answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0854:target`.
-/
theorem problem_phyx_mini_0854
    (setup : FixedElectronsProtonSetup)
    (hScenario : MatchesThreeParticleScenario setup)
    (hFixed : ElectronsAreFixed setup)
    (hFigure : MatchesSuppliedElectrostaticFigure setup)
    (hGeometry : UsesSuppliedFigureGeometry setup)
    (hCharges : UsesElectronAndProtonCharges setup)
    (hPhysical : HasPhysicalElectrostaticParameters setup)
    (hCoulombConstant : UsesVacuumCoulombConstant setup)
    (hLaws : SatisfiesPointChargeCoulombPotentialEnergyLaw setup) :
    energyInJoules setup.protonElectricPotentialEnergy =
        -coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant *
          elementaryChargeInCoulombs ^ 2 *
          (1 / Real.sqrt
                (lengthInMeters setup.protonHorizontalOffset ^ 2 +
                  lengthInMeters setup.upperElectronVerticalOffset ^ 2) +
            1 / Real.sqrt
                (lengthInMeters setup.protonHorizontalOffset ^ 2 +
                  lengthInMeters setup.lowerElectronVerticalOffset ^ 2)) ∧
      MatchesDisplayedPotentialEnergy setup .D ∧
      IsUniqueMatchingDisplayedPotentialEnergy setup .D := by
  clear hScenario hFixed hPhysical
  have hFormula :=
    protonPotentialEnergy_coulombFormula setup hGeometry hCharges hLaws
  have lengthInMeters_fromNanometers (length : LengthQuantity) :
      lengthInMeters length =
        lengthInNanometers length / (10 : ℝ) ^ 9 := by
    have hscale := length.property
      ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
    change
      length
          ({UnitChoices.SI with
            length := LengthUnit.meters} : UnitChoices) =
        UnitChoices.dimScale
              ({UnitChoices.SI with
                length := LengthUnit.nanometers} : UnitChoices)
              ({UnitChoices.SI with
                length := LengthUnit.meters} : UnitChoices) L𝓭 •
          length
            ({UnitChoices.SI with
              length := LengthUnit.nanometers} : UnitChoices) at hscale
    have hdim :
        UnitChoices.dimScale
              ({UnitChoices.SI with
                length := LengthUnit.nanometers} : UnitChoices)
              ({UnitChoices.SI with
                length := LengthUnit.meters} : UnitChoices) L𝓭 =
          ((10 : NNReal) ^ 9)⁻¹ := by
      ext
      norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
        Dimension.L𝓭]
      rfl
    change
      (((length
          ({UnitChoices.SI with
            length := LengthUnit.meters} : UnitChoices)).val : NNReal) : ℝ) =
        (((length
            ({UnitChoices.SI with
              length := LengthUnit.nanometers} : UnitChoices)).val :
                NNReal) : ℝ) / (10 : ℝ) ^ 9
    rw [hscale, hdim]
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul,
      NNReal.coe_inv, NNReal.coe_pow]
    norm_num
    ring
  have hUpperNanometers :
      lengthInNanometers setup.upperElectronVerticalOffset = 1 / 2 :=
    hGeometry.upperOffsetCalibration.trans hFigure.upperOffsetReadout
  have hLowerNanometers :
      lengthInNanometers setup.lowerElectronVerticalOffset = 1 / 2 :=
    hGeometry.lowerOffsetCalibration.trans hFigure.lowerOffsetReadout
  have hHorizontalNanometers :
      lengthInNanometers setup.protonHorizontalOffset = 2 :=
    hGeometry.horizontalOffsetCalibration.trans
      hFigure.horizontalOffsetReadout
  have hUpperMeters :
      lengthInMeters setup.upperElectronVerticalOffset =
        ((1 : ℝ) / 2) / 10 ^ 9 := by
    rw [lengthInMeters_fromNanometers, hUpperNanometers]
  have hLowerMeters :
      lengthInMeters setup.lowerElectronVerticalOffset =
        ((1 : ℝ) / 2) / 10 ^ 9 := by
    rw [lengthInMeters_fromNanometers, hLowerNanometers]
  have hHorizontalMeters :
      lengthInMeters setup.protonHorizontalOffset =
        (2 : ℝ) / 10 ^ 9 := by
    rw [lengthInMeters_fromNanometers, hHorizontalNanometers]
  have hCoulombReadout :
      coulombConstantInJouleMetersPerCoulombSquared
          setup.coulombConstant =
        (89875517923 : ℝ) / 10 :=
    hCoulombConstant.agreesWithElectromagneticSystem.trans
      hCoulombConstant.vacuumSIReadout
  have hElementaryCharge :
      elementaryChargeInCoulombs = (1602176634 : ℝ) / 10 ^ 28 := by
    calc
      elementaryChargeInCoulombs = (1.602176634e-19 : ℝ) := by
        rw [elementaryChargeInCoulombs, ChargeUnit.elementaryCharge,
          ChargeUnit.scale_div_self]
        rfl
      _ = (1602176634 : ℝ) / 10 ^ 28 := by norm_num
  let radicand : ℝ :=
    ((2 : ℝ) / 10 ^ 9) ^ 2 + (((1 : ℝ) / 2) / 10 ^ 9) ^ 2
  have hEnergy :
      energyInJoules setup.protonElectricPotentialEnergy =
        -(2 * ((89875517923 : ℝ) / 10) *
            ((1602176634 : ℝ) / 10 ^ 28) ^ 2 /
          Real.sqrt radicand) := by
    rw [hFormula, hCoulombReadout, hElementaryCharge,
      hHorizontalMeters, hUpperMeters, hLowerMeters]
    dsimp [radicand]
    ring
  have hRadicand :
      radicand = (17 : ℝ) / (4 * 10 ^ 18) := by
    norm_num [radicand]
  have hRadicandPositive : 0 < radicand := by
    rw [hRadicand]
    norm_num
  have hSqrtPositive : 0 < Real.sqrt radicand :=
    Real.sqrt_pos.2 hRadicandPositive
  have hSqrtSquare :
      Real.sqrt radicand ^ 2 = radicand :=
    Real.sq_sqrt hRadicandPositive.le
  have hSqrtLower :
      (2061 : ℝ) / 10 ^ 12 < Real.sqrt radicand := by
    rw [hRadicand] at hSqrtSquare ⊢
    nlinarith [
      Real.sqrt_nonneg ((17 : ℝ) / (4 * 10 ^ 18))]
  have hSqrtUpper :
      Real.sqrt radicand < (2062 : ℝ) / 10 ^ 12 := by
    rw [hRadicand] at hSqrtSquare ⊢
    nlinarith [
      Real.sqrt_nonneg ((17 : ℝ) / (4 * 10 ^ 18))]
  have hNumeratorLower :
      ((43 / 20 : ℝ) / 10 ^ 19) * ((2062 : ℝ) / 10 ^ 12) <
        2 * ((89875517923 : ℝ) / 10) *
          ((1602176634 : ℝ) / 10 ^ 28) ^ 2 := by
    norm_num
  have hNumeratorUpper :
      2 * ((89875517923 : ℝ) / 10) *
          ((1602176634 : ℝ) / 10 ^ 28) ^ 2 <
        ((9 / 4 : ℝ) / 10 ^ 19) * ((2061 : ℝ) / 10 ^ 12) := by
    norm_num
  have hMagnitudeLower :
      (43 / 20 : ℝ) / 10 ^ 19 <
        2 * ((89875517923 : ℝ) / 10) *
            ((1602176634 : ℝ) / 10 ^ 28) ^ 2 /
          Real.sqrt radicand := by
    rw [lt_div_iff₀ hSqrtPositive]
    have hmul := mul_lt_mul_of_pos_left hSqrtUpper
      (by positivity : 0 < (43 / 20 : ℝ) / 10 ^ 19)
    exact hmul.trans hNumeratorLower
  have hMagnitudeUpper :
      2 * ((89875517923 : ℝ) / 10) *
            ((1602176634 : ℝ) / 10 ^ 28) ^ 2 /
          Real.sqrt radicand <
        (9 / 4 : ℝ) / 10 ^ 19 := by
    rw [div_lt_iff₀ hSqrtPositive]
    have hmul := mul_lt_mul_of_pos_left hSqrtLower
      (by positivity : 0 < (9 / 4 : ℝ) / 10 ^ 19)
    exact hNumeratorUpper.trans hmul
  have hEnergyBounds :
      -(9 / 4 : ℝ) / 10 ^ 19 <
          energyInJoules setup.protonElectricPotentialEnergy ∧
        energyInJoules setup.protonElectricPotentialEnergy <
          -(43 / 20 : ℝ) / 10 ^ 19 := by
    rw [hEnergy]
    constructor <;> linarith
  have hMatchesD : MatchesDisplayedPotentialEnergy setup .D := by
    unfold MatchesDisplayedPotentialEnergy
    rw [abs_lt]
    change
      -((1 / 20 : ℝ) / 10 ^ 19) <
          energyInJoules setup.protonElectricPotentialEnergy -
            (-(11 / 5 : ℝ) / 10 ^ 19) ∧
        energyInJoules setup.protonElectricPotentialEnergy -
            (-(11 / 5 : ℝ) / 10 ^ 19) <
          (1 / 20 : ℝ) / 10 ^ 19
    constructor <;> linarith [hEnergyBounds.1, hEnergyBounds.2]
  refine ⟨hFormula, hMatchesD, hMatchesD, ?_⟩
  intro other hOther
  fin_cases other
  · exfalso
    unfold MatchesDisplayedPotentialEnergy at hOther
    rw [abs_lt] at hOther
    norm_num [AnswerChoice.displayedPotentialEnergyInJoules,
      displayedEnergyRoundingToleranceInJoules] at hOther
    linarith [hEnergyBounds.2]
  · exfalso
    unfold MatchesDisplayedPotentialEnergy at hOther
    rw [abs_lt] at hOther
    norm_num [AnswerChoice.displayedPotentialEnergyInJoules,
      displayedEnergyRoundingToleranceInJoules] at hOther
    linarith [hEnergyBounds.2]
  · exfalso
    unfold MatchesDisplayedPotentialEnergy at hOther
    rw [abs_lt] at hOther
    norm_num [AnswerChoice.displayedPotentialEnergyInJoules,
      displayedEnergyRoundingToleranceInJoules] at hOther
    linarith [hEnergyBounds.2]
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0854
