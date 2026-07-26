import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0853

open Dimension
open scoped BigOperators

/-!
# Escape speed of the middle electron

Three electrons are initially arranged on a vertical line, with the middle
electron one millimetre from each fixed outer electron.  A small horizontal
displacement releases the middle electron from the unstable equilibrium.  Its
repulsive Coulomb potential energy becomes kinetic energy as both separations
from the fixed electrons tend to infinity.

Physical lengths, positions, masses, charges, speeds, energies, and Coulomb's
constant are represented by unit-independent Physlib quantities.  Real
numbers below occur only at explicit coherent-SI readout boundaries, in
literal figure labels, or in the displayed answer values.

The small displacement is modeled explicitly: the outer particles keep their
positions, while the centre particle is shifted horizontally by at most one
percent of the depicted adjacent spacing.  Thus the release distances are
the actual Euclidean distances after the perturbation rather than being
silently identified with the unperturbed one-millimetre distances.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of Coulomb's constant, equivalently `J m / C²`. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent signed planar position. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A positive physical mass, represented independently of any unit choice. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Signed physical kinetic or electrostatic potential energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- A nonnegative, dimensionful value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Coordinate `0`, horizontal and positive toward the right of the image. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive toward the top of the image. -/
def yAxis : Fin 2 := 1

/-- Read a physical length in a selected named unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in millimetres, as used by the two figure labels. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  1000 * lengthInMeters length

/-- Read a planar physical position as Cartesian coordinates in metres. -/
def positionInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a physical energy in coherent-SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read Coulomb's constant in coherent SI, `J m / C²`. -/
def coulombConstantInJouleMetersPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Physlib's elementary-charge unit expressed as a number of coulombs. -/
def elementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Electron labels, stages, and primary-figure vocabulary -/

/-- The particle numbers printed in the supplied diagram. -/
inductive ElectronLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The two fixed outer electrons. -/
inductive OuterElectron where
  | upperOne
  | lowerThree
  deriving DecidableEq, Fintype, Repr

/-- The particle number corresponding to an outer-electron label. -/
def OuterElectron.electronLabel : OuterElectron → ElectronLabel
  | .upperOne => .one
  | .lowerThree => .three

/-- The two pair-distance labels displayed in the figure. -/
inductive CenterOuterPair where
  | r12
  | r23
  deriving DecidableEq, Fintype, Repr

/-- The fixed outer electron occurring in a displayed pair. -/
def CenterOuterPair.outerElectron : CenterOuterPair → OuterElectron
  | .r12 => .upperOne
  | .r23 => .lowerThree

/-- The two energy-balance states: release and asymptotically far away. -/
inductive EscapeState where
  | release
  | farAway
  deriving DecidableEq, Fintype, Repr

/-- The headings written over the two halves of the supplied diagram. -/
inductive DiagramPanel where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- The only horizontal direction used by the perturbation and velocity arrow. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Whether a depicted pair distance is finite or asymptotically infinite. -/
inductive SeparationRegime where
  | finite
  | approximatelyInfinite
  deriving DecidableEq, Repr

/-- Particle species distinguished by the problem statement. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Electric-charge signs visible inside the three circles. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-!
Literal content of image `853.png`.  The initial distance markers are physical
lengths; numerical millimetre readouts are supplied separately.
-/
structure ThreeElectronEscapeFigure where
  panelHeading : DiagramPanel → String
  particleCircleShown : DiagramPanel → ElectronLabel → Bool
  printedParticleNumber : ElectronLabel → String
  printedChargeSign : DiagramPanel → ElectronLabel → ChargeSign
  initialDistanceMarker : CenterOuterPair → LengthQuantity
  initialDistanceSymbol : CenterOuterPair → String
  finalDistanceSymbol : CenterOuterPair → String
  finalDistanceRegime : CenterOuterPair → SeparationRegime
  initialVelocityLabel : String
  finalVelocityLabel : String
  finalVelocityArrowShown : Bool
  finalVelocityArrowDirection : HorizontalDirection

/-! ## Independent physical setup -/

/-!
The unknown final speed and all intermediate energies are independent fields.
No field is defined using the recorded answer `1000 m/s`.
-/
structure ThreeElectronEscapeSetup where
  species : ElectronLabel → ParticleSpecies
  electronMass : ElectronLabel → MassQuantity
  electronCharge : ElectronLabel → SignedChargeQuantity
  coulombConstant : CoulombConstantQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  adjacentVerticalSpacing : LengthQuantity
  horizontalPerturbation : LengthQuantity
  unperturbedPosition : ElectronLabel → PlanarPositionQuantity
  releasePosition : ElectronLabel → PlanarPositionQuantity
  releasePairDistance : CenterOuterPair → LengthQuantity
  outerElectronIsFixed : OuterElectron → Bool
  centerSpeed : EscapeState → SpeedQuantity
  centerKineticEnergy : EscapeState → EnergyQuantity
  centerElectrostaticPotentialEnergy : EscapeState → EnergyQuantity
  perturbationDirection : HorizontalDirection
  farAwayVelocityDirection : HorizontalDirection
  figure : ThreeElectronEscapeFigure

/-! ## Scenario, figure/data readouts, and geometry -/

/-- Qualitative content stated in the problem, excluding the requested speed. -/
structure MatchesThreeElectronScenario
    (setup : ThreeElectronEscapeSetup) : Prop where
  allParticlesAreElectrons :
    ∀ particle, setup.species particle = .electron
  bothOuterElectronsAreFixed :
    ∀ outer, setup.outerElectronIsFixed outer = true
  centerReleasedFromRest :
    speedInMetersPerSecond (setup.centerSpeed .release) = 0
  perturbationIsHorizontalAndRightward :
    setup.perturbationDirection = .rightward
  escapeVelocityIsHorizontalAndRightward :
    setup.farAwayVelocityDirection = .rightward

/-! All unambiguous words, labels, signs, and arrows visible in image `853.png`. -/
structure MatchesPrimaryThreeElectronFigure
    (setup : ThreeElectronEscapeSetup) : Prop where
  beforeHeading : setup.figure.panelHeading .before = "Before"
  afterHeading : setup.figure.panelHeading .after = "After"
  everyParticleShownInBothPanels :
    ∀ panel particle, setup.figure.particleCircleShown panel particle = true
  particleOneNumber : setup.figure.printedParticleNumber .one = "1"
  particleTwoNumber : setup.figure.printedParticleNumber .two = "2"
  particleThreeNumber : setup.figure.printedParticleNumber .three = "3"
  allShownChargesAreNegative :
    ∀ panel particle, setup.figure.printedChargeSign panel particle = .negative
  r12InitialSymbol : setup.figure.initialDistanceSymbol .r12 = "(r₁₂)ᵢ"
  r23InitialSymbol : setup.figure.initialDistanceSymbol .r23 = "(r₂₃)ᵢ"
  r12FinalSymbol : setup.figure.finalDistanceSymbol .r12 = "(r₁₂)f"
  r23FinalSymbol : setup.figure.finalDistanceSymbol .r23 = "(r₂₃)f"
  bothInitialDistanceMarkersMatchSpacing :
    ∀ pair,
      setup.figure.initialDistanceMarker pair = setup.adjacentVerticalSpacing
  bothInitialDistanceLabelsAreOneMillimeter :
    ∀ pair, lengthInMillimeters (setup.figure.initialDistanceMarker pair) = 1
  bothFinalSeparationsAreApproximatelyInfinite :
    ∀ pair,
      setup.figure.finalDistanceRegime pair = .approximatelyInfinite
  initialVelocityLabel : setup.figure.initialVelocityLabel = "vᵢ = 0"
  finalVelocityLabel : setup.figure.finalVelocityLabel = "v_f"
  finalVelocityArrowShown : setup.figure.finalVelocityArrowShown = true
  finalVelocityArrowPointsRight :
    setup.figure.finalVelocityArrowDirection = .rightward

/-!
Cartesian geometry for the aligned figure and the perturbed release state.
The origin is the unperturbed centre-electron position.  The actual release
distances are metric distances, so the small displacement is not erased from
the Coulomb-energy calculation.
-/
structure HasDepictedAndReleaseGeometry
    (setup : ThreeElectronEscapeSetup) : Prop where
  unperturbedXCoordinates :
    ∀ particle, positionInMeters (setup.unperturbedPosition particle) xAxis = 0
  unperturbedCenterYCoordinate :
    positionInMeters (setup.unperturbedPosition .two) yAxis = 0
  unperturbedUpperYCoordinate :
    positionInMeters (setup.unperturbedPosition .one) yAxis =
      lengthInMeters setup.adjacentVerticalSpacing
  unperturbedLowerYCoordinate :
    positionInMeters (setup.unperturbedPosition .three) yAxis =
      -lengthInMeters setup.adjacentVerticalSpacing
  fixedOuterReleasePositions :
    ∀ outer : OuterElectron,
      setup.releasePosition outer.electronLabel =
        setup.unperturbedPosition outer.electronLabel
  releasedCenterXCoordinate :
    positionInMeters (setup.releasePosition .two) xAxis =
      lengthInMeters setup.horizontalPerturbation
  releasedCenterYCoordinate :
    positionInMeters (setup.releasePosition .two) yAxis = 0
  releaseDistanceIsMetricDistance : ∀ pair,
    lengthInMeters (setup.releasePairDistance pair) =
      dist (positionInMeters
          (setup.releasePosition pair.outerElectron.electronLabel))
        (positionInMeters (setup.releasePosition .two))

/-!
The phrase "small distance" is quantified as at most one percent of the
one-millimetre spacing.  This is a conservative explicit idealization: it
keeps the displacement nonzero while being far too small to change which
widely separated answer choice is closest.
-/
structure HasSmallPhysicalPerturbation
    (setup : ThreeElectronEscapeSetup) : Prop where
  adjacentSpacingPositive :
    0 < lengthInMeters setup.adjacentVerticalSpacing
  perturbationPositive :
    0 < lengthInMeters setup.horizontalPerturbation
  perturbationAtMostOnePercentOfSpacing :
    lengthInMeters setup.horizontalPerturbation ≤
      lengthInMeters setup.adjacentVerticalSpacing / 100
  releaseDistancesPositive :
    ∀ pair, 0 < lengthInMeters (setup.releasePairDistance pair)

/-!
Standard electron and vacuum-electrostatics calibrations.  These are
reference data, not the requested far-away speed.
-/
structure UsesElectronAndVacuumReferenceData
    (setup : ThreeElectronEscapeSetup) : Prop where
  everyElectronHasNegativeElementaryCharge : ∀ particle,
    chargeInCoulombs (setup.electronCharge particle) =
      -elementaryChargeInCoulombs
  everyElectronHasStandardRestMass : ∀ particle,
    massInKilograms (setup.electronMass particle) =
      (9.1093837139 : ℝ) * 10 ^ (-31 : ℤ)
  dimensionfulCoulombConstantAgreesWithSystem :
    coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant =
      setup.electromagneticSystem.coulombConstant
  vacuumCoulombConstantSI :
    setup.electromagneticSystem.coulombConstant =
      (89875517923 : ℝ) / 10
  elementaryChargeSI :
    elementaryChargeInCoulombs =
      (1.602176634 : ℝ) * 10 ^ (-19 : ℤ)

/-! ## Governing electrostatic and mechanical laws -/

/-!
The centre electron's potential energy is the sum of its two pairwise Coulomb
energies.  At asymptotically infinite separations that potential vanishes.
Kinetic energy obeys `K = m v² / 2`, and total mechanical energy is conserved.
These laws are generic in the setup quantities and contain neither the target
squared-speed formula nor any answer-choice value.
-/
structure SatisfiesCoulombEscapeAndEnergyLaws
    (setup : ThreeElectronEscapeSetup) : Prop where
  releaseCoulombPotentialEnergy :
    energyInJoules
        (setup.centerElectrostaticPotentialEnergy .release) =
      ∑ pair : CenterOuterPair,
        coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant *
            chargeInCoulombs (setup.electronCharge .two) *
            chargeInCoulombs
              (setup.electronCharge pair.outerElectron.electronLabel) /
          lengthInMeters (setup.releasePairDistance pair)
  farAwayPotentialEnergyVanishes :
    energyInJoules
        (setup.centerElectrostaticPotentialEnergy .farAway) = 0
  centerKineticEnergyLaw : ∀ state,
    energyInJoules (setup.centerKineticEnergy state) =
      (1 / 2 : ℝ) * massInKilograms (setup.electronMass .two) *
        speedInMetersPerSecond (setup.centerSpeed state) ^ 2
  mechanicalEnergyConservation :
    energyInJoules (setup.centerKineticEnergy .release) +
        energyInJoules
          (setup.centerElectrostaticPotentialEnergy .release) =
      energyInJoules (setup.centerKineticEnergy .farAway) +
        energyInJoules
          (setup.centerElectrostaticPotentialEnergy .farAway)

/-! ## Displayed choices and current target -/

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed printed beside each answer choice, in metres per second. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 1500
  | .B => 1400
  | .C => 1250
  | .D => 1000

/-!
A displayed choice is uniquely closest to the calculated far-away speed.
This generic comparison predicate does not privilege any particular label.
-/
def IsUniqueClosestDisplayedSpeed
    (setup : ThreeElectronEscapeSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |speedInMetersPerSecond (setup.centerSpeed .farAway) -
        displayedSpeedInMetersPerSecond choice| <
      |speedInMetersPerSecond (setup.centerSpeed .farAway) -
        displayedSpeedInMetersPerSecond other|

/-!
Energy conservation gives the exact squared-speed balance before numerical
rounding.  With the electron constants and one-millimetre geometry, the speed
is approximately `1006.5 m/s`; hence `1000 m/s` (answer D) is the unique
closest displayed value.

This formalizes blueprint label `thm:physics:phyx_mini_0853:target`.
-/
theorem problem_phyx_mini_0853
    (setup : ThreeElectronEscapeSetup)
    (scenario : MatchesThreeElectronScenario setup)
    (figure : MatchesPrimaryThreeElectronFigure setup)
    (geometry : HasDepictedAndReleaseGeometry setup)
    (physical : HasSmallPhysicalPerturbation setup)
    (reference : UsesElectronAndVacuumReferenceData setup)
    (laws : SatisfiesCoulombEscapeAndEnergyLaws setup) :
    speedInMetersPerSecond (setup.centerSpeed .farAway) ^ 2 =
        (2 / massInKilograms (setup.electronMass .two)) *
          ∑ pair : CenterOuterPair,
            coulombConstantInJouleMetersPerCoulombSquared
                  setup.coulombConstant *
                chargeInCoulombs (setup.electronCharge .two) *
                chargeInCoulombs
                  (setup.electronCharge pair.outerElectron.electronLabel) /
              lengthInMeters (setup.releasePairDistance pair) ∧
      IsUniqueClosestDisplayedSpeed setup .D := by
  have hspeed_sq :
      speedInMetersPerSecond (setup.centerSpeed .farAway) ^ 2 =
        (2 / massInKilograms (setup.electronMass .two)) *
          ∑ pair : CenterOuterPair,
            coulombConstantInJouleMetersPerCoulombSquared
                  setup.coulombConstant *
                chargeInCoulombs (setup.electronCharge .two) *
                chargeInCoulombs
                  (setup.electronCharge pair.outerElectron.electronLabel) /
              lengthInMeters (setup.releasePairDistance pair) := by
    have hm :
        massInKilograms (setup.electronMass .two) ≠ 0 := by
      rw [reference.everyElectronHasStandardRestMass .two]
      norm_num
    have hconservation := laws.mechanicalEnergyConservation
    rw [laws.centerKineticEnergyLaw .release,
      laws.releaseCoulombPotentialEnergy,
      laws.centerKineticEnergyLaw .farAway,
      laws.farAwayPotentialEnergyVanishes,
      scenario.centerReleasedFromRest] at hconservation
    field_simp [hm]
    norm_num at hconservation ⊢
    nlinarith
  constructor
  · exact hspeed_sq
  · unfold IsUniqueClosestDisplayedSpeed
    intro other hother
    have hdist_sq : ∀ pair : CenterOuterPair,
        lengthInMeters (setup.releasePairDistance pair) ^ 2 =
          lengthInMeters setup.horizontalPerturbation ^ 2 +
            lengthInMeters setup.adjacentVerticalSpacing ^ 2 := by
      intro pair
      rw [geometry.releaseDistanceIsMetricDistance pair,
        EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
      cases pair with
      | r12 =>
          simp only [CenterOuterPair.outerElectron,
            OuterElectron.electronLabel]
          have hfixed :
              setup.releasePosition .one =
                setup.unperturbedPosition .one := by
            simpa [OuterElectron.electronLabel] using
              geometry.fixedOuterReleasePositions .upperOne
          have houterX :
              positionInMeters (setup.unperturbedPosition .one) 0 = 0 := by
            simpa [xAxis] using geometry.unperturbedXCoordinates .one
          have hcenterX :
              positionInMeters (setup.releasePosition .two) 0 =
                lengthInMeters setup.horizontalPerturbation := by
            simpa [xAxis] using geometry.releasedCenterXCoordinate
          have houterY :
              positionInMeters (setup.unperturbedPosition .one) 1 =
                lengthInMeters setup.adjacentVerticalSpacing := by
            simpa [yAxis] using geometry.unperturbedUpperYCoordinate
          have hcenterY :
              positionInMeters (setup.releasePosition .two) 1 = 0 := by
            simpa [yAxis] using geometry.releasedCenterYCoordinate
          rw [congrArg positionInMeters hfixed]
          rw [houterX, hcenterX, houterY, hcenterY]
          simp [Real.dist_eq]
      | r23 =>
          simp only [CenterOuterPair.outerElectron,
            OuterElectron.electronLabel]
          have hfixed :
              setup.releasePosition .three =
                setup.unperturbedPosition .three := by
            simpa [OuterElectron.electronLabel] using
              geometry.fixedOuterReleasePositions .lowerThree
          have houterX :
              positionInMeters (setup.unperturbedPosition .three) 0 = 0 := by
            simpa [xAxis] using geometry.unperturbedXCoordinates .three
          have hcenterX :
              positionInMeters (setup.releasePosition .two) 0 =
                lengthInMeters setup.horizontalPerturbation := by
            simpa [xAxis] using geometry.releasedCenterXCoordinate
          have houterY :
              positionInMeters (setup.unperturbedPosition .three) 1 =
                -lengthInMeters setup.adjacentVerticalSpacing := by
            simpa [yAxis] using geometry.unperturbedLowerYCoordinate
          have hcenterY :
              positionInMeters (setup.releasePosition .two) 1 = 0 := by
            simpa [yAxis] using geometry.releasedCenterYCoordinate
          rw [congrArg positionInMeters hfixed]
          rw [houterX, hcenterX, houterY, hcenterY]
          simp [Real.dist_eq]
    let v : ℝ :=
      speedInMetersPerSecond (setup.centerSpeed .farAway)
    let s : ℝ :=
      lengthInMeters setup.adjacentVerticalSpacing
    let x : ℝ :=
      lengthInMeters setup.horizontalPerturbation
    let d₁ : ℝ :=
      lengthInMeters (setup.releasePairDistance .r12)
    let d₃ : ℝ :=
      lengthInMeters (setup.releasePairDistance .r23)
    have hs : s = 1 / 1000 := by
      have hlabel :=
        figure.bothInitialDistanceLabelsAreOneMillimeter .r12
      rw [figure.bothInitialDistanceMarkersMatchSpacing .r12] at hlabel
      dsimp [s]
      rw [lengthInMillimeters] at hlabel
      norm_num at hlabel ⊢
      linarith
    have hxpos : 0 < x := by
      simpa [x] using physical.perturbationPositive
    have hxle : x ≤ s / 100 := by
      simpa [x, s] using
        physical.perturbationAtMostOnePercentOfSpacing
    have hd₁pos : 0 < d₁ := by
      simpa [d₁] using physical.releaseDistancesPositive .r12
    have hd₃pos : 0 < d₃ := by
      simpa [d₃] using physical.releaseDistancesPositive .r23
    have hd₁sq : d₁ ^ 2 = x ^ 2 + s ^ 2 := by
      simpa [d₁, x, s] using hdist_sq .r12
    have hd₃sq : d₃ ^ 2 = x ^ 2 + s ^ 2 := by
      simpa [d₃, x, s] using hdist_sq .r23
    have hxnonneg : 0 ≤ x := le_of_lt hxpos
    have hx_product_nonneg : 0 ≤ x * (s / 100 - x) :=
      mul_nonneg hxnonneg (sub_nonneg.mpr hxle)
    have hd₁_lower : 1 / 1000 < d₁ := by
      rw [hs] at hd₁sq
      nlinarith
    have hd₃_lower : 1 / 1000 < d₃ := by
      rw [hs] at hd₃sq
      nlinarith
    have hd₁_upper : d₁ < 101 / 100000 := by
      rw [hs] at hxle hd₁sq hx_product_nonneg
      norm_num at hxle hd₁sq hx_product_nonneg ⊢
      nlinarith
    have hd₃_upper : d₃ < 101 / 100000 := by
      rw [hs] at hxle hd₃sq hx_product_nonneg
      norm_num at hxle hd₃sq hx_product_nonneg ⊢
      nlinarith
    have centerOuterPair_sum (f : CenterOuterPair → ℝ) :
        (∑ pair, f pair) = f .r12 + f .r23 := by
      rw [show (Finset.univ : Finset CenterOuterPair) =
          {.r12, .r23} by
        ext pair
        cases pair <;> simp]
      simp
    have hspeed_numeric := hspeed_sq
    rw [centerOuterPair_sum,
      reference.everyElectronHasStandardRestMass .two,
      reference.dimensionfulCoulombConstantAgreesWithSystem,
      reference.vacuumCoulombConstantSI,
      reference.everyElectronHasNegativeElementaryCharge .two] at hspeed_numeric
    simp only [CenterOuterPair.outerElectron,
      OuterElectron.electronLabel] at hspeed_numeric
    rw [
      reference.everyElectronHasNegativeElementaryCharge .one,
      reference.everyElectronHasNegativeElementaryCharge .three,
      reference.elementaryChargeSI] at hspeed_numeric
    change v ^ 2 =
      (2 / ((9.1093837139 : ℝ) * 10 ^ (-31 : ℤ))) *
        (((89875517923 : ℝ) / 10) *
              (-((1.602176634 : ℝ) * 10 ^ (-19 : ℤ))) *
              (-((1.602176634 : ℝ) * 10 ^ (-19 : ℤ))) / d₁ +
          ((89875517923 : ℝ) / 10) *
              (-((1.602176634 : ℝ) * 10 ^ (-19 : ℤ))) *
              (-((1.602176634 : ℝ) * 10 ^ (-19 : ℤ))) / d₃)
      at hspeed_numeric
    have hv_nonneg : 0 ≤ v := by
      dsimp [v, speedInMetersPerSecond]
      positivity
    let A : ℝ :=
      2 / ((9.1093837139 : ℝ) * 10 ^ (-31 : ℤ))
    let C : ℝ :=
      ((89875517923 : ℝ) / 10) *
        (-((1.602176634 : ℝ) * 10 ^ (-19 : ℤ))) *
        (-((1.602176634 : ℝ) * 10 ^ (-19 : ℤ)))
    change v ^ 2 = A * (C / d₁ + C / d₃) at hspeed_numeric
    have hApos : 0 < A := by
      dsimp [A]
      positivity
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    have hC_lower_d₁ : C / (101 / 100000) < C / d₁ := by
      apply (div_lt_div_iff₀ (by norm_num) hd₁pos).2
      exact mul_lt_mul_of_pos_left hd₁_upper hCpos
    have hC_lower_d₃ : C / (101 / 100000) < C / d₃ := by
      apply (div_lt_div_iff₀ (by norm_num) hd₃pos).2
      exact mul_lt_mul_of_pos_left hd₃_upper hCpos
    have hC_upper_d₁ : C / d₁ < C / (1 / 1000) := by
      apply (div_lt_div_iff₀ hd₁pos (by norm_num)).2
      exact mul_lt_mul_of_pos_left hd₁_lower hCpos
    have hC_upper_d₃ : C / d₃ < C / (1 / 1000) := by
      apply (div_lt_div_iff₀ hd₃pos (by norm_num)).2
      exact mul_lt_mul_of_pos_left hd₃_lower hCpos
    have hnumeric_lower :
        (1000 : ℝ) ^ 2 <
          A * (C / (101 / 100000) + C / (101 / 100000)) := by
      norm_num [A, C]
    have hnumeric_upper :
        A * (C / (1 / 1000) + C / (1 / 1000)) <
          (1125 : ℝ) ^ 2 := by
      norm_num [A, C]
    have hv_sq_lower : (1000 : ℝ) ^ 2 < v ^ 2 := by
      calc
        (1000 : ℝ) ^ 2 <
            A * (C / (101 / 100000) + C / (101 / 100000)) :=
          hnumeric_lower
        _ < A * (C / d₁ + C / d₃) :=
          mul_lt_mul_of_pos_left
            (add_lt_add hC_lower_d₁ hC_lower_d₃) hApos
        _ = v ^ 2 := hspeed_numeric.symm
    have hv_sq_upper : v ^ 2 < (1125 : ℝ) ^ 2 := by
      calc
        v ^ 2 = A * (C / d₁ + C / d₃) := hspeed_numeric
        _ < A * (C / (1 / 1000) + C / (1 / 1000)) :=
          mul_lt_mul_of_pos_left
            (add_lt_add hC_upper_d₁ hC_upper_d₃) hApos
        _ < (1125 : ℝ) ^ 2 := hnumeric_upper
    have hv_lower : 1000 < v := by
      nlinarith
    have hv_upper : v < 1125 := by
      nlinarith
    change
      |v - displayedSpeedInMetersPerSecond .D| <
        |v - displayedSpeedInMetersPerSecond other|
    cases other with
    | A =>
        norm_num [displayedSpeedInMetersPerSecond]
        rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
        linarith
    | B =>
        norm_num [displayedSpeedInMetersPerSecond]
        rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
        linarith
    | C =>
        norm_num [displayedSpeedInMetersPerSecond]
        rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
        linarith
    | D =>
        exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0853
