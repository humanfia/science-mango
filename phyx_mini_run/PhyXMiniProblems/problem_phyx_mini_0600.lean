import Mathlib.Analysis.Real.Sqrt
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0600

open Dimension

/-!
# Neutron absorption at an abrupt nuclear potential drop

A free neutron with kinetic energy `4 MeV` approaches a nucleus from the left.
At the nuclear boundary its potential energy drops abruptly from zero to
`-12 MeV`.  The one-dimensional downward-step model determines the probability
flux transmitted into the nucleus.  Identifying every transmitted neutron
with an absorbed neutron that initiates fission is represented separately as
an explicit idealized capture assumption; it is not a consequence of step
scattering alone.

Physical energies, mass, action, position, and wave numbers retain their
dimensions through Physlib.  Real numbers below are used only for calibrated
unit readouts, dimensionless probabilities, raster measurements, and values
printed beside answer choices.

Assumption/target split:

* `MatchesNeutronNucleusScenario` records the neutron, its rightward incidence,
  the interface geometry, and the potentials `0` and `-V₀`;
* `MatchesProblemEnergyReadouts` records only the supplied `4 MeV` kinetic
  energy and `12 MeV` well depth;
* `MatchesSuppliedPotentialDropFigure` records the axes, labels, cart, arrow,
  potential levels, and rounded pixel locations visible in image `600.png`;
* `SatisfiesAbruptPotentialDropLaws` states regional energy balance,
  Schrödinger dispersion, the general sharp-step flux coefficients, and flux
  conservation;
* `ModelsEntryAsAbsorptionInducingFission` states the source's additional
  idealized identification of nuclear entry with absorption initiating
  fission; and
* the wave-number ratio `2`, transmission probability `8/9`, conditional
  absorption probability `8/9`, and answer C occur only in derived
  conclusions, never in a premise.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, equivalently energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A signed, unit-independent position along the scattering axis. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative wave-number magnitude, of inverse-length dimension. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Coherent-SI readout of a physical energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a physical energy in megaelectron-volts. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy /
    (1_000_000 * energyInJoules DimEnergy.electronVolt)

/-- Coherent-SI readout of a physical mass, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read a signed position in metres. -/
def positionInMeters (position : SignedLengthQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a wave-number magnitude in inverse metres. -/
def waveNumberInInverseMeters (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure labels -/

/-- Particle species relevant to the stated nuclear-entry scenario. -/
inductive ParticleSpecies where
  | neutron
  deriving DecidableEq, Repr

/-- The two constant-potential regions separated by the nuclear boundary. -/
inductive PotentialRegion where
  | outsideNucleus
  | insideNucleus
  deriving DecidableEq, Fintype, Repr

/-- Events whose probabilities are distinguished by the physical model. -/
inductive ScatteringEvent where
  | reflectedOutside
  | transmittedIntoNucleus
  | absorbedInitiatingFission
  deriving DecidableEq, Fintype, Repr

/-- Directions along the horizontal `x` axis. -/
inductive HorizontalDirection where
  | towardNegativeX
  | towardPositiveX
  deriving DecidableEq, Repr

/-- The two coordinate axes drawn in the potential-energy diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Literal symbols printed at the ends of the axes. -/
inductive AxisSymbol where
  | x
  | VofX
  deriving DecidableEq, Repr

/-- The negative inside-potential label printed beside the lower plateau. -/
inductive PotentialLevelLabel where
  | negativeV₀
  deriving DecidableEq, Repr

/-!
Qualitative contents and rounded pixel readouts from the `851 × 406` primary
raster.  Pixel coordinates are dimensionless presentation data, not physical
positions or energies.  The rounded zero and lower-level ordinates give a
drawn drop of about `177` pixels, but no physical energy is inferred from that
uncalibrated distance.
-/
structure AbruptPotentialDropFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  axisSymbol : FigureAxis → AxisSymbol
  boundaryXPixel : ℝ
  zeroPotentialYPixel : ℝ
  negativePotentialYPixel : ℝ
  horizontalAxisShown : Bool
  verticalAxisShown : Bool
  outsideZeroLevelShown : Bool
  insideNegativePlateauShown : Bool
  boundaryCoincidesWithVerticalAxis : Bool
  negativeLevelLabel : PotentialLevelLabel
  incomingCartShown : Bool
  cartWheelCount : ℕ
  incomingMotionArrowShown : Bool
  incomingMotionDirection : HorizontalDirection

/-!
Independent physical quantities of the scattering experiment.  In
particular, the three event probabilities are stored independently; none is
defined from an answer value or from the sharp-step coefficient.
-/
structure NeutronPotentialDropSetup where
  particleSpecies : ParticleSpecies
  particleMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  interfacePosition : SignedLengthQuantity
  incidentDirection : HorizontalDirection
  totalEnergy : DimEnergy
  wellDepth : DimEnergy
  potentialEnergy : PotentialRegion → DimEnergy
  kineticEnergy : PotentialRegion → DimEnergy
  waveNumber : PotentialRegion → WaveNumberQuantity
  eventProbability : ScatteringEvent → ℝ
  figure : AbruptPotentialDropFigure

/-- Probability flux transmitted from outside into the nucleus. -/
def transmissionProbability (setup : NeutronPotentialDropSetup) : ℝ :=
  setup.eventProbability .transmittedIntoNucleus

/-- Probability that the neutron is reflected and remains outside. -/
def reflectionProbability (setup : NeutronPotentialDropSetup) : ℝ :=
  setup.eventProbability .reflectedOutside

/-- Probability requested by the problem: absorption initiating fission. -/
def absorptionProbability (setup : NeutronPotentialDropSetup) : ℝ :=
  setup.eventProbability .absorbedInitiatingFission

/-! ## Scenario, supplied data, figure evidence, and governing physics -/

/-!
The neutron comes from the left, the boundary is chosen as `x = 0`, and the
potential drops from zero outside to `-V₀` inside.  These are general scenario
relations and contain neither the supplied MeV values nor the answer.
-/
structure MatchesNeutronNucleusScenario
    (setup : NeutronPotentialDropSetup) : Prop where
  particleIsNeutron : setup.particleSpecies = .neutron
  incidentMotionIsRightward :
    setup.incidentDirection = .towardPositiveX
  interfaceAtOrigin : positionInMeters setup.interfacePosition = 0
  outsidePotentialIsZero :
    energyInJoules (setup.potentialEnergy .outsideNucleus) = 0
  insidePotentialIsNegativeWellDepth :
    energyInJoules (setup.potentialEnergy .insideNucleus) =
      -energyInJoules setup.wellDepth

/-!
The two numerical energies stated in the prose.  The inside kinetic energy,
wave-number ratio, and absorption probability are intentionally absent.
-/
structure MatchesProblemEnergyReadouts
    (setup : NeutronPotentialDropSetup) : Prop where
  incidentKineticEnergyMeV :
    energyInMegaElectronVolts
        (setup.kineticEnergy .outsideNucleus) = 4
  nuclearWellDepthMeV :
    energyInMegaElectronVolts setup.wellDepth = 12

/-!
Direct evidence from image `600.png`.  This premise contains no physical
probability, wave number, MeV calibration, or answer-choice label.
-/
structure MatchesSuppliedPotentialDropFigure
    (figure : AbruptPotentialDropFigure) : Prop where
  rasterWidth : figure.rasterWidthPixels = 851
  rasterHeight : figure.rasterHeightPixels = 406
  horizontalAxisLabel : figure.axisSymbol .horizontal = .x
  verticalAxisLabel : figure.axisSymbol .vertical = .VofX
  roundedBoundaryAbscissa : figure.boundaryXPixel = 278
  roundedZeroLevelOrdinate : figure.zeroPotentialYPixel = 168
  roundedNegativeLevelOrdinate : figure.negativePotentialYPixel = 345
  horizontalAxisVisible : figure.horizontalAxisShown = true
  verticalAxisVisible : figure.verticalAxisShown = true
  zeroOutsideSegmentVisible : figure.outsideZeroLevelShown = true
  lowerInsidePlateauVisible : figure.insideNegativePlateauShown = true
  potentialBoundaryAtVerticalAxis :
    figure.boundaryCoincidesWithVerticalAxis = true
  lowerPlateauLabel : figure.negativeLevelLabel = .negativeV₀
  incomingCartVisible : figure.incomingCartShown = true
  twoCartWheelsVisible : figure.cartWheelCount = 2
  incomingArrowVisible : figure.incomingMotionArrowShown = true
  incomingArrowPointsRight :
    figure.incomingMotionDirection = .towardPositiveX

/-- Positivity and ordinary probability bounds for the physical branch. -/
structure HasPhysicalPotentialDropParameters
    (setup : NeutronPotentialDropSetup) : Prop where
  particleMassPositive : 0 < massInKilograms setup.particleMass
  reducedPlanckActionPositive :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  totalEnergyPositive : 0 < energyInJoules setup.totalEnergy
  wellDepthPositive : 0 < energyInJoules setup.wellDepth
  regionalKineticEnergyPositive : ∀ region,
    0 < energyInJoules (setup.kineticEnergy region)
  regionalWaveNumberPositive : ∀ region,
    0 < waveNumberInInverseMeters (setup.waveNumber region)
  eventProbabilityBounds : ∀ event,
    0 ≤ setup.eventProbability event ∧ setup.eventProbability event ≤ 1

/-!
Physlib's standard reduced Planck constant, calibrated in SI
joule-seconds.  Its value is common to both regions and does not determine the
answer on its own.
-/
structure UsesStandardReducedPlanckConstant
    (setup : NeutronPotentialDropSetup) : Prop where
  reducedPlanckActionJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/-!
Governing laws for a stationary one-dimensional downward potential step:

* regional kinetic energy is `E - V`;
* `ℏ² k² = 2 m K` in each constant-potential region;
* the sharp-interface transmission and reflection flux coefficients are
  expressed in terms of the still-unknown regional wave numbers; and
* incident probability flux is conserved.

These laws are general in all energies and wave numbers.  They contain no
specialization to `4 MeV`, `12 MeV`, `k_inside/k_outside = 2`, or `8/9`.
-/
structure SatisfiesAbruptPotentialDropLaws
    (setup : NeutronPotentialDropSetup) : Prop where
  regionalEnergyBalance : ∀ region : PotentialRegion,
    energyInJoules (setup.kineticEnergy region) =
      energyInJoules setup.totalEnergy -
        energyInJoules (setup.potentialEnergy region)
  regionalDispersion : ∀ region : PotentialRegion,
    actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
        waveNumberInInverseMeters (setup.waveNumber region) ^ 2 =
      2 * massInKilograms setup.particleMass *
        energyInJoules (setup.kineticEnergy region)
  transmissionFluxCoefficient :
    transmissionProbability setup =
      4 * waveNumberInInverseMeters
            (setup.waveNumber .outsideNucleus) *
          waveNumberInInverseMeters (setup.waveNumber .insideNucleus) /
        (waveNumberInInverseMeters (setup.waveNumber .outsideNucleus) +
          waveNumberInInverseMeters (setup.waveNumber .insideNucleus)) ^ 2
  reflectionFluxCoefficient :
    reflectionProbability setup =
      ((waveNumberInInverseMeters (setup.waveNumber .outsideNucleus) -
          waveNumberInInverseMeters (setup.waveNumber .insideNucleus)) /
        (waveNumberInInverseMeters (setup.waveNumber .outsideNucleus) +
          waveNumberInInverseMeters (setup.waveNumber .insideNucleus))) ^ 2
  probabilityFluxConservation :
    reflectionProbability setup + transmissionProbability setup = 1

/-!
An additional idealized capture model: every neutron represented by transmitted
probability flux is absorbed and initiates another fission.  Sharp-step
scattering itself does not imply this equality.  This is an event-identification
law, not a numerical absorption formula.
-/
structure ModelsEntryAsAbsorptionInducingFission
    (setup : NeutronPotentialDropSetup) : Prop where
  absorptionEqualsTransmittedFlux :
    absorptionProbability setup = transmissionProbability setup

/-! ## Derived relations and answer semantics -/

/-!
The `4 MeV` outside kinetic energy and `12 MeV` downward potential change make
the inside kinetic energy `16 MeV`.  With common positive mass and `ℏ`, the
dispersion law therefore yields `k_inside / k_outside = 2`.
-/
lemma insideToOutsideWaveNumberRatio
    (setup : NeutronPotentialDropSetup)
    (_scenario : MatchesNeutronNucleusScenario setup)
    (_data : MatchesProblemEnergyReadouts setup)
    (_physical : HasPhysicalPotentialDropParameters setup)
    (_laws : SatisfiesAbruptPotentialDropLaws setup) :
    waveNumberInInverseMeters (setup.waveNumber .insideNucleus) /
        waveNumberInInverseMeters (setup.waveNumber .outsideNucleus) = 2 := by
  let mev : ℝ :=
    1_000_000 * energyInJoules DimEnergy.electronVolt
  have hOutsideReadout :
      energyInJoules (setup.kineticEnergy .outsideNucleus) / mev = 4 := by
    simpa [energyInMegaElectronVolts, mev] using
      _data.incidentKineticEnergyMeV
  have hWellReadout :
      energyInJoules setup.wellDepth / mev = 12 := by
    simpa [energyInMegaElectronVolts, mev] using
      _data.nuclearWellDepthMeV
  have hMev : mev ≠ 0 := by
    intro h
    rw [h] at hOutsideReadout
    norm_num at hOutsideReadout
  have hOutsideScale :
      energyInJoules (setup.kineticEnergy .outsideNucleus) = 4 * mev :=
    (div_eq_iff hMev).mp hOutsideReadout
  have hWellScale :
      energyInJoules setup.wellDepth = 12 * mev :=
    (div_eq_iff hMev).mp hWellReadout
  have hWellTriple :
      energyInJoules setup.wellDepth =
        3 * energyInJoules (setup.kineticEnergy .outsideNucleus) := by
    rw [hOutsideScale, hWellScale]
    ring
  have hOutsideEnergy :=
    _laws.regionalEnergyBalance PotentialRegion.outsideNucleus
  rw [_scenario.outsidePotentialIsZero] at hOutsideEnergy
  have hInsideEnergy :=
    _laws.regionalEnergyBalance PotentialRegion.insideNucleus
  rw [_scenario.insidePotentialIsNegativeWellDepth] at hInsideEnergy
  have hInsideFourfold :
      energyInJoules (setup.kineticEnergy .insideNucleus) =
        4 * energyInJoules (setup.kineticEnergy .outsideNucleus) := by
    linarith
  have hOutsideDispersion :=
    _laws.regionalDispersion PotentialRegion.outsideNucleus
  have hInsideDispersion :=
    _laws.regionalDispersion PotentialRegion.insideNucleus
  rw [hInsideFourfold] at hInsideDispersion
  have hWaveSquares :
      waveNumberInInverseMeters (setup.waveNumber .insideNucleus) ^ 2 =
        4 *
          waveNumberInInverseMeters (setup.waveNumber .outsideNucleus) ^ 2 := by
    have hActionNe :
        actionInJouleSeconds setup.reducedPlanckAction ^ 2 ≠ 0 :=
      pow_ne_zero 2 (ne_of_gt _physical.reducedPlanckActionPositive)
    apply (mul_left_cancel₀ hActionNe)
    calc
      actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
          waveNumberInInverseMeters (setup.waveNumber .insideNucleus) ^ 2 =
          2 * massInKilograms setup.particleMass *
            (4 *
              energyInJoules
                (setup.kineticEnergy .outsideNucleus)) := hInsideDispersion
      _ =
          actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
            (4 *
              waveNumberInInverseMeters
                (setup.waveNumber .outsideNucleus) ^ 2) := by
            calc
              2 * massInKilograms setup.particleMass *
                  (4 *
                    energyInJoules
                      (setup.kineticEnergy .outsideNucleus)) =
                  4 *
                    (2 * massInKilograms setup.particleMass *
                      energyInJoules
                        (setup.kineticEnergy .outsideNucleus)) := by ring
              _ =
                  4 *
                    (actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
                      waveNumberInInverseMeters
                        (setup.waveNumber .outsideNucleus) ^ 2) := by
                    rw [hOutsideDispersion]
              _ =
                  actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
                    (4 *
                      waveNumberInInverseMeters
                        (setup.waveNumber .outsideNucleus) ^ 2) := by ring
  have hFactor :
      (waveNumberInInverseMeters (setup.waveNumber .insideNucleus) -
          2 * waveNumberInInverseMeters (setup.waveNumber .outsideNucleus)) *
        (waveNumberInInverseMeters (setup.waveNumber .insideNucleus) +
          2 * waveNumberInInverseMeters (setup.waveNumber .outsideNucleus)) =
        0 := by
    nlinarith
  have hInsideDouble :
      waveNumberInInverseMeters (setup.waveNumber .insideNucleus) =
        2 * waveNumberInInverseMeters (setup.waveNumber .outsideNucleus) := by
    rcases mul_eq_zero.mp hFactor with h | h
    · linarith
    · have hInsidePositive :=
        _physical.regionalWaveNumberPositive PotentialRegion.insideNucleus
      have hOutsidePositive :=
        _physical.regionalWaveNumberPositive PotentialRegion.outsideNucleus
      linarith
  exact
    (div_eq_iff
      (ne_of_gt
        (_physical.regionalWaveNumberPositive
          PotentialRegion.outsideNucleus))).2 hInsideDouble

/-- Labels of the four absorption-probability choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless decimal probability printed beside each answer choice. -/
def displayedAbsorptionProbability : AnswerChoice → ℝ
  | .A => 6667 / 10000
  | .B => 5556 / 10000
  | .C => 8889 / 10000
  | .D => 7778 / 10000

/-- Dataset metadata recording answer C; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice is at least as close as every alternative. -/
def IsNearestAnswerChoice (probability : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    abs (probability - displayedAbsorptionProbability choice) ≤
      abs (probability - displayedAbsorptionProbability other)

/-!
Agreement with a probability printed to four decimal places.  Half of one
unit in the final decimal place is `1 / 20000`.
-/
def AgreesWhenRoundedToFourDecimals
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  abs (probability - displayedAbsorptionProbability choice) < 1 / 20000

/-!
For a `4 MeV` neutron entering a `12 MeV` downward nuclear well,
`k_inside/k_outside = 2`.  Substitution into the general transmitted-flux
coefficient gives the physically supported entry probability `8/9`.  Its
four-decimal display is `0.8889`, answer C.  This conclusion does not identify
entry with nuclear absorption.
-/
theorem neutronEntryTransmissionProbabilityAtNuclearPotentialDrop
    (setup : NeutronPotentialDropSetup)
    (_scenario : MatchesNeutronNucleusScenario setup)
    (_data : MatchesProblemEnergyReadouts setup)
    (_figure : MatchesSuppliedPotentialDropFigure setup.figure)
    (_physical : HasPhysicalPotentialDropParameters setup)
    (_standardPlanck : UsesStandardReducedPlanckConstant setup)
    (_laws : SatisfiesAbruptPotentialDropLaws setup) :
    transmissionProbability setup = (8 : ℝ) / 9 ∧
      AgreesWhenRoundedToFourDecimals (transmissionProbability setup) .C ∧
      IsNearestAnswerChoice (transmissionProbability setup) .C := by
  have hRatio :=
    insideToOutsideWaveNumberRatio setup _scenario _data _physical _laws
  have hOutsidePositive :=
    _physical.regionalWaveNumberPositive PotentialRegion.outsideNucleus
  have hInsideDouble :
      waveNumberInInverseMeters (setup.waveNumber .insideNucleus) =
        2 * waveNumberInInverseMeters (setup.waveNumber .outsideNucleus) :=
    (div_eq_iff (ne_of_gt hOutsidePositive)).mp hRatio
  have hTransmission : transmissionProbability setup = (8 : ℝ) / 9 := by
    rw [_laws.transmissionFluxCoefficient, hInsideDouble]
    field_simp [ne_of_gt hOutsidePositive]
    ring
  refine ⟨hTransmission, ?_, ?_⟩
  · rw [hTransmission]
    norm_num [AgreesWhenRoundedToFourDecimals,
      displayedAbsorptionProbability, abs_of_nonpos]
  · rw [hTransmission]
    intro other
    cases other <;>
      norm_num [displayedAbsorptionProbability, abs_of_nonneg, abs_of_nonpos]

/-!
The source calls the displayed `8/9` entry probability an absorption
probability.  Under the separately stated idealization that every transmitted
neutron is absorbed and initiates fission, the same value and answer choice
therefore apply to absorption.  Without `_capture`, only the preceding
transmission theorem is claimed.

Blueprint: `thm:physics:phyx_mini_0600:target`.
-/
theorem neutronAbsorptionProbabilityAtNuclearPotentialDrop
    (setup : NeutronPotentialDropSetup)
    (_scenario : MatchesNeutronNucleusScenario setup)
    (_data : MatchesProblemEnergyReadouts setup)
    (_figure : MatchesSuppliedPotentialDropFigure setup.figure)
    (_physical : HasPhysicalPotentialDropParameters setup)
    (_standardPlanck : UsesStandardReducedPlanckConstant setup)
    (_laws : SatisfiesAbruptPotentialDropLaws setup)
    (_capture : ModelsEntryAsAbsorptionInducingFission setup) :
    absorptionProbability setup = (8 : ℝ) / 9 ∧
      AgreesWhenRoundedToFourDecimals (absorptionProbability setup) .C ∧
      IsNearestAnswerChoice (absorptionProbability setup) .C := by
  rw [_capture.absorptionEqualsTransmittedFlux]
  exact
    neutronEntryTransmissionProbabilityAtNuclearPotentialDrop setup
      _scenario _data _figure _physical _standardPlanck _laws

end PhyXMiniProblems.ProblemPhyXMini0600
