import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Photon absorption with electron--positron pair creation

A photon of wavelength `lambda` travels along the positive horizontal axis and
is absorbed by a stationary target of mass `M`.  The final state consists of
the recoiling target, an electron, and a positron.  The primary image shows the
target recoil along the original photon direction and the two leptons at the
same speed in directions making angles `+phi` and `-phi` with that axis.

Mass, length, speed, energy, and spatial momentum retain their physical
dimensions.  Real numbers below are used only for explicit SI or MeV readouts,
angles in radians, and individual momentum components.

Assumption/target boundary:

* `MatchesPairProductionScenario` records the reaction channel, the initially
  stationary target, unchanged target mass, and the stated equality of the
  electron and positron masses and speeds.
* `MatchesPrimaryPairProductionFigure` records only the labels, panels,
  directions, angle geometry, and component decompositions visible in the
  primary image.
* `SatisfiesRelativisticPairProductionLaws` states the photon
  momentum--wavelength and energy--momentum relations, the massive-particle
  relativistic relations, and total energy and plane-momentum conservation.
* There are no previous-part results and no numerical wavelength, mass, speed,
  or angle readouts in the supplied source.
* The recorded `10.0 MeV` value and answer A occur only in the
  displayed-answer metadata.  Since the source omits the data needed to select
  a number, the theorem concludes the two symbolic incident-energy formulas
  supported by the governing laws.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0613

open Dimension

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical rest mass. -/
abbrev RestMassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A dimensionful two-dimensional momentum in the plane of the figure. -/
abbrev PlaneMomentum : Type := Dimensionful (Momentum 2)

/-- The two coordinate axes determined by the incident-photon direction. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index corresponding to a named diagram axis. -/
def DiagramAxis.toFin : DiagramAxis -> Fin 2
  | .x => 0
  | .y => 1

/-- SI mass readout in kilograms. -/
def restMassInKilograms (mass : RestMassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- SI wavelength readout in metres. -/
def wavelengthInMeters (wavelength : WavelengthQuantity) : ℝ :=
  ((wavelength UnitChoices.SI).val : ℝ)

/-- SI energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Energy readout in megaelectron-volts. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy /
    (1_000_000 * energyInJoules DimEnergy.electronVolt)

/-- SI speed readout in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- A massive particle's speed as the dimensionless ratio `v/c`. -/
def speedRatioToLight (speed : DimSpeed) : ℝ :=
  speedInMetersPerSecond speed / speedOfLightInMetersPerSecond

/-- One plane-momentum component in coherent SI units `kg m / s`. -/
def momentumComponentInSI
    (momentum : PlaneMomentum) (axis : DiagramAxis) : ℝ :=
  (momentum UnitChoices.SI).val axis.toFin

/-- Euclidean magnitude of a plane momentum in coherent SI units. -/
def momentumMagnitudeInSI (momentum : PlaneMomentum) : ℝ :=
  Real.sqrt
    (momentumComponentInSI momentum .x ^ 2 +
      momentumComponentInSI momentum .y ^ 2)

/-- Rest-energy readout `m c^2` in joules. -/
def restEnergyInJoules (mass : RestMassQuantity) : ℝ :=
  restMassInKilograms mass * speedOfLightInMetersPerSecond ^ 2

/-! ## Physical states and primary-figure vocabulary -/

/-- The four massive-particle states before and after the interaction. -/
inductive MassiveStateLabel where
  | targetBefore
  | targetAfter
  | electron
  | positron
  deriving DecidableEq, Fintype, Repr

/-- The reaction channel described in the problem, distinguished from others. -/
inductive ReactionChannel where
  | photonAbsorptionWithPairCreation
  | other
  deriving DecidableEq, Repr

/-- A massive particle's independent relativistic state variables. -/
structure MassiveParticleState where
  restMass : RestMassQuantity
  speed : DimSpeed
  totalEnergy : DimEnergy
  spatialMomentum : PlaneMomentum

/-- The incident photon's independent physical state variables. -/
structure PhotonState where
  wavelength : WavelengthQuantity
  energy : DimEnergy
  spatialMomentum : PlaneMomentum

/-- The two panels printed in the primary image. -/
inductive FigurePanel where
  | beforeInteraction
  | afterInteraction
  deriving DecidableEq, Fintype, Repr

/-- Object labels visible in one or both panels. -/
inductive FigureEntity where
  | photon
  | targetM
  | electron
  | positron
  deriving DecidableEq, Fintype, Repr

/-- Symbolic quantity labels printed beside arrows or angle marks. -/
inductive FigureQuantityLabel where
  | lambda
  | targetSpeedVM
  | leptonSpeedV
  | emissionAnglePhi
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions in the primary image. -/
inductive PlanarDirection where
  | positiveX
  | upperRight
  | lowerRight
  deriving DecidableEq, Repr

/-- Literal panel, label, and arrow information carried by the primary image. -/
structure PairProductionFigure where
  panelTitleShown : FigurePanel -> Bool
  entityShown : FigurePanel -> FigureEntity -> Bool
  quantityLabelShown : FigureQuantityLabel -> Bool
  angleMarkCount : ℕ
  arrowDirection : FigureEntity -> PlanarDirection
  phiRadians : ℝ

/-- The complete pair-production setup, with the answer energy left independent. -/
structure PhotonPairProductionSetup where
  reactionChannel : ReactionChannel
  incidentPhoton : PhotonState
  massiveState : MassiveStateLabel -> MassiveParticleState
  figure : PairProductionFigure

/-! ## Problem statement, figure evidence, and governing physics -/

/-!
The prose scenario.  The equality of the lepton speeds is explicitly supplied
in the question.  No field here fixes the incident photon energy.
-/
structure MatchesPairProductionScenario
    (setup : PhotonPairProductionSetup) : Prop where
  correctReactionChannel :
    setup.reactionChannel = .photonAbsorptionWithPairCreation
  targetMassUnchanged :
    (setup.massiveState .targetAfter).restMass =
      (setup.massiveState .targetBefore).restMass
  electronPositronMassesEqual :
    (setup.massiveState .electron).restMass =
      (setup.massiveState .positron).restMass
  electronPositronSpeedsEqual :
    (setup.massiveState .electron).speed =
      (setup.massiveState .positron).speed
  targetInitiallyStationary :
    speedInMetersPerSecond (setup.massiveState .targetBefore).speed = 0
  targetInitialMomentumIsZero : forall axis : DiagramAxis,
    momentumComponentInSI
      (setup.massiveState .targetBefore).spatialMomentum axis = 0

/-!
Primary-image evidence.  The component equations attach the printed `phi` to
the upper electron and lower positron trajectories and attach the photon and
target recoil arrows to the original positive horizontal direction.
-/
structure MatchesPrimaryPairProductionFigure
    (setup : PhotonPairProductionSetup) : Prop where
  bothPanelTitlesShown : forall panel,
    setup.figure.panelTitleShown panel = true
  photonShownBefore :
    setup.figure.entityShown .beforeInteraction .photon = true
  targetShownBefore :
    setup.figure.entityShown .beforeInteraction .targetM = true
  targetShownAfter :
    setup.figure.entityShown .afterInteraction .targetM = true
  electronShownAfter :
    setup.figure.entityShown .afterInteraction .electron = true
  positronShownAfter :
    setup.figure.entityShown .afterInteraction .positron = true
  everyQuantityLabelShown : forall label,
    setup.figure.quantityLabelShown label = true
  twoPhiAngleMarks : setup.figure.angleMarkCount = 2
  photonPointsAlongPositiveX :
    setup.figure.arrowDirection .photon = .positiveX
  targetRecoilPointsAlongPositiveX :
    setup.figure.arrowDirection .targetM = .positiveX
  electronPointsUpperRight :
    setup.figure.arrowDirection .electron = .upperRight
  positronPointsLowerRight :
    setup.figure.arrowDirection .positron = .lowerRight
  phiPositive : 0 < setup.figure.phiRadians
  phiAcute : setup.figure.phiRadians < Real.pi / 2
  photonHorizontalMomentum :
    momentumComponentInSI setup.incidentPhoton.spatialMomentum .x =
      momentumMagnitudeInSI setup.incidentPhoton.spatialMomentum
  photonVerticalMomentum :
    momentumComponentInSI setup.incidentPhoton.spatialMomentum .y = 0
  targetRecoilHorizontalMomentum :
    momentumComponentInSI
        (setup.massiveState .targetAfter).spatialMomentum .x =
      momentumMagnitudeInSI
        (setup.massiveState .targetAfter).spatialMomentum
  targetRecoilVerticalMomentum :
    momentumComponentInSI
        (setup.massiveState .targetAfter).spatialMomentum .y = 0
  electronHorizontalMomentum :
    momentumComponentInSI
        (setup.massiveState .electron).spatialMomentum .x =
      momentumMagnitudeInSI
          (setup.massiveState .electron).spatialMomentum *
        Real.cos setup.figure.phiRadians
  electronVerticalMomentum :
    momentumComponentInSI
        (setup.massiveState .electron).spatialMomentum .y =
      momentumMagnitudeInSI
          (setup.massiveState .electron).spatialMomentum *
        Real.sin setup.figure.phiRadians
  positronHorizontalMomentum :
    momentumComponentInSI
        (setup.massiveState .positron).spatialMomentum .x =
      momentumMagnitudeInSI
          (setup.massiveState .positron).spatialMomentum *
        Real.cos setup.figure.phiRadians
  positronVerticalMomentum :
    momentumComponentInSI
        (setup.massiveState .positron).spatialMomentum .y =
      -(momentumMagnitudeInSI
          (setup.massiveState .positron).spatialMomentum *
        Real.sin setup.figure.phiRadians)

/-- Positivity and subluminality conditions selecting physical states. -/
structure HasPhysicalPairProductionParameters
    (setup : PhotonPairProductionSetup) : Prop where
  positivePhotonWavelength :
    0 < wavelengthInMeters setup.incidentPhoton.wavelength
  positivePhotonEnergy :
    0 < energyInJoules setup.incidentPhoton.energy
  positiveRestMass : forall particle,
    0 < restMassInKilograms (setup.massiveState particle).restMass
  positiveMassiveEnergy : forall particle,
    0 < energyInJoules (setup.massiveState particle).totalEnergy
  subluminalMassiveSpeed : forall particle,
    speedInMetersPerSecond (setup.massiveState particle).speed <
      speedOfLightInMetersPerSecond
  positiveSpeedOfLight : 0 < speedOfLightInMetersPerSecond
  positiveElectronVolt : 0 < energyInJoules DimEnergy.electronVolt

/-!
Governing laws for the isolated relativistic interaction:

* `|p_gamma| = h / lambda`, with `h = 2 pi hbar`;
* the photon obeys `E_gamma = c |p_gamma|`;
* every massive state obeys `E = gamma(v/c) m c^2`,
  `E^2 = (m c^2)^2 + (p c)^2`, and `p c^2 = E v`;
* total energy and both displayed momentum components are conserved.

The photon laws are deliberately factored through momentum, so the requested
symbolic energy--wavelength formula is a consequence rather than a premise.
Likewise, no premise contains the theorem's combined recoil-plus-pair energy
formula.  These laws contain neither `10 MeV` nor an answer choice.
-/
structure SatisfiesRelativisticPairProductionLaws
    (setup : PhotonPairProductionSetup) : Prop where
  photonMomentumWavelengthRelation :
    momentumMagnitudeInSI setup.incidentPhoton.spatialMomentum =
      (2 * Real.pi * (Constants.ℏ : ℝ)) /
      wavelengthInMeters setup.incidentPhoton.wavelength
  photonEnergyMomentumRelation :
    energyInJoules setup.incidentPhoton.energy =
      speedOfLightInMetersPerSecond *
        momentumMagnitudeInSI setup.incidentPhoton.spatialMomentum
  massiveEnergySpeedRelation : forall particle : MassiveStateLabel,
    energyInJoules (setup.massiveState particle).totalEnergy =
      LorentzGroup.γ
          (speedRatioToLight (setup.massiveState particle).speed) *
        restEnergyInJoules (setup.massiveState particle).restMass
  massiveEnergyMomentumRelation : forall particle : MassiveStateLabel,
    energyInJoules (setup.massiveState particle).totalEnergy ^ 2 =
      restEnergyInJoules (setup.massiveState particle).restMass ^ 2 +
        (speedOfLightInMetersPerSecond *
          momentumMagnitudeInSI
            (setup.massiveState particle).spatialMomentum) ^ 2
  massiveMomentumSpeedRelation : forall particle : MassiveStateLabel,
    momentumMagnitudeInSI
          (setup.massiveState particle).spatialMomentum *
        speedOfLightInMetersPerSecond ^ 2 =
      energyInJoules (setup.massiveState particle).totalEnergy *
        speedInMetersPerSecond (setup.massiveState particle).speed
  totalEnergyConservation :
    energyInJoules setup.incidentPhoton.energy +
        energyInJoules (setup.massiveState .targetBefore).totalEnergy =
      energyInJoules (setup.massiveState .targetAfter).totalEnergy +
        energyInJoules (setup.massiveState .electron).totalEnergy +
        energyInJoules (setup.massiveState .positron).totalEnergy
  planeMomentumConservation : forall axis : DiagramAxis,
    momentumComponentInSI setup.incidentPhoton.spatialMomentum axis +
        momentumComponentInSI
          (setup.massiveState .targetBefore).spatialMomentum axis =
      momentumComponentInSI
          (setup.massiveState .targetAfter).spatialMomentum axis +
        momentumComponentInSI
          (setup.massiveState .electron).spatialMomentum axis +
        momentumComponentInSI
          (setup.massiveState .positron).spatialMomentum axis

/-! ## Conservation consequence, answer metadata, and symbolic target -/

/-!
The direct symbolic answer supplied by energy conservation, before inserting
any missing numerical data.
-/
lemma incidentPhotonEnergy_from_energyConservation
    (setup : PhotonPairProductionSetup)
    (laws : SatisfiesRelativisticPairProductionLaws setup) :
    energyInJoules setup.incidentPhoton.energy =
      energyInJoules (setup.massiveState .targetAfter).totalEnergy +
        energyInJoules (setup.massiveState .electron).totalEnergy +
        energyInJoules (setup.massiveState .positron).totalEnergy -
        energyInJoules (setup.massiveState .targetBefore).totalEnergy := by
  linarith [laws.totalEnergyConservation]

/-- Labels printed beside the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Incident-photon energy in MeV printed beside each answer choice. -/
def displayedIncidentPhotonEnergyMeV : AnswerChoice -> ℝ
  | .A => 10
  | .B => 56 / 5
  | .C => 62 / 5
  | .D => 133 / 10

/-- Dataset metadata records answer choice A. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
The recorded answer table says `10.0 MeV`, answer A, but the supplied chapter
contains no numerical value for `lambda`, `M`, `V_M`, `v`, `phi`, or the
electron mass.  The numeric choice therefore remains metadata rather than an
unsupported physics conclusion.

The first conjunct below derives `E_gamma = h c / lambda` by combining the
separate photon momentum--wavelength and energy--momentum laws.  The second
derives the same energy from total energy conservation, the relativistic
massive-particle energy law, the stationary initial target, and the equal
electron/positron masses and speeds.  Neither complete target formula occurs
in any premise.

Blueprint label: `thm:physics:phyx_mini_0613:target`.
-/
theorem problem_phyx_mini_0613
    (setup : PhotonPairProductionSetup)
    (scenario : MatchesPairProductionScenario setup)
    (_figure : MatchesPrimaryPairProductionFigure setup)
    (physical : HasPhysicalPairProductionParameters setup)
    (laws : SatisfiesRelativisticPairProductionLaws setup) :
    energyInJoules setup.incidentPhoton.energy =
        speedOfLightInMetersPerSecond *
          ((2 * Real.pi * (Constants.ℏ : ℝ)) /
            wavelengthInMeters setup.incidentPhoton.wavelength) ∧
      energyInJoules setup.incidentPhoton.energy =
        (LorentzGroup.γ
              (speedRatioToLight
                (setup.massiveState .targetAfter).speed) - 1) *
            restEnergyInJoules
              (setup.massiveState .targetBefore).restMass +
          2 *
            LorentzGroup.γ
              (speedRatioToLight
                (setup.massiveState .electron).speed) *
            restEnergyInJoules
              (setup.massiveState .electron).restMass := by
  constructor
  · rw [laws.photonEnergyMomentumRelation,
        laws.photonMomentumWavelengthRelation]
  · rw [incidentPhotonEnergy_from_energyConservation setup laws]
    rw [laws.massiveEnergySpeedRelation .targetAfter,
        laws.massiveEnergySpeedRelation .electron,
        laws.massiveEnergySpeedRelation .positron,
        laws.massiveEnergySpeedRelation .targetBefore]
    rw [scenario.targetMassUnchanged]
    rw [← scenario.electronPositronSpeedsEqual,
        ← scenario.electronPositronMassesEqual]
    have hInitialSpeedRatio :
        speedRatioToLight (setup.massiveState .targetBefore).speed = 0 := by
      simp [speedRatioToLight, scenario.targetInitiallyStationary]
    rw [hInitialSpeedRatio, LorentzGroup.γ_zero]
    ring

end PhyXMiniProblems.ProblemPhyXMini0613
