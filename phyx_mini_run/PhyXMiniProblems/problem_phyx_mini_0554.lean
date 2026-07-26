import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# K-minus--proton reaction producing a lambda and neutral pion

A charged kaon with kinetic energy `152.4 MeV` strikes a proton at rest and
produces a lambda particle and a neutral pion.  The pion's kinetic energy is
`254.8 MeV`; the requested quantity is the lambda's kinetic energy.

The supplied primary image has two panels.  In panel (a), the kaon travels
along the positive `x`-axis toward the proton.  In panel (b), the pion leaves
into the upper half-plane at angle `theta` from the positive `x`-axis and the
lambda leaves into the lower half-plane at angle `phi` from that axis.  This
primary-image reading takes precedence over the auxiliary caption's ambiguous
angle description.

Rest masses, kinetic energies, and plane momenta retain physical dimensions.
Real numbers occur only as scalar readouts in kilograms, joules, MeV/c^2,
MeV, radians, or SI momentum units.

Assumption/target boundary:

* `MatchesReactionProblemData` contains the four supplied rest-mass readouts,
  the two supplied kinetic-energy readouts, and the stationary-proton datum.
* `MatchesPrimaryReactionFigure` contains only panel, label, direction, and
  angle geometry read from the primary image.
* `SatisfiesRelativisticReactionLaws` states general relativistic dispersion
  together with energy and plane-momentum conservation.
* There are no previous-part results.
* The lambda value `78.9 MeV` and answer D occur only in the conclusions and
  in the table of displayed answers, never in a premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0554

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical rest mass with mass dimension `M`. -/
abbrev RestMassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A dimensionful two-dimensional momentum in the plane of the diagram. -/
abbrev PlaneMomentum : Type := Dimensionful (Momentum 2)

/-- The two coordinate axes printed in both panels of the primary image. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- The `Fin 2` coordinate corresponding to a diagram-axis label. -/
def DiagramAxis.toFin : DiagramAxis -> Fin 2
  | .x => 0
  | .y => 1

/-- Kilogram readout of a physical rest mass. -/
def restMassInKilograms (mass : RestMassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- MeV readout of a physical energy. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy /
    (1_000_000 * energyInJoules DimEnergy.electronVolt)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Rest-energy equivalent `m c^2`, expressed in joules. -/
def restEnergyEquivalentInJoules (mass : RestMassQuantity) : ℝ :=
  restMassInKilograms mass * speedOfLightInMetersPerSecond ^ 2

/--
Read a rest mass in the high-energy unit MeV/c^2.  Numerically this is the
mass's rest-energy equivalent divided by one MeV.
-/
def restMassInMegaElectronVoltsPerC2 (mass : RestMassQuantity) : ℝ :=
  restEnergyEquivalentInJoules mass /
    (1_000_000 * energyInJoules DimEnergy.electronVolt)

/-- One momentum component read in coherent SI units `kg m / s`. -/
def momentumComponentInSI
    (momentum : PlaneMomentum) (axis : DiagramAxis) : ℝ :=
  (momentum UnitChoices.SI).val axis.toFin

/-- Euclidean magnitude of a plane momentum in `kg m / s`. -/
def momentumMagnitudeInSI (momentum : PlaneMomentum) : ℝ :=
  Real.sqrt
    (momentumComponentInSI momentum .x ^ 2 +
      momentumComponentInSI momentum .y ^ 2)

/-! ## Reaction particles and primary-figure vocabulary -/

/-- The four particle species named in the reaction channel. -/
inductive ParticleLabel where
  | kaonMinus
  | proton
  | lambdaZero
  | pionZero
  deriving DecidableEq, Fintype, Repr

/-- Whether a particle belongs to the incoming or outgoing side. -/
inductive ReactionSide where
  | incoming
  | outgoing
  deriving DecidableEq, Repr

/-- The reaction side fixed by `K^- + p -> Lambda^0 + pi^0`. -/
def particleSide : ParticleLabel -> ReactionSide
  | .kaonMinus => .incoming
  | .proton => .incoming
  | .lambdaZero => .outgoing
  | .pionZero => .outgoing

/-- The before- and after-interaction panels labelled (a) and (b). -/
inductive FigurePanel where
  | beforeInteraction
  | afterInteraction
  deriving DecidableEq, Fintype, Repr

/-- Qualitative momentum-arrow directions visible in the primary image. -/
inductive PlanarDirection where
  | positiveX
  | upperRight
  | lowerRight
  deriving DecidableEq, Repr

/--
Qualitative labels and geometry transcribed from the primary raster.  The two
angles are uncalibrated real radian readouts because the image names but does
not numerically measure them.
-/
structure KaonProtonReactionFigure where
  panelShown : FigurePanel -> Bool
  axisShown : FigurePanel -> DiagramAxis -> Bool
  particleShown : FigurePanel -> ParticleLabel -> Bool
  kaonDrawnLeftOfProton : Bool
  protonAtAxesIntersection : Bool
  kaonArrowDirection : PlanarDirection
  pionArrowDirection : PlanarDirection
  lambdaArrowDirection : PlanarDirection
  thetaRadians : ℝ
  phiRadians : ℝ

/-!
The independent physical state of one massive particle.  In particular, the
lambda kinetic energy is an unconstrained dimensionful field here rather than
being defined from the recorded answer.
-/
structure ParticleState where
  restMass : RestMassQuantity
  kineticEnergy : DimEnergy
  spatialMomentum : PlaneMomentum

/-- All four particle states and the supplied two-panel figure. -/
structure KaonProtonReactionSetup where
  state : ParticleLabel -> ParticleState
  figure : KaonProtonReactionFigure

/-- Total relativistic energy `m c^2 + K` of a particle, in joules. -/
def totalRelativisticEnergyInJoules (state : ParticleState) : ℝ :=
  restEnergyEquivalentInJoules state.restMass +
    energyInJoules state.kineticEnergy

/-! ## Problem data, figure readouts, and governing laws -/

/-!
Numerical quantities stated in the prose.  The lambda kinetic energy is
deliberately absent.  The proton-at-rest condition fixes both its kinetic
energy and its two spatial-momentum components to zero.
-/
structure MatchesReactionProblemData
    (setup : KaonProtonReactionSetup) : Prop where
  kaonRestMassMeVPerC2 :
    restMassInMegaElectronVoltsPerC2
        (setup.state .kaonMinus).restMass = 4937 / 10
  protonRestMassMeVPerC2 :
    restMassInMegaElectronVoltsPerC2
        (setup.state .proton).restMass = 9383 / 10
  lambdaRestMassMeVPerC2 :
    restMassInMegaElectronVoltsPerC2
        (setup.state .lambdaZero).restMass = 11157 / 10
  pionRestMassMeVPerC2 :
    restMassInMegaElectronVoltsPerC2
        (setup.state .pionZero).restMass = 135
  incidentKaonKineticEnergyMeV :
    energyInMegaElectronVolts
        (setup.state .kaonMinus).kineticEnergy = 762 / 5
  outgoingPionKineticEnergyMeV :
    energyInMegaElectronVolts
        (setup.state .pionZero).kineticEnergy = 1274 / 5
  protonKineticEnergyIsZero :
    energyInJoules (setup.state .proton).kineticEnergy = 0
  protonSpatialMomentumIsZero : forall axis : DiagramAxis,
    momentumComponentInSI (setup.state .proton).spatialMomentum axis = 0

/-!
Primary-image evidence.  The outgoing component formulas express the two
arrow directions at the named acute angles.  No angle value and no lambda
kinetic-energy value is inferred from the raster.
-/
structure MatchesPrimaryReactionFigure
    (setup : KaonProtonReactionSetup) : Prop where
  bothPanelsShown : forall panel, setup.figure.panelShown panel = true
  bothAxesShown : forall panel axis,
    setup.figure.axisShown panel axis = true
  kaonShownBefore :
    setup.figure.particleShown .beforeInteraction .kaonMinus = true
  protonShownBefore :
    setup.figure.particleShown .beforeInteraction .proton = true
  pionShownAfter :
    setup.figure.particleShown .afterInteraction .pionZero = true
  lambdaShownAfter :
    setup.figure.particleShown .afterInteraction .lambdaZero = true
  kaonStartsLeftOfProton : setup.figure.kaonDrawnLeftOfProton = true
  protonDrawnAtOrigin : setup.figure.protonAtAxesIntersection = true
  kaonPointsAlongPositiveX :
    setup.figure.kaonArrowDirection = .positiveX
  pionPointsUpperRight : setup.figure.pionArrowDirection = .upperRight
  lambdaPointsLowerRight : setup.figure.lambdaArrowDirection = .lowerRight
  thetaPositive : 0 < setup.figure.thetaRadians
  thetaAcute : setup.figure.thetaRadians < Real.pi / 2
  phiPositive : 0 < setup.figure.phiRadians
  phiAcute : setup.figure.phiRadians < Real.pi / 2
  kaonHorizontalComponent :
    momentumComponentInSI (setup.state .kaonMinus).spatialMomentum .x =
      momentumMagnitudeInSI (setup.state .kaonMinus).spatialMomentum
  kaonVerticalComponent :
    momentumComponentInSI (setup.state .kaonMinus).spatialMomentum .y = 0
  pionHorizontalComponent :
    momentumComponentInSI (setup.state .pionZero).spatialMomentum .x =
      momentumMagnitudeInSI (setup.state .pionZero).spatialMomentum *
        Real.cos setup.figure.thetaRadians
  pionVerticalComponent :
    momentumComponentInSI (setup.state .pionZero).spatialMomentum .y =
      momentumMagnitudeInSI (setup.state .pionZero).spatialMomentum *
        Real.sin setup.figure.thetaRadians
  lambdaHorizontalComponent :
    momentumComponentInSI (setup.state .lambdaZero).spatialMomentum .x =
      momentumMagnitudeInSI (setup.state .lambdaZero).spatialMomentum *
        Real.cos setup.figure.phiRadians
  lambdaVerticalComponent :
    momentumComponentInSI (setup.state .lambdaZero).spatialMomentum .y =
      -(momentumMagnitudeInSI (setup.state .lambdaZero).spatialMomentum *
        Real.sin setup.figure.phiRadians)

/-- Positivity conditions selecting physically meaningful particle states. -/
structure HasPhysicalReactionParameters
    (setup : KaonProtonReactionSetup) : Prop where
  restMassPositive : forall particle,
    0 < restMassInKilograms (setup.state particle).restMass
  kineticEnergyNonnegative : forall particle,
    0 <= energyInJoules (setup.state particle).kineticEnergy
  momentumMagnitudeNonnegative : forall particle,
    0 <= momentumMagnitudeInSI (setup.state particle).spatialMomentum

/-!
Governing laws for the isolated two-body reaction:

* each massive particle obeys `E^2 = (m c^2)^2 + (p c)^2`, with
  `E = m c^2 + K`;
* total relativistic energy is conserved; and
* both displayed spatial-momentum components are conserved.

These laws relate independent state fields and contain no numerical lambda
kinetic energy or displayed answer choice.
-/
structure SatisfiesRelativisticReactionLaws
    (setup : KaonProtonReactionSetup) : Prop where
  relativisticEnergyMomentum : forall particle : ParticleLabel,
    totalRelativisticEnergyInJoules (setup.state particle) ^ 2 =
      restEnergyEquivalentInJoules
          (setup.state particle).restMass ^ 2 +
        (speedOfLightInMetersPerSecond *
          momentumMagnitudeInSI
            (setup.state particle).spatialMomentum) ^ 2
  totalEnergyConservation :
    totalRelativisticEnergyInJoules (setup.state .kaonMinus) +
        totalRelativisticEnergyInJoules (setup.state .proton) =
      totalRelativisticEnergyInJoules (setup.state .lambdaZero) +
        totalRelativisticEnergyInJoules (setup.state .pionZero)
  planeMomentumConservation : forall axis : DiagramAxis,
    momentumComponentInSI
          (setup.state .kaonMinus).spatialMomentum axis +
        momentumComponentInSI
          (setup.state .proton).spatialMomentum axis =
      momentumComponentInSI
          (setup.state .lambdaZero).spatialMomentum axis +
        momentumComponentInSI
          (setup.state .pionZero).spatialMomentum axis

/-! ## Displayed answers and formalization target -/

/-- Labels attached to the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kinetic-energy readout in MeV printed beside each answer choice. -/
def displayedLambdaKineticEnergyMeV : AnswerChoice -> ℝ
  | .A => 328 / 5
  | .B => 452 / 5
  | .C => 331 / 10
  | .D => 789 / 10

/-- Dataset metadata records answer choice D. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Energy conservation gives

`K_Lambda = (m_K + m_p - m_Lambda - m_pi)c^2 + K_K - K_pi`

and the supplied MeV and MeV/c^2 readouts evaluate to `78.9 MeV`, answer D.
The first conjunct states the requested physical value directly; the second
connects that derived value to the recorded multiple-choice label.

Blueprint label: `thm:physics:phyx_mini_0554:target`.
-/
theorem problem_phyx_mini_0554
    (setup : KaonProtonReactionSetup)
    (_data : MatchesReactionProblemData setup)
    (_figure : MatchesPrimaryReactionFigure setup)
    (_physical : HasPhysicalReactionParameters setup)
    (_laws : SatisfiesRelativisticReactionLaws setup) :
    energyInMegaElectronVolts
          (setup.state .lambdaZero).kineticEnergy = 789 / 10 ∧
      energyInMegaElectronVolts
          (setup.state .lambdaZero).kineticEnergy =
        displayedLambdaKineticEnergyMeV recordedAnswerChoice := by
  have hscale :
      1_000_000 * energyInJoules DimEnergy.electronVolt ≠ 0 := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hKaonRestRatio :
      restEnergyEquivalentInJoules (setup.state .kaonMinus).restMass /
          (1_000_000 * energyInJoules DimEnergy.electronVolt) = 4937 / 10 := by
    simpa [restMassInMegaElectronVoltsPerC2] using
      _data.kaonRestMassMeVPerC2
  have hProtonRestRatio :
      restEnergyEquivalentInJoules (setup.state .proton).restMass /
          (1_000_000 * energyInJoules DimEnergy.electronVolt) = 9383 / 10 := by
    simpa [restMassInMegaElectronVoltsPerC2] using
      _data.protonRestMassMeVPerC2
  have hLambdaRestRatio :
      restEnergyEquivalentInJoules (setup.state .lambdaZero).restMass /
          (1_000_000 * energyInJoules DimEnergy.electronVolt) = 11157 / 10 := by
    simpa [restMassInMegaElectronVoltsPerC2] using
      _data.lambdaRestMassMeVPerC2
  have hPionRestRatio :
      restEnergyEquivalentInJoules (setup.state .pionZero).restMass /
          (1_000_000 * energyInJoules DimEnergy.electronVolt) = 135 := by
    simpa [restMassInMegaElectronVoltsPerC2] using
      _data.pionRestMassMeVPerC2
  have hKaonKineticRatio :
      energyInJoules (setup.state .kaonMinus).kineticEnergy /
          (1_000_000 * energyInJoules DimEnergy.electronVolt) = 762 / 5 := by
    simpa [energyInMegaElectronVolts] using
      _data.incidentKaonKineticEnergyMeV
  have hPionKineticRatio :
      energyInJoules (setup.state .pionZero).kineticEnergy /
          (1_000_000 * energyInJoules DimEnergy.electronVolt) = 1274 / 5 := by
    simpa [energyInMegaElectronVolts] using
      _data.outgoingPionKineticEnergyMeV
  have hKaonRest := (div_eq_iff hscale).mp hKaonRestRatio
  have hProtonRest := (div_eq_iff hscale).mp hProtonRestRatio
  have hLambdaRest := (div_eq_iff hscale).mp hLambdaRestRatio
  have hPionRest := (div_eq_iff hscale).mp hPionRestRatio
  have hKaonKinetic := (div_eq_iff hscale).mp hKaonKineticRatio
  have hPionKinetic := (div_eq_iff hscale).mp hPionKineticRatio
  have henergy := _laws.totalEnergyConservation
  unfold totalRelativisticEnergyInJoules at henergy
  have hLambdaKinetic :
      energyInJoules (setup.state .lambdaZero).kineticEnergy =
        (789 / 10) *
          (1_000_000 * energyInJoules DimEnergy.electronVolt) := by
    nlinarith [_data.protonKineticEnergyIsZero]
  have hLambdaMeV :
      energyInMegaElectronVolts
          (setup.state .lambdaZero).kineticEnergy = 789 / 10 := by
    rw [energyInMegaElectronVolts]
    exact (div_eq_iff hscale).mpr hLambdaKinetic
  constructor
  · exact hLambdaMeV
  · simpa [displayedLambdaKineticEnergyMeV, recordedAnswerChoice] using
      hLambdaMeV

end PhyXMiniProblems.ProblemPhyXMini0554
