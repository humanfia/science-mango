import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/-!
# Equal-angle Compton scattering

An incident photon of energy `E₀ = 0.880 MeV` strikes a free electron at
rest.  The supplied figure places the outgoing electron above the incident
axis and the scattered photon below it, with both outgoing tracks making the
same angle `θ` with that axis.  The requested quantity is the magnitude of the
outgoing electron's momentum in `kg · m / s`.

The physical quantities below retain their dimensions.  Scalar real numbers
appear only after an explicit SI or MeV readout.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0531

/-- A dimensionful two-dimensional momentum, suitable for the plane of the
scattering diagram.  `Momentum 2` supplies the physical dimension
`M L T⁻¹`; `Dimensionful` makes the vector independent of a unit choice. -/
abbrev PlaneMomentum : Type := Dimensionful (Momentum 2)

/-- The two coordinate directions displayed in the scattering figure. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq

/-- The `Fin 2` coordinate associated with a labelled diagram axis. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .horizontal => 0
  | .vertical => 1

/-- A momentum component read in SI units, hence in `kg · m / s`. -/
def momentumComponentInSI (momentum : PlaneMomentum) (axis : DiagramAxis) : ℝ :=
  (momentum UnitChoices.SI).val axis.toFin

/-- Euclidean magnitude of a plane momentum, read in `kg · m / s`. -/
def momentumMagnitudeInSI (momentum : PlaneMomentum) : ℝ :=
  Real.sqrt
    (momentumComponentInSI momentum .horizontal ^ 2 +
      momentumComponentInSI momentum .vertical ^ 2)

/-- A dimensionful energy read in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- A dimensionful energy read in megaelectronvolts. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy /
    (1_000_000 * energyInJoules DimEnergy.electronVolt)

/-- Physlib's exact speed of light, read in meters per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Labels for the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq

/-- Momentum values printed beside the four choices, in `kg · m / s`. -/
def answerChoiceMomentumInSI : AnswerChoice → ℝ
  | .A => 981 / (10 : ℝ) ^ 25
  | .B => 108 / (10 : ℝ) ^ 24
  | .C => 981 / (10 : ℝ) ^ 24
  | .D => 321 / (10 : ℝ) ^ 24

/-- A choice is correct when its printed momentum is at least as close to the
exact prediction as every other displayed option.  This is the appropriate
relation for the multiple-choice source: its printed D value is a textbook
approximation rather than an exact SI equality. -/
def IsClosestAnswerChoice (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |actual - answerChoiceMomentumInSI choice| ≤
      |actual - answerChoiceMomentumInSI other|

/-- The labels and two equal-angle arcs that are visible in the supplied
scattering diagram. -/
structure EqualAngleComptonFigure where
  incomingPhotonEnergyLabel : DimEnergy
  thetaLabel : ℝ
  electronScatteringAngle : ℝ
  photonScatteringAngle : ℝ

/-- All physical quantities before and after the collision.  Electron total
energy and rest energy are kept separate so that the initial-rest condition
and the outgoing relativistic dispersion law can be stated as laws. -/
structure ComptonScatteringSetup where
  figure : EqualAngleComptonFigure
  incomingPhotonEnergy : DimEnergy
  electronRestEnergy : DimEnergy
  initialElectronTotalEnergy : DimEnergy
  scatteredPhotonEnergy : DimEnergy
  scatteredElectronTotalEnergy : DimEnergy
  incomingPhotonMomentum : PlaneMomentum
  initialElectronMomentum : PlaneMomentum
  scatteredPhotonMomentum : PlaneMomentum
  scatteredElectronMomentum : PlaneMomentum

/-- Literal geometry read from the figure.  The incident photon travels along
the positive horizontal axis, the electron leaves above that axis, and the
scattered photon leaves below it. -/
structure FigureReadout (setup : ComptonScatteringSetup) : Prop where
  energyLabelMatchesIncoming :
    setup.figure.incomingPhotonEnergyLabel = setup.incomingPhotonEnergy
  electronAngleHasThetaLabel :
    setup.figure.electronScatteringAngle = setup.figure.thetaLabel
  photonAngleHasThetaLabel :
    setup.figure.photonScatteringAngle = setup.figure.thetaLabel
  thetaPositive : 0 < setup.figure.thetaLabel
  thetaAcute : setup.figure.thetaLabel < Real.pi / 2
  incomingPhotonHorizontal :
    momentumComponentInSI setup.incomingPhotonMomentum .horizontal =
      momentumMagnitudeInSI setup.incomingPhotonMomentum
  incomingPhotonHasNoVerticalComponent :
    momentumComponentInSI setup.incomingPhotonMomentum .vertical = 0
  scatteredElectronHorizontalComponent :
    momentumComponentInSI setup.scatteredElectronMomentum .horizontal =
      momentumMagnitudeInSI setup.scatteredElectronMomentum *
        Real.cos setup.figure.electronScatteringAngle
  scatteredElectronVerticalComponent :
    momentumComponentInSI setup.scatteredElectronMomentum .vertical =
      momentumMagnitudeInSI setup.scatteredElectronMomentum *
        Real.sin setup.figure.electronScatteringAngle
  scatteredPhotonHorizontalComponent :
    momentumComponentInSI setup.scatteredPhotonMomentum .horizontal =
      momentumMagnitudeInSI setup.scatteredPhotonMomentum *
        Real.cos setup.figure.photonScatteringAngle
  scatteredPhotonVerticalComponent :
    momentumComponentInSI setup.scatteredPhotonMomentum .vertical =
      -(momentumMagnitudeInSI setup.scatteredPhotonMomentum *
        Real.sin setup.figure.photonScatteringAngle)

/-- Numerical readouts and the calibrated electron rest-energy constant used
for this instance of the problem.  The source supplies `0.880 MeV`; the
standard electron rest energy is represented at the precision `0.511 MeV`
used by the answer choices. -/
structure ComptonProblemData (setup : ComptonScatteringSetup) : Prop where
  incomingPhotonEnergyMeV :
    energyInMegaElectronVolts setup.incomingPhotonEnergy = 22 / 25
  electronRestEnergyMeV :
    energyInMegaElectronVolts setup.electronRestEnergy = 511 / 1000

/-- Governing laws for the isolated photon-electron collision: the initial
electron is at rest, energy and both momentum components are conserved,
photons obey `E = pc`, and the outgoing electron obeys the relativistic
energy-momentum relation. -/
structure SatisfiesComptonScatteringLaws
    (setup : ComptonScatteringSetup) : Prop where
  initialElectronAtRest : ∀ axis : DiagramAxis,
    momentumComponentInSI setup.initialElectronMomentum axis = 0
  initialElectronEnergyIsRestEnergy :
    setup.initialElectronTotalEnergy = setup.electronRestEnergy
  momentumConservation : ∀ axis : DiagramAxis,
    momentumComponentInSI setup.incomingPhotonMomentum axis +
        momentumComponentInSI setup.initialElectronMomentum axis =
      momentumComponentInSI setup.scatteredPhotonMomentum axis +
        momentumComponentInSI setup.scatteredElectronMomentum axis
  energyConservation :
    energyInJoules setup.incomingPhotonEnergy +
        energyInJoules setup.initialElectronTotalEnergy =
      energyInJoules setup.scatteredPhotonEnergy +
        energyInJoules setup.scatteredElectronTotalEnergy
  incomingPhotonEnergyMomentum :
    energyInJoules setup.incomingPhotonEnergy =
      speedOfLightInMetersPerSecond *
        momentumMagnitudeInSI setup.incomingPhotonMomentum
  scatteredPhotonEnergyMomentum :
    energyInJoules setup.scatteredPhotonEnergy =
      speedOfLightInMetersPerSecond *
        momentumMagnitudeInSI setup.scatteredPhotonMomentum
  scatteredElectronEnergyMomentum :
    energyInJoules setup.scatteredElectronTotalEnergy ^ 2 =
      energyInJoules setup.electronRestEnergy ^ 2 +
        (speedOfLightInMetersPerSecond *
          momentumMagnitudeInSI setup.scatteredElectronMomentum) ^ 2
  incomingEnergyPositive : 0 < energyInJoules setup.incomingPhotonEnergy
  electronRestEnergyPositive : 0 < energyInJoules setup.electronRestEnergy
  scatteredPhotonMomentumNonnegative :
    0 ≤ momentumMagnitudeInSI setup.scatteredPhotonMomentum
  scatteredElectronMomentumNonnegative :
    0 ≤ momentumMagnitudeInSI setup.scatteredElectronMomentum
  scatteredElectronTotalEnergyPositive :
    0 < energyInJoules setup.scatteredElectronTotalEnergy

/-- **Blueprint label:** `thm:physics:phyx_mini_0531:target`.

The laws first determine the exact SI momentum through the equal-angle
Compton-scattering relation.  With the figure/data readouts, answer choice D,
printed as `3.21 × 10⁻²² kg · m / s`, is the closest displayed value. -/
theorem scatteredElectronMomentum_is_choice_D
    (setup : ComptonScatteringSetup)
    (figureReadout : FigureReadout setup)
    (data : ComptonProblemData setup)
    (laws : SatisfiesComptonScatteringLaws setup) :
    momentumMagnitudeInSI setup.scatteredElectronMomentum =
        (energyInJoules setup.incomingPhotonEnergy *
          (energyInJoules setup.incomingPhotonEnergy +
            2 * energyInJoules setup.electronRestEnergy)) /
          (2 *
            (energyInJoules setup.incomingPhotonEnergy +
              energyInJoules setup.electronRestEnergy) *
            speedOfLightInMetersPerSecond) ∧
      IsClosestAnswerChoice
        (momentumMagnitudeInSI setup.scatteredElectronMomentum)
        .D := by
  have htheta_lt_pi : setup.figure.thetaLabel < Real.pi := by
    nlinarith [figureReadout.thetaAcute, Real.pi_pos]
  have hsin_pos : 0 < Real.sin setup.figure.thetaLabel :=
    Real.sin_pos_of_pos_of_lt_pi figureReadout.thetaPositive htheta_lt_pi
  have hvertical := laws.momentumConservation .vertical
  rw [laws.initialElectronAtRest .vertical,
    figureReadout.incomingPhotonHasNoVerticalComponent,
    figureReadout.scatteredPhotonVerticalComponent,
    figureReadout.scatteredElectronVerticalComponent,
    figureReadout.photonAngleHasThetaLabel,
    figureReadout.electronAngleHasThetaLabel] at hvertical
  have hmomentum_product :
      (momentumMagnitudeInSI setup.scatteredElectronMomentum -
          momentumMagnitudeInSI setup.scatteredPhotonMomentum) *
        Real.sin setup.figure.thetaLabel = 0 := by
    nlinarith [hvertical]
  have helectron_eq_photon :
      momentumMagnitudeInSI setup.scatteredElectronMomentum =
        momentumMagnitudeInSI setup.scatteredPhotonMomentum := by
    apply sub_eq_zero.mp
    exact Or.resolve_right (mul_eq_zero.mp hmomentum_product) (ne_of_gt hsin_pos)
  have henergy := laws.energyConservation
  rw [laws.initialElectronEnergyIsRestEnergy,
    laws.scatteredPhotonEnergyMomentum, ← helectron_eq_photon] at henergy
  have hmomentum_polynomial :
      2 *
          (energyInJoules setup.incomingPhotonEnergy +
            energyInJoules setup.electronRestEnergy) *
          speedOfLightInMetersPerSecond *
          momentumMagnitudeInSI setup.scatteredElectronMomentum =
        energyInJoules setup.incomingPhotonEnergy *
          (energyInJoules setup.incomingPhotonEnergy +
            2 * energyInJoules setup.electronRestEnergy) := by
    nlinarith [laws.scatteredElectronEnergyMomentum,
      laws.incomingEnergyPositive, laws.electronRestEnergyPositive,
      laws.scatteredElectronTotalEnergyPositive]
  have hc_value : speedOfLightInMetersPerSecond = 299792458 := by
    norm_num [speedOfLightInMetersPerSecond, DimSpeed.speedOfLight,
      CarriesDimension.toDimensionful_apply_apply]
  have hc_pos : 0 < speedOfLightInMetersPerSecond := by
    rw [hc_value]
    norm_num
  have hdenominator_ne :
      2 *
          (energyInJoules setup.incomingPhotonEnergy +
            energyInJoules setup.electronRestEnergy) *
          speedOfLightInMetersPerSecond ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (ne_of_gt (add_pos laws.incomingEnergyPositive
          laws.electronRestEnergyPositive)))
      (ne_of_gt hc_pos)
  have hexact :
      momentumMagnitudeInSI setup.scatteredElectronMomentum =
        (energyInJoules setup.incomingPhotonEnergy *
          (energyInJoules setup.incomingPhotonEnergy +
            2 * energyInJoules setup.electronRestEnergy)) /
          (2 *
            (energyInJoules setup.incomingPhotonEnergy +
              energyInJoules setup.electronRestEnergy) *
            speedOfLightInMetersPerSecond) := by
    apply (eq_div_iff hdenominator_ne).2
    nlinarith [hmomentum_polynomial]
  have hincoming_value :
      energyInJoules setup.incomingPhotonEnergy =
        (22 / 25 : ℝ) *
          (1_000_000 * ((1602176634 : ℝ) / 10 ^ 28)) := by
    have h := data.incomingPhotonEnergyMeV
    norm_num [energyInMegaElectronVolts, energyInJoules,
      DimEnergy.electronVolt, CarriesDimension.toDimensionful_apply_apply] at h ⊢
    linarith
  have hrest_value :
      energyInJoules setup.electronRestEnergy =
        (511 / 1000 : ℝ) *
          (1_000_000 * ((1602176634 : ℝ) / 10 ^ 28)) := by
    have h := data.electronRestEnergyMeV
    norm_num [energyInMegaElectronVolts, energyInJoules,
      DimEnergy.electronVolt, CarriesDimension.toDimensionful_apply_apply] at h ⊢
    linarith
  refine ⟨hexact, ?_⟩
  unfold IsClosestAnswerChoice
  intro other
  rw [hexact, hincoming_value, hrest_value, hc_value]
  cases other <;>
    norm_num [answerChoiceMomentumInSI, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0531
