import Mathlib
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0549

open Dimension

/-!
# Planck's constant from a stopping-potential graph

The supplied figure plots the magnitude of the photoelectric stopping
potential against incident-light frequency. Its horizontal coordinate is
measured in units of `10^14 Hz`, and its vertical coordinate is measured in
volts. The straight line passes through `A = (5, 0)` and `B = (10, 2)`.

Physical frequency, potential, charge, energy, and action are represented by
Physlib dimensionful quantities. Real numbers occur only at explicit SI
readout boundaries, as dimensionless graph coordinates, and as printed answer
values. In particular, the experimental Planck constant is an independent
field and is not defined from answer D.

Assumption/target split:

* governing laws: `K_max = e |U_a|` and `h ν = φ + K_max` at A and B;
* previous-part results: none;
* figure/data readouts: axis roles and units, O/A/B coordinates, `10^14 Hz`
  horizontal scale, volt vertical scale, dashed guides, angle `θ`, and the
  exact Physlib elementary charge;
* current conclusions: the Planck-constant slope formula and the fact that D
  is the unique displayed value matching the inferred constant after rounding.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Electric potential has the dimension energy divided by charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Action, the dimensional role of Planck's constant, is energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative magnitude of electric potential. -/
abbrev StoppingPotentialMagnitude : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative physical quantity with the dimension of action. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Coherent-SI scalar component of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Frequency readout in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Stopping-potential magnitude readout in volts. -/
def stoppingPotentialInVolts
    (potential : StoppingPotentialMagnitude) : ℝ :=
  nonnegativeSIReadout potential

/-- Charge-magnitude readout in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Planck-constant readout in joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  nonnegativeSIReadout constant

/-- Energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Physlib's elementary-charge unit expressed as a scalar number of coulombs.
The experiment itself still stores charge as a dimensionful quantity.
-/
def physlibElementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Primary-figure vocabulary -/

/-- Labels printed at the three relevant landmarks in the supplied graph. -/
inductive FigurePoint where
  | O
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The two measured points on the plotted photoelectric line. -/
inductive MeasuredPoint where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The graph point carrying the same printed label as a measured point. -/
def MeasuredPoint.toFigurePoint : MeasuredPoint → FigurePoint
  | .A => .A
  | .B => .B

/-- The two coordinate axes in the figure. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity represented by an axis. -/
inductive AxisQuantity where
  | incidentLightFrequency
  | stoppingPotentialMagnitude
  deriving DecidableEq, Repr

/-- Unit name printed as part of an axis label. -/
inductive AxisUnit where
  | hertz
  | volt
  deriving DecidableEq, Repr

/-!
Presentation data for the raster. Coordinates are dimensionless printed
numbers; `horizontalScaleInHertz` and `verticalScaleInVolts` give the physical
amount represented by one coordinate unit. The angle field records the
figure's `θ` label at A between the horizontal axis and the rising AB line.
-/
structure StoppingPotentialFrequencyFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisUnit : FigureAxis → AxisUnit
  horizontalScaleInHertz : ℝ
  verticalScaleInVolts : ℝ
  horizontalCoordinateAt : FigurePoint → ℝ
  verticalCoordinateAt : FigurePoint → ℝ
  plottedLineIsStraight : Bool
  plottedLineEndpoints : FigurePoint × FigurePoint
  horizontalDashedGuideThrough : Option FigurePoint
  verticalDashedGuideThrough : Option FigurePoint
  inclinationAngleVertex : FigurePoint
  inclinationAngleAgainstAxis : FigureAxis
  inclinationAngleRadians : ℝ

/-!
Independent physical quantities in the experiment. The work function and
maximum kinetic energies use Physlib's dimensionful energy type.
-/
structure PhotoelectricExperiment where
  incidentFrequencyAt : MeasuredPoint → FrequencyQuantity
  stoppingPotentialAt : MeasuredPoint → StoppingPotentialMagnitude
  maximumPhotoelectronKineticEnergyAt : MeasuredPoint → DimEnergy
  metalWorkFunction : DimEnergy
  electronChargeMagnitude : ChargeMagnitudeQuantity
  experimentalPlanckConstant : PlanckConstantQuantity
  figure : StoppingPotentialFrequencyFigure

/-! ## Figure evidence, calibrations, and governing laws -/

/-- Axis labels, plotted line, dashed guides, and the displayed angle role. -/
structure HasSuppliedFigurePresentation
    (setup : PhotoelectricExperiment) : Prop where
  horizontalQuantity :
    setup.figure.axisQuantity .horizontal = .incidentLightFrequency
  verticalQuantity :
    setup.figure.axisQuantity .vertical = .stoppingPotentialMagnitude
  horizontalUnit : setup.figure.axisUnit .horizontal = .hertz
  verticalUnit : setup.figure.axisUnit .vertical = .volt
  lineIsStraight : setup.figure.plottedLineIsStraight = true
  lineEndpoints : setup.figure.plottedLineEndpoints = (.A, .B)
  horizontalDashedGuide :
    setup.figure.horizontalDashedGuideThrough = some .B
  verticalDashedGuide :
    setup.figure.verticalDashedGuideThrough = some .B
  angleVertex : setup.figure.inclinationAngleVertex = .A
  angleAgainstHorizontalAxis :
    setup.figure.inclinationAngleAgainstAxis = .horizontal
  angleIsAcute :
    0 < setup.figure.inclinationAngleRadians ∧
      setup.figure.inclinationAngleRadians < Real.pi / 2

/-!
Literal coordinate and scale readouts from image 549. These are figure data,
not a conclusion about Planck's constant.
-/
structure HasSuppliedFigureReadouts
    (setup : PhotoelectricExperiment) : Prop where
  horizontalScale :
    setup.figure.horizontalScaleInHertz = (10 : ℝ) ^ 14
  verticalScale : setup.figure.verticalScaleInVolts = 1
  originHorizontal : setup.figure.horizontalCoordinateAt .O = 0
  originVertical : setup.figure.verticalCoordinateAt .O = 0
  pointAHorizontal : setup.figure.horizontalCoordinateAt .A = 5
  pointAVertical : setup.figure.verticalCoordinateAt .A = 0
  pointBHorizontal : setup.figure.horizontalCoordinateAt .B = 10
  pointBVertical : setup.figure.verticalCoordinateAt .B = 2

/-!
Calibration from raw graph coordinates to the physical measurements at A and
B. It states how the axes are read and does not prescribe the inferred value
of Planck's constant.
-/
structure UsesSuppliedAxisCalibration
    (setup : PhotoelectricExperiment) : Prop where
  frequencyCalibration : ∀ point,
    frequencyInHertz (setup.incidentFrequencyAt point) =
      setup.figure.horizontalCoordinateAt point.toFigurePoint *
        setup.figure.horizontalScaleInHertz
  potentialCalibration : ∀ point,
    stoppingPotentialInVolts (setup.stoppingPotentialAt point) =
      setup.figure.verticalCoordinateAt point.toFigurePoint *
        setup.figure.verticalScaleInVolts

/-- Physical sign conditions for the photoelectric experiment. -/
structure HasPhysicalPhotoelectricParameters
    (setup : PhotoelectricExperiment) : Prop where
  electronChargePositive :
    0 < chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  planckConstantPositive :
    0 < planckConstantInJouleSeconds setup.experimentalPlanckConstant
  workFunctionNonnegative : 0 ≤ energyInJoules setup.metalWorkFunction
  frequenciesPositive : ∀ point,
    0 < frequencyInHertz (setup.incidentFrequencyAt point)
  stoppingPotentialsNonnegative : ∀ point,
    0 ≤ stoppingPotentialInVolts (setup.stoppingPotentialAt point)
  maximumKineticEnergiesNonnegative : ∀ point,
    0 ≤ energyInJoules
      (setup.maximumPhotoelectronKineticEnergyAt point)

/-- The known electron charge is calibrated to Physlib's elementary charge. -/
structure UsesPhyslibElementaryCharge
    (setup : PhotoelectricExperiment) : Prop where
  chargeCalibration :
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
      physlibElementaryChargeInCoulombs

/-!
The two governing photoelectric-effect relations at each measured point:

* stopping the fastest emitted electrons requires `K_max = e |U_a|`;
* Einstein's energy balance is `h ν = φ + K_max`.

Neither law mentions the requested numerical answer.
-/
structure SatisfiesPhotoelectricEffectLaws
    (setup : PhotoelectricExperiment) : Prop where
  stoppingPotentialRelation : ∀ point,
    energyInJoules
        (setup.maximumPhotoelectronKineticEnergyAt point) =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        stoppingPotentialInVolts (setup.stoppingPotentialAt point)
  einsteinEnergyBalance : ∀ point,
    planckConstantInJouleSeconds setup.experimentalPlanckConstant *
        frequencyInHertz (setup.incidentFrequencyAt point) =
      energyInJoules setup.metalWorkFunction +
        energyInJoules
          (setup.maximumPhotoelectronKineticEnergyAt point)

/-! ## Inferred value and printed choices -/

/-!
Subtracting the photoelectric equations at B and A cancels the material work
function. The graph rise is `2 V` and its frequency run is
`5 × 10^14 Hz`, so `h = e ΔV / Δν`.
-/
lemma inferredPlanckConstant_eq_elementaryCharge_mul_graphSlope
    (setup : PhotoelectricExperiment)
    (hData : HasSuppliedFigureReadouts setup)
    (hCalibration : UsesSuppliedAxisCalibration setup)
    (hCharge : UsesPhyslibElementaryCharge setup)
    (hLaws : SatisfiesPhotoelectricEffectLaws setup) :
    planckConstantInJouleSeconds setup.experimentalPlanckConstant =
      physlibElementaryChargeInCoulombs *
        (2 / (5 * (10 : ℝ) ^ 14)) := by
  have hFreqA := hCalibration.frequencyCalibration MeasuredPoint.A
  have hFreqB := hCalibration.frequencyCalibration MeasuredPoint.B
  have hPotentialA := hCalibration.potentialCalibration MeasuredPoint.A
  have hPotentialB := hCalibration.potentialCalibration MeasuredPoint.B
  simp only [MeasuredPoint.toFigurePoint] at hFreqA hFreqB hPotentialA hPotentialB
  rw [hData.pointAHorizontal, hData.horizontalScale] at hFreqA
  rw [hData.pointBHorizontal, hData.horizontalScale] at hFreqB
  rw [hData.pointAVertical, hData.verticalScale] at hPotentialA
  rw [hData.pointBVertical, hData.verticalScale] at hPotentialB
  have hKineticA := hLaws.stoppingPotentialRelation MeasuredPoint.A
  have hKineticB := hLaws.stoppingPotentialRelation MeasuredPoint.B
  rw [hPotentialA] at hKineticA
  rw [hPotentialB] at hKineticB
  have hEinsteinA := hLaws.einsteinEnergyBalance MeasuredPoint.A
  have hEinsteinB := hLaws.einsteinEnergyBalance MeasuredPoint.B
  rw [hFreqA, hKineticA] at hEinsteinA
  rw [hFreqB, hKineticB] at hEinsteinB
  rw [← hCharge.chargeCalibration]
  norm_num at hEinsteinA hEinsteinB ⊢
  linarith

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Planck-constant value printed for each choice, in joule-seconds. -/
def displayedPlanckConstantInJouleSeconds : AnswerChoice → ℝ
  | .A => 534 / (10 : ℝ) ^ 36
  | .B => 411 / (10 : ℝ) ^ 36
  | .C => 912 / (10 : ℝ) ^ 36
  | .D => 64 / (10 : ℝ) ^ 35

/-!
Half of the last displayed decimal step for choice D:
`0.05 × 10^-34 J·s = 5 × 10^-36 J·s`.
-/
def displayedAnswerToleranceInJouleSeconds : ℝ :=
  5 / (10 : ℝ) ^ 36

/-- The inferred physical value rounds to the value printed for a choice. -/
def MatchesDisplayedPlanckConstant
    (setup : PhotoelectricExperiment) (choice : AnswerChoice) : Prop :=
  |planckConstantInJouleSeconds setup.experimentalPlanckConstant -
      displayedPlanckConstantInJouleSeconds choice| <
    displayedAnswerToleranceInJouleSeconds

/-- Exactly one printed answer lies within the rounding interval. -/
def IsUniqueMatchingDisplayedPlanckConstant
    (setup : PhotoelectricExperiment) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPlanckConstant setup choice ∧
    ∀ other : AnswerChoice, other ≠ choice →
      ¬ MatchesDisplayedPlanckConstant setup other

/-- The source dataset's recorded answer, retained as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The supplied graph and photoelectric laws infer
`h = e · 2/(5 × 10^14)`, which rounds to `6.4 × 10^-34 J·s`; hence D is the
unique matching displayed choice.

This formalizes `thm:physics:phyx_mini_0549:target`.
-/
theorem problem_phyx_mini_0549
    (setup : PhotoelectricExperiment)
    (hFigure : HasSuppliedFigurePresentation setup)
    (hData : HasSuppliedFigureReadouts setup)
    (hCalibration : UsesSuppliedAxisCalibration setup)
    (hPhysical : HasPhysicalPhotoelectricParameters setup)
    (hCharge : UsesPhyslibElementaryCharge setup)
    (hLaws : SatisfiesPhotoelectricEffectLaws setup) :
    planckConstantInJouleSeconds setup.experimentalPlanckConstant =
        physlibElementaryChargeInCoulombs *
          (2 / (5 * (10 : ℝ) ^ 14)) ∧
      IsUniqueMatchingDisplayedPlanckConstant setup .D := by
  have hElementary :
      physlibElementaryChargeInCoulombs = (1.602176634e-19 : ℝ) := by
    rw [physlibElementaryChargeInCoulombs, ChargeUnit.elementaryCharge,
      ChargeUnit.scale_div_self]
    rfl
  have hPlanck :=
    inferredPlanckConstant_eq_elementaryCharge_mul_graphSlope
      setup hData hCalibration hCharge hLaws
  refine ⟨hPlanck, ?_⟩
  unfold IsUniqueMatchingDisplayedPlanckConstant
  constructor
  · unfold MatchesDisplayedPlanckConstant
    rw [hPlanck, hElementary]
    norm_num [displayedPlanckConstantInJouleSeconds,
      displayedAnswerToleranceInJouleSeconds, abs_of_nonneg, abs_of_nonpos]
  · intro other hOther
    fin_cases other
    · unfold MatchesDisplayedPlanckConstant
      rw [hPlanck, hElementary]
      norm_num [displayedPlanckConstantInJouleSeconds,
        displayedAnswerToleranceInJouleSeconds, abs_of_nonneg, abs_of_nonpos]
    · unfold MatchesDisplayedPlanckConstant
      rw [hPlanck, hElementary]
      norm_num [displayedPlanckConstantInJouleSeconds,
        displayedAnswerToleranceInJouleSeconds, abs_of_nonneg, abs_of_nonpos]
    · unfold MatchesDisplayedPlanckConstant
      rw [hPlanck, hElementary]
      norm_num [displayedPlanckConstantInJouleSeconds,
        displayedAnswerToleranceInJouleSeconds, abs_of_nonneg, abs_of_nonpos]
    · exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0549
