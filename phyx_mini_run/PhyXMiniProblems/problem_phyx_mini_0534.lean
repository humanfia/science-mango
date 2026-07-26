import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0534

open Dimension

/-!
# Transmission through an upward quantum potential step

A particle approaches from the left a one-dimensional potential step at
`x = 0`.  The potential is zero on the left and has positive height `U` on
the right, while the particle's total energy `E` is above the step.

Energy, mass, action, position, and wave number are represented by
unit-independent Physlib quantities.  Real numbers below are used only for
specified unit readouts, dimensionless probabilities, raster measurements,
and the values printed with the answer choices.  In particular, the
transmission probability is an independent field constrained by the general
quantum step laws; it is not defined to be the recorded answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, equivalently energy times time. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A signed, unit-independent position along the scattering axis. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative wave-number magnitude, carrying inverse-length dimension. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Coherent-SI readout of a mass, in kilograms. -/
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

/-! ## Physical and primary-figure labels -/

/-- The two constant-potential regions separated by `x = 0`. -/
inductive PotentialRegion where
  | leftOfStep
  | rightOfStep
  deriving DecidableEq, Fintype, Repr

/-- The three plane-wave components in above-barrier step scattering. -/
inductive ScatteringComponent where
  | incident
  | reflected
  | transmitted
  deriving DecidableEq, Fintype, Repr

/-- The two directions along the horizontal scattering axis. -/
inductive HorizontalDirection where
  | towardNegativeX
  | towardPositiveX
  deriving DecidableEq, Repr

/-!
Visible contents and rounded measurements of the `428 × 236` source raster.
The energy and step arrows have rounded tip-to-tip vertical spans of `154`
and `110` pixels, respectively, giving the intended drawn scale `E : U = 7 : 5`.
The pixel fields are dimensionless image readouts, not physical energies.
-/
structure PotentialStepFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  boundaryXPixel : ℝ
  energyArrowLengthPixels : ℝ
  stepArrowLengthPixels : ℝ
  incomingParticleShown : Bool
  incomingArrowShown : Bool
  lowerPotentialLineShown : Bool
  upperPotentialLineShown : Bool
  zeroPotentialLabelShown : Bool
  stepHeightLabelUShown : Bool
  totalEnergyLabelEShown : Bool

/-!
Independent quantities in the scattering experiment.  The two outcome
probabilities and the regional wave numbers remain unknown fields here.
-/
structure QuantumPotentialStepSetup where
  particleMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  totalEnergy : DimEnergy
  stepHeight : DimEnergy
  potentialEnergy : PotentialRegion → DimEnergy
  boundaryPosition : SignedLengthQuantity
  componentRegion : ScatteringComponent → PotentialRegion
  componentDirection : ScatteringComponent → HorizontalDirection
  waveNumber : PotentialRegion → WaveNumberQuantity
  outcomeProbability : ScatteringComponent → ℝ
  figure : PotentialStepFigure

/-- The probability requested by the problem. -/
def transmissionProbability (setup : QuantumPotentialStepSetup) : ℝ :=
  setup.outcomeProbability .transmitted

/-- The reflected fraction mentioned in the scenario. -/
def reflectionProbability (setup : QuantumPotentialStepSetup) : ℝ :=
  setup.outcomeProbability .reflected

/-! ## Scenario, figure readouts, and governing physics -/

/-!
The step is at the origin, the left potential is zero, and the right potential
is the stated step height.  The component roles encode incidence from the
left, reflection back to the left, and transmission into the right region.
-/
structure MatchesPotentialStepScenario
    (setup : QuantumPotentialStepSetup) : Prop where
  boundaryAtOrigin : positionInMeters setup.boundaryPosition = 0
  leftPotentialZero :
    energyInJoules (setup.potentialEnergy .leftOfStep) = 0
  rightPotentialIsStepHeight :
    energyInJoules (setup.potentialEnergy .rightOfStep) =
      energyInJoules setup.stepHeight
  incidentComponentOnLeft :
    setup.componentRegion .incident = .leftOfStep
  reflectedComponentOnLeft :
    setup.componentRegion .reflected = .leftOfStep
  transmittedComponentOnRight :
    setup.componentRegion .transmitted = .rightOfStep
  incidentMovesRight :
    setup.componentDirection .incident = .towardPositiveX
  reflectedMovesLeft :
    setup.componentDirection .reflected = .towardNegativeX
  transmittedMovesRight :
    setup.componentDirection .transmitted = .towardPositiveX

/-!
Qualitative labels and rounded raster measurements from image `534.png`.
This premise contains neither a probability nor an answer-choice label.
-/
structure MatchesSuppliedPotentialStepFigure
    (figure : PotentialStepFigure) : Prop where
  rasterWidth : figure.rasterWidthPixels = 428
  rasterHeight : figure.rasterHeightPixels = 236
  stepBoundaryX : figure.boundaryXPixel = 187
  energyArrowSpan : figure.energyArrowLengthPixels = 154
  potentialArrowSpan : figure.stepArrowLengthPixels = 110
  incomingParticleVisible : figure.incomingParticleShown = true
  incomingArrowVisible : figure.incomingArrowShown = true
  lowerPotentialLineVisible : figure.lowerPotentialLineShown = true
  upperPotentialLineVisible : figure.upperPotentialLineShown = true
  zeroPotentialLabelVisible : figure.zeroPotentialLabelShown = true
  stepHeightLabelVisible : figure.stepHeightLabelUShown = true
  totalEnergyLabelVisible : figure.totalEnergyLabelEShown = true

/-!
The diagram uses one common linear vertical energy scale for its `E` and `U`
arrows.  Cross-multiplication avoids dividing by an image length.  This is a
figure-calibration law, not a transmission-probability formula.
-/
structure UsesLinearFigureEnergyScale
    (setup : QuantumPotentialStepSetup) : Prop where
  energyArrowCalibration :
    energyInJoules setup.totalEnergy *
        setup.figure.stepArrowLengthPixels =
      energyInJoules setup.stepHeight *
        setup.figure.energyArrowLengthPixels

/-- Positivity, above-step energy, and probability bounds for the physical branch. -/
structure HasPhysicalPotentialStepParameters
    (setup : QuantumPotentialStepSetup) : Prop where
  particleMassPositive : 0 < massInKilograms setup.particleMass
  reducedPlanckActionPositive :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  stepHeightPositive : 0 < energyInJoules setup.stepHeight
  energyAboveStep :
    energyInJoules setup.stepHeight < energyInJoules setup.totalEnergy
  waveNumbersPositive :
    ∀ region, 0 < waveNumberInInverseMeters (setup.waveNumber region)
  reflectedProbabilityBounds : 0 ≤ reflectionProbability setup ∧
    reflectionProbability setup ≤ 1
  transmittedProbabilityBounds : 0 ≤ transmissionProbability setup ∧
    transmissionProbability setup ≤ 1

/-!
Physlib's standard reduced Planck constant, calibrated in SI
joule-seconds.  This datum does not constrain either outcome probability.
-/
structure UsesStandardReducedPlanckConstant
    (setup : QuantumPotentialStepSetup) : Prop where
  reducedPlanckActionJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/-!
The governing laws for a stationary one-dimensional upward step with
`E > U`:

* the free-region Schrödinger dispersion relation
  `ℏ² k² = 2m(E - V)` on both sides;
* the probability-flux transmission and reflection coefficients obtained by
  matching the wave function and its derivative at the sharp interface;
* conservation of incident probability flux.

All formulas are stated for the setup's still-unknown energies and wave
numbers.  None specializes the transmission probability to the current
figure's numerical answer.
-/
structure SatisfiesQuantumPotentialStepLaws
    (setup : QuantumPotentialStepSetup) : Prop where
  regionalDispersion : ∀ region : PotentialRegion,
    actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
        waveNumberInInverseMeters (setup.waveNumber region) ^ 2 =
      2 * massInKilograms setup.particleMass *
        (energyInJoules setup.totalEnergy -
          energyInJoules (setup.potentialEnergy region))
  transmissionFluxCoefficient :
    transmissionProbability setup =
      4 * waveNumberInInverseMeters (setup.waveNumber .leftOfStep) *
          waveNumberInInverseMeters (setup.waveNumber .rightOfStep) /
        (waveNumberInInverseMeters (setup.waveNumber .leftOfStep) +
          waveNumberInInverseMeters (setup.waveNumber .rightOfStep)) ^ 2
  reflectionFluxCoefficient :
    reflectionProbability setup =
      ((waveNumberInInverseMeters (setup.waveNumber .leftOfStep) -
          waveNumberInInverseMeters (setup.waveNumber .rightOfStep)) /
        (waveNumberInInverseMeters (setup.waveNumber .leftOfStep) +
          waveNumberInInverseMeters (setup.waveNumber .rightOfStep))) ^ 2
  probabilityFluxConservation :
    reflectionProbability setup + transmissionProbability setup = 1

/-! ## Derived relation and answer semantics -/

/-!
The figure scale and regional dispersion imply
`k_right / k_left = sqrt (2/7)`.  This is a derived intermediate result, not
an assumption and not the requested transmission probability.
-/
lemma transmittedToIncidentWaveNumberRatio
    (setup : QuantumPotentialStepSetup)
    (_scenario : MatchesPotentialStepScenario setup)
    (_figure : MatchesSuppliedPotentialStepFigure setup.figure)
    (_scale : UsesLinearFigureEnergyScale setup)
    (_physical : HasPhysicalPotentialStepParameters setup)
    (_laws : SatisfiesQuantumPotentialStepLaws setup) :
    waveNumberInInverseMeters (setup.waveNumber .rightOfStep) /
        waveNumberInInverseMeters (setup.waveNumber .leftOfStep) =
      Real.sqrt ((2 : ℝ) / 7) := by
  let E := energyInJoules setup.totalEnergy
  let U := energyInJoules setup.stepHeight
  let m := massInKilograms setup.particleMass
  let ℏ := actionInJouleSeconds setup.reducedPlanckAction
  let k₁ :=
    waveNumberInInverseMeters (setup.waveNumber .leftOfStep)
  let k₂ :=
    waveNumberInInverseMeters (setup.waveNumber .rightOfStep)
  have hcalibration : E * 110 = U * 154 := by
    simpa [E, U, _figure.potentialArrowSpan, _figure.energyArrowSpan] using
      _scale.energyArrowCalibration
  have henergy : 7 * (E - U) = 2 * E := by
    nlinarith [hcalibration]
  have hleft : ℏ ^ 2 * k₁ ^ 2 = 2 * m * E := by
    simpa [ℏ, k₁, m, E, _scenario.leftPotentialZero] using
      _laws.regionalDispersion .leftOfStep
  have hright : ℏ ^ 2 * k₂ ^ 2 = 2 * m * (E - U) := by
    simpa [ℏ, k₂, m, E, U, _scenario.rightPotentialIsStepHeight] using
      _laws.regionalDispersion .rightOfStep
  have hdispersion :
      7 * (ℏ ^ 2 * k₂ ^ 2) = 2 * (ℏ ^ 2 * k₁ ^ 2) := by
    calc
      7 * (ℏ ^ 2 * k₂ ^ 2) = 7 * (2 * m * (E - U)) := by rw [hright]
      _ = 2 * m * (7 * (E - U)) := by ring
      _ = 2 * m * (2 * E) := by rw [henergy]
      _ = 2 * (2 * m * E) := by ring
      _ = 2 * (ℏ ^ 2 * k₁ ^ 2) := by rw [hleft]
  have hℏ : 0 < ℏ := by
    simpa [ℏ] using _physical.reducedPlanckActionPositive
  have hfactor : ℏ ^ 2 * (7 * k₂ ^ 2 - 2 * k₁ ^ 2) = 0 := by
    nlinarith [hdispersion]
  have hcore : 7 * k₂ ^ 2 = 2 * k₁ ^ 2 := by
    have hz :=
      (mul_eq_zero.mp hfactor).resolve_left
        (pow_ne_zero 2 (ne_of_gt hℏ))
    nlinarith
  have hk₁ : 0 < k₁ := by
    simpa [k₁] using _physical.waveNumbersPositive .leftOfStep
  have hk₂ : 0 < k₂ := by
    simpa [k₂] using _physical.waveNumbersPositive .rightOfStep
  have hratioSq : (k₂ / k₁) ^ 2 = (2 : ℝ) / 7 := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 (ne_of_gt hk₁))).2
    nlinarith [hcore]
  have hsqrtSq :
      (Real.sqrt ((2 : ℝ) / 7)) ^ 2 = (2 : ℝ) / 7 :=
    Real.sq_sqrt (by norm_num)
  have hratioNonnegative : 0 ≤ k₂ / k₁ :=
    le_of_lt (div_pos hk₂ hk₁)
  change k₂ / k₁ = Real.sqrt ((2 : ℝ) / 7)
  nlinarith [hratioSq, hsqrtSq, Real.sqrt_nonneg ((2 : ℝ) / 7)]

/-- Labels of the four transmission-probability choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless probability printed beside each answer choice. -/
def displayedTransmissionProbability : AnswerChoice → ℝ
  | .A => 939 / 1000
  | .B => 866 / 1000
  | .C => 745 / 1000
  | .D => 908 / 1000

/-- Dataset metadata recording answer D; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice is at least as close as every alternative. -/
def IsNearestAnswerChoice (probability : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    abs (probability - displayedTransmissionProbability choice) ≤
      abs (probability - displayedTransmissionProbability other)

/-!
Agreement with a probability printed to three decimal places.  Half of one
unit in the final decimal place is `1 / 2000`.
-/
def AgreesWhenRoundedToThreeDecimals
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  abs (probability - displayedTransmissionProbability choice) < 1 / 2000

/--
For the step drawn with `E : U = 7 : 5`, the transmitted-to-incident wave
number ratio is `sqrt (2/7)`.  Substitution in the general probability-flux
coefficient gives a transmission probability approximately `0.9079866`,
which rounds to `0.908` and selects choice D.

Blueprint: `thm:physics:phyx_mini_0534:target`.
-/
theorem transmissionProbabilityForFigurePotentialStep
    (setup : QuantumPotentialStepSetup)
    (_scenario : MatchesPotentialStepScenario setup)
    (_figure : MatchesSuppliedPotentialStepFigure setup.figure)
    (_scale : UsesLinearFigureEnergyScale setup)
    (_physical : HasPhysicalPotentialStepParameters setup)
    (_standardPlanck : UsesStandardReducedPlanckConstant setup)
    (_laws : SatisfiesQuantumPotentialStepLaws setup) :
    transmissionProbability setup =
        4 * Real.sqrt ((2 : ℝ) / 7) /
          (1 + Real.sqrt ((2 : ℝ) / 7)) ^ 2 ∧
      AgreesWhenRoundedToThreeDecimals
        (transmissionProbability setup) .D ∧
      IsNearestAnswerChoice (transmissionProbability setup) .D := by
  let k₁ :=
    waveNumberInInverseMeters (setup.waveNumber .leftOfStep)
  let k₂ :=
    waveNumberInInverseMeters (setup.waveNumber .rightOfStep)
  let s := Real.sqrt ((2 : ℝ) / 7)
  have hk₁ : 0 < k₁ := by
    simpa [k₁] using _physical.waveNumbersPositive .leftOfStep
  have hk₂ : 0 < k₂ := by
    simpa [k₂] using _physical.waveNumbersPositive .rightOfStep
  have hs : 0 ≤ s := by
    exact Real.sqrt_nonneg ((2 : ℝ) / 7)
  have hsSq : s ^ 2 = (2 : ℝ) / 7 := by
    exact Real.sq_sqrt (by norm_num)
  have hratio : k₂ / k₁ = s := by
    simpa [k₁, k₂, s] using
      transmittedToIncidentWaveNumberRatio
        setup _scenario _figure _scale _physical _laws
  have hk₂eq : k₂ = s * k₁ :=
    (div_eq_iff (ne_of_gt hk₁)).mp hratio
  have hsOne : 0 < 1 + s := by
    nlinarith
  have hformula :
      transmissionProbability setup =
        4 * Real.sqrt ((2 : ℝ) / 7) /
          (1 + Real.sqrt ((2 : ℝ) / 7)) ^ 2 := by
    rw [_laws.transmissionFluxCoefficient]
    change 4 * k₁ * k₂ / (k₁ + k₂) ^ 2 =
      4 * s / (1 + s) ^ 2
    rw [hk₂eq]
    field_simp [ne_of_gt hk₁, ne_of_gt hsOne]
  have hsLower : (267 : ℝ) / 500 < s := by
    have hcSq : ((267 : ℝ) / 500) ^ 2 < (2 : ℝ) / 7 := by
      norm_num
    by_contra h
    have hsc : s ≤ (267 : ℝ) / 500 := le_of_not_gt h
    have hsum : 0 ≤ s + (267 : ℝ) / 500 := by
      nlinarith
    have hprod :
        (s - (267 : ℝ) / 500) * (s + (267 : ℝ) / 500) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsc) hsum
    nlinarith
  have hsUpper : s ≤ (681 : ℝ) / 1274 := by
    have hcSq : (2 : ℝ) / 7 < ((681 : ℝ) / 1274) ^ 2 := by
      norm_num
    by_contra h
    have hsc : (681 : ℝ) / 1274 < s := lt_of_not_ge h
    have hsum : 0 < s + (681 : ℝ) / 1274 := by
      nlinarith
    have hprod :
        0 < (s - (681 : ℝ) / 1274) *
          (s + (681 : ℝ) / 1274) :=
      mul_pos (sub_pos.mpr hsc) hsum
    nlinarith
  have hdenominator : 0 < (1 + s) ^ 2 :=
    pow_pos hsOne 2
  have hexpressionLower :
      (363 : ℝ) / 400 < 4 * s / (1 + s) ^ 2 := by
    apply (lt_div_iff₀ hdenominator).2
    nlinarith [hsSq, hsLower]
  have hexpressionUpper :
      4 * s / (1 + s) ^ 2 ≤ (227 : ℝ) / 250 := by
    apply (div_le_iff₀ hdenominator).2
    nlinarith [hsSq, hsUpper]
  have hprobabilityLower :
      (363 : ℝ) / 400 < transmissionProbability setup := by
    rw [hformula]
    exact hexpressionLower
  have hprobabilityUpper :
      transmissionProbability setup ≤ (227 : ℝ) / 250 := by
    rw [hformula]
    exact hexpressionUpper
  refine ⟨hformula, ?_, ?_⟩
  · change
      abs (transmissionProbability setup - (908 : ℝ) / 1000) <
        (1 : ℝ) / 2000
    have hnonpositive :
        transmissionProbability setup - (908 : ℝ) / 1000 ≤ 0 := by
      norm_num at hprobabilityUpper ⊢
      exact hprobabilityUpper
    rw [abs_of_nonpos hnonpositive]
    norm_num at hprobabilityLower ⊢
    linarith
  · intro other
    have hDnonpositive :
        transmissionProbability setup - (908 : ℝ) / 1000 ≤ 0 := by
      norm_num at hprobabilityUpper ⊢
      exact hprobabilityUpper
    cases other with
    | A =>
        change
          abs (transmissionProbability setup - (908 : ℝ) / 1000) ≤
            abs (transmissionProbability setup - (939 : ℝ) / 1000)
        have hAnonpositive :
            transmissionProbability setup - (939 : ℝ) / 1000 ≤ 0 := by
          norm_num at hprobabilityUpper ⊢
          linarith
        rw [abs_of_nonpos hDnonpositive, abs_of_nonpos hAnonpositive]
        norm_num
    | B =>
        change
          abs (transmissionProbability setup - (908 : ℝ) / 1000) ≤
            abs (transmissionProbability setup - (866 : ℝ) / 1000)
        have hBnonnegative :
            0 ≤ transmissionProbability setup - (866 : ℝ) / 1000 := by
          norm_num at hprobabilityLower ⊢
          linarith
        rw [abs_of_nonpos hDnonpositive, abs_of_nonneg hBnonnegative]
        norm_num at hprobabilityLower ⊢
        linarith
    | C =>
        change
          abs (transmissionProbability setup - (908 : ℝ) / 1000) ≤
            abs (transmissionProbability setup - (745 : ℝ) / 1000)
        have hCnonnegative :
            0 ≤ transmissionProbability setup - (745 : ℝ) / 1000 := by
          norm_num at hprobabilityLower ⊢
          linarith
        rw [abs_of_nonpos hDnonpositive, abs_of_nonneg hCnonnegative]
        norm_num at hprobabilityLower ⊢
        linarith
    | D =>
        rfl

end PhyXMiniProblems.ProblemPhyXMini0534
