import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.QuantumMechanics.RectangularBarrier.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0615

open Dimension

/-!
# Alpha-particle tunneling through a rectangular nuclear barrier

An alpha particle trapped in a simple nuclear model encounters a rectangular
potential-energy barrier.  The particle mass, barrier width, energy levels,
reduced Planck action, and evanescent wave number are dimensionful physical
quantities.  Real numbers occur only as explicitly unit-labelled readouts,
the dimensionless transmission probability, and displayed answer values.

The problem prose says that the incident energy is `10.0 MeV` below the
barrier top, whereas the supplied primary image visibly prints `1.0 MeV` by
the energy-gap arrow.  Both source facts are represented below: the prose
deficit controls the physical model, while the conflicting image value is a
separate figure annotation and is not identified with that deficit.

Physlib's `QuantumMechanics.RectangularBarrier` supplies the one-dimensional
rectangular potential shape.  Since it does not currently expose a tunneling
transmission coefficient, the exact stationary-scattering coefficient for a
finite rectangular barrier is stated explicitly as a governing law.  In
particular, no opaque-barrier or other asymptotic approximation is asserted as
a global equality.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent physical energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- The dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical action, used for the reduced Planck constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative physical wave number, carrying inverse-length dimension. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Femtometre readout of a physical length. -/
def lengthInFemtometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.femtometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Electron-volt readout of a physical energy. -/
def energyInElectronVolts (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.electronVolt UnitChoices.SI).val

/-- Mega-electron-volt readout of a physical energy. -/
def energyInMegaElectronVolts (energy : EnergyQuantity) : ℝ :=
  energyInElectronVolts energy / 1000000

/-- Joule-second readout of a physical action. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Inverse-metre readout of a physical wave number. -/
def waveNumberInInverseMeters (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-! ## Scenario roles and vocabulary from the supplied figure -/

/-- Particle species used in the simple nuclear model. -/
inductive ParticleSpecies where
  | alphaParticle
  | other
  deriving DecidableEq, Repr

/-- Qualitative model selected for the nuclear potential. -/
inductive NuclearPotentialModel where
  | oneDimensionalRectangularBarrier
  | other
  deriving DecidableEq, Repr

/-- The two axes drawn in the supplied barrier graph. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to an axis of the supplied graph. -/
inductive PlotAxisQuantity where
  | radialCoordinateR
  | potentialEnergyUOfR
  deriving DecidableEq, Repr

/-- Shape of the potential-energy curve in the supplied graph. -/
inductive PotentialCurveShape where
  | rectangularBarrier
  | other
  deriving DecidableEq, Repr

/-- Literal symbolic or numerical annotations visible in the primary image. -/
inductive FigureAnnotation where
  | originO
  | barrierTopU0
  | incidentEnergyE
  | barrierWidthTwoFemtometers
  | energyGapOneMegaElectronVolt
  deriving DecidableEq, Fintype, Repr

/-!
The figure's energy-gap annotation is an independent field because its printed
`1.0 MeV` conflicts with the problem prose's physical `10.0 MeV` deficit.
-/
structure RectangularBarrierFigure where
  axisQuantity : PlotAxis → PlotAxisQuantity
  axisHasPrintedLabel : PlotAxis → Bool
  annotationIsPrinted : FigureAnnotation → Bool
  potentialCurveShape : PotentialCurveShape
  barrierWidthShown : LengthQuantity
  barrierTopLevelShown : EnergyQuantity
  incidentEnergyLevelShown : EnergyQuantity
  annotatedEnergyGapShown : EnergyQuantity

/-!
Independent physical quantities in the alpha-tunneling model.  In particular,
the attenuation wave number and tunneling probability are independent fields;
the governing laws below constrain them without defining either as the
recorded answer.
-/
structure AlphaRectangularBarrierSetup where
  particleSpecies : ParticleSpecies
  potentialModel : NuclearPotentialModel
  particleIsTrappedInsideNucleus : Bool
  particleEncountersBarrier : Bool
  alphaMass : MassQuantity
  barrierWidth : LengthQuantity
  barrierHeight : EnergyQuantity
  incidentKineticEnergy : EnergyQuantity
  energyBelowBarrierTop : EnergyQuantity
  reducedPlanckAction : ActionQuantity
  attenuationWaveNumber : WaveNumberQuantity
  tunnelingProbability : ℝ
  scalarBarrierModel : QuantumMechanics.RectangularBarrier
  figure : RectangularBarrierFigure

/-! ## Scenario, figure/data readouts, calibrations, and governing laws -/

/-- Qualitative physical scenario stated in the problem prose. -/
structure MatchesAlphaNucleusScenario
    (setup : AlphaRectangularBarrierSetup) : Prop where
  particleIsAlpha : setup.particleSpecies = .alphaParticle
  rectangularPotentialSelected :
    setup.potentialModel = .oneDimensionalRectangularBarrier
  initiallyTrapped : setup.particleIsTrappedInsideNucleus = true
  encountersPotentialBarrier : setup.particleEncountersBarrier = true

/-!
Axes, labels, rectangular geometry, and energy levels read from the primary
image.  The printed `1.0 MeV` annotation is deliberately not equated to the
prose deficit, since doing so would make the supplied data inconsistent.
This premise contains no tunneling probability or answer choice.
-/
structure MatchesSuppliedBarrierFigure
    (setup : AlphaRectangularBarrierSetup) : Prop where
  horizontalAxisIsRadius :
    setup.figure.axisQuantity .horizontal = .radialCoordinateR
  verticalAxisIsPotential :
    setup.figure.axisQuantity .vertical = .potentialEnergyUOfR
  horizontalAxisLabeled :
    setup.figure.axisHasPrintedLabel .horizontal = true
  verticalAxisLabeled : setup.figure.axisHasPrintedLabel .vertical = true
  originPrinted : setup.figure.annotationIsPrinted .originO = true
  barrierTopPrinted :
    setup.figure.annotationIsPrinted .barrierTopU0 = true
  incidentEnergyPrinted :
    setup.figure.annotationIsPrinted .incidentEnergyE = true
  widthAnnotationPrinted :
    setup.figure.annotationIsPrinted .barrierWidthTwoFemtometers = true
  gapAnnotationPrinted :
    setup.figure.annotationIsPrinted .energyGapOneMegaElectronVolt = true
  rectangularCurve :
    setup.figure.potentialCurveShape = .rectangularBarrier
  shownWidthIsPhysicalWidth :
    setup.figure.barrierWidthShown = setup.barrierWidth
  shownTopIsBarrierHeight :
    setup.figure.barrierTopLevelShown = setup.barrierHeight
  shownEnergyIsIncidentEnergy :
    setup.figure.incidentEnergyLevelShown = setup.incidentKineticEnergy
  annotatedGapMegaElectronVolts :
    energyInMegaElectronVolts setup.figure.annotatedEnergyGapShown = 1.0

/-!
Numerical physical data supplied by the problem prose.  The final field states
that the incident level is the specified deficit below the barrier top; it
does not state a transmission probability.
-/
structure MatchesProblemReadouts
    (setup : AlphaRectangularBarrierSetup) : Prop where
  alphaMassKilograms : massInKilograms setup.alphaMass = 6.64e-27
  barrierWidthFemtometers :
    lengthInFemtometers setup.barrierWidth = 2.0
  barrierHeightMegaElectronVolts :
    energyInMegaElectronVolts setup.barrierHeight = 30.0
  energyDeficitMegaElectronVolts :
    energyInMegaElectronVolts setup.energyBelowBarrierTop = 10.0
  energyLevelIsBelowTopByDeficit :
    energyInMegaElectronVolts setup.barrierHeight -
        energyInMegaElectronVolts setup.incidentKineticEnergy =
      energyInMegaElectronVolts setup.energyBelowBarrierTop

/-- The standard reduced Planck constant used by the numerical model. -/
structure UsesStandardReducedPlanckConstant
    (setup : AlphaRectangularBarrierSetup) : Prop where
  reducedPlanckActionJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction =
      (Constants.ℏ : ℝ)

/-!
Calibrate Physlib's scalar rectangular-barrier parameters by coherent-SI
readouts of the dimensionful physical quantities.  The absolute radial
location of the two faces is left free because the image specifies only their
separation.
-/
structure MatchesPhyslibRectangularBarrier
    (setup : AlphaRectangularBarrierSetup) : Prop where
  scalarMassIsKilogramReadout :
    setup.scalarBarrierModel.m = massInKilograms setup.alphaMass
  scalarWidthIsMeterReadout :
    setup.scalarBarrierModel.upper - setup.scalarBarrierModel.lower =
      lengthInMeters setup.barrierWidth
  scalarHeightIsJouleReadout :
    setup.scalarBarrierModel.V₀ = energyInJoules setup.barrierHeight

/-- Positivity and range conditions selecting a physical tunneling setup. -/
structure HasPhysicalTunnelingParameters
    (setup : AlphaRectangularBarrierSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.alphaMass
  positiveWidth : 0 < lengthInMeters setup.barrierWidth
  positiveBarrierHeight : 0 < energyInJoules setup.barrierHeight
  positiveIncidentEnergy : 0 < energyInJoules setup.incidentKineticEnergy
  incidentEnergyBelowBarrier :
    energyInJoules setup.incidentKineticEnergy <
      energyInJoules setup.barrierHeight
  positiveEnergyDeficit :
    0 < energyInJoules setup.energyBelowBarrierTop
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  positiveAttenuationWaveNumber :
    0 < waveNumberInInverseMeters setup.attenuationWaveNumber
  probabilityInUnitInterval : setup.tunnelingProbability ∈ Set.Icc 0 1

/-!
The two exact textbook relations used for the recorded multiple-choice
computation in the one-dimensional, nonrelativistic, stationary rectangular-
barrier model.

* In the classically forbidden region,
  `ℏ² κ² = 2 m (U₀ - E)`.
* Exact matching of the stationary wavefunction and its derivative at both
  barrier faces gives
  `T = (1 + U₀² sinh²(κ L) / (4 E (U₀ - E)))⁻¹` for `0 < E < U₀`.

Every term is an SI readout of a dimensionally typed quantity except the
dimensionless ratios, exponent, and probability.  Neither law contains the
number `0.014` or a displayed answer label.
-/
structure ObeysTextbookRectangularBarrierTunneling
    (setup : AlphaRectangularBarrierSetup) : Prop where
  attenuationWaveNumberLaw :
    actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
        waveNumberInInverseMeters setup.attenuationWaveNumber ^ 2 =
      2 * massInKilograms setup.alphaMass *
        (energyInJoules setup.barrierHeight -
          energyInJoules setup.incidentKineticEnergy)
  exactBarrierTransmissionLaw :
    setup.tunnelingProbability =
      (1 +
        energyInJoules setup.barrierHeight ^ 2 *
          Real.sinh
            (waveNumberInInverseMeters setup.attenuationWaveNumber *
              lengthInMeters setup.barrierWidth) ^ 2 /
          (4 * energyInJoules setup.incidentKineticEnergy *
            (energyInJoules setup.barrierHeight -
              energyInJoules setup.incidentKineticEnergy)))⁻¹

/-! ## Displayed choices and current target -/

/-- Labels of the four tunneling-probability choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless probabilities printed beside the four choices. -/
def displayedTunnelingProbability : AnswerChoice → ℝ
  | .A => 0.014
  | .B => 0.023
  | .C => 0.09
  | .D => 0.031

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
`value` rounds to `reported` at three decimal places.  The half-open interval
implements ordinary nearest-thousandth rounding away from the upper tie.
-/
def RoundsToThreeDecimalPlaces (value reported : ℝ) : Prop :=
  reported - (1 : ℝ) / 2000 ≤ value ∧
    value < reported + (1 : ℝ) / 2000

/-- A displayed choice agrees with the modeled probability to three decimals. -/
def MatchesDisplayedTunnelingProbability
    (setup : AlphaRectangularBarrierSetup) (choice : AnswerChoice) : Prop :=
  RoundsToThreeDecimalPlaces setup.tunnelingProbability
    (displayedTunnelingProbability choice)

/-- A choice is the unique displayed value matching the modeled probability. -/
def IsUniqueMatchingTunnelingChoice
    (setup : AlphaRectangularBarrierSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedTunnelingProbability setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedTunnelingProbability setup other → other = choice

/-- The prose energy separation implies an incident energy of `20 MeV`. -/
lemma incident_kinetic_energy_megaelectronvolts_eq
    (setup : AlphaRectangularBarrierSetup)
    (h_readouts : MatchesProblemReadouts setup) :
    energyInMegaElectronVolts setup.incidentKineticEnergy = 20 := by
  rcases h_readouts with ⟨hm, hL, hU, hD, hE⟩
  norm_num at hU hD ⊢
  linarith

/-!
The dimensionful data and the exact rectangular-barrier tunneling laws put the
transmission probability in the interval that rounds to `0.014`.
-/
lemma tunneling_probability_rounds_to_0_014
    (setup : AlphaRectangularBarrierSetup)
    (h_physical : HasPhysicalTunnelingParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_reference : UsesStandardReducedPlanckConstant setup)
    (h_laws : ObeysTextbookRectangularBarrierTunneling setup) :
    RoundsToThreeDecimalPlaces setup.tunnelingProbability 0.014 := by
  have h_energy_conversion (energy : EnergyQuantity) :
      energyInJoules energy =
        1.602176634e-13 * energyInMegaElectronVolts energy := by
    simp [energyInJoules, energyInMegaElectronVolts,
      energyInElectronVolts, DimEnergy.joule, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
    ring
  have h_length_conversion (length : LengthQuantity) :
      lengthInMeters length = 1e-15 * lengthInFemtometers length := by
    have hscale := congrArg (fun x => (x.val : ℝ)) (length.2
      ({UnitChoices.SI with length := LengthUnit.femtometers})
        UnitChoices.SI)
    norm_num [lengthInMeters, lengthInFemtometers, lengthReadout,
      UnitChoices.SI, UnitChoices.dimScale, LengthUnit.femtometers,
      LengthUnit.scale, LengthUnit.meters, LengthUnit.div_eq_val]
      at hscale ⊢
    exact hscale
  have h_E_MeV :=
    incident_kinetic_energy_megaelectronvolts_eq setup h_readouts
  have h_width : lengthInMeters setup.barrierWidth = 2e-15 := by
    rw [h_length_conversion, h_readouts.barrierWidthFemtometers]
    norm_num
  have h_U :
      energyInJoules setup.barrierHeight = 30 * 1.602176634e-13 := by
    rw [h_energy_conversion,
      h_readouts.barrierHeightMegaElectronVolts]
    norm_num
  have h_E :
      energyInJoules setup.incidentKineticEnergy =
        20 * 1.602176634e-13 := by
    rw [h_energy_conversion, h_E_MeV]
    norm_num
  have h_hbar :
      actionInJouleSeconds setup.reducedPlanckAction =
        1.054571817e-34 := by
    rw [h_reference.reducedPlanckActionJouleSeconds]
    rfl
  have hk := h_laws.attenuationWaveNumberLaw
  rw [h_hbar, h_U, h_E, h_readouts.alphaMassKilograms] at hk
  let x : ℝ :=
    waveNumberInInverseMeters setup.attenuationWaveNumber *
      lengthInMeters setup.barrierWidth
  have hx_sq :
      x ^ 2 = (945640253312000000 : ℝ) / 123569079690075721 := by
    dsimp [x]
    rw [h_width, mul_pow]
    norm_num at hk ⊢
    nlinarith [hk]
  have hx_pos : 0 < x := by
    exact mul_pos h_physical.positiveAttenuationWaveNumber
      h_physical.positiveWidth
  have hx_lower : (2.766 : ℝ) < x := by
    nlinarith
  have hx_upper : x < (2.767 : ℝ) := by
    nlinarith
  have hexp_one_lower : (2.718 : ℝ) < Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ))
      (by norm_num) 7
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hexp_one_upper : Real.exp 1 < (2.719 : ℝ) := by
    have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num)
      (by norm_num) (n := 9) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hexp_0766_lower : (2.15 : ℝ) < Real.exp 0.766 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.766 : ℝ))
      (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hexp_0767_upper : Real.exp 0.767 < (2.154 : ℝ) := by
    have h := Real.exp_bound' (x := (0.767 : ℝ)) (by norm_num)
      (by norm_num) (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hexp_lower : (15.88 : ℝ) < Real.exp x := by
    calc
      (15.88 : ℝ) < 2.718 * 2.718 * 2.15 := by norm_num
      _ < Real.exp 1 * Real.exp 1 * Real.exp 0.766 := by gcongr
      _ = Real.exp 2.766 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      _ < Real.exp x := Real.exp_lt_exp.mpr hx_lower
  have hexp_upper : Real.exp x < (16 : ℝ) := by
    calc
      Real.exp x < Real.exp 2.767 := Real.exp_lt_exp.mpr hx_upper
      _ = Real.exp 1 * Real.exp 1 * Real.exp 0.767 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      _ < 2.719 * 2.719 * 2.154 := by gcongr
      _ < (16 : ℝ) := by norm_num
  have hexp_neg_upper : Real.exp (-x) < (0.063 : ℝ) := by
    rw [Real.exp_neg]
    calc
      (Real.exp x)⁻¹ < (15.88 : ℝ)⁻¹ :=
        (inv_lt_inv₀ (Real.exp_pos x) (by norm_num)).2 hexp_lower
      _ < (0.063 : ℝ) := by norm_num
  have hsinh_lower : (7.9 : ℝ) < Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  have hsinh_upper : Real.sinh x < (8 : ℝ) := by
    calc
      Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 :=
        Real.sinh_eq x
      _ < Real.exp x / 2 :=
        (div_lt_div_iff_of_pos_right (by norm_num)).2
          (sub_lt_self _ (Real.exp_pos (-x)))
      _ < (8 : ℝ) :=
        (div_lt_iff₀ (by norm_num)).2 (by linarith)
  have h_trans :
      setup.tunnelingProbability =
        (1 + (9 / 8 : ℝ) * Real.sinh x ^ 2)⁻¹ := by
    rw [h_laws.exactBarrierTransmissionLaw]
    dsimp [x]
    rw [h_U, h_E]
    congr 2
    field_simp
    ring
  have hsinh_pos : 0 < Real.sinh x := by
    linarith
  have hsinh_sq_lower :
      (7.9 : ℝ) ^ 2 < Real.sinh x ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hsinh_pos.le).2 hsinh_lower
  have hsinh_sq_upper :
      Real.sinh x ^ 2 < (8 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hsinh_pos.le (by norm_num)).2 hsinh_upper
  let d : ℝ := 1 + (9 / 8 : ℝ) * Real.sinh x ^ 2
  have hd_pos : 0 < d := by
    dsimp [d]
    positivity
  have hd_lower : (69 : ℝ) < d := by
    dsimp [d]
    nlinarith
  have hd_upper : d < (73 : ℝ) := by
    dsimp [d]
    nlinarith
  have hprob_lower : (0.0135 : ℝ) ≤ d⁻¹ := by
    have h_inv : (73 : ℝ)⁻¹ < d⁻¹ :=
      (inv_lt_inv₀ (by norm_num) hd_pos).2 hd_upper
    norm_num at h_inv ⊢
    linarith
  have hprob_upper : d⁻¹ < (0.0145 : ℝ) := by
    have h_inv : d⁻¹ < (69 : ℝ)⁻¹ :=
      (inv_lt_inv₀ hd_pos (by norm_num)).2 hd_lower
    norm_num at h_inv ⊢
    linarith
  rw [h_trans]
  unfold RoundsToThreeDecimalPlaces
  norm_num at hprob_lower hprob_upper ⊢
  simpa [d] using And.intro hprob_lower hprob_upper

/-!
For the alpha mass `6.64 × 10⁻²⁷ kg`, width `2.0 fm`, height `30.0 MeV`,
and incident energy `10.0 MeV` below the top, the exact one-dimensional
stationary rectangular-barrier model yields a tunneling probability that
rounds to `0.014`.  This uniquely selects choice A.

This formalizes `thm:physics:phyx_mini_0615:target`.  Neither the numerical
probability, its rounding interval, nor choice A occurs in any scenario,
figure, calibration, positivity, or governing-law premise.
-/
theorem problem_phyx_mini_0615
    (setup : AlphaRectangularBarrierSetup)
    (h_scenario : MatchesAlphaNucleusScenario setup)
    (h_figure : MatchesSuppliedBarrierFigure setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_reference : UsesStandardReducedPlanckConstant setup)
    (h_barrier : MatchesPhyslibRectangularBarrier setup)
    (h_physical : HasPhysicalTunnelingParameters setup)
    (h_laws : ObeysTextbookRectangularBarrierTunneling setup) :
    energyInMegaElectronVolts setup.incidentKineticEnergy = 20 ∧
      RoundsToThreeDecimalPlaces setup.tunnelingProbability 0.014 ∧
      IsUniqueMatchingTunnelingChoice setup .A := by
  have h_energy :=
    incident_kinetic_energy_megaelectronvolts_eq setup h_readouts
  have h_rounds :=
    tunneling_probability_rounds_to_0_014 setup h_physical h_readouts
      h_reference h_laws
  refine ⟨h_energy, h_rounds, h_rounds, ?_⟩
  intro other h_other
  cases other <;>
    norm_num [MatchesDisplayedTunnelingProbability,
      RoundsToThreeDecimalPlaces, displayedTunnelingProbability]
      at h_rounds h_other ⊢ <;>
    linarith

end PhyXMiniProblems.ProblemPhyXMini0615
