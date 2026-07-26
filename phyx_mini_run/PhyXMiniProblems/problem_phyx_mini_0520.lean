import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.QuantumMechanics.RectangularBarrier.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0520

open Dimension

/-!
# Alpha-particle tunneling through a rectangular nuclear barrier

An alpha particle encounters a rectangular potential-energy barrier.  The
particle mass, barrier width, energy levels, reduced Planck action, and
evanescent wave number are dimensionful physical quantities.  Real numbers
occur only as explicitly unit-labelled readouts, the dimensionless
transmission probability, and the displayed answer values.

The Physlib `QuantumMechanics.RectangularBarrier` object supplies the
one-dimensional rectangular potential shape.  Its scalar parameters are tied
below to SI readouts of the dimensionful quantities.  Since Physlib does not
currently provide a transmission coefficient for that object, the exact
finite rectangular-barrier coefficient and the textbook opaque-barrier
estimate are stated locally and kept distinct.  Their asymptotic equivalence
at large opacity is explicit; the approximation is never asserted to be the
exact probability at the finite opacity shown in the problem.
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
The physical width and energy levels represented by the graph are fields,
separate from the Boolean record of which labels are printed.
-/
structure RectangularBarrierFigure where
  axisQuantity : PlotAxis → PlotAxisQuantity
  axisHasPrintedLabel : PlotAxis → Bool
  annotationIsPrinted : FigureAnnotation → Bool
  potentialCurveShape : PotentialCurveShape
  barrierWidthShown : LengthQuantity
  barrierTopLevelShown : EnergyQuantity
  incidentEnergyLevelShown : EnergyQuantity

/-!
Independent physical quantities in the alpha-tunneling model.  In particular,
the attenuation wave number, exact tunneling probability, and opaque-barrier
estimate are independent fields.  The governing laws below constrain them
without defining any one of them to be a recorded answer value.
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
  opaqueBarrierEstimate : ℝ
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
image.  This premise contains no transmission probability or answer choice.
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

/-!
Numerical physical data in the prose and figure.  The final field states that
the incident level is the displayed deficit below the barrier top; it does not
state a transmission probability.
-/
structure MatchesProblemReadouts
    (setup : AlphaRectangularBarrierSetup) : Prop where
  alphaMassKilograms : massInKilograms setup.alphaMass = 6.64e-27
  barrierWidthFemtometers :
    lengthInFemtometers setup.barrierWidth = 2.0
  barrierHeightMegaElectronVolts :
    energyInMegaElectronVolts setup.barrierHeight = 30.0
  energyDeficitMegaElectronVolts :
    energyInMegaElectronVolts setup.energyBelowBarrierTop = 1.0
  energyLevelIsBelowTopByDeficit :
    energyInMegaElectronVolts setup.barrierHeight -
        energyInMegaElectronVolts setup.incidentKineticEnergy =
      energyInMegaElectronVolts setup.energyBelowBarrierTop

/-! The standard reduced Planck constant used by the numerical model. -/
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

/-! ## Exact finite-barrier coefficient and its controlled opaque limit -/

/-- The dimensionless barrier opacity `κ L` at the supplied finite width. -/
def barrierOpacity (setup : AlphaRectangularBarrierSetup) : ℝ :=
  waveNumberInInverseMeters setup.attenuationWaveNumber *
    lengthInMeters setup.barrierWidth

/-!
The exact transmission coefficient for a one-dimensional rectangular barrier
with equal exterior potentials, written as a function of the dimensionless
opacity `x = κ L`.  The physical branch assumptions `0 < E < U₀` are imposed
where this function is used as a law.
-/
def exactFiniteBarrierTransmission
    (incidentEnergy barrierHeight opacity : ℝ) : ℝ :=
  (1 +
    barrierHeight ^ 2 * Real.sinh opacity ^ 2 /
      (4 * incidentEnergy * (barrierHeight - incidentEnergy)))⁻¹

/-!
The leading opaque-barrier estimate, including the interface-matching
prefactor.  This is a named estimator, not the exact finite-opacity
probability.
-/
def opaqueBarrierTransmissionEstimate
    (incidentEnergy barrierHeight opacity : ℝ) : ℝ :=
  16 * (incidentEnergy / barrierHeight) *
    (1 - incidentEnergy / barrierHeight) * Real.exp (-2 * opacity)

/-!
For fixed energies `0 < E < U₀`, the exact rectangular-barrier coefficient is
asymptotically equivalent to the opaque-barrier estimate as `κ L → +∞`.
This is the precise large-opacity contract behind the approximation.
-/
lemma exactFiniteBarrierTransmission_isEquivalent_opaqueEstimate
    (incidentEnergy barrierHeight : ℝ)
    (h_incidentEnergy : 0 < incidentEnergy)
    (h_belowBarrier : incidentEnergy < barrierHeight) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun opacity : ℝ =>
        exactFiniteBarrierTransmission
          incidentEnergy barrierHeight opacity)
      (fun opacity : ℝ =>
        opaqueBarrierTransmissionEstimate
          incidentEnergy barrierHeight opacity) := by
  have h_barrier_ne : barrierHeight ≠ 0 :=
    ne_of_gt (lt_trans h_incidentEnergy h_belowBarrier)
  have h_gap_ne : barrierHeight - incidentEnergy ≠ 0 :=
    ne_of_gt (sub_pos.mpr h_belowBarrier)
  have h_exp :
      Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x))
        Filter.atTop (nhds 0) := by
    have h_two :
        Filter.Tendsto (fun x : ℝ => 2 * x)
          Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (by norm_num)
    have h_comp :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h_two
    convert h_comp using 1
    funext x
    congr 1
    ring
  let prefactor : ℝ :=
    16 * (incidentEnergy / barrierHeight) *
      (1 - incidentEnergy / barrierHeight)
  have h_denominator :
      Filter.Tendsto
        (fun x : ℝ =>
          prefactor * Real.exp (-2 * x) +
            (1 - Real.exp (-2 * x)) ^ 2)
        Filter.atTop (nhds 1) := by
    convert
      ((tendsto_const_nhds.mul h_exp).add
        ((tendsto_const_nhds.sub h_exp).pow 2)) using 1 <;>
      norm_num
  have h_inverse :
      Filter.Tendsto
        (fun x : ℝ =>
          (prefactor * Real.exp (-2 * x) +
            (1 - Real.exp (-2 * x)) ^ 2)⁻¹)
        Filter.atTop (nhds 1) := by
    convert h_denominator.inv₀ (by norm_num) using 1 <;>
      norm_num
  apply Asymptotics.isEquivalent_of_tendsto_one
  convert h_inverse using 1
  funext x
  dsimp [prefactor]
  unfold exactFiniteBarrierTransmission
    opaqueBarrierTransmissionEstimate
  rw [Real.sinh_eq]
  rw [show -2 * x = (-x) + (-x) by ring, Real.exp_add, Real.exp_neg]
  field_simp [ne_of_gt h_incidentEnergy, h_barrier_ne, h_gap_ne,
    Real.exp_ne_zero]
  ring

/-!
The exact finite-barrier physics and the separately named opaque-limit
estimate used for the recorded multiple-choice computation.

* In the classically forbidden region,
  `ℏ² κ² = 2 m (U₀ - E)`.
* The physical finite-width probability is the exact hyperbolic-sine
  coefficient.
* The opaque estimate is the leading asymptotic expression
  `16 (E/U₀) (1-E/U₀) exp(-2 κ L)`.

Every term is an SI readout of a dimensionally typed quantity except the
dimensionless ratios, exponent, and probability.  Neither law contains the
numbers `0.090` or `0.116`, nor a displayed answer label.
-/
structure ObeysFiniteRectangularBarrierTunneling
    (setup : AlphaRectangularBarrierSetup) : Prop where
  attenuationWaveNumberLaw :
    actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
        waveNumberInInverseMeters setup.attenuationWaveNumber ^ 2 =
      2 * massInKilograms setup.alphaMass *
        (energyInJoules setup.barrierHeight -
          energyInJoules setup.incidentKineticEnergy)
  exactFiniteBarrierTransmissionLaw :
    setup.tunnelingProbability =
      exactFiniteBarrierTransmission
        (energyInJoules setup.incidentKineticEnergy)
        (energyInJoules setup.barrierHeight)
        (barrierOpacity setup)
  opaqueBarrierEstimateLaw :
    setup.opaqueBarrierEstimate =
      opaqueBarrierTransmissionEstimate
        (energyInJoules setup.incidentKineticEnergy)
        (energyInJoules setup.barrierHeight)
        (barrierOpacity setup)

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
  | .A => 0.065
  | .B => 0.042
  | .C => 0.084
  | .D => 0.090

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
`value` rounds to `reported` at three decimal places.  The half-open interval
implements ordinary nearest-thousandth rounding away from the upper tie.
-/
def RoundsToThreeDecimalPlaces (value reported : ℝ) : Prop :=
  reported - (1 : ℝ) / 2000 ≤ value ∧
    value < reported + (1 : ℝ) / 2000

/-- A displayed choice agrees with a supplied probability to three decimals. -/
def MatchesDisplayedTunnelingProbability
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  RoundsToThreeDecimalPlaces probability
    (displayedTunnelingProbability choice)

/-- A choice is the unique displayed value matching the modeled probability. -/
def IsUniqueMatchingTunnelingChoice
    (probability : ℝ) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedTunnelingProbability probability choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedTunnelingProbability probability other → other = choice

/-- No source choice rounds to the supplied probability at three decimals. -/
def NoDisplayedTunnelingChoiceMatches (probability : ℝ) : Prop :=
  ∀ choice : AnswerChoice,
    ¬ MatchesDisplayedTunnelingProbability probability choice

/-- The displayed energy separation implies an incident energy of `29 MeV`. -/
lemma incident_kinetic_energy_megaelectronvolts_eq
    (setup : AlphaRectangularBarrierSetup)
    (h_readouts : MatchesProblemReadouts setup) :
    energyInMegaElectronVolts setup.incidentKineticEnergy = 29 := by
  linarith [h_readouts.barrierHeightMegaElectronVolts,
    h_readouts.energyDeficitMegaElectronVolts,
    h_readouts.energyLevelIsBelowTopByDeficit]

/-!
The source data put the opacity at about `0.875`, so this finite barrier is not
in a quantitatively large-opacity regime.
-/
lemma barrier_opacity_rounds_to_0_875
    (setup : AlphaRectangularBarrierSetup)
    (h_physical : HasPhysicalTunnelingParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_reference : UsesStandardReducedPlanckConstant setup)
    (h_laws : ObeysFiniteRectangularBarrierTunneling setup) :
    RoundsToThreeDecimalPlaces (barrierOpacity setup) 0.875 := by
  have length_meter_femtometer (x : LengthQuantity) :
      lengthInMeters x = lengthInFemtometers x / 10 ^ 15 := by
    have h_ratio :
        ((UnitChoices.SI.length / LengthUnit.femtometers : NNReal) : ℝ) =
          10 ^ 15 := by
      rw [LengthUnit.div_eq_val]
      norm_num [LengthUnit.femtometers, LengthUnit.scale,
        LengthUnit.meters, UnitChoices.SI, NNReal.toReal]
    have h_scale :
        UnitChoices.SI.dimScale
            {UnitChoices.SI with length := LengthUnit.femtometers} L𝓭 =
          (1000000000000000 : NNReal) := by
      rw [UnitChoices.dimScale_apply]
      simp only [L𝓭, Rat.cast_one, Rat.cast_zero, NNReal.rpow_one,
        NNReal.rpow_zero, mul_one]
      exact_mod_cast h_ratio
    have h := congrArg (fun y : WithDim L𝓭 NNReal => (y.val : ℝ))
      (x.property UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.femtometers})
    simp only [WithDim.dim_apply, WithDim.smul_val] at h
    rw [h_scale] at h
    change
      lengthInFemtometers x =
        1000000000000000 * lengthInMeters x at h
    norm_num at h ⊢
    linarith
  have energy_joule_megaelectronvolt (x : EnergyQuantity) :
      energyInJoules x =
        1.602176634e-13 * energyInMegaElectronVolts x := by
    simp [energyInJoules, energyInMegaElectronVolts,
      energyInElectronVolts, DimEnergy.joule, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
    ring
  have h_mass :
      massInKilograms setup.alphaMass = 6.64e-27 :=
    h_readouts.alphaMassKilograms
  have h_width :
      lengthInMeters setup.barrierWidth = 2e-15 := by
    rw [length_meter_femtometer,
      h_readouts.barrierWidthFemtometers]
    norm_num
  have h_gap_mev :
      energyInMegaElectronVolts setup.barrierHeight -
          energyInMegaElectronVolts setup.incidentKineticEnergy =
        1 := by
    rw [h_readouts.energyLevelIsBelowTopByDeficit,
      h_readouts.energyDeficitMegaElectronVolts]
    norm_num
  have h_gap_joule :
      energyInJoules setup.barrierHeight -
          energyInJoules setup.incidentKineticEnergy =
        1.602176634e-13 := by
    rw [energy_joule_megaelectronvolt,
      energy_joule_megaelectronvolt]
    nlinarith
  have h_planck :
      actionInJouleSeconds setup.reducedPlanckAction =
        1.054571817e-34 := by
    rw [h_reference.reducedPlanckActionJouleSeconds]
    rfl
  have h_wave := h_laws.attenuationWaveNumberLaw
  rw [h_planck, h_mass, h_gap_joule] at h_wave
  have h_opacity_pos : 0 < barrierOpacity setup := by
    exact mul_pos h_physical.positiveAttenuationWaveNumber
      h_physical.positiveWidth
  unfold RoundsToThreeDecimalPlaces
  constructor
  · unfold barrierOpacity at h_opacity_pos ⊢
    rw [h_width] at h_opacity_pos ⊢
    norm_num at h_wave ⊢
    nlinarith [h_wave]
  · unfold barrierOpacity at h_opacity_pos ⊢
    rw [h_width] at h_opacity_pos ⊢
    norm_num at h_wave ⊢
    nlinarith [h_wave]

/-!
The exact finite rectangular-barrier coefficient is about `0.116072`; it
rounds to `0.116`, which is absent from the four displayed choices.
-/
lemma exact_tunneling_probability_rounds_to_0_116
    (setup : AlphaRectangularBarrierSetup)
    (h_physical : HasPhysicalTunnelingParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_reference : UsesStandardReducedPlanckConstant setup)
    (h_laws : ObeysFiniteRectangularBarrierTunneling setup) :
    RoundsToThreeDecimalPlaces setup.tunnelingProbability 0.116 := by
  have energy_joule_megaelectronvolt (x : EnergyQuantity) :
      energyInJoules x =
        1.602176634e-13 * energyInMegaElectronVolts x := by
    simp [energyInJoules, energyInMegaElectronVolts,
      energyInElectronVolts, DimEnergy.joule, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
    ring
  have h_incident_mev :
      energyInMegaElectronVolts setup.incidentKineticEnergy = 29 :=
    incident_kinetic_energy_megaelectronvolts_eq setup h_readouts
  have h_incident_joule :
      energyInJoules setup.incidentKineticEnergy =
        29 * 1.602176634e-13 := by
    rw [energy_joule_megaelectronvolt, h_incident_mev]
    ring
  have h_barrier_joule :
      energyInJoules setup.barrierHeight =
        30 * 1.602176634e-13 := by
    rw [energy_joule_megaelectronvolt,
      h_readouts.barrierHeightMegaElectronVolts]
    norm_num
  have h_opacity :=
    barrier_opacity_rounds_to_0_875 setup h_physical h_readouts
      h_reference h_laws
  rcases h_opacity with ⟨h_opacity_lower, h_opacity_upper⟩
  norm_num at h_opacity_lower h_opacity_upper
  have h_sinh_endpoint_lower :
      (0.99 : ℝ) ≤ Real.sinh 0.8745 := by
    calc
      (0.99 : ℝ) ≤
          ∑ n ∈ Finset.range 3,
            (0.8745 : ℝ) ^ (2 * n + 1) /
              ((2 * n + 1).factorial : ℝ) := by
        norm_num [Finset.sum_range_succ]
      _ ≤ Real.sinh 0.8745 := by
        rw [Real.sinh_eq_tsum]
        exact Summable.sum_le_tsum (Finset.range 3)
          (fun i _ => by positivity)
          (Real.hasSum_sinh 0.8745).summable
  have h_sinh_endpoint_upper :
      Real.sinh 0.8755 ≤ (0.993 : ℝ) := by
    have h_exp_pos :=
      Real.exp_bound (x := (0.8755 : ℝ)) (n := 10)
        (by norm_num) (by norm_num)
    have h_exp_neg :=
      Real.exp_bound (x := (-0.8755 : ℝ)) (n := 10)
        (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h_exp_pos h_exp_neg
    rw [Real.sinh_eq]
    nlinarith [abs_le.mp h_exp_pos, abs_le.mp h_exp_neg]
  have h_sinh_lower :
      (0.99 : ℝ) ≤ Real.sinh (barrierOpacity setup) := by
    norm_num at h_sinh_endpoint_lower ⊢
    exact h_sinh_endpoint_lower.trans
      (Real.sinh_le_sinh.mpr h_opacity_lower)
  have h_sinh_upper :
      Real.sinh (barrierOpacity setup) ≤ (0.993 : ℝ) := by
    norm_num at h_sinh_endpoint_upper ⊢
    exact (Real.sinh_le_sinh.mpr (le_of_lt h_opacity_upper)).trans
      h_sinh_endpoint_upper
  have h_sinh_sq_lower :
      (0.99 : ℝ) * 0.99 ≤
        Real.sinh (barrierOpacity setup) *
          Real.sinh (barrierOpacity setup) :=
    mul_self_le_mul_self (by norm_num) h_sinh_lower
  have h_sinh_sq_upper :
      Real.sinh (barrierOpacity setup) *
          Real.sinh (barrierOpacity setup) ≤
        (0.993 : ℝ) * 0.993 :=
    mul_self_le_mul_self
      (le_trans (by norm_num) h_sinh_lower) h_sinh_upper
  have h_probability := h_laws.exactFiniteBarrierTransmissionLaw
  rw [h_incident_joule, h_barrier_joule] at h_probability
  norm_num [exactFiniteBarrierTransmission] at h_probability
  unfold RoundsToThreeDecimalPlaces
  rw [h_probability]
  constructor
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [h_sinh_sq_upper]
  · rw [inv_eq_one_div]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [h_sinh_sq_lower]

/-!
The leading opaque-barrier estimate is about `0.089626`; unlike the exact
finite-barrier probability, this estimate rounds to the source value `0.090`.
-/
lemma opaque_barrier_estimate_rounds_to_0_090
    (setup : AlphaRectangularBarrierSetup)
    (h_physical : HasPhysicalTunnelingParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_reference : UsesStandardReducedPlanckConstant setup)
    (h_laws : ObeysFiniteRectangularBarrierTunneling setup) :
    RoundsToThreeDecimalPlaces setup.opaqueBarrierEstimate 0.090 := by
  have energy_joule_megaelectronvolt (x : EnergyQuantity) :
      energyInJoules x =
        1.602176634e-13 * energyInMegaElectronVolts x := by
    simp [energyInJoules, energyInMegaElectronVolts,
      energyInElectronVolts, DimEnergy.joule, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
    ring
  have h_incident_mev :
      energyInMegaElectronVolts setup.incidentKineticEnergy = 29 :=
    incident_kinetic_energy_megaelectronvolts_eq setup h_readouts
  have h_incident_joule :
      energyInJoules setup.incidentKineticEnergy =
        29 * 1.602176634e-13 := by
    rw [energy_joule_megaelectronvolt, h_incident_mev]
    ring
  have h_barrier_joule :
      energyInJoules setup.barrierHeight =
        30 * 1.602176634e-13 := by
    rw [energy_joule_megaelectronvolt,
      h_readouts.barrierHeightMegaElectronVolts]
    norm_num
  have h_opacity :=
    barrier_opacity_rounds_to_0_875 setup h_physical h_readouts
      h_reference h_laws
  rcases h_opacity with ⟨h_opacity_lower, h_opacity_upper⟩
  norm_num at h_opacity_lower h_opacity_upper
  have h_exp_endpoint_lower :
      (0.4166536 : ℝ) ≤ Real.exp (-0.8755) := by
    have h_exp :=
      Real.exp_bound (x := (-0.8755 : ℝ)) (n := 12)
        (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h_exp
    nlinarith [abs_le.mp h_exp]
  have h_exp_endpoint_upper :
      Real.exp (-0.8745) ≤ (0.418 : ℝ) := by
    have h_exp :=
      Real.exp_bound (x := (-0.8745 : ℝ)) (n := 10)
        (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h_exp
    nlinarith [abs_le.mp h_exp]
  have h_exp_lower :
      (0.4166536 : ℝ) ≤ Real.exp (-(barrierOpacity setup)) := by
    norm_num at h_exp_endpoint_lower ⊢
    exact h_exp_endpoint_lower.trans
      (le_of_lt (Real.exp_lt_exp.mpr (neg_lt_neg h_opacity_upper)))
  have h_exp_upper :
      Real.exp (-(barrierOpacity setup)) ≤ (0.418 : ℝ) := by
    norm_num at h_exp_endpoint_upper ⊢
    exact (Real.exp_le_exp.mpr (neg_le_neg h_opacity_lower)).trans
      h_exp_endpoint_upper
  have h_exp_sq_lower :
      (0.4166536 : ℝ) * 0.4166536 ≤
        Real.exp (-(barrierOpacity setup)) *
          Real.exp (-(barrierOpacity setup)) :=
    mul_self_le_mul_self (by norm_num) h_exp_lower
  have h_exp_sq_upper :
      Real.exp (-(barrierOpacity setup)) *
          Real.exp (-(barrierOpacity setup)) ≤
        (0.418 : ℝ) * 0.418 :=
    mul_self_le_mul_self (le_of_lt (Real.exp_pos _)) h_exp_upper
  have h_estimate := h_laws.opaqueBarrierEstimateLaw
  rw [h_incident_joule, h_barrier_joule] at h_estimate
  norm_num [opaqueBarrierTransmissionEstimate] at h_estimate
  rw [show -(2 * barrierOpacity setup) =
      (-(barrierOpacity setup)) + (-(barrierOpacity setup)) by ring,
    Real.exp_add] at h_estimate
  unfold RoundsToThreeDecimalPlaces
  rw [h_estimate]
  constructor
  · nlinarith [h_exp_sq_lower]
  · nlinarith [h_exp_sq_upper]

/-!
For the alpha mass `6.64 × 10⁻²⁷ kg`, width `2.0 fm`, height `30.0 MeV`,
and incident energy `1.0 MeV` below the top, the exact finite rectangular-
barrier coefficient rounds to `0.116`.  None of the supplied choices matches
that physical probability.  The separately identified opaque-limit estimate
rounds to `0.090` and uniquely explains the dataset's recorded choice D, even
though the computed opacity is only about `0.875`.

This formalizes `thm:physics:phyx_mini_0520:target`.  None of the numerical
conclusions, their rounding intervals, the no-choice conclusion, or choice D
occurs in any scenario, figure, calibration, positivity, or governing-law
premise.
-/
theorem problem_phyx_mini_0520
    (setup : AlphaRectangularBarrierSetup)
    (h_scenario : MatchesAlphaNucleusScenario setup)
    (h_figure : MatchesSuppliedBarrierFigure setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_reference : UsesStandardReducedPlanckConstant setup)
    (h_barrier : MatchesPhyslibRectangularBarrier setup)
    (h_physical : HasPhysicalTunnelingParameters setup)
    (h_laws : ObeysFiniteRectangularBarrierTunneling setup) :
    energyInMegaElectronVolts setup.incidentKineticEnergy = 29 ∧
      RoundsToThreeDecimalPlaces (barrierOpacity setup) 0.875 ∧
      RoundsToThreeDecimalPlaces setup.tunnelingProbability 0.116 ∧
      NoDisplayedTunnelingChoiceMatches setup.tunnelingProbability ∧
      RoundsToThreeDecimalPlaces setup.opaqueBarrierEstimate 0.090 ∧
      IsUniqueMatchingTunnelingChoice setup.opaqueBarrierEstimate .D := by
  clear h_scenario h_figure h_barrier
  have h_incident :=
    incident_kinetic_energy_megaelectronvolts_eq setup h_readouts
  have h_opacity :=
    barrier_opacity_rounds_to_0_875 setup h_physical h_readouts
      h_reference h_laws
  have h_exact :=
    exact_tunneling_probability_rounds_to_0_116 setup h_physical
      h_readouts h_reference h_laws
  have h_opaque :=
    opaque_barrier_estimate_rounds_to_0_090 setup h_physical
      h_readouts h_reference h_laws
  refine ⟨h_incident, h_opacity, h_exact, ?_, h_opaque, ?_⟩
  · unfold NoDisplayedTunnelingChoiceMatches
    intro choice h_choice
    unfold MatchesDisplayedTunnelingProbability at h_choice
    cases choice <;>
      norm_num [RoundsToThreeDecimalPlaces,
        displayedTunnelingProbability] at h_choice h_exact <;>
      linarith
  · unfold IsUniqueMatchingTunnelingChoice
    constructor
    · simpa [MatchesDisplayedTunnelingProbability,
        displayedTunnelingProbability] using h_opaque
    · intro other h_other
      cases other with
      | A =>
          exfalso
          norm_num [MatchesDisplayedTunnelingProbability,
            RoundsToThreeDecimalPlaces,
            displayedTunnelingProbability] at h_other h_opaque
          linarith
      | B =>
          exfalso
          norm_num [MatchesDisplayedTunnelingProbability,
            RoundsToThreeDecimalPlaces,
            displayedTunnelingProbability] at h_other h_opaque
          linarith
      | C =>
          exfalso
          norm_num [MatchesDisplayedTunnelingProbability,
            RoundsToThreeDecimalPlaces,
            displayedTunnelingProbability] at h_other h_opaque
          linarith
      | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0520
