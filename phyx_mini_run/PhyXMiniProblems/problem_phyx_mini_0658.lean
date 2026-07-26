import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0658

open Dimension

/-!
# Four lowest vibrations of an aluminum ion in a one-dimensional lattice

The supplied figure shows three positive ions on one horizontal line.  Both
adjacent separations are labelled `b`, and a double-headed arrow over the
middle ion depicts its one-dimensional vibration.  The model below treats the
two outer ions as the nearest neighbors of that vibrating ion.

Mass, charge, length, effective spring constant, and vibrational energy are
unit-independent Physlib quantities.  Real numbers occur only at explicitly
named unit-readout boundaries, in Physlib's scalar oscillator APIs, and in the
printed answer-choice values.

The exact two-neighbor Coulomb force and its linearization are governing laws.
The effective spring-constant formula is stated separately as a derived lemma.
The numerical answer and the identification of choice C occur only in the
conclusion of the blueprint-target theorem.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The dimension of a spring constant, `N/m = kg/s²`. -/
def springConstantDimension : Dimension := M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent effective spring constant. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim springConstantDimension NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Read a charge magnitude in a selected Physlib charge unit. -/
def chargeReadout
    (unit : ChargeUnit) (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge {UnitChoices.SI with charge := unit}).val : ℝ)

/-- Coherent-SI coulomb readout of a physical charge magnitude. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeReadout ChargeUnit.coulombs charge

/-- Read a charge magnitude as a multiple of the elementary charge `e`. -/
def chargeInElementaryCharges (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeReadout ChargeUnit.elementaryCharge charge

/-- Coherent-SI `N/m` readout of an effective spring constant. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-- Coherent-SI joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- The joule value of Physlib's dimensionful electron volt. -/
def electronVoltInJoules : ℝ :=
  energyInJoules DimEnergy.electronVolt

/-- Electron-volt readout of a physical energy. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / electronVoltInJoules

/-! ## Physical roles and literal figure vocabulary -/

/-- The three positive ions displayed in the primary figure. -/
inductive IonSite where
  | left
  | center
  | right
  deriving DecidableEq, Fintype, Repr

/-- The two adjacent gaps whose distances are both labelled `b`. -/
inductive AdjacentGap where
  | leftCenter
  | centerRight
  deriving DecidableEq, Fintype, Repr

/-- The literal symbolic distance label visible under each gap arrow. -/
inductive FigureDistanceLabel where
  | b
  deriving DecidableEq, Fintype, Repr

/-- Atomic species needed by the physical scenario. -/
inductive IonSpecies where
  | aluminum
  | other
  deriving DecidableEq, Repr

/-- Literal presentation data from image 658. -/
structure CrystalLatticeFigure where
  ionShown : IonSite → Bool
  positiveSignShown : IonSite → Bool
  centersAreHorizontallyCollinear : Bool
  gapHasDoubleHeadedArrow : AdjacentGap → Bool
  gapLabel : AdjacentGap → FigureDistanceLabel
  middleIonHasBidirectionalMotionArrow : Bool

/-!
Physical data for the displayed lattice cell and the vibrating middle ion.
The map `vibrationalEnergy` stores the energy observable at each quantum level;
it is not defined from any answer choice.
-/
structure AluminumIonLatticeSetup where
  ionSpecies : IonSpecies
  ionMass : MassQuantity
  ionChargeMagnitude : ChargeMagnitudeQuantity
  equilibriumSpacing : LengthQuantity
  adjacentSeparation : AdjacentGap → LengthQuantity
  effectiveSpringConstant : SpringConstantQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  classicalOscillator : ClassicalMechanics.HarmonicOscillator
  quantumOscillator : QuantumMechanics.OneDimension.HarmonicOscillator
  vibrationalEnergy : ℕ → DimEnergy
  netNeighborForceNewtons : ℝ → ℝ
  regularOneDimensionalLattice : Bool
  conductionElectronSeaPresent : Bool
  figure : CrystalLatticeFigure

/-! ## Scenario, primary-figure evidence, and reference data -/

/-- The material and spacing stated in the problem source. -/
structure MatchesAluminumCrystalScenario
    (setup : AluminumIonLatticeSetup) : Prop where
  speciesIsAluminum : setup.ionSpecies = .aluminum
  regularOneDimensionalModel : setup.regularOneDimensionalLattice = true
  conductionElectronSea : setup.conductionElectronSeaPresent = true
  ionChargeIsPositiveElementaryCharge :
    chargeInElementaryCharges setup.ionChargeMagnitude = 1
  statedEquilibriumSpacingNanometers :
    lengthInNanometers setup.equilibriumSpacing = 3 / 10

/--
All unambiguous geometric and charge evidence read from the primary image.
The image supplies no energy value.
-/
structure MatchesPrimaryLatticeFigure
    (setup : AluminumIonLatticeSetup) : Prop where
  everyIonShown : ∀ site, setup.figure.ionShown site = true
  everyIonHasPositiveSign :
    ∀ site, setup.figure.positiveSignShown site = true
  centersAreCollinear :
    setup.figure.centersAreHorizontallyCollinear = true
  bothGapArrowsShown :
    ∀ gap, setup.figure.gapHasDoubleHeadedArrow gap = true
  bothGapLabelsAreB : ∀ gap, setup.figure.gapLabel gap = .b
  bothPhysicalGapsEqualB :
    ∀ gap, setup.adjacentSeparation gap = setup.equilibriumSpacing
  middleIonVibrationArrowShown :
    setup.figure.middleIonHasBidirectionalMotionArrow = true

/-!
Rounded independent constants used by the textbook numerical estimate.
The mass `4.5 × 10⁻²⁶ kg` is the usual two-significant-figure aluminum-ion
mass, and `9 × 10⁹ N m²/C²` is the corresponding rounded Coulomb constant.
-/
structure UsesRoundedAluminumReferenceData
    (setup : AluminumIonLatticeSetup) : Prop where
  aluminumIonMassKilograms :
    massInKilograms setup.ionMass = 4.5e-26
  vacuumCoulombConstant :
    setup.electromagneticSystem.coulombConstant = 9e9

/-! ## Governing electrostatic, harmonic, and quantum laws -/

/-!
For a signed displacement `x` of the middle ion, the left neighbor contributes
a force toward the right and the right neighbor contributes a force toward
the left.  Their exact one-dimensional Coulomb-force difference is valid in
the open interval `|x| < b`.  The derivative at equilibrium defines the
negative effective spring constant.  Neither clause contains a vibrational
energy or an answer-choice value.
-/
structure SatisfiesTwoNeighborCoulombLaw
    (setup : AluminumIonLatticeSetup) : Prop where
  exactNeighborForce : ∀ x : ℝ,
    |x| < lengthInMeters setup.equilibriumSpacing →
      setup.netNeighborForceNewtons x =
        setup.electromagneticSystem.coulombConstant *
          (chargeInCoulombs setup.ionChargeMagnitude) ^ 2 *
          (1 / (lengthInMeters setup.equilibriumSpacing + x) ^ 2 -
            1 / (lengthInMeters setup.equilibriumSpacing - x) ^ 2)
  linearizationDefinesSpringConstant :
    deriv setup.netNeighborForceNewtons 0 =
      -springConstantInNewtonsPerMeter setup.effectiveSpringConstant

/-!
The dimensionful mass and spring constant are supplied to Physlib's classical
oscillator through coherent-SI readouts.  Its frequency is then the frequency
of Physlib's quantum oscillator for the middle ion.
-/
structure RealizesSmallOscillationModel
    (setup : AluminumIonLatticeSetup) : Prop where
  classicalMassReadout :
    setup.classicalOscillator.m = massInKilograms setup.ionMass
  classicalSpringReadout :
    setup.classicalOscillator.k =
      springConstantInNewtonsPerMeter setup.effectiveSpringConstant
  quantumMassReadout :
    setup.quantumOscillator.m = massInKilograms setup.ionMass
  sameAngularFrequency :
    setup.quantumOscillator.ω = setup.classicalOscillator.ω

/-!
The time-independent Schrödinger eigenstate law for the dimensionful energy
observable.  This governing equation does not assume the closed-form
eigenvalue, any of the requested energy readouts, or a multiple-choice option.
Physlib independently proves the same equation with
`quantumOscillator.eigenValue n` as its coefficient; comparing the two
equations is the later proof route to the energy formula.
-/
structure SatisfiesVibrationalSchrodingerEquation
    (setup : AluminumIonLatticeSetup) : Prop where
  stationaryStateEquation : ∀ (n : ℕ) (x : ℝ),
    setup.quantumOscillator.schrodingerOperator
        (setup.quantumOscillator.eigenfunction n) x =
      (energyInJoules (setup.vibrationalEnergy n) : ℂ) *
        setup.quantumOscillator.eigenfunction n x

/-!
The exact effective spring constant obtained by differentiating the two-neighbor
Coulomb force at the equilibrium position.
-/
theorem effectiveSpringConstant_eq_coulombLinearization
    (setup : AluminumIonLatticeSetup)
    (hScenario : MatchesAluminumCrystalScenario setup)
    (hCoulomb : SatisfiesTwoNeighborCoulombLaw setup) :
    springConstantInNewtonsPerMeter setup.effectiveSpringConstant =
      4 * setup.electromagneticSystem.coulombConstant *
        (chargeInCoulombs setup.ionChargeMagnitude) ^ 2 /
        (lengthInMeters setup.equilibriumSpacing) ^ 3 := by
  have hb_nm := hScenario.statedEquilibriumSpacingNanometers
  norm_num [lengthInNanometers, lengthReadout, LengthUnit.nanometers,
    LengthUnit.scale] at hb_nm
  have hb_scale := congrArg (fun z : WithDim L𝓭 NNReal => (z.val : ℝ))
    (setup.equilibriumSpacing.property
      {UnitChoices.SI with length := LengthUnit.nanometers} UnitChoices.SI)
  norm_num [UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.scale,
    LengthUnit.div_eq_val] at hb_scale
  rw [hb_nm] at hb_scale
  have hb : lengthInMeters setup.equilibriumSpacing = 3 / 10000000000 := by
    calc
      _ = ((setup.equilibriumSpacing UnitChoices.SI).val : ℝ) := rfl
      _ = _ := by
        rw [hb_scale]
        change (1 / 1000000000 : ℝ) * (3 / 10) = _
        norm_num
  have hb_pos : 0 < lengthInMeters setup.equilibriumSpacing := by
    rw [hb]
    norm_num
  let b : ℝ := lengthInMeters setup.equilibriumSpacing
  have hb0 : b ≠ 0 := (show 0 < b from hb_pos).ne'
  have hplus : HasDerivAt (fun x : ℝ => b + x) 1 0 :=
    (hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).const_add b
  have hminus : HasDerivAt (fun x : ℝ => b - x) (-1) 0 :=
    (hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).const_sub b
  have hrat := ((hplus.pow 2).inv (by simp [hb0])).sub
    ((hminus.pow 2).inv (by simp [hb0]))
  have hfun : (fun x : ℝ => 1 / (b + x) ^ 2 - 1 / (b - x) ^ 2) =
      (((fun x : ℝ => b + x) ^ 2)⁻¹ - ((fun x : ℝ => b - x) ^ 2)⁻¹) := by
    ext x
    simp only [Pi.pow_apply, Pi.inv_apply, Pi.sub_apply, one_div]
  have hcoef : (-4 / b ^ 3 : ℝ) =
      (-(2 * (b + 0) ^ (2 - 1) * 1) /
          (((fun x : ℝ => b + x) ^ 2) 0) ^ 2 -
       -(2 * (b - 0) ^ (2 - 1) * (-1)) /
          (((fun x : ℝ => b - x) ^ 2) 0) ^ 2) := by
    norm_num [Pi.pow_apply]
    field_simp [hb0]
    ring
  have hrat' : HasDerivAt
      (fun x : ℝ => 1 / (b + x) ^ 2 - 1 / (b - x) ^ 2)
      (-4 / b ^ 3) 0 := by
    rw [hfun, hcoef]
    exact hrat
  let C : ℝ := setup.electromagneticSystem.coulombConstant *
    chargeInCoulombs setup.ionChargeMagnitude ^ 2
  have hg := hrat'.const_mul C
  have hEq : setup.netNeighborForceNewtons =ᶠ[nhds 0]
      (fun x : ℝ => C * (1 / (b + x) ^ 2 - 1 / (b - x) ^ 2)) := by
    filter_upwards [Ioo_mem_nhds
        (neg_lt_zero.mpr (show 0 < b from hb_pos))
        (show 0 < b from hb_pos)] with x hx
    exact hCoulomb.exactNeighborForce x (abs_lt.mpr hx)
  have hd : deriv setup.netNeighborForceNewtons 0 = C * (-4 / b ^ 3) := by
    calc
      _ = deriv
          (fun x : ℝ => C * (1 / (b + x) ^ 2 - 1 / (b - x) ^ 2)) 0 :=
        hEq.deriv_eq
      _ = _ := hg.deriv
  rw [hCoulomb.linearizationDefinesSpringConstant] at hd
  dsimp [C, b] at hd ⊢
  field_simp [hb0] at hd ⊢
  linarith

/-! ## Four-level readout and multiple-choice target -/

/-- The oscillator quantum `ℏω`, expressed in electron volts. -/
def energyQuantumInElectronVolts (setup : AluminumIonLatticeSetup) : ℝ :=
  (Constants.ℏ : ℝ) * setup.quantumOscillator.ω / electronVoltInJoules

/-- The four answer choices printed in the problem source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The electron-volt number printed beside an answer choice. -/
def answerChoiceEnergyElectronVolts : AnswerChoice → ℝ
  | .A => 428 / 10000
  | .B => 531 / 10000
  | .C => 634 / 10000
  | .D => 832 / 10000

/-- Numerical tolerance appropriate to the rounded textbook input data. -/
def answerAgreementToleranceElectronVolts : ℝ := 1 / 1000

/-!
A generic criterion saying that a printed value agrees, to the stated
tolerance, with the fourth-lowest level (`n = 3`).  It does not privilege C.
-/
def AnswerChoice.agreesWithFourthLevel
    (choice : AnswerChoice) (setup : AluminumIonLatticeSetup) : Prop :=
  |energyInElectronVolts (setup.vibrationalEnergy 3) -
      answerChoiceEnergyElectronVolts choice| ≤
    answerAgreementToleranceElectronVolts

/-!
**Blueprint target** `thm:physics:phyx_mini_0658:target`.

The first conjunct gives all four lowest energy readouts (`n = 0,1,2,3`) in
the quantum-harmonic-oscillator form.  The second records their strict order.
The remaining conjuncts state that the displayed value `0.0634 eV` (choice C)
is compatible with the rounded aluminum-lattice calculation and is the unique
compatible printed option.
-/
theorem aluminum_ion_four_lowest_vibrational_energies
    (setup : AluminumIonLatticeSetup)
    (hScenario : MatchesAluminumCrystalScenario setup)
    (hFigure : MatchesPrimaryLatticeFigure setup)
    (hReference : UsesRoundedAluminumReferenceData setup)
    (hCoulomb : SatisfiesTwoNeighborCoulombLaw setup)
    (hOscillator : RealizesSmallOscillationModel setup)
    (hQuantum : SatisfiesVibrationalSchrodingerEquation setup) :
    (∀ i : Fin 4,
      energyInElectronVolts (setup.vibrationalEnergy i.1) =
        ((i.1 : ℝ) + 1 / 2) * energyQuantumInElectronVolts setup) ∧
    (∀ i j : Fin 4, i < j →
      energyInJoules (setup.vibrationalEnergy i.1) <
        energyInJoules (setup.vibrationalEnergy j.1)) ∧
    AnswerChoice.C.agreesWithFourthLevel setup ∧
    (∀ choice : AnswerChoice,
      choice.agreesWithFourthLevel setup → choice = .C) := by
  have hEnergyJ (n : ℕ) :
      energyInJoules (setup.vibrationalEnergy n) =
        setup.quantumOscillator.eigenValue n := by
    have hne : setup.quantumOscillator.eigenfunction n ≠ 0 := by
      intro hz
      have hn := setup.quantumOscillator.eigenfunction_normalized n
      rw [QuantumMechanics.OneDimension.HilbertSpace.inner_mk_mk] at hn
      simp only [hz, Pi.zero_apply, map_zero, zero_mul,
        MeasureTheory.integral_zero] at hn
      exact zero_ne_one hn
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
    have hmul := (hQuantum.stationaryStateEquation n x).symm.trans
      (setup.quantumOscillator.schrodingerOperator_eigenfunction n x)
    exact_mod_cast (mul_right_cancel₀ hx hmul)
  have heV : electronVoltInJoules = 1.602176634e-19 := by
    norm_num [electronVoltInJoules, energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale]
  have hb_nm := hScenario.statedEquilibriumSpacingNanometers
  norm_num [lengthInNanometers, lengthReadout, LengthUnit.nanometers,
    LengthUnit.scale] at hb_nm
  have hb_scale := congrArg (fun z : WithDim L𝓭 NNReal => (z.val : ℝ))
    (setup.equilibriumSpacing.property
      {UnitChoices.SI with length := LengthUnit.nanometers} UnitChoices.SI)
  norm_num [UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.scale,
    LengthUnit.div_eq_val] at hb_scale
  rw [hb_nm] at hb_scale
  have hb : lengthInMeters setup.equilibriumSpacing = 3 / 10000000000 := by
    calc
      _ = ((setup.equilibriumSpacing UnitChoices.SI).val : ℝ) := rfl
      _ = _ := by
        rw [hb_scale]
        change (1 / 1000000000 : ℝ) * (3 / 10) = _
        norm_num
  have hq_e := hScenario.ionChargeIsPositiveElementaryCharge
  norm_num [chargeInElementaryCharges, chargeReadout,
    ChargeUnit.elementaryCharge, ChargeUnit.scale] at hq_e
  have hq_scale := congrArg (fun z : WithDim C𝓭 NNReal => (z.val : ℝ))
    (setup.ionChargeMagnitude.property
      {UnitChoices.SI with charge := ChargeUnit.elementaryCharge} UnitChoices.SI)
  norm_num [UnitChoices.dimScale, ChargeUnit.elementaryCharge, ChargeUnit.scale,
    ChargeUnit.div_eq_val] at hq_scale
  rw [hq_e] at hq_scale
  norm_num [C𝓭] at hq_scale
  have hq : chargeInCoulombs setup.ionChargeMagnitude = 1.602176634e-19 := by
    calc
      _ = ((setup.ionChargeMagnitude UnitChoices.SI).val : ℝ) := rfl
      _ = _ := by
        rw [hq_scale]
        change (801088317 / 5000000000000000000000000000 : ℝ) = _
        norm_num
  have hk :=
    effectiveSpringConstant_eq_coulombLinearization setup hScenario hCoulomb
  rw [hReference.vacuumCoulombConstant, hq, hb] at hk
  norm_num at hk
  have hωsq :
      setup.quantumOscillator.ω ^ 2 = 760583693788317024000000000 := by
    rw [hOscillator.sameAngularFrequency]
    rw [setup.classicalOscillator.ω_sq,
      hOscillator.classicalSpringReadout, hOscillator.classicalMassReadout,
      hk, hReference.aluminumIonMassKilograms]
    norm_num
  have hωlower : (27578600000000 : ℝ) < setup.quantumOscillator.ω := by
    nlinarith [setup.quantumOscillator.ω_pos]
  have hωupper : setup.quantumOscillator.ω < (27578700000000 : ℝ) := by
    nlinarith [setup.quantumOscillator.ω_pos]
  have hE3 : energyInElectronVolts (setup.vibrationalEnergy 3) =
      (7 / 2 : ℝ) * (1.054571817e-34 * setup.quantumOscillator.ω /
        1.602176634e-19) := by
    rw [energyInElectronVolts, hEnergyJ, heV]
    norm_num [QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue,
      Constants.ℏ]
    ring
  have hE3lower : (6353 / 100000 : ℝ) <
      energyInElectronVolts (setup.vibrationalEnergy 3) := by
    rw [hE3]
    norm_num at hωlower ⊢
    linarith
  have hE3upper : energyInElectronVolts (setup.vibrationalEnergy 3) <
      (6354 / 100000 : ℝ) := by
    rw [hE3]
    norm_num at hωupper ⊢
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [energyInElectronVolts, hEnergyJ]
    simp only [QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue,
      energyQuantumInElectronVolts]
    ring
  · intro i j hij
    rw [hEnergyJ, hEnergyJ]
    unfold QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue
    have hijR : (i.1 : ℝ) < j.1 := by
      exact_mod_cast hij
    have hp : 0 < (Constants.ℏ : ℝ) * setup.quantumOscillator.ω :=
      mul_pos Constants.ℏ_pos setup.quantumOscillator.ω_pos
    nlinarith
  · change |energyInElectronVolts (setup.vibrationalEnergy 3) -
        634 / 10000| ≤ 1 / 1000
    rw [abs_le]
    constructor <;> linarith
  · intro choice hchoice
    cases choice with
    | A =>
        change |energyInElectronVolts (setup.vibrationalEnergy 3) -
          428 / 10000| ≤ 1 / 1000 at hchoice
        rw [abs_le] at hchoice
        exfalso
        linarith
    | B =>
        change |energyInElectronVolts (setup.vibrationalEnergy 3) -
          531 / 10000| ≤ 1 / 1000 at hchoice
        rw [abs_le] at hchoice
        exfalso
        linarith
    | C => rfl
    | D =>
        change |energyInElectronVolts (setup.vibrationalEnergy 3) -
          832 / 10000| ≤ 1 / 1000 at hchoice
        rw [abs_le] at hchoice
        exfalso
        linarith

end PhyXMiniProblems.ProblemPhyXMini0658
