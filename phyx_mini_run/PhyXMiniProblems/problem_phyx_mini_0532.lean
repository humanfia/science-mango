import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0532

open Dimension

/-!
# Nickel-lattice spacing in the Davisson--Germer experiment

A beam of `54.0 eV` electrons produces its first diffraction maximum at the
scattering angle `phi = 50.0 degrees`. The supplied figure labels the angle
between the incident-beam direction and a family of slanted atomic planes by
`theta`, the perpendicular plane spacing by `d`, and the horizontal separation
of vertical atom columns by `a`.

Energies, masses, actions, and lengths are dimensionful. Only explicit readout
functions cross to coherent-SI or named-unit real components. The de Broglie
and Bragg relations and the two pieces of figure geometry are assumptions; the
requested numerical value of `a` occurs only in the conclusion and the printed
answer-choice table.
-/

/-! ## Dimensionful quantities and readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The dimension of action, used for the reduced Planck constant. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- The joule readout of Physlib's dimensionful electron volt. -/
def electronVoltInJoules : ℝ :=
  energyInJoules DimEnergy.electronVolt

/-- Read a dimensionful energy as a scalar number of electron volts. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / electronVoltInJoules

/-- Coherent-SI readout of a mass, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-! ## Physical and figure vocabulary -/

/-- Species of particle in the incident beam. -/
inductive BeamParticle where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Crystal material used as the diffraction target. -/
inductive CrystalMaterial where
  | nickel
  | other
  deriving DecidableEq, Repr

/-- Text or symbolic labels visible in the supplied lattice diagram. -/
inductive FigureLabel where
  | electronBeam
  | scatteredElectrons
  | incidenceAngleTheta
  | scatteringAnglePhi
  | columnSpacingA
  | interplanarSpacingD
  deriving DecidableEq, Fintype, Repr

/-- Geometrical objects drawn in the supplied lattice diagram. -/
inductive FigureObject where
  | regularAtomRows
  | verticalAtomColumns
  | slantedAtomicPlanes
  | incidentBeamRay
  | scatteredElectronRays
  | atomicPlaneNormal
  deriving DecidableEq, Fintype, Repr

/-!
Presentation-level data from the primary figure. It records only which labels
and objects are shown; their physical quantities live in the experiment setup.
-/
structure DavissonGermerFigure where
  labelShown : FigureLabel → Bool
  objectShown : FigureObject → Bool

/-!
The physical experiment and all quantities named in the prose or figure.
Angles use `Real.Angle`; `toReal` supplies the principal radian representative
needed for the pictured acute-angle geometry.
-/
structure ElectronDiffractionSetup where
  beamParticle : BeamParticle
  crystalMaterial : CrystalMaterial
  electronKineticEnergy : DimEnergy
  electronMass : MassQuantity
  reducedPlanckConstant : ActionQuantity
  electronWavelength : LengthQuantity
  interplanarSpacingD : LengthQuantity
  latticeColumnSpacingA : LengthQuantity
  braggMaximumOrder : ℕ
  incidenceAngleTheta : Real.Angle
  scatteringAnglePhi : Real.Angle
  figure : DavissonGermerFigure

/-! ## Problem readouts, figure geometry, and governing laws -/

/-!
Numerical and categorical data stated in the prose: electrons strike nickel
with kinetic energy `54.0 eV`, and the observed first maximum has
`phi = 50 degrees = 5*pi/18` radians. No value of `a` is assumed.
-/
structure MatchesProblemReadouts
    (setup : ElectronDiffractionSetup) : Prop where
  particleIsElectron : setup.beamParticle = .electron
  targetIsNickel : setup.crystalMaterial = .nickel
  kineticEnergyElectronVolts :
    energyInElectronVolts setup.electronKineticEnergy = 54
  firstMaximum : setup.braggMaximumOrder = 1
  scatteringAngleRadians :
    setup.scatteringAnglePhi.toReal = 5 * Real.pi / 18

/-!
Physical sign and branch conditions. The angular bounds select the pictured
acute incidence angle and non-reflex scattering angle without determining the
requested lattice spacing.
-/
structure HasPhysicalElectronDiffractionParameters
    (setup : ElectronDiffractionSetup) : Prop where
  kineticEnergyPositive : 0 < energyInJoules setup.electronKineticEnergy
  electronMassPositive : 0 < massInKilograms setup.electronMass
  reducedPlanckConstantPositive :
    0 < actionInJouleSeconds setup.reducedPlanckConstant
  wavelengthPositive : 0 < lengthInMeters setup.electronWavelength
  interplanarSpacingPositive : 0 < lengthInMeters setup.interplanarSpacingD
  latticeColumnSpacingPositive :
    0 < lengthInMeters setup.latticeColumnSpacingA
  incidenceAngleAcute :
    0 < setup.incidenceAngleTheta.toReal ∧
      setup.incidenceAngleTheta.toReal < Real.pi / 2
  scatteringAngleNonreflex :
    0 < setup.scatteringAnglePhi.toReal ∧
      setup.scatteringAnglePhi.toReal < Real.pi

/-!
Calibration of the electron constants used by the de Broglie relation.
Physlib supplies the reduced Planck constant in joule-seconds. Since no
electron-rest-mass declaration was found, its kilogram readout is explicit.
-/
structure UsesReferenceElectronConstants
    (setup : ElectronDiffractionSetup) : Prop where
  reducedPlanckConstantCalibration :
    actionInJouleSeconds setup.reducedPlanckConstant = (Constants.ℏ : ℝ)
  electronMassCalibration :
    massInKilograms setup.electronMass = 9.1093837139e-31

/-!
The qualitative labels and objects, together with the quantitative relations
read from the diagram. Since `phi` is measured from the backward extension of
the incident beam, `2*theta + phi = pi`. Since `a` is horizontal while `d` is
perpendicular to the slanted planes, `d = a*cos(theta)` in every length unit.
-/
structure MatchesSuppliedFigure
    (setup : ElectronDiffractionSetup) : Prop where
  allLabelsShown : ∀ label : FigureLabel,
    setup.figure.labelShown label = true
  allObjectsShown : ∀ object : FigureObject,
    setup.figure.objectShown object = true
  angleGeometry :
    2 * setup.incidenceAngleTheta.toReal +
        setup.scatteringAnglePhi.toReal = Real.pi
  spacingGeometry : ∀ unit : LengthUnit,
    lengthReadout unit setup.interplanarSpacingD =
      lengthReadout unit setup.latticeColumnSpacingA *
        Real.Angle.cos setup.incidenceAngleTheta

/-!
The electron wave obeys the nonrelativistic de Broglie relation
`lambda = 2*pi*hbar/sqrt(2*m*K)`. Constructive interference from adjacent
atomic planes obeys Bragg's law `n*lambda = 2*d*sin(theta)`. These are
governing laws and contain no numerical lattice-spacing answer.
-/
structure SatisfiesDeBroglieAndBraggLaws
    (setup : ElectronDiffractionSetup) : Prop where
  deBroglieRelation :
    lengthInMeters setup.electronWavelength =
      2 * Real.pi * actionInJouleSeconds setup.reducedPlanckConstant /
        Real.sqrt
          (2 * massInKilograms setup.electronMass *
            energyInJoules setup.electronKineticEnergy)
  braggRelation : ∀ unit : LengthUnit,
    (setup.braggMaximumOrder : ℝ) *
        lengthReadout unit setup.electronWavelength =
      2 * lengthReadout unit setup.interplanarSpacingD *
        Real.Angle.sin setup.incidenceAngleTheta

/-! ## Printed answers and target -/

/-- Labels of the four answer choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Lattice-spacing value printed beside each answer, in nanometres. -/
def AnswerChoice.spacingInNanometers : AnswerChoice → ℝ
  | .A => 153 / 500
  | .B => 359 / 1000
  | .C => 59 / 500
  | .D => 109 / 500

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A choice is uniquely closest to the lattice spacing inferred from the model.
This compares the inferred value with source metadata; it is not an assumed
experimental law.
-/
def IsUniqueClosestDisplayedSpacing
    (setup : ElectronDiffractionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInNanometers setup.latticeColumnSpacingA -
        choice.spacingInNanometers| <
      |lengthInNanometers setup.latticeColumnSpacingA -
        other.spacingInNanometers|

/-!
For 54-eV electrons and the pictured first maximum at `phi = 50 degrees`, the
de Broglie wavelength, Bragg law, and lattice geometry give a column spacing
which rounds to `0.218 nm` (within half of `0.001 nm`). Thus choice D is the
unique closest displayed answer.

This formalizes `thm:physics:phyx_mini_0532:target`. Neither the rounding bound
nor the assertion that choice D is closest occurs in any readout, calibration,
figure, or governing-law premise.
-/
theorem problem_phyx_mini_0532
    (setup : ElectronDiffractionSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalElectronDiffractionParameters setup)
    (h_constants : UsesReferenceElectronConstants setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_laws : SatisfiesDeBroglieAndBraggLaws setup) :
    |lengthInNanometers setup.latticeColumnSpacingA - 109 / 500| ≤
        1 / 2000 ∧
      IsUniqueClosestDisplayedSpacing setup .D := by
  have heV :
      electronVoltInJoules = (1.602176634e-19 : ℝ) := by
    norm_num [electronVoltInJoules, energyInJoules,
      DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply,
      NNReal.coe_ofScientific]
  have heVpos : 0 < electronVoltInJoules := by
    rw [heV]
    norm_num
  have hK := h_readouts.kineticEnergyElectronVolts
  simp only [energyInElectronVolts] at hK
  field_simp [ne_of_gt heVpos] at hK
  have nanometers_eq_meters (length : LengthQuantity) :
      lengthInNanometers length =
        1000000000 * lengthInMeters length := by
    have h := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    have hval := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInNanometers length =
      ((UnitChoices.dimScale
        {UnitChoices.SI with length := LengthUnit.meters}
        {UnitChoices.SI with length := LengthUnit.nanometers} L𝓭) •
          (length {UnitChoices.SI with length := LengthUnit.meters})).val
        at hval
    norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val] at hval
    rw [hval]
    norm_num [lengthInMeters, lengthReadout, LengthUnit.meters]
    left
    rfl
  have htheta :
      setup.incidenceAngleTheta.toReal = 13 * Real.pi / 36 := by
    nlinarith only [h_figure.angleGeometry,
      h_readouts.scatteringAngleRadians]
  have htrig :
      2 * Real.cos (13 * Real.pi / 36) *
          Real.sin (13 * Real.pi / 36) =
        Real.sin (5 * Real.pi / 18) := by
    calc
      2 * Real.cos (13 * Real.pi / 36) *
            Real.sin (13 * Real.pi / 36) =
          2 * Real.sin (13 * Real.pi / 36) *
            Real.cos (13 * Real.pi / 36) := by ring
      _ = Real.sin (2 * (13 * Real.pi / 36)) := by
        rw [Real.sin_two_mul]
      _ = Real.sin (Real.pi - 5 * Real.pi / 18) := by
        congr 1
        ring
      _ = Real.sin (5 * Real.pi / 18) := by
        rw [Real.sin_pi_sub]
  have hwave_nm :
      lengthInNanometers setup.electronWavelength =
        lengthInNanometers setup.latticeColumnSpacingA *
          Real.sin (5 * Real.pi / 18) := by
    have hbragg := h_laws.braggRelation LengthUnit.nanometers
    have hspacing := h_figure.spacingGeometry LengthUnit.nanometers
    rw [h_readouts.firstMaximum] at hbragg
    norm_num at hbragg
    rw [← Real.Angle.sin_toReal, htheta] at hbragg
    rw [← Real.Angle.cos_toReal, htheta] at hspacing
    rw [hspacing] at hbragg
    calc
      lengthInNanometers setup.electronWavelength =
          2 *
            (lengthInNanometers setup.latticeColumnSpacingA *
              Real.cos (13 * Real.pi / 36)) *
            Real.sin (13 * Real.pi / 36) := hbragg
      _ = lengthInNanometers setup.latticeColumnSpacingA *
          Real.sin (5 * Real.pi / 18) := by
        rw [← htrig]
        ring
  have hwave_m := h_laws.deBroglieRelation
  rw [h_constants.reducedPlanckConstantCalibration,
    h_constants.electronMassCalibration, hK] at hwave_m
  rw [heV] at hwave_m
  simp only [Constants.ℏ] at hwave_m
  let q : ℝ :=
    2 * 91093837139e-41 * (1602176634e-28 * 54)
  let r : ℝ := Real.sqrt q
  change
    lengthInMeters setup.electronWavelength =
      2 * Real.pi * 1054571817e-43 / r at hwave_m
  have hq_pos : 0 < q := by
    norm_num [q]
  have hr_pos : 0 < r := by
    exact Real.sqrt_pos.2 hq_pos
  have hr_sq : r ^ 2 = q := by
    exact Real.sq_sqrt hq_pos.le
  have hr_lower : (3.9701e-24 : ℝ) < r := by
    dsimp [q] at hr_sq
    nlinarith only [hr_sq, hr_pos]
  have hr_upper : r < (3.9703e-24 : ℝ) := by
    dsimp [q] at hr_sq
    nlinarith only [hr_sq, hr_pos]
  have hwave_product :
      lengthInNanometers setup.electronWavelength * r =
        1000000000 * (2 * Real.pi * 1054571817e-43) := by
    rw [nanometers_eq_meters, hwave_m]
    field_simp
  let A : ℝ := lengthInNanometers setup.latticeColumnSpacingA
  let s : ℝ := Real.sin (5 * Real.pi / 18)
  have hAsr :
      A * s * r =
        1000000000 * (2 * Real.pi * 1054571817e-43) := by
    rw [← hwave_product]
    rw [hwave_nm]
  have hA_pos : 0 < A := by
    have hconversion :=
      nanometers_eq_meters setup.latticeColumnSpacingA
    dsimp [A]
    rw [hconversion]
    exact mul_pos (by norm_num)
      h_physical.latticeColumnSpacingPositive
  have hsqrtTwo_nonneg : 0 ≤ Real.sqrt 2 :=
    Real.sqrt_nonneg _
  have hsqrtTwo_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtTwo_lower : (1.41421 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hsqrtTwo_nonneg, hsqrtTwo_sq]
  have hsqrtTwo_upper : Real.sqrt 2 < (1.41422 : ℝ) := by
    nlinarith only [hsqrtTwo_nonneg, hsqrtTwo_sq]
  let u : ℝ := Real.sqrt (2 + Real.sqrt 2)
  have hu_nonneg : 0 ≤ u := Real.sqrt_nonneg _
  have hu_sq : u ^ 2 = 2 + Real.sqrt 2 := by
    exact Real.sq_sqrt (by positivity)
  have hu_lower : (1.847758 : ℝ) < u := by
    nlinarith only [hu_nonneg, hu_sq, hsqrtTwo_lower]
  have hu_upper : u < (1.847761 : ℝ) := by
    nlinarith only [hu_nonneg, hu_sq, hsqrtTwo_upper]
  let v : ℝ := Real.sqrt (2 + u)
  have hv_nonneg : 0 ≤ v := Real.sqrt_nonneg _
  have hv_sq : v ^ 2 = 2 + u := by
    exact Real.sq_sqrt (by positivity)
  have hv_lower : (1.961570 : ℝ) < v := by
    nlinarith only [hv_nonneg, hv_sq, hu_lower]
  have hv_upper : v < (1.961572 : ℝ) := by
    nlinarith only [hv_nonneg, hv_sq, hu_upper]
  let w : ℝ := Real.sqrt (2 - v)
  have hw_arg : 0 ≤ 2 - v := by
    nlinarith only [hv_upper]
  have hw_nonneg : 0 ≤ w := Real.sqrt_nonneg _
  have hw_sq : w ^ 2 = 2 - v := by
    exact Real.sq_sqrt hw_arg
  have hw_lower : (0.196030 : ℝ) < w := by
    nlinarith only [hw_nonneg, hw_sq, hv_upper]
  have hw_upper : w < (0.196036 : ℝ) := by
    nlinarith only [hw_nonneg, hw_sq, hv_lower]
  have hsin_pi_thirty_two_lower :
      (0.098015 : ℝ) < Real.sin (Real.pi / 32) := by
    rw [Real.sin_pi_div_thirty_two]
    change (0.098015 : ℝ) <
      Real.sqrt (2 - v) / 2
    dsimp [w] at hw_lower
    linarith only [hw_lower]
  have hsin_pi_thirty_two_upper :
      Real.sin (Real.pi / 32) < (0.098018 : ℝ) := by
    rw [Real.sin_pi_div_thirty_two]
    change Real.sqrt (2 - v) / 2 <
      (0.098018 : ℝ)
    dsimp [w] at hw_upper
    linarith only [hw_upper]
  have hsin_three_point_fourteen_upper :
      Real.sin ((3.14 : ℝ) / 32) < (0.098015 : ℝ) := by
    have h := Real.sin_bound
      (x := (3.14 : ℝ) / 32) (by norm_num)
    rw [abs_of_nonneg
      (by norm_num : (0 : ℝ) ≤ (3.14 : ℝ) / 32)] at h
    rcases abs_le.mp h with ⟨_, hupper⟩
    norm_num at hupper ⊢
    linarith only [hupper]
  have hsin_three_point_one_four_two_lower :
      (0.098018 : ℝ) < Real.sin ((3.142 : ℝ) / 32) := by
    have h := Real.sin_bound
      (x := (3.142 : ℝ) / 32) (by norm_num)
    rw [abs_of_nonneg
      (by norm_num : (0 : ℝ) ≤ (3.142 : ℝ) / 32)] at h
    rcases abs_le.mp h with ⟨hlower, _⟩
    norm_num at hlower ⊢
    linarith only [hlower]
  have hpi_lower : (3.14 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.14 : ℝ) := le_of_not_gt h
    have hmono :
        Real.sin (Real.pi / 32) ≤
          Real.sin ((3.14 : ℝ) / 32) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.two_le_pi]
      · nlinarith only [hpi_le]
    linarith only [hsin_pi_thirty_two_lower,
      hmono, hsin_three_point_fourteen_upper]
  have hpi_upper : Real.pi < (3.142 : ℝ) := by
    by_contra h
    have hpi_ge : (3.142 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hmono :
        Real.sin ((3.142 : ℝ) / 32) ≤
          Real.sin (Real.pi / 32) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
      · nlinarith only [hpi_ge]
    linarith only [hsin_three_point_one_four_two_lower,
      hmono, hsin_pi_thirty_two_upper]
  have small_trig_bounds {x L U : ℝ}
      (hL0 : 0 ≤ L) (hLx : L ≤ x)
      (hxU : x ≤ U) (hU1 : U ≤ 1) :
      L - U ^ 3 / 6 - U ^ 4 * (5 / 96) ≤ Real.sin x ∧
        Real.sin x ≤ U - L ^ 3 / 6 + U ^ 4 * (5 / 96) ∧
        1 - U ^ 2 / 2 - U ^ 4 * (5 / 96) ≤ Real.cos x ∧
        Real.cos x ≤ 1 - L ^ 2 / 2 + U ^ 4 * (5 / 96) := by
    have hx0 : 0 ≤ x := hL0.trans hLx
    have hx1 : |x| ≤ 1 := by
      rw [abs_of_nonneg hx0]
      exact hxU.trans hU1
    have hL2 : L ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ hL0 hLx 2
    have hL3 : L ^ 3 ≤ x ^ 3 :=
      pow_le_pow_left₀ hL0 hLx 3
    have hx2 : x ^ 2 ≤ U ^ 2 :=
      pow_le_pow_left₀ hx0 hxU 2
    have hx3 : x ^ 3 ≤ U ^ 3 :=
      pow_le_pow_left₀ hx0 hxU 3
    have hx4 : x ^ 4 ≤ U ^ 4 :=
      pow_le_pow_left₀ hx0 hxU 4
    have hsine := abs_le.mp (Real.sin_bound hx1)
    have hcosine := abs_le.mp (Real.cos_bound hx1)
    rw [abs_of_nonneg hx0] at hsine hcosine
    constructor
    · linarith only [hsine.1, hLx, hx3, hx4]
    constructor
    · linarith only [hsine.2, hxU, hL3, hx4]
    constructor
    · linarith only [hcosine.1, hx2, hx4]
    · linarith only [hcosine.2, hL2, hx4]
  let t : ℝ := Real.pi / 36
  have ht_lower : (3.14 : ℝ) / 36 ≤ t := by
    dsimp [t]
    linarith only [hpi_lower]
  have ht_upper : t ≤ (3.142 : ℝ) / 36 := by
    dsimp [t]
    linarith only [hpi_upper]
  have ht_bounds := small_trig_bounds
    (x := t) (L := (3.14 : ℝ) / 36)
    (U := (3.142 : ℝ) / 36)
    (by norm_num) ht_lower ht_upper (by norm_num)
  have hsint_lower : (0.0871 : ℝ) < Real.sin t := by
    nlinarith only [ht_bounds.1]
  have hsint_upper : Real.sin t < (0.08718 : ℝ) := by
    nlinarith only [ht_bounds.2.1]
  have hcost_lower : (0.99618 : ℝ) < Real.cos t := by
    nlinarith only [ht_bounds.2.2.1]
  have hcost_upper : Real.cos t < (0.99620 : ℝ) := by
    nlinarith only [ht_bounds.2.2.2]
  have hsine_identity :
      s = Real.sqrt 2 / 2 * (Real.cos t + Real.sin t) := by
    dsimp [s, t]
    rw [show 5 * Real.pi / 18 =
        Real.pi / 4 + Real.pi / 36 by ring,
      Real.sin_add, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    ring
  have hsum_lower :
      (1.08328 : ℝ) < Real.cos t + Real.sin t := by
    linarith only [hsint_lower, hcost_lower]
  have hsum_upper :
      Real.cos t + Real.sin t < (1.08338 : ℝ) := by
    linarith only [hsint_upper, hcost_upper]
  have hprod_lower :
      (1.41421 : ℝ) * 1.08328 <
        Real.sqrt 2 * (Real.cos t + Real.sin t) :=
    mul_lt_mul hsqrtTwo_lower hsum_lower.le
      (by norm_num) hsqrtTwo_nonneg
  have hprod_upper :
      Real.sqrt 2 * (Real.cos t + Real.sin t) <
        (1.41422 : ℝ) * 1.08338 :=
    mul_lt_mul hsqrtTwo_upper hsum_upper.le
      (by linarith only [hsum_lower]) (by norm_num)
  have hs_lower : (0.7659 : ℝ) < s := by
    nlinarith only [hsine_identity, hprod_lower]
  have hs_upper : s < (0.7661 : ℝ) := by
    nlinarith only [hsine_identity, hprod_upper]
  have hs_pos : 0 < s := by
    nlinarith only [hs_lower]
  have hA_lower : (0.2175 : ℝ) < A := by
    by_contra h
    have hA_le : A ≤ (0.2175 : ℝ) := le_of_not_gt h
    have hfirst :
        s * A < (0.7661 : ℝ) * 0.2175 :=
      mul_lt_mul hs_upper hA_le hA_pos (by norm_num)
    have hsecond :
        (s * A) * r <
          ((0.7661 : ℝ) * 0.2175) * 3.9703e-24 :=
      mul_lt_mul hfirst hr_upper.le hr_pos
        (mul_nonneg (by norm_num) (by norm_num))
    nlinarith only [hsecond, hAsr, hpi_lower]
  have hA_upper : A < (0.2185 : ℝ) := by
    by_contra h
    have hA_ge : (0.2185 : ℝ) ≤ A := le_of_not_gt h
    have hfirst :
        (0.7659 : ℝ) * 0.2185 < s * A :=
      mul_lt_mul hs_lower hA_ge (by norm_num) hs_pos.le
    have hsecond :
        ((0.7659 : ℝ) * 0.2185) * 3.9701e-24 <
          (s * A) * r :=
      mul_lt_mul hfirst hr_lower.le (by norm_num)
        (mul_nonneg hs_pos.le hA_pos.le)
    nlinarith only [hsecond, hAsr, hpi_upper]
  have hround :
      |A - 109 / 500| ≤ (1 / 2000 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith only [hA_lower, hA_upper]
  constructor
  · simpa only [A] using hround
  · unfold IsUniqueClosestDisplayedSpacing
    intro other hother
    change
      |A - AnswerChoice.D.spacingInNanometers| <
        |A - other.spacingInNanometers|
    cases other with
    | A =>
        have hcompetitor :
            (1 / 2000 : ℝ) <
              |A - AnswerChoice.A.spacingInNanometers| := by
          simp only [AnswerChoice.spacingInNanometers]
          rw [abs_of_nonpos]
          · nlinarith only [hA_upper]
          · nlinarith only [hA_upper]
        exact lt_of_le_of_lt hround hcompetitor
    | B =>
        have hcompetitor :
            (1 / 2000 : ℝ) <
              |A - AnswerChoice.B.spacingInNanometers| := by
          simp only [AnswerChoice.spacingInNanometers]
          rw [abs_of_nonpos]
          · nlinarith only [hA_upper]
          · nlinarith only [hA_upper]
        exact lt_of_le_of_lt hround hcompetitor
    | C =>
        have hcompetitor :
            (1 / 2000 : ℝ) <
              |A - AnswerChoice.C.spacingInNanometers| := by
          simp only [AnswerChoice.spacingInNanometers]
          rw [abs_of_nonneg]
          · nlinarith only [hA_lower]
          · nlinarith only [hA_lower]
        exact lt_of_le_of_lt hround hcompetitor
    | D =>
        exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0532
