import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0571

open Dimension

/-!
# Rotational excitation of the water molecule

The primary figure shows a bent `H₂O` molecule with two equal `O-H` bonds,
each labeled `0.0958 nm`, and a bond angle labeled `105°`.  Its dashed line is
the in-plane bond-angle bisector used as the rotation axis.  Thus the oxygen
lies on the axis and each hydrogen has perpendicular lever arm
`r * sin (105° / 2)`.

The molecule is modeled as a rigid rotor.  Its rotational energies, absorbed
photon energy, and required photon wavelength are independent dimensionful
physical quantities.  Governing-law premises relate them; in particular, the
wavelength is not defined from the recorded answer choice.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of a moment of inertia, `mass * length^2`. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- The physical dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-!
A unit-independent speed with a real carrier.  This matches the exact type of
Physlib's dimensionful `DimSpeed.speedOfLight` constant.
-/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Micrometre readout of a physical length. -/
def lengthInMicrometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.micrometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Coherent-SI readout of a moment of inertia, in `kg m²`. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Coherent-SI readout of a speed, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-! ## Molecular and primary-figure vocabulary -/

/-- The three labeled atomic sites in the depicted molecule. -/
inductive AtomSite where
  | oxygen
  | upperHydrogen
  | lowerHydrogen
  deriving DecidableEq, Fintype, Repr

/-- Chemical-element labels occurring in the figure. -/
inductive ChemicalElement where
  | hydrogen
  | oxygen
  deriving DecidableEq, Repr

/-- The two drawn oxygen-hydrogen bonds. -/
inductive OHBond where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- The hydrogen endpoint associated with each depicted bond. -/
def OHBond.hydrogenSite : OHBond → AtomSite
  | .upper => .upperHydrogen
  | .lower => .lowerHydrogen

/-- The two shades used to distinguish the element types in the raster. -/
inductive AtomShade where
  | lightBlue
  | darkGray
  deriving DecidableEq, Repr

/-- The rotation-axis role of the dashed line in the supplied diagram. -/
inductive RotationAxis where
  | depictedBondAngleBisector
  | other
  deriving DecidableEq, Repr

/-- The two rotational levels mentioned in the question. -/
inductive RotationalLevel where
  | l0
  | l1
  deriving DecidableEq, Fintype, Repr

/-- Orbital angular-momentum quantum number attached to each named level. -/
def RotationalLevel.quantumNumber : RotationalLevel → ℕ
  | .l0 => 0
  | .l1 => 1

/-!
Visible content of the primary molecular diagram.  The numerical labels here
are scalar raster readouts; the setup below separately stores the associated
physical length and angle.
-/
structure WaterMoleculeFigure where
  atomIsShown : AtomSite → Bool
  elementAt : AtomSite → ChemicalElement
  shadeAt : AtomSite → AtomShade
  bondIsShown : OHBond → Bool
  bondLengthLabelNanometers : OHBond → ℝ
  bondAngleLabelDegrees : ℝ
  oxygenDrawnCentrally : Bool
  bentMolecularShape : Bool
  dashedReferenceAxisShown : Bool
  dashedAxisPassesThroughOxygen : Bool
  dashedAxisBisectsBondAngle : Bool

/-! ## Physical setup, source data, and governing laws -/

/-!
Independent physical quantities of the rotor and photon.  The perpendicular
distances, inertia, level energies, photon energy, and photon wavelength are
fields rather than definitions, and are related only by the law structures
below.
-/
structure WaterMoleculeRotorSetup where
  atomMass : AtomSite → MassQuantity
  oxygenHydrogenBondLength : LengthQuantity
  bondAngleRadians : ℝ
  rotationAxis : RotationAxis
  perpendicularDistanceToAxis : AtomSite → LengthQuantity
  momentOfInertiaAboutAxis : MomentOfInertiaQuantity
  rotationalEnergy : RotationalLevel → DimEnergy
  transitionInitialLevel : RotationalLevel
  transitionFinalLevel : RotationalLevel
  absorbedPhotonEnergy : DimEnergy
  requiredPhotonWavelength : LengthQuantity
  reducedPlanckAction : ActionQuantity
  lightSpeed : SpeedQuantity
  figure : WaterMoleculeFigure

/-!
The categorical scenario and the requested transition.  This fixes only the
roles `l = 0` and `l = 1`, not their energy gap or the photon wavelength.
-/
structure MatchesWaterRotationalExcitationScenario
    (setup : WaterMoleculeRotorSetup) : Prop where
  usesDepictedBisectorAxis :
    setup.rotationAxis = .depictedBondAngleBisector
  startsAtLZero : setup.transitionInitialLevel = .l0
  endsAtLOne : setup.transitionFinalLevel = .l1

/-!
All salient labels and qualitative geometry visible in image 571.  The two
physical `O-H` bonds share the figure's `0.0958 nm` readout, and the physical
angle is the radian conversion of its `105°` label.  No photon wavelength or
answer choice occurs here.
-/
structure MatchesPrimaryWaterMoleculeFigure
    (setup : WaterMoleculeRotorSetup) : Prop where
  everyAtomShown : ∀ site, setup.figure.atomIsShown site = true
  oxygenElementLabel :
    setup.figure.elementAt .oxygen = .oxygen
  upperHydrogenElementLabel :
    setup.figure.elementAt .upperHydrogen = .hydrogen
  lowerHydrogenElementLabel :
    setup.figure.elementAt .lowerHydrogen = .hydrogen
  oxygenDarkGray : setup.figure.shadeAt .oxygen = .darkGray
  upperHydrogenLightBlue :
    setup.figure.shadeAt .upperHydrogen = .lightBlue
  lowerHydrogenLightBlue :
    setup.figure.shadeAt .lowerHydrogen = .lightBlue
  everyBondShown : ∀ bond, setup.figure.bondIsShown bond = true
  everyBondLabelNanometers :
    ∀ bond, setup.figure.bondLengthLabelNanometers bond = 0.0958
  physicalBondLengthMatchesLabels : ∀ bond,
    lengthInNanometers setup.oxygenHydrogenBondLength =
      setup.figure.bondLengthLabelNanometers bond
  angleLabelDegrees : setup.figure.bondAngleLabelDegrees = 105
  physicalAngleMatchesLabel :
    setup.bondAngleRadians =
      setup.figure.bondAngleLabelDegrees * Real.pi / 180
  oxygenCentral : setup.figure.oxygenDrawnCentrally = true
  moleculeBent : setup.figure.bentMolecularShape = true
  dashedAxisShown : setup.figure.dashedReferenceAxisShown = true
  dashedAxisThroughOxygen :
    setup.figure.dashedAxisPassesThroughOxygen = true
  dashedAxisIsBisector :
    setup.figure.dashedAxisBisectsBondAngle = true

/-!
Textbook reference values needed for the numerical calculation.  Physlib's
`Constants.ℏ` and `DimSpeed.speedOfLight` ground the two universal constants.
The oxygen mass is retained even though an atom on the selected axis makes no
contribution to this moment of inertia.  No target wavelength appears here.
-/
structure UsesTextbookReferenceData
    (setup : WaterMoleculeRotorSetup) : Prop where
  upperHydrogenMassKilograms :
    massInKilograms (setup.atomMass .upperHydrogen) = 1.67e-27
  lowerHydrogenMassKilograms :
    massInKilograms (setup.atomMass .lowerHydrogen) = 1.67e-27
  oxygenMassKilograms :
    massInKilograms (setup.atomMass .oxygen) = 16 * 1.67e-27
  reducedPlanckActionJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction =
      (Constants.ℏ : ℝ)
  standardSpeedOfLight :
    speedInMetersPerSecond setup.lightSpeed =
      speedInMetersPerSecond DimSpeed.speedOfLight

/-- Positivity and physical-branch conditions for the rotor and photon. -/
structure HasPhysicalWaterRotorParameters
    (setup : WaterMoleculeRotorSetup) : Prop where
  everyAtomicMassPositive :
    ∀ site, 0 < massInKilograms (setup.atomMass site)
  bondLengthPositive :
    0 < lengthInMeters setup.oxygenHydrogenBondLength
  bondAnglePositive : 0 < setup.bondAngleRadians
  bondAngleLessThanPi : setup.bondAngleRadians < Real.pi
  inertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutAxis
  rotationalEnergiesNonnegative :
    ∀ level, 0 ≤ energyInJoules (setup.rotationalEnergy level)
  absorbedPhotonEnergyPositive :
    0 < energyInJoules setup.absorbedPhotonEnergy
  photonWavelengthPositive :
    0 < lengthInMeters setup.requiredPhotonWavelength
  reducedPlanckActionPositive :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  lightSpeedPositive : 0 < speedInMetersPerSecond setup.lightSpeed

/-!
Geometry of the dashed bisector axis.  Oxygen has zero perpendicular distance
to it, while each hydrogen has lever arm `r sin (θ/2)`.  This is a general
geometric relation and does not contain the requested wavelength.
-/
structure SatisfiesDepictedBisectorGeometry
    (setup : WaterMoleculeRotorSetup) : Prop where
  oxygenOnAxis :
    lengthInMeters (setup.perpendicularDistanceToAxis .oxygen) = 0
  upperHydrogenLeverArm :
    lengthInMeters
        (setup.perpendicularDistanceToAxis .upperHydrogen) =
      lengthInMeters setup.oxygenHydrogenBondLength *
        Real.sin (setup.bondAngleRadians / 2)
  lowerHydrogenLeverArm :
    lengthInMeters
        (setup.perpendicularDistanceToAxis .lowerHydrogen) =
      lengthInMeters setup.oxygenHydrogenBondLength *
        Real.sin (setup.bondAngleRadians / 2)

/-!
The governing physics used by the calculation:

* the point-mass moment of inertia is `Σ mᵢ dᵢ²` about the selected axis;
* a rigid rotor has `E_l = ℏ² l(l+1)/(2I)`;
* the absorbed photon energy equals the final-minus-initial level gap; and
* the photon obeys `E λ = h c = 2πℏc`.

All relations are stated for independent physical fields.  None specializes
the wavelength to a choice value.
-/
structure SatisfiesRigidRotorPhotonLaws
    (setup : WaterMoleculeRotorSetup) : Prop where
  pointMassMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAxis =
      ∑ site : AtomSite,
        massInKilograms (setup.atomMass site) *
          lengthInMeters (setup.perpendicularDistanceToAxis site) ^ 2
  rigidRotorSpectrum : ∀ level : RotationalLevel,
    energyInJoules (setup.rotationalEnergy level) =
      actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
          (level.quantumNumber : ℝ) *
          ((level.quantumNumber : ℝ) + 1) /
        (2 * momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAxis)
  photonEnergyIsTransitionGap :
    energyInJoules setup.absorbedPhotonEnergy =
      energyInJoules
          (setup.rotationalEnergy setup.transitionFinalLevel) -
        energyInJoules
          (setup.rotationalEnergy setup.transitionInitialLevel)
  planckEinsteinWavelengthLaw :
    energyInJoules setup.absorbedPhotonEnergy *
        lengthInMeters setup.requiredPhotonWavelength =
      2 * Real.pi *
        actionInJouleSeconds setup.reducedPlanckAction *
        speedInMetersPerSecond setup.lightSpeed

/-! ## Displayed choices and current target -/

/-- Labels of the four wavelength choices in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Wavelength printed beside each answer choice, in micrometres. -/
def AnswerChoice.wavelengthMicrometers : AnswerChoice → ℝ
  | .A => 123
  | .B => 452
  | .C => 344
  | .D => 425

/-- Dataset metadata records choice C; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Absolute error between the physical wavelength and a displayed choice. -/
def answerChoiceErrorMicrometers
    (setup : WaterMoleculeRotorSetup) (choice : AnswerChoice) : ℝ :=
  |lengthInMicrometers setup.requiredPhotonWavelength -
    choice.wavelengthMicrometers|

/-!
Agreement with the whole-micrometre textbook value, allowing `1 μm` for the
rounded atomic-mass and rigid-point-mass approximation.
-/
def AgreesWithDisplayedWavelength
    (setup : WaterMoleculeRotorSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorMicrometers setup choice < 1

/-- A choice is strictly closer than every other displayed wavelength. -/
def IsUniqueClosestWavelengthChoice
    (setup : WaterMoleculeRotorSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMicrometers setup choice <
      answerChoiceErrorMicrometers setup other

/-!
The bisector geometry gives
`I = 2 m_H (r sin (105°/2))²`.  Combining the rigid-rotor gap for
`l = 0 → 1` with `Eλ = 2πℏc` yields a wavelength within `1 μm` of
`344 μm`, uniquely selecting choice C.

Blueprint: `thm:physics:phyx_mini_0571:target`.
-/
theorem requiredPhotonWavelength_is_choiceC
    (setup : WaterMoleculeRotorSetup)
    (_scenario : MatchesWaterRotationalExcitationScenario setup)
    (_figure : MatchesPrimaryWaterMoleculeFigure setup)
    (_reference : UsesTextbookReferenceData setup)
    (_physical : HasPhysicalWaterRotorParameters setup)
    (_geometry : SatisfiesDepictedBisectorGeometry setup)
    (_laws : SatisfiesRigidRotorPhotonLaws setup) :
    AgreesWithDisplayedWavelength setup .C ∧
      IsUniqueClosestWavelengthChoice setup .C := by
  have nanometers_eq (length : LengthQuantity) :
      lengthInNanometers length =
        1000000000 * lengthInMeters length := by
    change
      ((length {UnitChoices.SI with length := LengthUnit.nanometers}).val : ℝ) =
        1000000000 * ((length UnitChoices.SI).val : ℝ)
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.nanometers}]
    change
      (↑(UnitChoices.dimScale UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.nanometers} L𝓭) : ℝ) *
          ((length UnitChoices.SI).val : ℝ) =
        1000000000 * ((length UnitChoices.SI).val : ℝ)
    congr 1
    norm_num [UnitChoices.dimScale, UnitChoices.SI, LengthUnit.nanometers,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters]
    rfl
  have micrometers_eq (length : LengthQuantity) :
      lengthInMicrometers length =
        1000000 * lengthInMeters length := by
    change
      ((length {UnitChoices.SI with length := LengthUnit.micrometers}).val : ℝ) =
        1000000 * ((length UnitChoices.SI).val : ℝ)
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.micrometers}]
    change
      (↑(UnitChoices.dimScale UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.micrometers} L𝓭) : ℝ) *
          ((length UnitChoices.SI).val : ℝ) =
        1000000 * ((length UnitChoices.SI).val : ℝ)
    congr 1
    norm_num [UnitChoices.dimScale, UnitChoices.SI, LengthUnit.micrometers,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters]
    rfl

  have h_bond_nm :
      lengthInNanometers setup.oxygenHydrogenBondLength = 0.0958 := by
    calc
      lengthInNanometers setup.oxygenHydrogenBondLength =
          setup.figure.bondLengthLabelNanometers .upper :=
        _figure.physicalBondLengthMatchesLabels .upper
      _ = 0.0958 := _figure.everyBondLabelNanometers .upper
  have h_bond_m :
      lengthInMeters setup.oxygenHydrogenBondLength =
        (479 : ℝ) / 5000000000000 := by
    rw [nanometers_eq] at h_bond_nm
    norm_num at h_bond_nm ⊢
    linarith
  have h_angle :
      setup.bondAngleRadians = Real.pi * (7 / 12 : ℝ) := by
    calc
      setup.bondAngleRadians =
          setup.figure.bondAngleLabelDegrees * Real.pi / 180 :=
        _figure.physicalAngleMatchesLabel
      _ = 105 * Real.pi / 180 := by rw [_figure.angleLabelDegrees]
      _ = Real.pi * (7 / 12 : ℝ) := by ring
  have h_oxygen_distance :
      lengthInMeters (setup.perpendicularDistanceToAxis .oxygen) = 0 :=
    _geometry.oxygenOnAxis
  have h_upper_distance :
      lengthInMeters
          (setup.perpendicularDistanceToAxis .upperHydrogen) =
        (479 : ℝ) / 5000000000000 *
          Real.sin (Real.pi * (7 / 24 : ℝ)) := by
    rw [_geometry.upperHydrogenLeverArm, h_bond_m, h_angle]
    congr 2
    ring
  have h_lower_distance :
      lengthInMeters
          (setup.perpendicularDistanceToAxis .lowerHydrogen) =
        (479 : ℝ) / 5000000000000 *
          Real.sin (Real.pi * (7 / 24 : ℝ)) := by
    rw [_geometry.lowerHydrogenLeverArm, h_bond_m, h_angle]
    congr 2
    ring

  have h_inertia := _laws.pointMassMomentOfInertia
  rw [show (Finset.univ : Finset AtomSite) =
      {.oxygen, .upperHydrogen, .lowerHydrogen} by decide] at h_inertia
  simp at h_inertia
  rw [h_oxygen_distance, h_upper_distance, h_lower_distance,
    _reference.upperHydrogenMassKilograms,
    _reference.lowerHydrogenMassKilograms] at h_inertia
  norm_num at h_inertia

  have h_initial := _laws.rigidRotorSpectrum .l0
  have h_final := _laws.rigidRotorSpectrum .l1
  norm_num [RotationalLevel.quantumNumber] at h_initial h_final
  have h_energy := _laws.photonEnergyIsTransitionGap
  rw [_scenario.startsAtLZero, _scenario.endsAtLOne,
    h_initial, h_final] at h_energy
  ring_nf at h_energy
  have h_planck := _laws.planckEinsteinWavelengthLaw
  rw [h_energy] at h_planck
  have h_inertia_ne :
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAxis ≠ 0 :=
    ne_of_gt _physical.inertiaPositive
  have h_hbar_ne :
      actionInJouleSeconds setup.reducedPlanckAction ≠ 0 :=
    ne_of_gt _physical.reducedPlanckActionPositive
  have h_lambda_m :
      lengthInMeters setup.requiredPhotonWavelength =
        2 * Real.pi * speedInMetersPerSecond setup.lightSpeed *
            momentOfInertiaInKilogramMetersSquared
              setup.momentOfInertiaAboutAxis /
          actionInJouleSeconds setup.reducedPlanckAction := by
    field_simp [h_inertia_ne, h_hbar_ne] at h_planck ⊢
    nlinarith [h_planck]
  rw [_reference.standardSpeedOfLight,
    _reference.reducedPlanckActionJouleSeconds, h_inertia] at h_lambda_m
  norm_num [speedInMetersPerSecond, Constants.ℏ,
    DimSpeed.speedOfLight_in_SI] at h_lambda_m
  have h_lambda_um_units :=
    micrometers_eq setup.requiredPhotonWavelength
  rw [h_lambda_m] at h_lambda_um_units
  ring_nf at h_lambda_um_units
  have h_lambda_um :
      lengthInMicrometers setup.requiredPhotonWavelength =
        (Real.pi * Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2) *
          (5743520893224163 / 32955369281250 : ℝ) := by
    exact h_lambda_um_units
  clear nanometers_eq micrometers_eq h_bond_nm h_bond_m h_angle
    h_oxygen_distance h_upper_distance h_lower_distance h_inertia
    h_initial h_final h_energy h_planck h_inertia_ne h_hbar_ne
    h_lambda_m h_lambda_um_units _scenario _figure _reference
    _physical _geometry _laws

  have hr2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2_lower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr2_upper : Real.sqrt 2 < (1.4143 : ℝ) := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hr3_lower : (1.732 : ℝ) < Real.sqrt 3 := by
    nlinarith only [hr3_sq, hr3_nonneg]
  have hr3_upper : Real.sqrt 3 < (1.7321 : ℝ) := by
    nlinarith only [hr3_sq, hr3_nonneg]
  have hroot_product_lower :
      (1.4142 : ℝ) * (1.732 - 1) <
        Real.sqrt 2 * (Real.sqrt 3 - 1) := by
    exact mul_lt_mul hr2_lower (by linarith) (by norm_num) hr2_nonneg
  have hroot_product_upper :
      Real.sqrt 2 * (Real.sqrt 3 - 1) <
        (1.4143 : ℝ) * (1.7321 - 1) := by
    exact mul_lt_mul hr2_upper (by linarith) (by linarith) (by norm_num)
  have h_sin_sq_exact :
      Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 =
        (1 / 2 : ℝ) + Real.sqrt 2 * (Real.sqrt 3 - 1) / 8 := by
    rw [Real.sin_sq_eq_half_sub]
    rw [show 2 * (Real.pi * (7 / 24 : ℝ)) =
        Real.pi / 4 + Real.pi / 3 by ring]
    rw [Real.cos_add, Real.cos_pi_div_four, Real.cos_pi_div_three,
      Real.sin_pi_div_four, Real.sin_pi_div_three]
    ring
  have h_sin_sq_lower :
      (0.62939 : ℝ) <
        Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 := by
    rw [h_sin_sq_exact]
    nlinarith [hroot_product_lower]
  have h_sin_sq_upper :
      Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 <
        (0.629428 : ℝ) := by
    rw [h_sin_sq_exact]
    nlinarith [hroot_product_upper]

  have hr2_nested_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
  have hr2_nested_sq :
      (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hr2_nested_arg
  have hr2_nested_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hr2_tight_upper : Real.sqrt 2 < (1.41422 : ℝ) := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr2_nested_lower :
      (1.8477 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hr2_nested_sq, hr2_nested_nonneg, hr2_lower]
  have hr2_nested_upper :
      Real.sqrt (2 + Real.sqrt 2) < (1.84777 : ℝ) := by
    nlinarith only [hr2_nested_sq, hr2_nested_nonneg, hr2_tight_upper]
  have hr3_nested_arg :
      0 ≤ (2 : ℝ) + Real.sqrt (2 + Real.sqrt 2) := by positivity
  have hr3_nested_sq :
      (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 + Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hr3_nested_arg
  have hr3_nested_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hr3_nested_lower :
      (1.96155 : ℝ) <
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [hr3_nested_sq, hr3_nested_nonneg, hr2_nested_lower]
  have hr3_nested_upper :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
        (1.96158 : ℝ) := by
    nlinarith only [hr3_nested_sq, hr3_nested_nonneg, hr2_nested_upper]
  have hsmall_root_arg :
      0 ≤ (2 : ℝ) -
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    linarith only [hr3_nested_upper]
  have hsmall_root_sq :
      (Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sq_sqrt hsmall_root_arg
  have hsmall_root_nonneg :
      0 ≤ Real.sqrt
        (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
    Real.sqrt_nonneg _
  have hsmall_root_lower :
      (0.196 : ℝ) <
        Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
    nlinarith only [hsmall_root_sq, hsmall_root_nonneg,
      hr3_nested_upper]
  have hsmall_root_upper :
      Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) <
        (0.1961 : ℝ) := by
    nlinarith only [hsmall_root_sq, hsmall_root_nonneg,
      hr3_nested_lower]
  have hsin_pi32_lower :
      (0.098 : ℝ) < Real.sin (Real.pi / 32) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith
  have hsin_pi32_upper :
      Real.sin (Real.pi / 32) < (0.09805 : ℝ) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith
  have hx_nonneg : 0 ≤ Real.pi / 32 := by positivity
  have hx_le_eighth : Real.pi / 32 ≤ (1 / 8 : ℝ) := by
    nlinarith [Real.pi_le_four]
  have hx_abs : |Real.pi / 32| ≤ 1 := by
    rw [abs_of_nonneg hx_nonneg]
    linarith
  have hsin_approx := Real.sin_bound hx_abs
  have hsin_approx_lower := (abs_le.mp hsin_approx).1
  have hsin_approx_upper := (abs_le.mp hsin_approx).2
  have hx_cube_nonneg : 0 ≤ (Real.pi / 32) ^ 3 := by positivity
  have hx_cube_le :
      (Real.pi / 32) ^ 3 ≤ (1 / 8 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx_nonneg hx_le_eighth 3
  have hx_fourth_le :
      (Real.pi / 32) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_le_eighth 4
  have hpi_lower : (3.135 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.135 : ℝ) := le_of_not_gt h
    rw [abs_of_nonneg hx_nonneg] at hsin_approx_upper
    nlinarith only [hsin_approx_upper, hsin_pi32_lower, hpi_le,
      hx_cube_nonneg, hx_cube_le, hx_fourth_le]
  have hpi_lt_coarse : Real.pi < (3.2 : ℝ) := by
    by_contra h
    have hpi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    rw [abs_of_nonneg hx_nonneg] at hsin_approx_lower
    nlinarith only [hsin_approx_lower, hsin_pi32_upper, hpi_ge,
      hx_cube_le, hx_fourth_le]
  have hx_le_tenth : Real.pi / 32 ≤ (1 / 10 : ℝ) := by
    linarith
  have hx_cube_le_tenth :
      (Real.pi / 32) ^ 3 ≤ (1 / 10 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx_nonneg hx_le_tenth 3
  have hx_fourth_le_tenth :
      (Real.pi / 32) ^ 4 ≤ (1 / 10 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_le_tenth 4
  have hpi_upper : Real.pi < (3.145 : ℝ) := by
    by_contra h
    have hpi_ge : (3.145 : ℝ) ≤ Real.pi := le_of_not_gt h
    rw [abs_of_nonneg hx_nonneg] at hsin_approx_lower
    nlinarith only [hsin_approx_lower, hsin_pi32_upper, hpi_ge,
      hx_cube_le_tenth, hx_fourth_le_tenth]

  have hpi_sin_sq_lower :
      (3.135 : ℝ) * 0.62939 <
        Real.pi * Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 := by
    calc
      (3.135 : ℝ) * 0.62939 < Real.pi * 0.62939 :=
        mul_lt_mul_of_pos_right hpi_lower (by norm_num)
      _ < Real.pi * Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 :=
        mul_lt_mul_of_pos_left h_sin_sq_lower Real.pi_pos
  have hpi_sin_sq_upper :
      Real.pi * Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 <
        (3.145 : ℝ) * 0.629428 := by
    calc
      Real.pi * Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 <
          (3.145 : ℝ) *
            Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2 :=
        mul_lt_mul_of_pos_right hpi_upper
          (by linarith only [h_sin_sq_lower])
      _ < (3.145 : ℝ) * 0.629428 :=
        mul_lt_mul_of_pos_left h_sin_sq_upper (by norm_num)
  have h_lambda_lower :
      (343 : ℝ) <
        lengthInMicrometers setup.requiredPhotonWavelength := by
    rw [h_lambda_um]
    calc
      (343 : ℝ) <
          ((3.135 : ℝ) * 0.62939) *
            (5743520893224163 / 32955369281250 : ℝ) := by norm_num
      _ < (Real.pi * Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2) *
          (5743520893224163 / 32955369281250 : ℝ) :=
        mul_lt_mul_of_pos_right hpi_sin_sq_lower (by norm_num)
  have h_lambda_upper :
      lengthInMicrometers setup.requiredPhotonWavelength < (345 : ℝ) := by
    rw [h_lambda_um]
    calc
      (Real.pi * Real.sin (Real.pi * (7 / 24 : ℝ)) ^ 2) *
          (5743520893224163 / 32955369281250 : ℝ) <
          ((3.145 : ℝ) * 0.629428) *
            (5743520893224163 / 32955369281250 : ℝ) :=
        mul_lt_mul_of_pos_right hpi_sin_sq_upper (by norm_num)
      _ < (345 : ℝ) := by norm_num

  have h_agrees : AgreesWithDisplayedWavelength setup .C := by
    rw [AgreesWithDisplayedWavelength, answerChoiceErrorMicrometers, abs_lt]
    simp only [AnswerChoice.wavelengthMicrometers]
    constructor <;> linarith only [h_lambda_lower, h_lambda_upper]
  have herror :
      |lengthInMicrometers setup.requiredPhotonWavelength - 344| < 1 := by
    simpa [AgreesWithDisplayedWavelength, answerChoiceErrorMicrometers,
      AnswerChoice.wavelengthMicrometers] using h_agrees
  refine ⟨h_agrees, ?_⟩
  intro other hother
  cases other with
  | A =>
      change
        |lengthInMicrometers setup.requiredPhotonWavelength - 344| <
          |lengthInMicrometers setup.requiredPhotonWavelength - 123|
      have hA :
          0 < lengthInMicrometers setup.requiredPhotonWavelength - 123 := by
        linarith only [h_lambda_lower]
      rw [abs_of_pos hA]
      linarith only [herror, h_lambda_lower]
  | B =>
      change
        |lengthInMicrometers setup.requiredPhotonWavelength - 344| <
          |lengthInMicrometers setup.requiredPhotonWavelength - 452|
      have hB :
          lengthInMicrometers setup.requiredPhotonWavelength - 452 < 0 := by
        linarith only [h_lambda_upper]
      rw [abs_of_neg hB]
      linarith only [herror, h_lambda_upper]
  | C => exact (hother rfl).elim
  | D =>
      change
        |lengthInMicrometers setup.requiredPhotonWavelength - 344| <
          |lengthInMicrometers setup.requiredPhotonWavelength - 425|
      have hD :
          lengthInMicrometers setup.requiredPhotonWavelength - 425 < 0 := by
        linarith only [h_lambda_upper]
      rw [abs_of_neg hD]
      linarith only [herror, h_lambda_upper]

end PhyXMiniProblems.ProblemPhyXMini0571
