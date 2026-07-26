import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0631

open Dimension

/-!
# A rotational--vibrational absorption line ending at `l = 0`

A colorless, odorless gas is one of `N₂`, `CO`, and `NO`.  The primary figure
shows the isotope mass numbers and bond lengths of all three candidates.  Five
near-infrared absorption wavelengths are measured.  They form the `P` and `R`
branches of a rigid-diatomic rotational--vibrational band, with the central
`Δl = 0` line absent.

Lengths, masses, moments of inertia, action, speed, and energy are represented
by unit-independent Physlib quantities.  Real numbers appear only as explicit
unit readouts, quantum numbers, or displayed measurements.  In particular,
the line quantum numbers and absorbed photon energies are independent fields:
no premise declares the `4.2972 μm` line to end at `l = 0`, and no premise sets
its energy equal to answer A.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The dimension of moment of inertia, mass times length squared. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- The dimension of action, equivalently energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent action such as reduced Planck action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-!
A signed-carrier speed quantity, matching the exact type of Physlib's
`DimSpeed.speedOfLight`.
-/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Picometre readout of a physical length. -/
def lengthInPicometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.picometers length

/-- Micrometre readout of a physical length. -/
def lengthInMicrometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.micrometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- A mass expressed as a dimensionless multiple of one atomic mass unit. -/
def massInAtomicMassUnits
    (mass atomicMassUnit : MassQuantity) : ℝ :=
  massInKilograms mass / massInKilograms atomicMassUnit

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

/-- Electron-volt readout of a physical energy. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Coherent-SI readout of a speed, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-! ## Molecular, figure, and spectrum vocabulary -/

/-- The three possible gases stated in the problem. -/
inductive MoleculeCandidate where
  | nitrogen
  | carbonMonoxide
  | nitricOxide
  deriving DecidableEq, Fintype, Repr

/-- Chemical-element labels visible beside the atoms in the figure. -/
inductive ChemicalElement where
  | nitrogen
  | carbon
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Left and right atomic sites of a depicted diatomic molecule. -/
inductive AtomSite where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Vertical positions of the three molecular diagrams in image `631.png`. -/
inductive FigureRow where
  | top
  | middle
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- Atom colors used in the raster to distinguish the elements. -/
inductive AtomColor where
  | blue
  | black
  | red
  deriving DecidableEq, Fintype, Repr

/-- The illumination named by the physical scenario. -/
inductive IlluminationKind where
  | whiteLight
  | other
  deriving DecidableEq, Repr

/-- The observed optical spectrum is an absorption rather than emission spectrum. -/
inductive SpectrumKind where
  | absorption
  | emission
  deriving DecidableEq, Repr

/-- Lower and upper vibrational manifolds of the observed band. -/
inductive VibrationalLevel where
  | lower
  | upper
  deriving DecidableEq, Fintype, Repr

/-!
Labels for the five bands, named by their wavelengths in units of
`10⁻⁴ μm`.  The declaration names are labels only; they do not encode any
rotational assignment.
-/
inductive AbsorptionBandLabel where
  | band42680
  | band42753
  | band42826
  | band42972
  | band43046
  deriving DecidableEq, Fintype, Repr

/-!
Literal content carried by the primary molecular-candidate figure.  Its mass
numbers and bond-length texts are scalar raster labels; independent physical
masses and lengths are stored in the setup below.
-/
structure DiatomicCandidatesFigure where
  rowIsShown : FigureRow → Bool
  moleculeAtRow : FigureRow → MoleculeCandidate
  atomIsShown : FigureRow → AtomSite → Bool
  elementAt : FigureRow → AtomSite → ChemicalElement
  atomicMassNumberLabel : FigureRow → AtomSite → ℕ
  atomColor : FigureRow → AtomSite → AtomColor
  bondIsShown : FigureRow → Bool
  bondLengthLabelPicometers : FigureRow → ℝ

/-!
Independent observables and quantum-number roles attached to one dark band.
The energy is not defined from its wavelength, and the final quantum number is
not defined from its label.
-/
structure AbsorptionBand where
  wavelength : LengthQuantity
  absorbedPhotonEnergy : DimEnergy
  initialRotationalQuantumNumber : ℕ
  finalRotationalQuantumNumber : ℕ

/-! ## Independent physical setup -/

/-!
The gas candidates, their rigid-rotor parameters, and the measured spectrum.
The vibrational term energies and full rovibrational energies are independent
dimensionful fields related only by the governing laws below.
-/
structure DiatomicAbsorptionSetup where
  absorbingMolecule : MoleculeCandidate
  gasIsColorless : Bool
  gasIsOdorless : Bool
  illumination : IlluminationKind
  spectrumKind : SpectrumKind
  atomMass : MoleculeCandidate → AtomSite → MassQuantity
  atomicMassUnit : MassQuantity
  equilibriumBondLength : MoleculeCandidate → LengthQuantity
  reducedMass : MoleculeCandidate → MassQuantity
  momentOfInertia : MoleculeCandidate → MomentOfInertiaQuantity
  vibrationalTermEnergy : MoleculeCandidate → VibrationalLevel → DimEnergy
  rovibrationalEnergy :
    MoleculeCandidate → VibrationalLevel → ℕ → DimEnergy
  absorptionBand : AbsorptionBandLabel → AbsorptionBand
  lineAppearsDark : AbsorptionBandLabel → Bool
  reducedPlanckAction : ActionQuantity
  vacuumLightSpeed : SpeedQuantity
  figure : DiatomicCandidatesFigure

/-! ## Scenario, figure evidence, and measured data -/

/-- Qualitative information stated in the prose scenario. -/
structure MatchesGasAbsorptionScenario
    (setup : DiatomicAbsorptionSetup) : Prop where
  colorlessGas : setup.gasIsColorless = true
  odorlessGas : setup.gasIsOdorless = true
  illuminatedByWhiteLight : setup.illumination = .whiteLight
  observedSpectrumIsAbsorption : setup.spectrumKind = .absorption
  eachListedBandIsDark : ∀ label, setup.lineAppearsDark label = true

/-!
Exact labels and qualitative geometry transcribed from the primary image.
The final three fields connect each displayed bond-length readout to the
corresponding independent physical candidate length.  Nothing here concerns a
spectral-line assignment or absorbed-energy answer.
-/
structure MatchesPrimaryDiatomicCandidatesFigure
    (setup : DiatomicAbsorptionSetup) : Prop where
  everyRowShown : ∀ row, setup.figure.rowIsShown row = true
  topIsNitrogen : setup.figure.moleculeAtRow .top = .nitrogen
  middleIsCarbonMonoxide :
    setup.figure.moleculeAtRow .middle = .carbonMonoxide
  bottomIsNitricOxide : setup.figure.moleculeAtRow .bottom = .nitricOxide
  everyAtomShown : ∀ row site, setup.figure.atomIsShown row site = true
  topLeftNitrogen : setup.figure.elementAt .top .left = .nitrogen
  topRightNitrogen : setup.figure.elementAt .top .right = .nitrogen
  middleLeftCarbon : setup.figure.elementAt .middle .left = .carbon
  middleRightOxygen : setup.figure.elementAt .middle .right = .oxygen
  bottomLeftNitrogen : setup.figure.elementAt .bottom .left = .nitrogen
  bottomRightOxygen : setup.figure.elementAt .bottom .right = .oxygen
  topLeftMassNumber : setup.figure.atomicMassNumberLabel .top .left = 14
  topRightMassNumber : setup.figure.atomicMassNumberLabel .top .right = 14
  middleLeftMassNumber : setup.figure.atomicMassNumberLabel .middle .left = 12
  middleRightMassNumber : setup.figure.atomicMassNumberLabel .middle .right = 16
  bottomLeftMassNumber : setup.figure.atomicMassNumberLabel .bottom .left = 14
  bottomRightMassNumber : setup.figure.atomicMassNumberLabel .bottom .right = 16
  topAtomsBlue : ∀ site, setup.figure.atomColor .top site = .blue
  middleLeftBlack : setup.figure.atomColor .middle .left = .black
  middleRightRed : setup.figure.atomColor .middle .right = .red
  bottomLeftBlue : setup.figure.atomColor .bottom .left = .blue
  bottomRightRed : setup.figure.atomColor .bottom .right = .red
  everyBondShown : ∀ row, setup.figure.bondIsShown row = true
  topBondLabelPicometers :
    setup.figure.bondLengthLabelPicometers .top = 110
  middleBondLabelPicometers :
    setup.figure.bondLengthLabelPicometers .middle = 118
  bottomBondLabelPicometers :
    setup.figure.bondLengthLabelPicometers .bottom = 115
  nitrogenBondLengthMatchesFigure :
    lengthInPicometers (setup.equilibriumBondLength .nitrogen) =
      setup.figure.bondLengthLabelPicometers .top
  carbonMonoxideBondLengthMatchesFigure :
    lengthInPicometers (setup.equilibriumBondLength .carbonMonoxide) =
      setup.figure.bondLengthLabelPicometers .middle
  nitricOxideBondLengthMatchesFigure :
    lengthInPicometers (setup.equilibriumBondLength .nitricOxide) =
      setup.figure.bondLengthLabelPicometers .bottom

/-- Agreement with a wavelength printed to four decimal places in micrometres. -/
def AgreesWithFourDecimalMicrometerReadout
    (wavelength : LengthQuantity) (displayedMicrometers : ℝ) : Prop :=
  |lengthInMicrometers wavelength - displayedMicrometers| <
    (1 / 20000 : ℝ)

/-- The five wavelength readouts supplied in the problem statement. -/
structure MatchesGivenAbsorptionWavelengths
    (setup : DiatomicAbsorptionSetup) : Prop where
  band42680Readout :
    AgreesWithFourDecimalMicrometerReadout
      (setup.absorptionBand .band42680).wavelength 4.2680
  band42753Readout :
    AgreesWithFourDecimalMicrometerReadout
      (setup.absorptionBand .band42753).wavelength 4.2753
  band42826Readout :
    AgreesWithFourDecimalMicrometerReadout
      (setup.absorptionBand .band42826).wavelength 4.2826
  band42972Readout :
    AgreesWithFourDecimalMicrometerReadout
      (setup.absorptionBand .band42972).wavelength 4.2972
  band43046Readout :
    AgreesWithFourDecimalMicrometerReadout
      (setup.absorptionBand .band43046).wavelength 4.3046

/-!
Atomic-mass-number approximation and universal constants used by the textbook
model.  Physlib grounds `ℏ`, the electron volt, and the speed of light.  This
reference data does not select an absorbing gas, spectral line, or answer.
-/
structure UsesTextbookReferenceData
    (setup : DiatomicAbsorptionSetup) : Prop where
  atomicMassUnitKilograms :
    massInKilograms setup.atomicMassUnit = 1.66053906660e-27
  nitrogenLeftMassNumberApproximation :
    massInAtomicMassUnits
      (setup.atomMass .nitrogen .left) setup.atomicMassUnit = 14
  nitrogenRightMassNumberApproximation :
    massInAtomicMassUnits
      (setup.atomMass .nitrogen .right) setup.atomicMassUnit = 14
  carbonMonoxideLeftMassNumberApproximation :
    massInAtomicMassUnits
      (setup.atomMass .carbonMonoxide .left) setup.atomicMassUnit = 12
  carbonMonoxideRightMassNumberApproximation :
    massInAtomicMassUnits
      (setup.atomMass .carbonMonoxide .right) setup.atomicMassUnit = 16
  nitricOxideLeftMassNumberApproximation :
    massInAtomicMassUnits
      (setup.atomMass .nitricOxide .left) setup.atomicMassUnit = 14
  nitricOxideRightMassNumberApproximation :
    massInAtomicMassUnits
      (setup.atomMass .nitricOxide .right) setup.atomicMassUnit = 16
  reducedPlanckActionJouleSeconds :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)
  standardVacuumLightSpeed :
    speedInMetersPerSecond setup.vacuumLightSpeed =
      speedInMetersPerSecond DimSpeed.speedOfLight

/-- Positivity and nondegeneracy conditions selecting physical parameters. -/
structure HasPhysicalDiatomicAbsorptionParameters
    (setup : DiatomicAbsorptionSetup) : Prop where
  everyAtomicMassPositive : ∀ molecule site,
    0 < massInKilograms (setup.atomMass molecule site)
  atomicMassUnitPositive : 0 < massInKilograms setup.atomicMassUnit
  everyBondLengthPositive : ∀ molecule,
    0 < lengthInMeters (setup.equilibriumBondLength molecule)
  everyReducedMassPositive : ∀ molecule,
    0 < massInKilograms (setup.reducedMass molecule)
  everyMomentOfInertiaPositive : ∀ molecule,
    0 < momentOfInertiaInKilogramMetersSquared
      (setup.momentOfInertia molecule)
  everyBandWavelengthPositive : ∀ label,
    0 < lengthInMeters (setup.absorptionBand label).wavelength
  everyAbsorbedEnergyPositive : ∀ label,
    0 < energyInJoules (setup.absorptionBand label).absorbedPhotonEnergy
  reducedPlanckActionPositive :
    0 < actionInJouleSeconds setup.reducedPlanckAction
  vacuumLightSpeedPositive :
    0 < speedInMetersPerSecond setup.vacuumLightSpeed
  electronVoltPositive : 0 < energyInJoules DimEnergy.electronVolt

/-! ## Governing molecular and spectroscopic laws -/

/-!
Two-body center-of-mass geometry for every candidate: the reduced mass obeys
`μ(m₁+m₂)=m₁m₂`, and a rigid diatomic of separation `r` has `I=μr²`.
-/
structure SatisfiesDiatomicMomentOfInertiaLaws
    (setup : DiatomicAbsorptionSetup) : Prop where
  reducedMassRelation : ∀ molecule,
    massInKilograms (setup.reducedMass molecule) *
        (massInKilograms (setup.atomMass molecule .left) +
          massInKilograms (setup.atomMass molecule .right)) =
      massInKilograms (setup.atomMass molecule .left) *
        massInKilograms (setup.atomMass molecule .right)
  rigidDiatomicMomentOfInertia : ∀ molecule,
    momentOfInertiaInKilogramMetersSquared
        (setup.momentOfInertia molecule) =
      massInKilograms (setup.reducedMass molecule) *
        lengthInMeters (setup.equilibriumBondLength molecule) ^ 2

/-!
The governing rigid-rotor and photon laws:

* within either vibrational manifold,
  `E(v,l) = G(v) + ℏ² l(l+1)/(2I)`;
* a band photon supplies the upper-minus-lower rovibrational gap;
* `Eγ λ = h c = 2πℏc`;
* the dipole rotational selection rule is `Δl = ±1`; and
* five distinct lines originate in the lowest states `l = 0,1,2`.

The final two clauses express the prose statement that the five lines are the
transitions from the lowest rotational states.  They do not associate any
particular wavelength label with any particular transition.
-/
structure SatisfiesRigidRotorAbsorptionLaws
    (setup : DiatomicAbsorptionSetup) : Prop where
  rigidRotorRovibrationalSpectrum :
    ∀ molecule vibration (l : ℕ),
      energyInJoules (setup.rovibrationalEnergy molecule vibration l) =
        energyInJoules (setup.vibrationalTermEnergy molecule vibration) +
          actionInJouleSeconds setup.reducedPlanckAction ^ 2 *
              (l : ℝ) * ((l : ℝ) + 1) /
            (2 * momentOfInertiaInKilogramMetersSquared
              (setup.momentOfInertia molecule))
  photonEnergyIsRovibrationalGap : ∀ label,
    energyInJoules (setup.absorptionBand label).absorbedPhotonEnergy =
      energyInJoules
          (setup.rovibrationalEnergy setup.absorbingMolecule .upper
            (setup.absorptionBand label).finalRotationalQuantumNumber) -
        energyInJoules
          (setup.rovibrationalEnergy setup.absorbingMolecule .lower
            (setup.absorptionBand label).initialRotationalQuantumNumber)
  planckEinsteinWavelengthLaw : ∀ label,
    energyInJoules (setup.absorptionBand label).absorbedPhotonEnergy *
        lengthInMeters (setup.absorptionBand label).wavelength =
      2 * Real.pi * actionInJouleSeconds setup.reducedPlanckAction *
        speedInMetersPerSecond setup.vacuumLightSpeed
  rotationalSelectionRule : ∀ label,
    (setup.absorptionBand label).finalRotationalQuantumNumber =
        (setup.absorptionBand label).initialRotationalQuantumNumber + 1 ∨
      (setup.absorptionBand label).initialRotationalQuantumNumber =
        (setup.absorptionBand label).finalRotationalQuantumNumber + 1
  originatesInLowestRotationalStates : ∀ label,
    (setup.absorptionBand label).initialRotationalQuantumNumber ≤ 2
  distinctTransitionAssignments : Function.Injective fun label =>
    ((setup.absorptionBand label).initialRotationalQuantumNumber,
      (setup.absorptionBand label).finalRotationalQuantumNumber)

/-! ## Displayed choices and target conclusions -/

/-- Labels of the four absorbed-energy choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The energy printed beside each answer label, in electron volts. -/
def displayedEnergyElectronVolts : AnswerChoice → ℝ
  | .A => 0.288528
  | .B => 0.298528
  | .C => 0.281258
  | .D => 0.282145

/-- Dataset metadata recording answer A; deliberately not used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Error between a band's physical energy and a displayed choice. -/
def answerEnergyErrorElectronVolts
    (setup : DiatomicAbsorptionSetup)
    (label : AbsorptionBandLabel) (choice : AnswerChoice) : ℝ :=
  |energyInElectronVolts (setup.absorptionBand label).absorbedPhotonEnergy -
    displayedEnergyElectronVolts choice|

/-!
Agreement with the source answer to `10⁻⁵ eV`.  This tolerance covers the
four-decimal-place wavelength readout and the rounding conventions used in the
answer list.
-/
def AgreesWithDisplayedEnergy
    (setup : DiatomicAbsorptionSetup)
    (label : AbsorptionBandLabel) (choice : AnswerChoice) : Prop :=
  answerEnergyErrorElectronVolts setup label choice < 1e-5

/-- The selected energy is strictly closer than every other displayed choice. -/
def IsUniqueClosestEnergyChoice
    (setup : DiatomicAbsorptionSetup)
    (label : AbsorptionBandLabel) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerEnergyErrorElectronVolts setup label choice <
      answerEnergyErrorElectronVolts setup label other

/-!
The ordered wavelengths, positive rigid-rotor spacing, `Δl = ±1`, and complete
set of distinct lowest-state transitions identify the first line on the
long-wavelength (`P`) side as `l = 1 → 0`.  This is a derived assignment, not
a premise.
-/
lemma band42972_is_transition_one_to_zero
    (setup : DiatomicAbsorptionSetup)
    (_wavelengths : MatchesGivenAbsorptionWavelengths setup)
    (_physical : HasPhysicalDiatomicAbsorptionParameters setup)
    (_laws : SatisfiesRigidRotorAbsorptionLaws setup) :
    (setup.absorptionBand .band42972).initialRotationalQuantumNumber = 1 ∧
      (setup.absorptionBand .band42972).finalRotationalQuantumNumber = 0 := by
  let wavelengthMicrometers (label : AbsorptionBandLabel) : ℝ :=
    lengthInMicrometers (setup.absorptionBand label).wavelength
  let wavelengthMeters (label : AbsorptionBandLabel) : ℝ :=
    lengthInMeters (setup.absorptionBand label).wavelength
  have wavelengthMeters_eq (label : AbsorptionBandLabel) :
      wavelengthMeters label = (1e-6 : ℝ) * wavelengthMicrometers label := by
    have h := (setup.absorptionBand label).wavelength.property
      ({UnitChoices.SI with length := LengthUnit.micrometers} : UnitChoices)
      UnitChoices.SI
    have hscale :
        ({UnitChoices.SI with length := LengthUnit.micrometers} :
          UnitChoices).dimScale UnitChoices.SI L𝓭 = (1e-6 : NNReal) := by
      rw [show LengthUnit.micrometers =
        LengthUnit.scale ((1 / 10 : ℝ) ^ 6) LengthUnit.meters by rfl]
      simp [UnitChoices.dimScale_apply]
      apply NNReal.eq
      rw [NNReal.coe_ofScientific]
      change (10 ^ 6 : ℝ)⁻¹ = 1e-6
      norm_num
    rw [WithDim.dim_apply, hscale] at h
    have hv := congrArg
      (fun y : WithDim L𝓭 NNReal => (y.val : ℝ)) h
    change
      (((setup.absorptionBand label).wavelength UnitChoices.SI).val : ℝ) =
        1e-6 *
          (((setup.absorptionBand label).wavelength
            ({UnitChoices.SI with length := LengthUnit.micrometers} :
              UnitChoices)).val : ℝ)
    exact hv
  have h42680 := _wavelengths.band42680Readout
  have h42753 := _wavelengths.band42753Readout
  have h42826 := _wavelengths.band42826Readout
  have h42972 := _wavelengths.band42972Readout
  have h43046 := _wavelengths.band43046Readout
  change |wavelengthMicrometers .band42680 - 4.2680| < (1 / 20000 : ℝ) at h42680
  change |wavelengthMicrometers .band42753 - 4.2753| < (1 / 20000 : ℝ) at h42753
  change |wavelengthMicrometers .band42826 - 4.2826| < (1 / 20000 : ℝ) at h42826
  change |wavelengthMicrometers .band42972 - 4.2972| < (1 / 20000 : ℝ) at h42972
  change |wavelengthMicrometers .band43046 - 4.3046| < (1 / 20000 : ℝ) at h43046
  rw [abs_lt] at h42680 h42753 h42826 h42972 h43046
  have hμ₁ :
      wavelengthMicrometers .band42680 < wavelengthMicrometers .band42753 := by
    norm_num at h42680 h42753 ⊢
    linarith
  have hμ₂ :
      wavelengthMicrometers .band42753 < wavelengthMicrometers .band42826 := by
    norm_num at h42753 h42826 ⊢
    linarith
  have hμ₃ :
      wavelengthMicrometers .band42826 < wavelengthMicrometers .band42972 := by
    norm_num at h42826 h42972 ⊢
    linarith
  have hμ₄ :
      wavelengthMicrometers .band42972 < wavelengthMicrometers .band43046 := by
    norm_num at h42972 h43046 ⊢
    linarith
  have hm₁ : wavelengthMeters .band42680 < wavelengthMeters .band42753 := by
    rw [wavelengthMeters_eq, wavelengthMeters_eq]
    norm_num
    exact hμ₁
  have hm₂ : wavelengthMeters .band42753 < wavelengthMeters .band42826 := by
    rw [wavelengthMeters_eq, wavelengthMeters_eq]
    norm_num
    exact hμ₂
  have hm₃ : wavelengthMeters .band42826 < wavelengthMeters .band42972 := by
    rw [wavelengthMeters_eq, wavelengthMeters_eq]
    norm_num
    exact hμ₃
  have hm₄ : wavelengthMeters .band42972 < wavelengthMeters .band43046 := by
    rw [wavelengthMeters_eq, wavelengthMeters_eq]
    norm_num
    exact hμ₄
  let photonEnergy (label : AbsorptionBandLabel) : ℝ :=
    energyInJoules (setup.absorptionBand label).absorbedPhotonEnergy
  have photonEnergy_pos (label : AbsorptionBandLabel) : 0 < photonEnergy label :=
    _physical.everyAbsorbedEnergyPositive label
  have wavelengthMeters_pos (label : AbsorptionBandLabel) :
      0 < wavelengthMeters label :=
    _physical.everyBandWavelengthPositive label
  have energy_decreases_with_wavelength
      {shorter longer : AbsorptionBandLabel}
      (hwavelength : wavelengthMeters shorter < wavelengthMeters longer) :
      photonEnergy longer < photonEnergy shorter := by
    have hshort := _laws.planckEinsteinWavelengthLaw shorter
    have hlong := _laws.planckEinsteinWavelengthLaw longer
    change photonEnergy shorter * wavelengthMeters shorter =
      2 * Real.pi * actionInJouleSeconds setup.reducedPlanckAction *
        speedInMetersPerSecond setup.vacuumLightSpeed at hshort
    change photonEnergy longer * wavelengthMeters longer =
      2 * Real.pi * actionInJouleSeconds setup.reducedPlanckAction *
        speedInMetersPerSecond setup.vacuumLightSpeed at hlong
    by_contra hnot
    have hle : photonEnergy shorter ≤ photonEnergy longer :=
      le_of_not_gt hnot
    have hprod_le :
        photonEnergy shorter * wavelengthMeters shorter ≤
          photonEnergy longer * wavelengthMeters shorter :=
      mul_le_mul_of_nonneg_right hle (le_of_lt (wavelengthMeters_pos shorter))
    have hprod_lt :
        photonEnergy longer * wavelengthMeters shorter <
          photonEnergy longer * wavelengthMeters longer :=
      mul_lt_mul_of_pos_left hwavelength (photonEnergy_pos longer)
    have hfalse := lt_of_le_of_lt hprod_le hprod_lt
    rw [hshort, hlong] at hfalse
    exact (lt_irrefl _ hfalse)
  have he₁ : photonEnergy .band43046 < photonEnergy .band42972 :=
    energy_decreases_with_wavelength hm₄
  have he₂ : photonEnergy .band42972 < photonEnergy .band42826 :=
    energy_decreases_with_wavelength hm₃
  have he₃ : photonEnergy .band42826 < photonEnergy .band42753 :=
    energy_decreases_with_wavelength hm₂
  have he₄ : photonEnergy .band42753 < photonEnergy .band42680 :=
    energy_decreases_with_wavelength hm₁
  let rotationCoefficient : ℝ :=
    actionInJouleSeconds setup.reducedPlanckAction ^ 2 /
      (2 * momentOfInertiaInKilogramMetersSquared
        (setup.momentOfInertia setup.absorbingMolecule))
  let vibrationalGap : ℝ :=
    energyInJoules
        (setup.vibrationalTermEnergy setup.absorbingMolecule .upper) -
      energyInJoules
        (setup.vibrationalTermEnergy setup.absorbingMolecule .lower)
  let rotationalTerm (label : AbsorptionBandLabel) : ℝ :=
    ((setup.absorptionBand label).finalRotationalQuantumNumber : ℝ) *
        (((setup.absorptionBand label).finalRotationalQuantumNumber : ℝ) + 1) -
      ((setup.absorptionBand label).initialRotationalQuantumNumber : ℝ) *
        (((setup.absorptionBand label).initialRotationalQuantumNumber : ℝ) + 1)
  have rotationCoefficient_pos : 0 < rotationCoefficient := by
    dsimp [rotationCoefficient]
    exact div_pos
      (pow_pos _physical.reducedPlanckActionPositive 2)
      (mul_pos (by norm_num)
        (_physical.everyMomentOfInertiaPositive setup.absorbingMolecule))
  have photonEnergy_formula (label : AbsorptionBandLabel) :
      photonEnergy label =
        vibrationalGap + rotationCoefficient * rotationalTerm label := by
    dsimp [photonEnergy]
    rw [_laws.photonEnergyIsRovibrationalGap label]
    rw [_laws.rigidRotorRovibrationalSpectrum
      setup.absorbingMolecule .upper
        (setup.absorptionBand label).finalRotationalQuantumNumber]
    rw [_laws.rigidRotorRovibrationalSpectrum
      setup.absorbingMolecule .lower
        (setup.absorptionBand label).initialRotationalQuantumNumber]
    dsimp [vibrationalGap, rotationCoefficient, rotationalTerm]
    ring
  have rotationalTerm_increases_with_energy
      {lowerEnergy higherEnergy : AbsorptionBandLabel}
      (henergy : photonEnergy lowerEnergy < photonEnergy higherEnergy) :
      rotationalTerm lowerEnergy < rotationalTerm higherEnergy := by
    rw [photonEnergy_formula, photonEnergy_formula] at henergy
    by_contra hnot
    have hle : rotationalTerm higherEnergy ≤ rotationalTerm lowerEnergy :=
      le_of_not_gt hnot
    have hmul :
        rotationCoefficient * rotationalTerm higherEnergy ≤
          rotationCoefficient * rotationalTerm lowerEnergy :=
      mul_le_mul_of_nonneg_left hle (le_of_lt rotationCoefficient_pos)
    linarith
  have ht₁ : rotationalTerm .band43046 < rotationalTerm .band42972 :=
    rotationalTerm_increases_with_energy he₁
  have ht₂ : rotationalTerm .band42972 < rotationalTerm .band42826 :=
    rotationalTerm_increases_with_energy he₂
  have ht₃ : rotationalTerm .band42826 < rotationalTerm .band42753 :=
    rotationalTerm_increases_with_energy he₃
  have ht₄ : rotationalTerm .band42753 < rotationalTerm .band42680 :=
    rotationalTerm_increases_with_energy he₄
  have transition_cases (label : AbsorptionBandLabel) :
      ((setup.absorptionBand label).initialRotationalQuantumNumber = 0 ∧
          (setup.absorptionBand label).finalRotationalQuantumNumber = 1) ∨
        ((setup.absorptionBand label).initialRotationalQuantumNumber = 1 ∧
          (setup.absorptionBand label).finalRotationalQuantumNumber = 0) ∨
        ((setup.absorptionBand label).initialRotationalQuantumNumber = 1 ∧
          (setup.absorptionBand label).finalRotationalQuantumNumber = 2) ∨
        ((setup.absorptionBand label).initialRotationalQuantumNumber = 2 ∧
          (setup.absorptionBand label).finalRotationalQuantumNumber = 1) ∨
        ((setup.absorptionBand label).initialRotationalQuantumNumber = 2 ∧
          (setup.absorptionBand label).finalRotationalQuantumNumber = 3) := by
    have hselection := _laws.rotationalSelectionRule label
    have hlow := _laws.originatesInLowestRotationalStates label
    omega
  have rotationalTerm_cases (label : AbsorptionBandLabel) :
      rotationalTerm label = -4 ∨ rotationalTerm label = -2 ∨
        rotationalTerm label = 2 ∨ rotationalTerm label = 4 ∨
          rotationalTerm label = 6 := by
    rcases transition_cases label with h | h | h | h | h
    all_goals rcases h with ⟨hinitial, hfinal⟩
    all_goals norm_num [rotationalTerm, hinitial, hfinal]
  have gap_of_allowed_terms {x y : ℝ}
      (hx : x = -4 ∨ x = -2 ∨ x = 2 ∨ x = 4 ∨ x = 6)
      (hy : y = -4 ∨ y = -2 ∨ y = 2 ∨ y = 4 ∨ y = 6)
      (hxy : x < y) : x + 2 ≤ y := by
    rcases hx with hx | hx | hx | hx | hx <;>
      subst x <;>
      rcases hy with hy | hy | hy | hy | hy <;>
      subst y <;>
      norm_num at hxy <;>
      norm_num
  have hgap₂ :
      rotationalTerm .band42972 + 2 ≤ rotationalTerm .band42826 :=
    gap_of_allowed_terms
      (rotationalTerm_cases .band42972)
      (rotationalTerm_cases .band42826) ht₂
  have hgap₃ :
      rotationalTerm .band42826 + 2 ≤ rotationalTerm .band42753 :=
    gap_of_allowed_terms
      (rotationalTerm_cases .band42826)
      (rotationalTerm_cases .band42753) ht₃
  have hgap₄ :
      rotationalTerm .band42753 + 2 ≤ rotationalTerm .band42680 :=
    gap_of_allowed_terms
      (rotationalTerm_cases .band42753)
      (rotationalTerm_cases .band42680) ht₄
  have htop : rotationalTerm .band42680 ≤ 6 := by
    rcases rotationalTerm_cases .band42680 with h | h | h | h | h <;>
      linarith
  have hbottom : -4 ≤ rotationalTerm .band43046 := by
    rcases rotationalTerm_cases .band43046 with h | h | h | h | h <;>
      linarith
  have hmiddle : rotationalTerm .band42972 ≤ 0 := by
    linarith
  have hterm42972 : rotationalTerm .band42972 = -2 := by
    rcases rotationalTerm_cases .band42972 with h | h | h | h | h <;>
      linarith
  rcases transition_cases .band42972 with h | h | h | h | h
  · norm_num [rotationalTerm, h.1, h.2] at hterm42972
  · exact h
  · norm_num [rotationalTerm, h.1, h.2] at hterm42972
  · norm_num [rotationalTerm, h.1, h.2] at hterm42972
  · norm_num [rotationalTerm, h.1, h.2] at hterm42972

/-!
Applying `Eγλ = hc` to the measured `4.2972 μm` wavelength gives an energy
within `10⁻⁵ eV` of `0.288528 eV`, and choice A is uniquely closest.
-/
lemma band42972_energy_is_choiceA
    (setup : DiatomicAbsorptionSetup)
    (_wavelengths : MatchesGivenAbsorptionWavelengths setup)
    (_reference : UsesTextbookReferenceData setup)
    (_physical : HasPhysicalDiatomicAbsorptionParameters setup)
    (_laws : SatisfiesRigidRotorAbsorptionLaws setup) :
    AgreesWithDisplayedEnergy setup .band42972 .A ∧
      IsUniqueClosestEnergyChoice setup .band42972 .A := by
  let wavelengthMicrometers : ℝ :=
    lengthInMicrometers (setup.absorptionBand .band42972).wavelength
  let wavelengthMeters : ℝ :=
    lengthInMeters (setup.absorptionBand .band42972).wavelength
  let photonEnergyJoules : ℝ :=
    energyInJoules (setup.absorptionBand .band42972).absorbedPhotonEnergy
  let photonEnergyElectronVolts : ℝ :=
    energyInElectronVolts
      (setup.absorptionBand .band42972).absorbedPhotonEnergy
  have wavelengthMeters_eq :
      wavelengthMeters = (1e-6 : ℝ) * wavelengthMicrometers := by
    have h := (setup.absorptionBand .band42972).wavelength.property
      ({UnitChoices.SI with length := LengthUnit.micrometers} : UnitChoices)
      UnitChoices.SI
    have hscale :
        ({UnitChoices.SI with length := LengthUnit.micrometers} :
          UnitChoices).dimScale UnitChoices.SI L𝓭 = (1e-6 : NNReal) := by
      rw [show LengthUnit.micrometers =
        LengthUnit.scale ((1 / 10 : ℝ) ^ 6) LengthUnit.meters by rfl]
      simp [UnitChoices.dimScale_apply]
      apply NNReal.eq
      rw [NNReal.coe_ofScientific]
      change (10 ^ 6 : ℝ)⁻¹ = 1e-6
      norm_num
    rw [WithDim.dim_apply, hscale] at h
    have hv := congrArg
      (fun y : WithDim L𝓭 NNReal => (y.val : ℝ)) h
    change
      (((setup.absorptionBand .band42972).wavelength UnitChoices.SI).val :
        ℝ) =
        1e-6 *
          (((setup.absorptionBand .band42972).wavelength
            ({UnitChoices.SI with length := LengthUnit.micrometers} :
              UnitChoices)).val : ℝ)
    exact hv
  have wavelength_readout := _wavelengths.band42972Readout
  change |wavelengthMicrometers - 4.2972| < (1 / 20000 : ℝ) at wavelength_readout
  rw [abs_lt] at wavelength_readout
  norm_num at wavelength_readout
  have speed_of_light_value :
      speedInMetersPerSecond setup.vacuumLightSpeed = 299792458 := by
    rw [_reference.standardVacuumLightSpeed]
    simp [speedInMetersPerSecond]
  have electron_volt_value :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have photonEnergyJoules_pos : 0 < photonEnergyJoules :=
    _physical.everyAbsorbedEnergyPositive .band42972
  have photonEnergyElectronVolts_pos : 0 < photonEnergyElectronVolts := by
    dsimp [photonEnergyElectronVolts, energyInElectronVolts]
    positivity
  have energy_conversion :
      photonEnergyJoules =
        photonEnergyElectronVolts * 1.602176634e-19 := by
    dsimp [photonEnergyJoules, photonEnergyElectronVolts,
      energyInElectronVolts]
    rw [electron_volt_value]
    field_simp
  have planck_law := _laws.planckEinsteinWavelengthLaw .band42972
  change photonEnergyJoules * wavelengthMeters =
    2 * Real.pi * actionInJouleSeconds setup.reducedPlanckAction *
      speedInMetersPerSecond setup.vacuumLightSpeed at planck_law
  rw [wavelengthMeters_eq, energy_conversion,
    _reference.reducedPlanckActionJouleSeconds,
    speed_of_light_value] at planck_law
  have normalized_planck_law :
      photonEnergyElectronVolts * wavelengthMicrometers =
        (2 * 1.054571817e-34 * 299792458 /
          (1.602176634e-19 * 1e-6)) * Real.pi := by
    norm_num [Constants.ℏ] at planck_law ⊢
    nlinarith
  have wavelengthMicrometers_pos : 0 < wavelengthMicrometers := by
    linarith [wavelength_readout.1]
  have photonEnergy_lower :
      (0.288518 : ℝ) < photonEnergyElectronVolts := by
    by_contra hnot
    have henergy_le :
        photonEnergyElectronVolts ≤ (0.288518 : ℝ) :=
      le_of_not_gt hnot
    have hwavelength_lt : wavelengthMicrometers < (4.29725 : ℝ) := by
      linarith [wavelength_readout.2]
    have hproduct_le :
        photonEnergyElectronVolts * wavelengthMicrometers ≤
          (0.288518 : ℝ) * wavelengthMicrometers :=
      mul_le_mul_of_nonneg_right henergy_le
        (le_of_lt wavelengthMicrometers_pos)
    have hproduct_lt :
        (0.288518 : ℝ) * wavelengthMicrometers <
          (0.288518 : ℝ) * 4.29725 :=
      mul_lt_mul_of_pos_left hwavelength_lt (by norm_num)
    have hcontradiction := lt_of_le_of_lt hproduct_le hproduct_lt
    rw [normalized_planck_law] at hcontradiction
    norm_num at hcontradiction
    nlinarith [Real.pi_gt_d20]
  have photonEnergy_upper :
      photonEnergyElectronVolts < (0.288538 : ℝ) := by
    by_contra hnot
    have henergy_ge :
        (0.288538 : ℝ) ≤ photonEnergyElectronVolts :=
      le_of_not_gt hnot
    have hwavelength_gt : (4.29715 : ℝ) < wavelengthMicrometers := by
      linarith [wavelength_readout.1]
    have hproduct_lt :
        (0.288538 : ℝ) * 4.29715 <
          (0.288538 : ℝ) * wavelengthMicrometers :=
      mul_lt_mul_of_pos_left hwavelength_gt (by norm_num)
    have hproduct_le :
        (0.288538 : ℝ) * wavelengthMicrometers ≤
          photonEnergyElectronVolts * wavelengthMicrometers :=
      mul_le_mul_of_nonneg_right henergy_ge
        (le_of_lt wavelengthMicrometers_pos)
    have hcontradiction := lt_of_lt_of_le hproduct_lt hproduct_le
    rw [normalized_planck_law] at hcontradiction
    norm_num at hcontradiction
    nlinarith [Real.pi_lt_d20]
  have agrees_with_A :
      |photonEnergyElectronVolts - 0.288528| < (1e-5 : ℝ) := by
    rw [abs_lt]
    constructor <;> norm_num <;> linarith
  constructor
  · exact agrees_with_A
  · intro other hother
    fin_cases other
    · exact (hother rfl).elim
    · change
        |photonEnergyElectronVolts - 0.288528| <
          |photonEnergyElectronVolts - 0.298528|
      have hnegative :
          photonEnergyElectronVolts - 0.298528 < 0 := by
        linarith [photonEnergy_upper]
      rw [abs_of_neg hnegative]
      norm_num at ⊢
      linarith [agrees_with_A]
    · change
        |photonEnergyElectronVolts - 0.288528| <
          |photonEnergyElectronVolts - 0.281258|
      have hpositive :
          0 < photonEnergyElectronVolts - 0.281258 := by
        linarith [photonEnergy_lower]
      rw [abs_of_pos hpositive]
      norm_num at ⊢
      linarith [agrees_with_A]
    · change
        |photonEnergyElectronVolts - 0.288528| <
          |photonEnergyElectronVolts - 0.282145|
      have hpositive :
          0 < photonEnergyElectronVolts - 0.282145 := by
        linarith [photonEnergy_lower]
      rw [abs_of_pos hpositive]
      norm_num at ⊢
      linarith [agrees_with_A]

/-!
Among the five absorbed energies, the `4.2972 μm` band is the transition to
`l = 0`, and its absorbed energy uniquely selects answer A (`0.288528 eV`).

This formalizes `thm:physics:phyx_mini_0631:target`.  Neither its rotational
assignment nor its energy answer occurs in any theorem premise.
-/
theorem problem_phyx_mini_0631
    (setup : DiatomicAbsorptionSetup)
    (_scenario : MatchesGasAbsorptionScenario setup)
    (_figure : MatchesPrimaryDiatomicCandidatesFigure setup)
    (_wavelengths : MatchesGivenAbsorptionWavelengths setup)
    (_reference : UsesTextbookReferenceData setup)
    (_physical : HasPhysicalDiatomicAbsorptionParameters setup)
    (_geometry : SatisfiesDiatomicMomentOfInertiaLaws setup)
    (_laws : SatisfiesRigidRotorAbsorptionLaws setup) :
    (setup.absorptionBand .band42972).initialRotationalQuantumNumber = 1 ∧
      (setup.absorptionBand .band42972).finalRotationalQuantumNumber = 0 ∧
      AgreesWithDisplayedEnergy setup .band42972 .A ∧
      IsUniqueClosestEnergyChoice setup .band42972 .A := by
  have htransition :=
    band42972_is_transition_one_to_zero
      setup _wavelengths _physical _laws
  have henergy :=
    band42972_energy_is_choiceA
      setup _wavelengths _reference _physical _laws
  exact ⟨htransition.1, htransition.2, henergy.1, henergy.2⟩

end PhyXMiniProblems.ProblemPhyXMini0631
