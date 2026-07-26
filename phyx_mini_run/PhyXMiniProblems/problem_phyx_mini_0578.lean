import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0578

open Dimension

/-!
# Internal magnetic field inferred from the sodium doublet

Excited sodium atoms emit two nearby lines at `588.995 nm` and `589.592 nm`.
The primary image shows two split upper levels, jointly labelled
`n = 3, ℓ = 1`, and a common lower level labelled `n = 3, ℓ = 0`. The
shorter-wavelength arrow begins at the higher upper member.

Wavelengths, energies, Planck action, electron spin magnetic moment, and
magnetic-field strength remain unit-independent physical quantities. Real
numbers appear only at named-unit readout boundaries, as raster coordinates,
or as the printed multiple-choice values. The requested field is an
independent setup quantity constrained by radiative and Zeeman laws; it is not
defined from the answer choice.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The physical dimension of energy, `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of action, energy multiplied by time. -/
def actionDimension : Dimension := energyDimension * T𝓭

/-- The physical dimension `M T⁻¹ C⁻¹` of magnetic-field strength. -/
def magneticFieldStrengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension of magnetic moment, energy divided by field. -/
def magneticMomentDimension : Dimension :=
  energyDimension * magneticFieldStrengthDimension⁻¹

/-- A nonnegative, unit-independent physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical quantity with the dimension of Planck's constant. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative magnitude of magnetic-field strength. -/
abbrev MagneticFieldStrengthQuantity : Type :=
  Dimensionful (WithDim magneticFieldStrengthDimension NNReal)

/-- A nonnegative magnitude of an electron spin magnetic moment. -/
abbrev MagneticMomentMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticMomentDimension NNReal)

/-- Read a physical wavelength in a selected length unit. -/
def wavelengthReadout
    (unit : LengthUnit) (wavelength : WavelengthQuantity) : ℝ :=
  ((wavelength {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical wavelength in metres. -/
def wavelengthInMeters (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.meters wavelength

/-- Read a physical wavelength in nanometres. -/
def wavelengthInNanometers (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.nanometers wavelength

/-- Read a physical energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read physical action in coherent-SI joule-seconds. -/
def planckConstantInJouleSeconds
    (constant : PlanckConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Read magnetic-field strength in coherent-SI teslas. -/
def magneticFieldStrengthInTeslas
    (strength : MagneticFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read magnetic-moment magnitude in coherent-SI joules per tesla. -/
def magneticMomentInJoulesPerTesla
    (moment : MagneticMomentMagnitudeQuantity) : ℝ :=
  ((moment UnitChoices.SI).val : ℝ)

/-- Physlib's vacuum light speed, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Exact coherent-SI calibration of the ordinary Planck constant. -/
def ordinaryPlanckConstantSIValue : ℝ :=
  (6.62607015 : ℝ) * 10 ^ (-34 : ℤ)

/-- Standard coherent-SI calibration of the Bohr magneton. -/
def bohrMagnetonSIValue : ℝ :=
  (9.2740100783 : ℝ) * 10 ^ (-24 : ℤ)

/-! ## Atomic levels, spin orientations, and spectral lines -/

/-- The two members of the spin-split upper `3p` level. -/
inductive UpperDoubletMember where
  | higherEnergy
  | lowerEnergy
  deriving DecidableEq, Fintype, Repr

/-- The common lower `3s` level and the two upper `3p` levels. -/
inductive AtomicLevel where
  | lower3s
  | upper3pHigher
  | upper3pLower
  deriving DecidableEq, Fintype, Repr

/-- Regard an upper-doublet member as its atomic level. -/
def upperAtomicLevel : UpperDoubletMember → AtomicLevel
  | .higherEnergy => .upper3pHigher
  | .lowerEnergy => .upper3pLower

/-- Both pictured manifolds have principal quantum number `n = 3`. -/
def principalQuantumNumber : AtomicLevel → Nat
  | .lower3s => 3
  | .upper3pHigher => 3
  | .upper3pLower => 3

/-- The lower level has `ℓ = 0`; both upper members have `ℓ = 1`. -/
def orbitalAngularMomentumQuantumNumber : AtomicLevel → Nat
  | .lower3s => 0
  | .upper3pHigher => 1
  | .upper3pLower => 1

/-- The two spin magnetic-moment orientations named in the problem. -/
inductive SpinOrientation where
  | parallel
  | antiparallel
  deriving DecidableEq, Fintype, Repr

/-- Sign in `-μ · B`: parallel has shift `-μB`, antiparallel has `+μB`. -/
def zeemanEnergySign : SpinOrientation → ℝ
  | .parallel => -1
  | .antiparallel => 1

/-- The two sodium-doublet emission lines printed in the source. -/
inductive DoubletLine where
  | shorter588995
  | longer589592
  deriving DecidableEq, Fintype, Repr

/-- The shorter line starts at the higher split upper level. -/
def lineUpperMember : DoubletLine → UpperDoubletMember
  | .shorter588995 => .higherEnergy
  | .longer589592 => .lowerEnergy

/-- Both lines end at the same lower `3s` level. -/
def lineLowerLevel (_line : DoubletLine) : AtomicLevel := .lower3s

/-! ## Primary-image presentation -/

/-- The two quantum-number captions in image 578. -/
inductive FigureLevelCaption where
  | bracketedUpperPair
  | commonLowerLevel
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation data from image 578. Display heights and wavelength
labels are scalar raster readouts; physical wavelengths are stored separately.
-/
structure SodiumDoubletFigure where
  levelLineShown : AtomicLevel → Bool
  verticalDisplayHeight : AtomicLevel → ℝ
  upperPairGroupedByBracket : Bool
  printedPrincipalQuantumNumber : FigureLevelCaption → Nat
  printedOrbitalQuantumNumber : FigureLevelCaption → Nat
  transitionArrowShown : DoubletLine → Bool
  transitionArrowPointsDown : DoubletLine → Bool
  transitionArrowInitialLevel : DoubletLine → AtomicLevel
  transitionArrowFinalLevel : DoubletLine → AtomicLevel
  printedWavelengthInNanometers : DoubletLine → ℝ

/-! ## Physical setup and assumption families -/

/-- Atomic species role named in the problem. -/
inductive AtomSpecies where
  | sodium
  | other
  deriving DecidableEq, Repr

/-!
Independent physical data for the sodium doublet. In particular, the internal
field is stored rather than defined from wavelengths or an answer choice.
-/
structure SodiumDoubletSetup where
  atomSpecies : AtomSpecies
  atomsExcited : Bool
  energyAtLevel : AtomicLevel → DimEnergy
  unperturbedUpper3pEnergy : DimEnergy
  transitionAllowed : DoubletLine → Bool
  emittedPhotonEnergy : DoubletLine → DimEnergy
  transitionWavelength : DoubletLine → WavelengthQuantity
  spinOrientationAt : UpperDoubletMember → SpinOrientation
  internalOrbitalMagneticFieldStrength : MagneticFieldStrengthQuantity
  electronSpinMagneticMomentMagnitude : MagneticMomentMagnitudeQuantity
  ordinaryPlanckConstant : PlanckConstantQuantity
  figure : SodiumDoubletFigure

/-- The prose describes excited sodium atoms emitting both doublet lines. -/
structure MatchesExcitedSodiumScenario (setup : SodiumDoubletSetup) : Prop where
  atomIsSodium : setup.atomSpecies = .sodium
  atomsAreExcited : setup.atomsExcited = true
  bothLinesAreAllowed : ∀ line, setup.transitionAllowed line = true
  higherMemberIsAntiparallel :
    setup.spinOrientationAt .higherEnergy = .antiparallel
  lowerMemberIsParallel :
    setup.spinOrientationAt .lowerEnergy = .parallel

/-!
Quantum-number labels, bracket, ordering, arrows, and wavelength text visible
in the primary image. This contains no magnetic-field value.
-/
structure MatchesSuppliedSodiumDoubletFigure
    (setup : SodiumDoubletSetup) : Prop where
  everyLevelLineShown : ∀ level, setup.figure.levelLineShown level = true
  upperPairBracketed : setup.figure.upperPairGroupedByBracket = true
  upperCaptionPrincipalNumber :
    setup.figure.printedPrincipalQuantumNumber .bracketedUpperPair = 3
  upperCaptionOrbitalNumber :
    setup.figure.printedOrbitalQuantumNumber .bracketedUpperPair = 1
  lowerCaptionPrincipalNumber :
    setup.figure.printedPrincipalQuantumNumber .commonLowerLevel = 3
  lowerCaptionOrbitalNumber :
    setup.figure.printedOrbitalQuantumNumber .commonLowerLevel = 0
  higherMemberDrawnAboveLowerMember :
    setup.figure.verticalDisplayHeight .upper3pLower <
      setup.figure.verticalDisplayHeight .upper3pHigher
  bothUpperMembersAboveCommonLowerLevel :
    setup.figure.verticalDisplayHeight .lower3s <
        setup.figure.verticalDisplayHeight .upper3pLower ∧
      setup.figure.verticalDisplayHeight .lower3s <
        setup.figure.verticalDisplayHeight .upper3pHigher
  everyTransitionArrowShown : ∀ line,
    setup.figure.transitionArrowShown line = true
  everyTransitionArrowPointsDown : ∀ line,
    setup.figure.transitionArrowPointsDown line = true
  transitionArrowInitialLevels : ∀ line,
    setup.figure.transitionArrowInitialLevel line =
      upperAtomicLevel (lineUpperMember line)
  transitionArrowFinalLevels : ∀ line,
    setup.figure.transitionArrowFinalLevel line = lineLowerLevel line
  shortLinePrintedWavelength :
    setup.figure.printedWavelengthInNanometers .shorter588995 = 588.995
  longLinePrintedWavelength :
    setup.figure.printedWavelengthInNanometers .longer589592 = 589.592

/-!
The printed nanometre labels calibrate the independent physical wavelengths.
They are data readouts, not conclusions about the requested field.
-/
structure MatchesSodiumDoubletWavelengthReadouts
    (setup : SodiumDoubletSetup) : Prop where
  printedLabelsRepresentPhysicalWavelengths : ∀ line,
    wavelengthInNanometers (setup.transitionWavelength line) =
      setup.figure.printedWavelengthInNanometers line

/-- Positivity and level ordering required by the physical model. -/
structure HasPhysicalSodiumDoubletQuantities
    (setup : SodiumDoubletSetup) : Prop where
  wavelengthsPositive : ∀ line,
    0 < wavelengthInMeters (setup.transitionWavelength line)
  photonEnergiesPositive : ∀ line,
    0 < energyInJoules (setup.emittedPhotonEnergy line)
  planckConstantPositive :
    0 < planckConstantInJouleSeconds setup.ordinaryPlanckConstant
  magneticMomentPositive :
    0 < magneticMomentInJoulesPerTesla
      setup.electronSpinMagneticMomentMagnitude
  internalFieldPositive :
    0 < magneticFieldStrengthInTeslas
      setup.internalOrbitalMagneticFieldStrength
  physicalUpperLevelOrdering :
    energyInJoules (setup.energyAtLevel .upper3pLower) <
      energyInJoules (setup.energyAtLevel .upper3pHigher)
  bothUpperLevelsAboveCommonLower : ∀ member,
    energyInJoules (setup.energyAtLevel .lower3s) <
      energyInJoules (setup.energyAtLevel (upperAtomicLevel member))

/-!
Standard SI calibrations of ordinary Planck action and the electron spin
magnetic-moment magnitude. Neither calibration mentions the requested field.
-/
structure UsesStandardSpectroscopicConstants
    (setup : SodiumDoubletSetup) : Prop where
  ordinaryPlanckConstantCalibration :
    planckConstantInJouleSeconds setup.ordinaryPlanckConstant =
      ordinaryPlanckConstantSIValue
  electronSpinMomentCalibration :
    magneticMomentInJoulesPerTesla
        setup.electronSpinMagneticMomentMagnitude =
      bohrMagnetonSIValue

/-!
Radiative laws for both lines: each photon carries the atomic energy drop and
obeys `Eγ = h c / λ`. No line is assigned a requested field value.
-/
structure SatisfiesSodiumRadiativeTransitionLaws
    (setup : SodiumDoubletSetup) : Prop where
  photonCarriesAtomicEnergyDrop : ∀ line,
    setup.transitionAllowed line = true →
      energyInJoules (setup.emittedPhotonEnergy line) =
        energyInJoules
            (setup.energyAtLevel (upperAtomicLevel (lineUpperMember line))) -
          energyInJoules (setup.energyAtLevel (lineLowerLevel line))
  photonEnergyWavelengthLaw : ∀ line,
    setup.transitionAllowed line = true →
      energyInJoules (setup.emittedPhotonEnergy line) =
        planckConstantInJouleSeconds setup.ordinaryPlanckConstant *
            speedOfLightInMetersPerSecond /
          wavelengthInMeters (setup.transitionWavelength line)

/-!
The general spin Zeeman law `E = E₀ + s μ_B B` for each upper member, with
sign determined by magnetic-moment orientation. It contains no wavelength or
numerical answer for the field.
-/
structure SatisfiesInternalSpinZeemanLaw
    (setup : SodiumDoubletSetup) : Prop where
  upperLevelZeemanShift : ∀ member,
    energyInJoules (setup.energyAtLevel (upperAtomicLevel member)) =
      energyInJoules setup.unperturbedUpper3pEnergy +
        zeemanEnergySign (setup.spinOrientationAt member) *
          magneticMomentInJoulesPerTesla
              setup.electronSpinMagneticMomentMagnitude *
            magneticFieldStrengthInTeslas
              setup.internalOrbitalMagneticFieldStrength

/-! ## Derived field relation and displayed answer -/

/-!
The field inferred from the wavelength readouts and calibrated constants.
This scalar prediction does not define the independently stored physical field.
-/
def inferredInternalFieldInTeslas (setup : SodiumDoubletSetup) : ℝ :=
  |planckConstantInJouleSeconds setup.ordinaryPlanckConstant *
          speedOfLightInMetersPerSecond /
        wavelengthInMeters (setup.transitionWavelength .shorter588995) -
      planckConstantInJouleSeconds setup.ordinaryPlanckConstant *
          speedOfLightInMetersPerSecond /
        wavelengthInMeters (setup.transitionWavelength .longer589592)| /
    (2 * magneticMomentInJoulesPerTesla
      setup.electronSpinMagneticMomentMagnitude)

/-- Labels of the four field-strength choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-field strength, in teslas, printed beside each answer label. -/
def displayedFieldInTeslas : AnswerChoice → ℝ
  | .A => 9
  | .B => 1.8
  | .C => 18
  | .D => 36

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A displayed field agrees when the physical value is within half a tesla of it.
The tolerance is a display convention, not a premise fixing the actual field.
-/
def MatchesDisplayedField
    (setup : SodiumDoubletSetup) (choice : AnswerChoice) : Prop :=
  |magneticFieldStrengthInTeslas
        setup.internalOrbitalMagneticFieldStrength -
      displayedFieldInTeslas choice| < 1 / 2

/-- Exactly one displayed field agrees with the physical field. -/
def IsUniqueMatchingDisplayedField
    (setup : SodiumDoubletSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedField setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedField setup other → other = choice

/-!
The shared lower level, energy-drop laws, and Zeeman shifts imply that the
photon-energy separation is `2 μ_B B`.
-/
lemma sodiumDoubletPhotonEnergyDifference
    (setup : SodiumDoubletSetup)
    (h_scenario : MatchesExcitedSodiumScenario setup)
    (h_radiative : SatisfiesSodiumRadiativeTransitionLaws setup)
    (h_zeeman : SatisfiesInternalSpinZeemanLaw setup) :
    |energyInJoules (setup.emittedPhotonEnergy .shorter588995) -
        energyInJoules (setup.emittedPhotonEnergy .longer589592)| =
      2 * magneticMomentInJoulesPerTesla
          setup.electronSpinMagneticMomentMagnitude *
        magneticFieldStrengthInTeslas
          setup.internalOrbitalMagneticFieldStrength := by
  have h_short :=
    h_radiative.photonCarriesAtomicEnergyDrop .shorter588995
      (h_scenario.bothLinesAreAllowed .shorter588995)
  have h_long :=
    h_radiative.photonCarriesAtomicEnergyDrop .longer589592
      (h_scenario.bothLinesAreAllowed .longer589592)
  have h_higher := h_zeeman.upperLevelZeemanShift .higherEnergy
  have h_lower := h_zeeman.upperLevelZeemanShift .lowerEnergy
  rw [h_scenario.higherMemberIsAntiparallel] at h_higher
  rw [h_scenario.lowerMemberIsParallel] at h_lower
  simp only [upperAtomicLevel] at h_higher h_lower
  have h_difference :
      energyInJoules (setup.emittedPhotonEnergy .shorter588995) -
          energyInJoules (setup.emittedPhotonEnergy .longer589592) =
        2 * magneticMomentInJoulesPerTesla
            setup.electronSpinMagneticMomentMagnitude *
          magneticFieldStrengthInTeslas
            setup.internalOrbitalMagneticFieldStrength := by
    rw [h_short, h_long]
    simp only [lineUpperMember, upperAtomicLevel, lineLowerLevel]
    rw [h_higher, h_lower]
    norm_num [zeemanEnergySign]
    ring
  rw [h_difference, abs_of_nonneg]
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (NNReal.coe_nonneg
          (setup.electronSpinMagneticMomentMagnitude UnitChoices.SI).val))
      (NNReal.coe_nonneg
        (setup.internalOrbitalMagneticFieldStrength UnitChoices.SI).val)

/-!
Combining the photon relation with the spin splitting gives the exact
wavelength formula for the independently stored internal field.
-/
lemma internalMagneticField_exactFormula
    (setup : SodiumDoubletSetup)
    (h_scenario : MatchesExcitedSodiumScenario setup)
    (h_physical : HasPhysicalSodiumDoubletQuantities setup)
    (h_radiative : SatisfiesSodiumRadiativeTransitionLaws setup)
    (h_zeeman : SatisfiesInternalSpinZeemanLaw setup) :
    magneticFieldStrengthInTeslas
        setup.internalOrbitalMagneticFieldStrength =
      inferredInternalFieldInTeslas setup := by
  have h_difference :=
    sodiumDoubletPhotonEnergyDifference setup h_scenario h_radiative h_zeeman
  have h_short :=
    h_radiative.photonEnergyWavelengthLaw .shorter588995
      (h_scenario.bothLinesAreAllowed .shorter588995)
  have h_long :=
    h_radiative.photonEnergyWavelengthLaw .longer589592
      (h_scenario.bothLinesAreAllowed .longer589592)
  rw [h_short, h_long] at h_difference
  unfold inferredInternalFieldInTeslas
  rw [h_difference]
  field_simp [ne_of_gt h_physical.magneticMomentPositive]

/-!
For the measured wavelengths and standard constants, the inferred field is
between `18 T` and `18.5 T`. It therefore matches the displayed `18 T` choice,
and no other supplied choice.

This formalizes `thm:physics:phyx_mini_0578:target`.
-/
theorem problem_phyx_mini_0578
    (setup : SodiumDoubletSetup)
    (h_scenario : MatchesExcitedSodiumScenario setup)
    (h_figure : MatchesSuppliedSodiumDoubletFigure setup)
    (h_wavelengths : MatchesSodiumDoubletWavelengthReadouts setup)
    (h_physical : HasPhysicalSodiumDoubletQuantities setup)
    (h_constants : UsesStandardSpectroscopicConstants setup)
    (h_radiative : SatisfiesSodiumRadiativeTransitionLaws setup)
    (h_zeeman : SatisfiesInternalSpinZeemanLaw setup) :
    magneticFieldStrengthInTeslas
          setup.internalOrbitalMagneticFieldStrength =
        inferredInternalFieldInTeslas setup ∧
      18 < magneticFieldStrengthInTeslas
          setup.internalOrbitalMagneticFieldStrength ∧
      magneticFieldStrengthInTeslas
          setup.internalOrbitalMagneticFieldStrength < 37 / 2 ∧
      IsUniqueMatchingDisplayedField setup .C := by
  have h_exact :=
    internalMagneticField_exactFormula setup h_scenario h_physical
      h_radiative h_zeeman
  have nanometers_eq_meters (wavelength : WavelengthQuantity) :
      wavelengthInNanometers wavelength =
        1000000000 * wavelengthInMeters wavelength := by
    have h := wavelength.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    have hv := congrArg (fun quantity => ((quantity.val : NNReal) : ℝ)) h
    norm_num [wavelengthInNanometers, wavelengthInMeters, wavelengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, Dimension.L𝓭,
      NNReal.smul_def] at hv ⊢
    exact hv
  have h_short_nm :=
    h_wavelengths.printedLabelsRepresentPhysicalWavelengths .shorter588995
  have h_long_nm :=
    h_wavelengths.printedLabelsRepresentPhysicalWavelengths .longer589592
  rw [h_figure.shortLinePrintedWavelength] at h_short_nm
  rw [h_figure.longLinePrintedWavelength] at h_long_nm
  have h_short_m :
      wavelengthInMeters (setup.transitionWavelength .shorter588995) =
        588.995 / 1000000000 := by
    have h_conversion :=
      nanometers_eq_meters (setup.transitionWavelength .shorter588995)
    nlinarith
  have h_long_m :
      wavelengthInMeters (setup.transitionWavelength .longer589592) =
        589.592 / 1000000000 := by
    have h_conversion :=
      nanometers_eq_meters (setup.transitionWavelength .longer589592)
    nlinarith
  have h_inferred_lower : 18 < inferredInternalFieldInTeslas setup := by
    unfold inferredInternalFieldInTeslas
    rw [h_constants.ordinaryPlanckConstantCalibration,
      h_constants.electronSpinMomentCalibration, h_short_m, h_long_m]
    norm_num [ordinaryPlanckConstantSIValue, bohrMagnetonSIValue,
      speedOfLightInMetersPerSecond, DimSpeed.speedOfLight_in_SI,
      abs_of_pos]
  have h_inferred_upper : inferredInternalFieldInTeslas setup < 37 / 2 := by
    unfold inferredInternalFieldInTeslas
    rw [h_constants.ordinaryPlanckConstantCalibration,
      h_constants.electronSpinMomentCalibration, h_short_m, h_long_m]
    norm_num [ordinaryPlanckConstantSIValue, bohrMagnetonSIValue,
      speedOfLightInMetersPerSecond, DimSpeed.speedOfLight_in_SI,
      abs_of_pos]
  have h_field_lower :
      18 < magneticFieldStrengthInTeslas
        setup.internalOrbitalMagneticFieldStrength := by
    rw [h_exact]
    exact h_inferred_lower
  have h_field_upper :
      magneticFieldStrengthInTeslas
          setup.internalOrbitalMagneticFieldStrength < 37 / 2 := by
    rw [h_exact]
    exact h_inferred_upper
  refine ⟨h_exact, h_field_lower, h_field_upper, ?_⟩
  constructor
  · unfold MatchesDisplayedField
    rw [abs_lt]
    norm_num [displayedFieldInTeslas]
    constructor <;> linarith
  · intro other h_other
    unfold MatchesDisplayedField at h_other
    rw [abs_lt] at h_other
    cases other <;>
      norm_num [displayedFieldInTeslas] at h_other ⊢ <;>
      linarith

end PhyXMiniProblems.ProblemPhyXMini0578
