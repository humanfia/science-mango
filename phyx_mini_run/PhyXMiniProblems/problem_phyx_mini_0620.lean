import Mathlib
import Physlib.QuantumMechanics.Hydrogen.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0620

open Dimension

/-!
# Energy of the `n = 3` hydrogen level

The source asks for the energy `E` (and mentions orbital angular momentum `L`)
at principal quantum number `n = 3`.  The accompanying raster is contextual:
it displays three `n = 2` orbital probability distributions rather than an
energy readout for the requested state.

Energies use Physlib's unit-independent `DimEnergy`.  Angular-momentum
magnitudes are separate dimensionful quantities with the dimension of action.
Real numbers occur only at explicit electron-volt, joule-second, or displayed
answer readout boundaries.
-/

/-! ## Dimensionful quantities and readouts -/

/-- Read a unit-independent energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an energy in electron volts using Physlib's calibrated unit. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- The dimension of orbital angular momentum, equivalently joule-seconds. -/
def angularMomentumDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent orbital-angular-momentum magnitude. -/
abbrev AngularMomentumQuantity : Type :=
  Dimensionful (WithDim angularMomentumDimension NNReal)

/-- Read an angular-momentum magnitude in coherent-SI joule-seconds. -/
def angularMomentumInJouleSeconds
    (angularMomentum : AngularMomentumQuantity) : ℝ :=
  ((angularMomentum UnitChoices.SI).val : ℝ)

/-! ## Primary-figure vocabulary and readouts -/

/-- Labels of the three subfigures in image `620.png`. -/
inductive OrbitalPanel where
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Repr

/-- Coordinate axes that are explicitly drawn in panels (b) and (c). -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Qualitative shapes of the orbital probability clouds in the raster. -/
inductive OrbitalCloudShape where
  | sphericalShell
  | twoLobesAlongZ
  | torusInXYPlane
  deriving DecidableEq, Repr

/-!
Literal presentation data for the orbital figure.  The integer collection in
the last field is a displayed magnetic-quantum-number annotation, not an
angular-momentum magnitude or an energy.
-/
structure AtomicOrbitalFigure where
  nucleusShown : OrbitalPanel → Bool
  displayedPrincipalQuantumNumber : OrbitalPanel → ℕ
  displayedOrbitalQuantumNumber : OrbitalPanel → ℕ
  displayedMagneticQuantumNumbers : OrbitalPanel → Finset ℤ
  cloudShape : OrbitalPanel → OrbitalCloudShape
  coordinateAxisShown : OrbitalPanel → CoordinateAxis → Bool

/-!
Facts read from the primary raster: all panels show the nucleus and have
`n = 2`; panel (a) is the `ℓ = 0, m_ℓ = 0` spherical cloud, panel (b) is the
`ℓ = 1, m_ℓ = 0` two-lobed cloud along `z`, and panel (c) is the
`ℓ = 1, m_ℓ = ±1` toroidal cloud in the `x-y` plane.  No field states an
`n = 3` energy or selects an answer choice.
-/
structure MatchesSuppliedAtomicOrbitalFigure
    (figure : AtomicOrbitalFigure) : Prop where
  nucleusVisibleInEveryPanel :
    ∀ panel, figure.nucleusShown panel = true
  everyPanelLabelledN2 :
    ∀ panel, figure.displayedPrincipalQuantumNumber panel = 2
  panelAOrbitalNumber : figure.displayedOrbitalQuantumNumber .a = 0
  panelBOrbitalNumber : figure.displayedOrbitalQuantumNumber .b = 1
  panelCOrbitalNumber : figure.displayedOrbitalQuantumNumber .c = 1
  panelAMagneticNumber :
    figure.displayedMagneticQuantumNumbers .a = {0}
  panelBMagneticNumber :
    figure.displayedMagneticQuantumNumbers .b = {0}
  panelCMagneticNumbers :
    figure.displayedMagneticQuantumNumbers .c = {(-1 : ℤ), 1}
  panelASpherical : figure.cloudShape .a = .sphericalShell
  panelBTwoLobedAlongZ : figure.cloudShape .b = .twoLobesAlongZ
  panelCTorusInXYPlane : figure.cloudShape .c = .torusInXYPlane
  panelAHasNoCoordinateAxes :
    ∀ axis, figure.coordinateAxisShown .a axis = false
  panelBShowsEveryCoordinateAxis :
    ∀ axis, figure.coordinateAxisShown .b axis = true
  panelCShowsEveryCoordinateAxis :
    ∀ axis, figure.coordinateAxisShown .c axis = true

/-! ## Physical setup, reference data, and governing laws -/

/-!
The independent quantities for the elementary hydrogen-level model.  Physlib's
`QuantumMechanics.HydrogenAtom` preserves the Coulomb-system role of the atom.
The discrete level energies and angular-momentum magnitudes remain independent
fields constrained below by generic spectrum laws.
-/
structure HydrogenNThreeSetup where
  atom : QuantumMechanics.HydrogenAtom
  principalQuantumNumber : ℕ
  levelEnergy : ℕ → DimEnergy
  groundStateEnergy : DimEnergy
  orbitalAngularMomentumMagnitude : ℕ → AngularMomentumQuantity
  reducedPlanckAngularMomentum : AngularMomentumQuantity
  isAllowedOrbitalQuantumNumber : ℕ → ℕ → Prop
  figure : AtomicOrbitalFigure

/-- The prose scenario specifies a three-dimensional hydrogen atom at `n = 3`. -/
structure MatchesHydrogenNThreeScenario
    (setup : HydrogenNThreeSetup) : Prop where
  atomHasThreeSpatialDimensions : setup.atom.d = 3
  attractiveCoulombCoefficient : 0 < setup.atom.k
  requestedPrincipalQuantumNumber : setup.principalQuantumNumber = 3

/-!
Textbook reference calibrations.  The ground-state energy is the conventional
`-13.6 eV`, and reduced Planck angular momentum is calibrated by Physlib's
`Constants.ℏ` in joule-seconds.  Neither calibration states the requested
`n = 3` energy.
-/
structure UsesStandardHydrogenReferenceData
    (setup : HydrogenNThreeSetup) : Prop where
  groundStateEnergyElectronVolts :
    energyInElectronVolts setup.groundStateEnergy = -(68 / 5 : ℝ)
  reducedPlanckAngularMomentumJouleSeconds :
    angularMomentumInJouleSeconds setup.reducedPlanckAngularMomentum =
      (Constants.ℏ : ℝ)

/-- Positivity and bound-state conditions for the elementary physical branch. -/
structure HasPhysicalHydrogenNThreeParameters
    (setup : HydrogenNThreeSetup) : Prop where
  principalQuantumNumberPositive : 0 < setup.principalQuantumNumber
  reducedPlanckAngularMomentumPositive :
    0 < angularMomentumInJouleSeconds setup.reducedPlanckAngularMomentum
  boundStateEnergiesNegative :
    ∀ n : ℕ, 0 < n → energyInElectronVolts (setup.levelEnergy n) < 0

/-!
The elementary hydrogenic spectrum and angular-momentum quantization laws:

* `E_n = E_1 / n²` for positive principal quantum number `n`;
* the allowed orbital numbers satisfy `0 ≤ ℓ < n` (the lower bound is
  automatic for `ℕ`);
* `|L_ℓ| = ℏ √(ℓ(ℓ+1))`.

Physlib models the Coulomb Hamiltonian and angular-momentum operators, but does
not currently supply these discrete textbook spectrum statements.  They are
therefore explicit governing laws here, uniform in `n` and `ℓ`; none contains
the specialized `n = 3` energy or a displayed answer value.
-/
structure SatisfiesHydrogenLevelAndAngularMomentumLaws
    (setup : HydrogenNThreeSetup) : Prop where
  hydrogenEnergySpectrum :
    ∀ n : ℕ, 0 < n →
      energyInElectronVolts (setup.levelEnergy n) =
        energyInElectronVolts setup.groundStateEnergy / (n : ℝ) ^ 2
  allowedOrbitalQuantumNumbers :
    ∀ n ℓ : ℕ, setup.isAllowedOrbitalQuantumNumber n ℓ ↔ ℓ < n
  orbitalAngularMomentumSpectrum :
    ∀ ℓ : ℕ,
      angularMomentumInJouleSeconds
          (setup.orbitalAngularMomentumMagnitude ℓ) =
        angularMomentumInJouleSeconds setup.reducedPlanckAngularMomentum *
          Real.sqrt ((ℓ : ℝ) * ((ℓ : ℝ) + 1))

/-! ## Derived `n = 3` relations -/

/-- At `n = 3`, the possible orbital angular-momentum numbers are `0, 1, 2`. -/
lemma allowedOrbitalQuantumNumbersAtNThree
    (setup : HydrogenNThreeSetup)
    (_scenario : MatchesHydrogenNThreeScenario setup)
    (_laws : SatisfiesHydrogenLevelAndAngularMomentumLaws setup) :
    ∀ ℓ : ℕ,
      setup.isAllowedOrbitalQuantumNumber setup.principalQuantumNumber ℓ ↔
        ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 := by
  intro ℓ
  simpa only [_scenario.requestedPrincipalQuantumNumber,
    _laws.allowedOrbitalQuantumNumbers] using
      (show ℓ < 3 ↔ ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 by omega)

/-!
The standard Bohr spectrum gives `E₃ = -13.6/3² = -68/45 eV`.  This is a
derived conclusion, not a calibration or governing-law field.
-/
lemma hydrogenNThreeEnergyElectronVolts
    (setup : HydrogenNThreeSetup)
    (_scenario : MatchesHydrogenNThreeScenario setup)
    (_reference : UsesStandardHydrogenReferenceData setup)
    (_laws : SatisfiesHydrogenLevelAndAngularMomentumLaws setup) :
    energyInElectronVolts
        (setup.levelEnergy setup.principalQuantumNumber) = -(68 / 45 : ℝ) := by
  rw [_scenario.requestedPrincipalQuantumNumber]
  rw [_laws.hydrogenEnergySpectrum 3 (by norm_num)]
  rw [_reference.groundStateEnergyElectronVolts]
  norm_num

/-! ## Displayed answers and target -/

/-- Labels of the four energy choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Energy printed beside each answer choice, in electron volts. -/
def AnswerChoice.energyElectronVolts : AnswerChoice → ℝ
  | .A => -(3 / 2 : ℝ)
  | .B => -(38 / 25 : ℝ)
  | .C => -(77 / 50 : ℝ)
  | .D => -(39 / 25 : ℝ)

/-- The answer label recorded by the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- One displayed value is strictly nearer to the physical energy than all others. -/
def IsUniqueClosestDisplayedEnergy
    (setup : HydrogenNThreeSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice, alternative ≠ choice →
    |energyInElectronVolts
          (setup.levelEnergy setup.principalQuantumNumber) -
        choice.energyElectronVolts| <
      |energyInElectronVolts
          (setup.levelEnergy setup.principalQuantumNumber) -
        alternative.energyElectronVolts|

/-!
For the standard hydrogen model the requested energy is `-68/45 eV`, and the
unique closest listed value is `-1.52 eV` (choice B).  The final conjunct
separately preserves the source metadata, which records choice C; it does not
claim that C agrees with the governing physics.

This formalizes `thm:physics:phyx_mini_0620:target` while exposing the source's
answer-key discrepancy for later blueprint review.
-/
theorem hydrogenNThreeEnergy_and_answerKeyAudit
    (setup : HydrogenNThreeSetup)
    (_scenario : MatchesHydrogenNThreeScenario setup)
    (_figure : MatchesSuppliedAtomicOrbitalFigure setup.figure)
    (_reference : UsesStandardHydrogenReferenceData setup)
    (_physical : HasPhysicalHydrogenNThreeParameters setup)
    (_laws : SatisfiesHydrogenLevelAndAngularMomentumLaws setup) :
    energyInElectronVolts
          (setup.levelEnergy setup.principalQuantumNumber) = -(68 / 45 : ℝ) ∧
      IsUniqueClosestDisplayedEnergy setup .B ∧
      recordedDatasetAnswer = .C := by
  refine
    ⟨hydrogenNThreeEnergyElectronVolts setup _scenario _reference _laws, ?_, rfl⟩
  intro alternative hne
  rw [hydrogenNThreeEnergyElectronVolts setup _scenario _reference _laws]
  fin_cases alternative
  · norm_num [AnswerChoice.energyElectronVolts]
  · contradiction
  · norm_num [AnswerChoice.energyElectronVolts]
  · norm_num [AnswerChoice.energyElectronVolts]

end PhyXMiniProblems.ProblemPhyXMini0620
