import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0586

open Dimension

/-!
# First excited-state energy in a finite quantum well

An electron initially occupies the ground level of a finite one-dimensional
energy well.  The primary figure shows four labels `E₁`, `E₂`, `E₃`, and `E₄`,
with `E₄` at the lower boundary of the nonquantized continuum.  The problem
reports two discrete absorption wavelengths and a continuum cutoff wavelength.

Energies and wavelengths below are unit-independent dimensionful quantities.
Real numbers occur only as calibrated readouts in electron volts or nanometres,
as dimensionless schematic figure coordinates, and as displayed answer values.
The first-excited-state energy is an independent field of the setup; it is not
defined to be the recorded answer.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A physical energy, carrying the dimension `mass * length² / time²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- A physical wavelength, carrying the dimension of length. -/
abbrev WavelengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical energy as a real number of electron volts. -/
def energyInElectronVolts (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.electronVolt UnitChoices.SI).val

/-- Read a physical wavelength as a real number in a selected length unit. -/
def wavelengthReadout
    (unit : LengthUnit) (wavelength : WavelengthQuantity) : ℝ :=
  (wavelength {UnitChoices.SI with length := unit}).val

/-- Nanometre readout of a physical wavelength. -/
def wavelengthInNanometers (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.nanometers wavelength

/-!
The rounded textbook value of `h c` used for photon-energy calculations when
energy is measured in electron volts and wavelength in nanometres.
-/
def photonEnergyWavelengthConstantEvNm : ℝ := 1240

/-! ## Physical roles and figure vocabulary -/

/-- Particle species placed in the well. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Number of spatial dimensions retained by the well model. -/
inductive WellDimension where
  | oneDimensional
  | other
  deriving DecidableEq, Repr

/-- Whether the confining well has finite or idealized infinite depth. -/
inductive WellDepthKind where
  | finite
  | infinite
  deriving DecidableEq, Repr

/-- The four energy labels printed beside the horizontal levels in the figure. -/
inductive EnergyLevelLabel where
  | E₁
  | E₂
  | E₃
  | E₄
  deriving DecidableEq, Fintype, Repr

/-- The three wavelength features reported in the problem statement. -/
inductive AbsorptionFeature where
  | lineA
  | lineB
  | continuumCutoff
  deriving DecidableEq, Fintype, Repr

/-- The two kinds of spectral region distinguished by the figure. -/
inductive SpectralRegionKind where
  | quantized
  | nonquantized
  deriving DecidableEq, Repr

/-!
Qualitative and schematic information transcribed from the primary raster.
The vertical coordinates record only the displayed order; they are not energy
measurements and are deliberately not assumed to be equally spaced.
-/
structure EnergyLevelFigure where
  verticalCoordinate : EnergyLevelLabel → ℝ
  levelLineVisible : EnergyLevelLabel → Bool
  levelLabelVisible : EnergyLevelLabel → Bool
  energyAxisVisible : Bool
  energyAxisLabelVisible : Bool
  zeroMarkVisible : Bool
  nonquantizedRegionVisible : Bool
  regionAboveBoundary : SpectralRegionKind
  continuumLowerBoundary : EnergyLevelLabel

/-!
Independent physical quantities and experimental predicates for the well.
In particular, `levelEnergy .E₂` is not assigned a numerical value here.
-/
structure FiniteWellAbsorptionSetup where
  particleSpecies : ParticleSpecies
  wellDimension : WellDimension
  wellDepthKind : WellDepthKind
  initiallyOccupiedLevel : EnergyLevelLabel
  levelEnergy : EnergyLevelLabel → EnergyQuantity
  continuumOnsetEnergy : EnergyQuantity
  wavelength : AbsorptionFeature → WavelengthQuantity
  photonEnergy : WavelengthQuantity → EnergyQuantity
  canAbsorb : WavelengthQuantity → Prop
  figure : EnergyLevelFigure

/-! ## Scenario, figure readouts, and governing laws -/

/-- The qualitative finite-well scenario stated in the problem. -/
structure MatchesFiniteOneDimensionalWellScenario
    (setup : FiniteWellAbsorptionSetup) : Prop where
  particle_is_electron : setup.particleSpecies = .electron
  well_is_one_dimensional : setup.wellDimension = .oneDimensional
  well_is_finite : setup.wellDepthKind = .finite
  electron_starts_in_ground_level : setup.initiallyOccupiedLevel = .E₁
  continuum_begins_at_E4 :
    setup.continuumOnsetEnergy = setup.levelEnergy .E₄

/-!
Numerical readouts stated in the prose: the continuum begins at `450.0 eV`,
the two line wavelengths are `14.588 nm` and `4.8437 nm`, and the continuum
cutoff wavelength is `2.9108 nm`.  No energy for `E₂` occurs in this premise.
-/
structure MatchesProblemReadouts
    (setup : FiniteWellAbsorptionSetup) : Prop where
  continuum_onset_electronVolts :
    energyInElectronVolts setup.continuumOnsetEnergy = 450.0
  lineA_nanometers :
    wavelengthInNanometers (setup.wavelength .lineA) = 14.588
  lineB_nanometers :
    wavelengthInNanometers (setup.wavelength .lineB) = 4.8437
  continuum_cutoff_nanometers :
    wavelengthInNanometers (setup.wavelength .continuumCutoff) = 2.9108

/-!
Primary-image transcription.  The raster places `E₁ < E₂ < E₃ < E₄`, marks
zero at the bottom of the energy axis, and begins the shaded nonquantized
region at `E₄`.  The auxiliary caption's claim of equal spacing is not used,
because the primary image visibly has unequal schematic gaps.
-/
structure MatchesPrimaryEnergyLevelFigure
    (figure : EnergyLevelFigure) : Prop where
  energy_axis : figure.energyAxisVisible = true
  energy_axis_label : figure.energyAxisLabelVisible = true
  zero_mark : figure.zeroMarkVisible = true
  every_level_line_visible : ∀ level, figure.levelLineVisible level = true
  every_level_label_visible : ∀ level, figure.levelLabelVisible level = true
  E1_below_E2 :
    figure.verticalCoordinate .E₁ < figure.verticalCoordinate .E₂
  E2_below_E3 :
    figure.verticalCoordinate .E₂ < figure.verticalCoordinate .E₃
  E3_below_E4 :
    figure.verticalCoordinate .E₃ < figure.verticalCoordinate .E₄
  nonquantized_region : figure.nonquantizedRegionVisible = true
  region_above_is_nonquantized :
    figure.regionAboveBoundary = .nonquantized
  E4_is_continuum_boundary : figure.continuumLowerBoundary = .E₄

/-- Positivity and ordering conditions selecting the physical finite-well regime. -/
structure HasPhysicalFiniteWellParameters
    (setup : FiniteWellAbsorptionSetup) : Prop where
  ground_energy_nonnegative :
    0 ≤ energyInElectronVolts (setup.levelEnergy .E₁)
  E1_below_E2 :
    energyInElectronVolts (setup.levelEnergy .E₁) <
      energyInElectronVolts (setup.levelEnergy .E₂)
  E2_below_E3 :
    energyInElectronVolts (setup.levelEnergy .E₂) <
      energyInElectronVolts (setup.levelEnergy .E₃)
  E3_below_E4 :
    energyInElectronVolts (setup.levelEnergy .E₃) <
      energyInElectronVolts (setup.levelEnergy .E₄)
  positive_reported_wavelengths :
    ∀ feature, 0 < wavelengthInNanometers (setup.wavelength feature)
  positive_photon_energies :
    ∀ feature,
      0 < energyInElectronVolts
        (setup.photonEnergy (setup.wavelength feature))

/-!
Photon absorption and ionization laws used by the solution:

* `Eγ λ = h c ≈ 1240 eV·nm` for every positive wavelength;
* absorption at `λₐ` raises the initially occupied level to `E₂`;
* absorption at `λ_b` raises it to `E₃`;
* the cutoff photon reaches the continuum onset;
* every positive wavelength shorter than the cutoff is absorbable into the
  continuum.

These relations contain no value for the first-excited-state energy and no
answer choice.
-/
structure SatisfiesFiniteWellPhotonAbsorptionLaws
    (setup : FiniteWellAbsorptionSetup) : Prop where
  photon_energy_wavelength_law :
    ∀ wavelength,
      0 < wavelengthInNanometers wavelength →
        energyInElectronVolts (setup.photonEnergy wavelength) *
            wavelengthInNanometers wavelength =
          photonEnergyWavelengthConstantEvNm
  lineA_transition :
    energyInElectronVolts (setup.levelEnergy .E₂) =
      energyInElectronVolts
          (setup.levelEnergy setup.initiallyOccupiedLevel) +
        energyInElectronVolts
          (setup.photonEnergy (setup.wavelength .lineA))
  lineB_transition :
    energyInElectronVolts (setup.levelEnergy .E₃) =
      energyInElectronVolts
          (setup.levelEnergy setup.initiallyOccupiedLevel) +
        energyInElectronVolts
          (setup.photonEnergy (setup.wavelength .lineB))
  continuum_threshold_transition :
    energyInElectronVolts setup.continuumOnsetEnergy =
      energyInElectronVolts
          (setup.levelEnergy setup.initiallyOccupiedLevel) +
        energyInElectronVolts
          (setup.photonEnergy (setup.wavelength .continuumCutoff))
  lineA_is_absorbable : setup.canAbsorb (setup.wavelength .lineA)
  lineB_is_absorbable : setup.canAbsorb (setup.wavelength .lineB)
  every_shorter_positive_wavelength_is_absorbable :
    ∀ wavelength,
      0 < wavelengthInNanometers wavelength →
      wavelengthInNanometers wavelength <
        wavelengthInNanometers (setup.wavelength .continuumCutoff) →
      setup.canAbsorb wavelength

/-! ## Displayed answer data and current target -/

/-- Labels of the four energy choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electron-volt readout printed beside each answer label. -/
def displayedEnergyInElectronVolts : AnswerChoice → ℝ
  | .A => 85
  | .B => 24
  | .C => 109
  | .D => 426

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A real energy readout rounds to a displayed whole number of electron volts. -/
def RoundsToNearestElectronVolt (value displayedValue : ℝ) : Prop :=
  |value - displayedValue| < 1 / 2

/-- A displayed choice agrees with the rounded first-excited-state energy. -/
def MatchesDisplayedFirstExcitedEnergy
    (setup : FiniteWellAbsorptionSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestElectronVolt
    (energyInElectronVolts (setup.levelEnergy .E₂))
    (displayedEnergyInElectronVolts choice)

/-- A choice is the unique displayed value matching the modeled energy. -/
def IsUniqueMatchingFirstExcitedEnergy
    (setup : FiniteWellAbsorptionSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedFirstExcitedEnergy setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedFirstExcitedEnergy setup other → other = choice

/-!
The continuum cutoff first determines the ground-state readout: the continuum
begins at `450 eV`, while a `2.9108 nm` photon supplies the ionization gap.
-/
lemma groundStateEnergyReadout
    (setup : FiniteWellAbsorptionSetup)
    (h_scenario : MatchesFiniteOneDimensionalWellScenario setup)
    (h_physical : HasPhysicalFiniteWellParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_laws : SatisfiesFiniteWellPhotonAbsorptionLaws setup) :
    energyInElectronVolts (setup.levelEnergy .E₁) =
      450 - photonEnergyWavelengthConstantEvNm / 2.9108 := by
  have hph :=
    h_laws.photon_energy_wavelength_law
      (setup.wavelength .continuumCutoff)
      (h_physical.positive_reported_wavelengths .continuumCutoff)
  rw [h_readouts.continuum_cutoff_nanometers] at hph
  have htrans := h_laws.continuum_threshold_transition
  rw [h_scenario.electron_starts_in_ground_level,
    h_readouts.continuum_onset_electronVolts] at htrans
  norm_num [photonEnergyWavelengthConstantEvNm] at hph ⊢
  linarith [htrans, hph]

/-!
Adding the `14.588 nm` line-photon energy to the ground-state energy gives the
unrounded first-excited-state energy readout.
-/
lemma firstExcitedEnergyReadout
    (setup : FiniteWellAbsorptionSetup)
    (h_scenario : MatchesFiniteOneDimensionalWellScenario setup)
    (h_physical : HasPhysicalFiniteWellParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_laws : SatisfiesFiniteWellPhotonAbsorptionLaws setup) :
    energyInElectronVolts (setup.levelEnergy .E₂) =
      450 - photonEnergyWavelengthConstantEvNm / 2.9108 +
        photonEnergyWavelengthConstantEvNm / 14.588 := by
  rw [h_laws.lineA_transition,
    h_scenario.electron_starts_in_ground_level,
    groundStateEnergyReadout setup h_scenario h_physical h_readouts h_laws]
  have hph :=
    h_laws.photon_energy_wavelength_law
      (setup.wavelength .lineA)
      (h_physical.positive_reported_wavelengths .lineA)
  rw [h_readouts.lineA_nanometers] at hph
  norm_num [photonEnergyWavelengthConstantEvNm] at hph ⊢
  linarith [hph]

/-!
The inferred first-excited-state energy is approximately `109.002 eV`, so it
rounds to `109 eV` and uniquely selects answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0586:target`.
-/
theorem problem_phyx_mini_0586
    (setup : FiniteWellAbsorptionSetup)
    (h_scenario : MatchesFiniteOneDimensionalWellScenario setup)
    (h_figure : MatchesPrimaryEnergyLevelFigure setup.figure)
    (h_physical : HasPhysicalFiniteWellParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_laws : SatisfiesFiniteWellPhotonAbsorptionLaws setup) :
    energyInElectronVolts (setup.levelEnergy .E₂) =
        450 - photonEnergyWavelengthConstantEvNm / 2.9108 +
          photonEnergyWavelengthConstantEvNm / 14.588 ∧
      RoundsToNearestElectronVolt
        (energyInElectronVolts (setup.levelEnergy .E₂)) 109 ∧
      IsUniqueMatchingFirstExcitedEnergy setup recordedDatasetAnswer := by
  have hE2 :=
    firstExcitedEnergyReadout
      setup h_scenario h_physical h_readouts h_laws
  refine ⟨hE2, ?_, ?_⟩
  · rw [hE2]
    norm_num [RoundsToNearestElectronVolt,
      photonEnergyWavelengthConstantEvNm]
  · constructor
    · simp only [MatchesDisplayedFirstExcitedEnergy,
        recordedDatasetAnswer, displayedEnergyInElectronVolts]
      rw [hE2]
      norm_num [RoundsToNearestElectronVolt,
        photonEnergyWavelengthConstantEvNm]
    · intro other hother
      rcases other with (_ | _ | _ | _)
      · simp only [MatchesDisplayedFirstExcitedEnergy,
          displayedEnergyInElectronVolts] at hother
        rw [hE2] at hother
        norm_num [RoundsToNearestElectronVolt,
          photonEnergyWavelengthConstantEvNm] at hother
      · simp only [MatchesDisplayedFirstExcitedEnergy,
          displayedEnergyInElectronVolts] at hother
        rw [hE2] at hother
        norm_num [RoundsToNearestElectronVolt,
          photonEnergyWavelengthConstantEvNm] at hother
      · rfl
      · simp only [MatchesDisplayedFirstExcitedEnergy,
          displayedEnergyInElectronVolts] at hother
        rw [hE2] at hother
        norm_num [RoundsToNearestElectronVolt,
          photonEnergyWavelengthConstantEvNm] at hother

end PhyXMiniProblems.ProblemPhyXMini0586
