import Mathlib
import Physlib.Units.WithDim.Pressure

/-!
# IPhO 2026 experimental problem 4, part A.1

This file models the inventory of the confined air column `CA` in the inner
cylinder `IC`. Physlib's dimension-tagged quantities are used whenever its
dimension system supports the physical role. Amount of substance, molar mass,
and the Avogadro constant are kept abstract because Physlib's dimension basis
has no amount-of-substance component.
-/

namespace IPhO2026Problems.IPhO2026_4_A_1

open Dimension

/-- A physical length, represented independently of the choice of units. -/
abbrev Length := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical volume, with dimension `L³`. -/
abbrev Volume := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical mass. -/
abbrev Mass := Dimensionful (WithDim M𝓭 ℝ)

/-- A mass density, with dimension `M L⁻³`. -/
abbrev MassDensity :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- An absolute temperature. -/
abbrev AbsoluteTemperature := Dimensionful (WithDim Θ𝓭 ℝ)

/-- A thermodynamic pressure, using Physlib's pressure quantity. -/
abbrev Pressure := DimPressure

/-- The real-valued readout of a Physlib dimensional quantity in SI units. -/
noncomputable def siValue {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/--
The missing amount-of-substance interface in Physlib.

Amount of substance, molecular population, molar mass, and molecules per mole
remain distinct abstract physical types. Only their scalar readouts in the
units used by this experiment are exposed.
-/
structure SubstanceCountingModel where
  AmountOfSubstance : Type
  MolecularPopulation : Type
  MolarMassQuantity : Type
  AvogadroQuantity : Type
  amountInMoles : AmountOfSubstance → ℝ
  moleculeCount : MolecularPopulation → ℝ
  molarMassInKilogramsPerMole : MolarMassQuantity → ℝ
  avogadroConstantPerMole : AvogadroQuantity → ℝ

/-- Thermodynamic state and inventory of the confined air column `CA`. -/
structure ConfinedAirState (model : SubstanceCountingModel) where
  mass : Mass
  amount : model.AmountOfSubstance
  molecules : model.MolecularPopulation
  pressure : Pressure
  absoluteTemperature : AbsoluteTemperature

/--
The dimensioned quantities read from the cylinder geometry in Figure 17.

The outer-cylinder fields retain the `OC` geometry even though only the
inner-cylinder geometry enters part A.1.
-/
structure Figure17Geometry where
  innerCylinderDiameter : Length
  innerCylinderRadius : Length
  innerCylinderUsableHeight : Length
  outerCylinderInnerRadius : Length
  outerCylinderUsableHeight : Length
  confinedAirHeight : Length
  propyleneGlycolHeight : Length
  confinedAirVolume : Volume

/--
The apparatus and constants relevant to part A.1.

The propositions record the labelled apparatus state without asserting that
the experimental instructions have already been carried out.
-/
structure IsochoricAirSetup (model : SubstanceCountingModel) where
  geometry : Figure17Geometry
  confinedAirCA : ConfinedAirState model
  ambientAirDensity : MassDensity
  airMolarMass : model.MolarMassQuantity
  universalGasConstantJPerMoleKelvin : ℝ
  avogadroConstant : model.AvogadroQuantity
  propyleneGlycolIntroducedIntoIC : Prop
  valveDClosed : Prop
  valveEClosed : Prop
  confinedAirColumnSealed : Prop
  confinedAirVolumeFixed : Prop
  outerCylinderWaterBathHeated : Prop

/--
The cylindrical volume of `CA` in cubic metres, as calculated from Figure 17.
-/
noncomputable def cylindricalAirVolumeSI (geometry : Figure17Geometry) : ℝ :=
  Real.pi * (siValue geometry.innerCylinderDiameter / 2) ^ 2 *
    siValue geometry.confinedAirHeight

/--
Governing physical laws for the confined air.

The primitive relations use the independently stored radius and physical
volume: diameter is twice radius, cylinder volume is `π r² H`, mass is
`ρ V`, mass is molar mass times amount, and molecular population is the
Avogadro quantity times amount. The ideal-gas equation is retained from the
problem statement. None of these fields contains the requested substituted
closed forms or numerical uncertainty conclusions.
-/
structure GoverningLaws (model : SubstanceCountingModel)
    (setup : IsochoricAirSetup model) : Prop where
  diameter_radius :
    siValue setup.geometry.innerCylinderDiameter =
      2 * siValue setup.geometry.innerCylinderRadius
  height_partition :
    siValue setup.geometry.confinedAirHeight +
        siValue setup.geometry.propyleneGlycolHeight =
      siValue setup.geometry.innerCylinderUsableHeight
  cylinder_geometry :
    siValue setup.geometry.confinedAirVolume =
      Real.pi * (siValue setup.geometry.innerCylinderRadius) ^ 2 *
        siValue setup.geometry.confinedAirHeight
  mass_density :
    siValue setup.confinedAirCA.mass =
      siValue setup.ambientAirDensity *
        siValue setup.geometry.confinedAirVolume
  ideal_gas :
    siValue setup.confinedAirCA.pressure *
        siValue setup.geometry.confinedAirVolume =
      model.amountInMoles setup.confinedAirCA.amount *
        setup.universalGasConstantJPerMoleKelvin *
          siValue setup.confinedAirCA.absoluteTemperature
  molar_mass_relation :
    siValue setup.confinedAirCA.mass =
      model.molarMassInKilogramsPerMole setup.airMolarMass *
        model.amountInMoles setup.confinedAirCA.amount
  avogadro_relation :
    model.moleculeCount setup.confinedAirCA.molecules =
      model.avogadroConstantPerMole setup.avogadroConstant *
        model.amountInMoles setup.confinedAirCA.amount

/--
Numerical source readouts from Figures 17--18, the procedure, and the
reference data used by the official solution.
-/
structure SourceReadouts (model : SubstanceCountingModel)
    (setup : IsochoricAirSetup model) : Prop where
  inner_diameter :
    siValue setup.geometry.innerCylinderDiameter = 0.0337
  confined_air_height :
    siValue setup.geometry.confinedAirHeight = 0.095
  glycol_height :
    siValue setup.geometry.propyleneGlycolHeight = 0.045
  ambient_density :
    siValue setup.ambientAirDensity = 1.12
  air_molar_mass :
    model.molarMassInKilogramsPerMole setup.airMolarMass = 0.02896
  avogadro_constant :
    model.avogadroConstantPerMole setup.avogadroConstant =
      6.02 * 10 ^ 23

/-- The apparatus conditions prescribed immediately before part A.1. -/
structure ExperimentalConditions (model : SubstanceCountingModel)
    (setup : IsochoricAirSetup model) : Prop where
  glycol_introduced : setup.propyleneGlycolIntroducedIntoIC
  valve_D_closed : setup.valveDClosed
  valve_E_closed : setup.valveEClosed
  air_column_sealed : setup.confinedAirColumnSealed
  volume_fixed : setup.confinedAirVolumeFixed
  water_bath_heated : setup.outerCylinderWaterBathHeated

/-- Positivity conditions required of the physical apparatus and constants. -/
structure PhysicalAdmissibility (model : SubstanceCountingModel)
    (setup : IsochoricAirSetup model) : Prop where
  inner_diameter_positive :
    0 < siValue setup.geometry.innerCylinderDiameter
  inner_radius_positive :
    0 < siValue setup.geometry.innerCylinderRadius
  confined_air_height_positive :
    0 < siValue setup.geometry.confinedAirHeight
  confined_air_volume_positive :
    0 < siValue setup.geometry.confinedAirVolume
  density_positive :
    0 < siValue setup.ambientAirDensity
  amount_positive :
    0 < model.amountInMoles setup.confinedAirCA.amount
  molar_mass_positive :
    0 < model.molarMassInKilogramsPerMole setup.airMolarMass
  pressure_positive :
    0 < siValue setup.confinedAirCA.pressure
  temperature_positive :
    0 < siValue setup.confinedAirCA.absoluteTemperature
  gas_constant_positive :
    0 < setup.universalGasConstantJPerMoleKelvin
  avogadro_constant_positive :
    0 < model.avogadroConstantPerMole setup.avogadroConstant

/-- A scalar experimental estimate, consisting of a centre and uncertainty. -/
structure ScalarEstimate where
  centralValue : ℝ
  uncertainty : ℝ

/--
The source-consistent corrected `0.094 ± 0.002 g`, expressed in kilograms.
-/
def officialMassEstimateKilograms : ScalarEstimate :=
  ⟨0.000094, 0.000002⟩

/-- The reported `3.24 mmol` with `0.7 mmol` uncertainty, expressed in moles. -/
def officialAmountEstimateMoles : ScalarEstimate :=
  ⟨0.00324, 0.0007⟩

/-- The reported `(1.95 ± 0.05) · 10²¹` molecules. -/
def officialMoleculeCountEstimate : ScalarEstimate :=
  ⟨1.95 * 10 ^ 21, 0.05 * 10 ^ 21⟩

/-- Whether a scalar readout lies within a stated experimental uncertainty. -/
def WithinEstimate (readout : ℝ) (estimate : ScalarEstimate) : Prop :=
  |readout - estimate.centralValue| ≤ estimate.uncertainty

/--
The source-grounded numerical inventory, using the corrected mass interval.
-/
def MatchesOfficialSample (model : SubstanceCountingModel)
    (setup : IsochoricAirSetup model) : Prop :=
  WithinEstimate (siValue setup.confinedAirCA.mass)
      officialMassEstimateKilograms ∧
    WithinEstimate (model.amountInMoles setup.confinedAirCA.amount)
      officialAmountEstimateMoles ∧
    WithinEstimate (model.moleculeCount setup.confinedAirCA.molecules)
      officialMoleculeCountEstimate

/--
Part A.1: determine the volume, mass, amount of substance, and molecular
population of the confined air column.

The symbolic conclusions substitute Figure 17's diameter-based cylinder
volume into the primitive laws, solve the molar-mass relation for amount, and
put the Avogadro relation in the requested order. The final conjunct asserts
the corrected mass interval and the reported amount and molecule intervals.
-/
theorem determineConfinedAirInventory
    (model : SubstanceCountingModel)
    (setup : IsochoricAirSetup model)
    (_readouts : SourceReadouts model setup)
    (_conditions : ExperimentalConditions model setup)
    (_admissible : PhysicalAdmissibility model setup)
    (_laws : GoverningLaws model setup) :
    siValue setup.geometry.confinedAirVolume =
        cylindricalAirVolumeSI setup.geometry ∧
      siValue setup.confinedAirCA.mass =
        siValue setup.ambientAirDensity *
          cylindricalAirVolumeSI setup.geometry ∧
      model.amountInMoles setup.confinedAirCA.amount =
        siValue setup.confinedAirCA.mass /
          model.molarMassInKilogramsPerMole setup.airMolarMass ∧
      model.moleculeCount setup.confinedAirCA.molecules =
        model.amountInMoles setup.confinedAirCA.amount *
          model.avogadroConstantPerMole setup.avogadroConstant ∧
      MatchesOfficialSample model setup := by
  have hvolume :
      siValue setup.geometry.confinedAirVolume =
        cylindricalAirVolumeSI setup.geometry := by
    rw [_laws.cylinder_geometry]
    unfold cylindricalAirVolumeSI
    rw [_laws.diameter_radius]
    ring
  have hmass :
      siValue setup.confinedAirCA.mass =
        siValue setup.ambientAirDensity *
          cylindricalAirVolumeSI setup.geometry := by
    rw [_laws.mass_density, hvolume]
  have hamount :
      model.amountInMoles setup.confinedAirCA.amount =
        siValue setup.confinedAirCA.mass /
          model.molarMassInKilogramsPerMole setup.airMolarMass := by
    apply (eq_div_iff (ne_of_gt _admissible.molar_mass_positive)).2
    rw [_laws.molar_mass_relation]
    ring
  have hmolecules :
      model.moleculeCount setup.confinedAirCA.molecules =
        model.amountInMoles setup.confinedAirCA.amount *
          model.avogadroConstantPerMole setup.avogadroConstant := by
    rw [_laws.avogadro_relation]
    ring
  refine ⟨hvolume, hmass, hamount, hmolecules, ?_⟩
  have hmass_numeric :
      siValue setup.confinedAirCA.mass =
        1.12 * (Real.pi * (0.0337 / 2) ^ 2 * 0.095) := by
    rw [hmass, cylindricalAirVolumeSI, _readouts.ambient_density,
      _readouts.inner_diameter, _readouts.confined_air_height]
  have hamount_numeric :
      model.amountInMoles setup.confinedAirCA.amount =
        (1.12 * (Real.pi * (0.0337 / 2) ^ 2 * 0.095)) / 0.02896 := by
    rw [hamount, hmass_numeric, _readouts.air_molar_mass]
  have hmolecules_numeric :
      model.moleculeCount setup.confinedAirCA.molecules =
        ((1.12 * (Real.pi * (0.0337 / 2) ^ 2 * 0.095)) / 0.02896) *
          (6.02 * 10 ^ 23) := by
    rw [hmolecules, hamount_numeric, _readouts.avogadro_constant]
  unfold MatchesOfficialSample
  rw [hmass_numeric, hamount_numeric, hmolecules_numeric]
  unfold WithinEstimate
  norm_num [officialMassEstimateKilograms, officialAmountEstimateMoles,
    officialMoleculeCountEstimate, abs_le]
  constructor
  · constructor <;> nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]
  · constructor
    · constructor <;> nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]
    · constructor <;> nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]

end IPhO2026Problems.IPhO2026_4_A_1
