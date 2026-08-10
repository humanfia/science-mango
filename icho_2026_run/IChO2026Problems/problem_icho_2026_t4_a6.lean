import IChO2026Chem
import CRNT.Basic.Reaction

/-!
# IChO 2026 T4, subproblem 4.6

The problem asks for the standard reaction enthalpy at 298 K of the combustion
of one mole of methane, with every component in the gas phase.  Numerical
enthalpies below are represented in `kJ mol⁻¹`; heat capacities are represented
in `J mol⁻¹ K⁻¹`.
-/

namespace IChO2026Problems.T4A6

/-- The four chemical species occurring in the gaseous methane-combustion reaction.
The gas phase is part of the species identity, as required by the question. -/
inductive GaseousSpecies where
  | methane
  | dioxygen
  | carbonDioxide
  | water
  deriving DecidableEq, Fintype

/-- A molar enthalpy expressed in `kJ mol⁻¹`. -/
abbrev MolarEnthalpy := ℝ

/-- A molar constant-pressure heat capacity expressed in `J mol⁻¹ K⁻¹`. -/
abbrev MolarHeatCapacity := ℝ

/-- The balanced gaseous reaction `CH₄ + 2 O₂ → CO₂ + 2 H₂O`. -/
def methaneCombustion : CRNT.Reaction GaseousSpecies where
  source
    | .methane => 1
    | .dioxygen => 2
    | .carbonDioxide => 0
    | .water => 0
  target
    | .methane => 0
    | .dioxygen => 0
    | .carbonDioxide => 1
    | .water => 2

/-- Thermodynamic data at 298 K for the gaseous species of this subproblem. -/
structure ThermodynamicData298 where
  standardFormationEnthalpy : GaseousSpecies → MolarEnthalpy
  constantPressureHeatCapacity : GaseousSpecies → MolarHeatCapacity

/-- The supplied formation enthalpies and heat capacities from the problem table.
The table does not list the formation enthalpy of gaseous dioxygen. -/
def MatchesSuppliedThermodynamicData (data : ThermodynamicData298) : Prop :=
  data.standardFormationEnthalpy .methane = -74.8 ∧
  data.standardFormationEnthalpy .water = -241.8 ∧
  data.standardFormationEnthalpy .carbonDioxide = -393.5 ∧
  data.constantPressureHeatCapacity .methane = 35 ∧
  data.constantPressureHeatCapacity .water = 34 ∧
  data.constantPressureHeatCapacity .dioxygen = 29 ∧
  data.constantPressureHeatCapacity .carbonDioxide = 37

/-- The standard reaction enthalpy obtained by summing formation enthalpies of
products and subtracting the corresponding sum for reactants. -/
def standardReactionEnthalpy
    (formationEnthalpy : GaseousSpecies → MolarEnthalpy)
    (reaction : CRNT.Reaction GaseousSpecies) : MolarEnthalpy :=
  (∑ species, (reaction.target species : ℝ) * formationEnthalpy species) -
    ∑ species, (reaction.source species : ℝ) * formationEnthalpy species

/-- For the supplied gaseous thermodynamic data, and using the conventional zero
standard formation enthalpy of elemental `O₂(g)`, methane combustion at 298 K
has molar standard reaction enthalpy `-802.3 kJ mol⁻¹`. -/
theorem methane_combustion_standard_reaction_enthalpy_298
    (data : ThermodynamicData298)
    (hdata : MatchesSuppliedThermodynamicData data)
    (hdioxygen : data.standardFormationEnthalpy .dioxygen = 0) :
    standardReactionEnthalpy data.standardFormationEnthalpy methaneCombustion = -802.3 := by
  rcases hdata with ⟨hmethane, hwater, hcarbonDioxide, -, -, -, -⟩
  have sum_gaseous (f : GaseousSpecies → ℝ) :
      (∑ species, f species) =
        f .methane + f .dioxygen + f .carbonDioxide + f .water := by
    calc
      (∑ species, f species) =
          (∑ species ∈ Finset.univ.erase .methane, f species) + f .methane :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ _)).symm
      _ = f .methane + f .dioxygen + f .carbonDioxide + f .water := by
        have hspecies : Finset.univ.erase GaseousSpecies.methane =
            {GaseousSpecies.dioxygen, GaseousSpecies.carbonDioxide,
              GaseousSpecies.water} := by
          ext species
          cases species <;> simp
        rw [hspecies]
        simp
        ring
  unfold standardReactionEnthalpy
  rw [sum_gaseous, sum_gaseous]
  norm_num [methaneCombustion, hmethane, hwater, hcarbonDioxide, hdioxygen]

end IChO2026Problems.T4A6
