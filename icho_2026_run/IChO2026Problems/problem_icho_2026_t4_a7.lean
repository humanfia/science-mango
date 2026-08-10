import IChO2026Chem
import Mathlib

/-!
# IChO 2026 T4-A7: methane-combustion enthalpy at 2000 K

The numerical scalar quantities in this file use the units printed in the
problem: temperatures are in K, molar heat capacities in J mol⁻¹ K⁻¹, and
molar reaction/formation enthalpies in kJ mol⁻¹.  Chemical identity and phase
are represented separately from these scalar readouts.
-/

namespace IChO2026Problems

/-- The four chemical species occurring in the stated methane-combustion reaction. -/
inductive CombustionSpecies where
  | methane
  | dioxygen
  | carbonDioxide
  | water
  deriving DecidableEq, Repr

/-- Elements needed to express conservation of atoms in the displayed reaction. -/
inductive ChemicalElement where
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Repr

/-- Physical phases, including the gas phase required in T4-A7. -/
inductive PhysicalPhase where
  | gas
  | liquid
  | solid
  | aqueous
  deriving DecidableEq, Repr

/-- A species together with its physical phase. -/
structure ChemicalEntity where
  species : CombustionSpecies
  phase : PhysicalPhase
  deriving DecidableEq, Repr

def methaneGas : ChemicalEntity := ⟨.methane, .gas⟩
def dioxygenGas : ChemicalEntity := ⟨.dioxygen, .gas⟩
def carbonDioxideGas : ChemicalEntity := ⟨.carbonDioxide, .gas⟩
def waterGas : ChemicalEntity := ⟨.water, .gas⟩

/-- Stoichiometric coefficients are molar amounts per mole of reaction. -/
abbrev StoichiometricCoefficient := ℝ

/-- A reaction records its reactant and product stoichiometric coefficients. -/
structure ChemicalReaction where
  reactants : ChemicalEntity → StoichiometricCoefficient
  products : ChemicalEntity → StoichiometricCoefficient

/-- Atomic composition of each species in the reaction. -/
def atomCount : CombustionSpecies → ChemicalElement → ℕ
  | .methane, .carbon => 1
  | .methane, .hydrogen => 4
  | .dioxygen, .oxygen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | _, _ => 0

/-- The balanced, all-gas reaction `CH₄ + 2 O₂ → CO₂ + 2 H₂O`. -/
def methaneCombustion : ChemicalReaction where
  reactants := fun entity =>
    if entity = methaneGas then 1 else if entity = dioxygenGas then 2 else 0
  products := fun entity =>
    if entity = carbonDioxideGas then 1 else if entity = waterGas then 2 else 0

/-- All nonzero coefficients of a reaction have gaseous entities. -/
def ChemicalReaction.usesOnlyGasPhase (reaction : ChemicalReaction) : Prop :=
  ∀ entity,
    reaction.reactants entity ≠ 0 ∨ reaction.products entity ≠ 0 → entity.phase = .gas

/-- Atom conservation, expanded over the four species in the stated reaction. -/
def ChemicalReaction.atomBalanced (reaction : ChemicalReaction) : Prop :=
  ∀ element,
    reaction.reactants methaneGas * atomCount .methane element +
        reaction.reactants dioxygenGas * atomCount .dioxygen element +
        reaction.reactants carbonDioxideGas * atomCount .carbonDioxide element +
        reaction.reactants waterGas * atomCount .water element =
      reaction.products methaneGas * atomCount .methane element +
        reaction.products dioxygenGas * atomCount .dioxygen element +
        reaction.products carbonDioxideGas * atomCount .carbonDioxide element +
        reaction.products waterGas * atomCount .water element

/-- A chemical reaction has nonnegative coefficients, the required phase, and atom conservation. -/
def ChemicalReaction.wellFormed (reaction : ChemicalReaction) : Prop :=
  (∀ entity, 0 ≤ reaction.reactants entity ∧ 0 ≤ reaction.products entity) ∧
    reaction.usesOnlyGasPhase ∧ reaction.atomBalanced

/-- The displayed methane-combustion equation meets its stoichiometric conservation contract. -/
theorem methane_combustion_wellFormed : methaneCombustion.wellFormed := by
  constructor
  · intro entity
    rcases entity with ⟨species, phase⟩
    cases species <;> cases phase <;>
      simp [methaneCombustion, methaneGas, dioxygenGas, carbonDioxideGas, waterGas]
  constructor
  · intro entity hnonzero
    rcases entity with ⟨species, phase⟩
    cases species <;> cases phase <;>
      simp_all [methaneCombustion, methaneGas, dioxygenGas, carbonDioxideGas, waterGas]
  · intro element
    cases element <;>
      simp [methaneCombustion, methaneGas, dioxygenGas, carbonDioxideGas, waterGas, atomCount] <;>
      norm_num

/-- Temperature, represented by its numerical value in K. -/
abbrev Temperature := ℝ

/-- A molar heat capacity, represented by its numerical value in J mol⁻¹ K⁻¹. -/
abbrev MolarHeatCapacity := ℝ

/-- A molar enthalpy, represented by its numerical value in kJ mol⁻¹. -/
abbrev MolarEnthalpy := ℝ

/-- The reference and requested temperatures from T4-A6 and T4-A7. -/
def referenceTemperature : Temperature := 298
def targetTemperature : Temperature := 2000

/--
The thermodynamic readouts relevant to the all-gaseous methane-combustion
reaction.  Values are not fixed in this structure; their empirical numerical
values are explicit hypotheses of the calculations below.
-/
structure MethaneCombustionThermodynamicData where
  reaction : ChemicalReaction
  standardFormationEnthalpy298 : ChemicalEntity → MolarEnthalpy
  heatCapacity : ChemicalEntity → Temperature → MolarHeatCapacity
  reactionEnthalpy : Temperature → MolarEnthalpy

/--
`ΔᵣH°₍₂₉₈₎ = Σᵢ (νᵢ(products) - νᵢ(reactants)) ΔfH°₍₂₉₈₎(i)` over
the four all-gaseous entities in the source reaction.
-/
def reactionFormationEnthalpyAt298 (data : MethaneCombustionThermodynamicData) : MolarEnthalpy :=
  (data.reaction.products methaneGas - data.reaction.reactants methaneGas) *
      data.standardFormationEnthalpy298 methaneGas +
    (data.reaction.products dioxygenGas - data.reaction.reactants dioxygenGas) *
      data.standardFormationEnthalpy298 dioxygenGas +
    (data.reaction.products carbonDioxideGas - data.reaction.reactants carbonDioxideGas) *
      data.standardFormationEnthalpy298 carbonDioxideGas +
    (data.reaction.products waterGas - data.reaction.reactants waterGas) *
      data.standardFormationEnthalpy298 waterGas

/--
`ΔCₚ = Σᵢ (νᵢ(products) - νᵢ(reactants)) Cₚ(i)` over the four all-gaseous
entities in the stored reaction.
-/
def reactionHeatCapacityChange (data : MethaneCombustionThermodynamicData)
    (temperature : Temperature) : MolarHeatCapacity :=
  (data.reaction.products methaneGas - data.reaction.reactants methaneGas) *
      data.heatCapacity methaneGas temperature +
    (data.reaction.products dioxygenGas - data.reaction.reactants dioxygenGas) *
      data.heatCapacity dioxygenGas temperature +
    (data.reaction.products carbonDioxideGas - data.reaction.reactants carbonDioxideGas) *
      data.heatCapacity carbonDioxideGas temperature +
    (data.reaction.products waterGas - data.reaction.reactants waterGas) *
      data.heatCapacity waterGas temperature

/-- The conventional fallback value supplied after T4-A6, not an asserted answer to T4-A7. -/
def suppliedFallbackEnthalpyAt298 : MolarEnthalpy := -750

/-- The fallback value supplied after T4-A7 for use only in later calculations. -/
def suppliedFallbackEnthalpyAt2000 : MolarEnthalpy := -700

/--
The previous-part enthalpy calculation reconstructed from the supplied
formation enthalpies.  It is local rather than imported because the dependency
policy permits only a natural-language prerequisite.
-/
theorem methane_combustion_enthalpy_at_298
    (data : MethaneCombustionThermodynamicData)
    (hreaction : data.reaction = methaneCombustion)
    (hformation_methane : data.standardFormationEnthalpy298 methaneGas = -74.8)
    (hformation_dioxygen : data.standardFormationEnthalpy298 dioxygenGas = 0)
    (hformation_carbonDioxide : data.standardFormationEnthalpy298 carbonDioxideGas = -393.5)
    (hformation_water : data.standardFormationEnthalpy298 waterGas = -241.8)
    (hreaction_at_298 :
      data.reactionEnthalpy referenceTemperature =
        reactionFormationEnthalpyAt298 data) :
    data.reactionEnthalpy referenceTemperature = -802.3 := by
  rw [hreaction_at_298]
  unfold reactionFormationEnthalpyAt298
  rw [hreaction, hformation_methane, hformation_dioxygen,
    hformation_carbonDioxide, hformation_water]
  simp [methaneCombustion, methaneGas, dioxygenGas, carbonDioxideGas, waterGas] ;
    norm_num

/--
T4-A7: with the supplied gaseous heat capacities and the constant-heat-capacity
Kirchhoff relation, calculate the reaction enthalpy at 2000 K.  The final
inequality records the one-decimal-place presentation `-781.9 kJ mol⁻¹`.
-/
theorem methane_combustion_enthalpy_at_2000
    (data : MethaneCombustionThermodynamicData)
    (hreaction : data.reaction = methaneCombustion)
    (henthalpy_at_298 : data.reactionEnthalpy referenceTemperature = -802.3)
    (hcp_methane : data.heatCapacity methaneGas referenceTemperature = 35)
    (hcp_dioxygen : data.heatCapacity dioxygenGas referenceTemperature = 29)
    (hcp_carbonDioxide : data.heatCapacity carbonDioxideGas referenceTemperature = 37)
    (hcp_water : data.heatCapacity waterGas referenceTemperature = 34)
    (hconstant_heat_capacities : ∀ entity temperature, entity.phase = .gas →
      data.heatCapacity entity temperature = data.heatCapacity entity referenceTemperature)
    (hkirchhoff : ∀ temperature, 0 < temperature →
      data.reactionEnthalpy temperature =
        data.reactionEnthalpy referenceTemperature +
          reactionHeatCapacityChange data temperature *
            (temperature - referenceTemperature) / 1000) :
    reactionHeatCapacityChange data referenceTemperature = 12 ∧
      data.reactionEnthalpy targetTemperature = -781.876 ∧
        |data.reactionEnthalpy targetTemperature - (-781.9)| < 0.05 := by
  have hcp_methane_target : data.heatCapacity methaneGas targetTemperature = 35 := by
    rw [hconstant_heat_capacities methaneGas targetTemperature (by rfl)]
    exact hcp_methane
  have hcp_dioxygen_target : data.heatCapacity dioxygenGas targetTemperature = 29 := by
    rw [hconstant_heat_capacities dioxygenGas targetTemperature (by rfl)]
    exact hcp_dioxygen
  have hcp_carbonDioxide_target :
      data.heatCapacity carbonDioxideGas targetTemperature = 37 := by
    rw [hconstant_heat_capacities carbonDioxideGas targetTemperature (by rfl)]
    exact hcp_carbonDioxide
  have hcp_water_target : data.heatCapacity waterGas targetTemperature = 34 := by
    rw [hconstant_heat_capacities waterGas targetTemperature (by rfl)]
    exact hcp_water
  have hdeltaCp_reference : reactionHeatCapacityChange data referenceTemperature = 12 := by
    unfold reactionHeatCapacityChange
    rw [hreaction, hcp_methane, hcp_dioxygen, hcp_carbonDioxide, hcp_water]
    simp [methaneCombustion, methaneGas, dioxygenGas, carbonDioxideGas, waterGas] ;
      norm_num
  have hdeltaCp_target : reactionHeatCapacityChange data targetTemperature = 12 := by
    unfold reactionHeatCapacityChange
    rw [hreaction, hcp_methane_target, hcp_dioxygen_target,
      hcp_carbonDioxide_target, hcp_water_target]
    simp [methaneCombustion, methaneGas, dioxygenGas, carbonDioxideGas, waterGas] ;
      norm_num
  have htarget : data.reactionEnthalpy targetTemperature = -781.876 := by
    calc
      data.reactionEnthalpy targetTemperature =
          data.reactionEnthalpy referenceTemperature +
            reactionHeatCapacityChange data targetTemperature *
              (targetTemperature - referenceTemperature) / 1000 :=
        hkirchhoff targetTemperature (by norm_num [targetTemperature])
      _ = -781.876 := by
        rw [henthalpy_at_298, hdeltaCp_target]
        norm_num [referenceTemperature, targetTemperature]
  exact ⟨hdeltaCp_reference, htarget, by rw [htarget]; norm_num⟩

/--
If the source's T4-A6 fallback is used in place of the previous conclusion,
the same temperature correction produces the corresponding conditional value.
-/
theorem methane_combustion_enthalpy_at_2000_from_t4_a6_fallback
    (data : MethaneCombustionThermodynamicData)
    (hreaction : data.reaction = methaneCombustion)
    (henthalpy_at_298 : data.reactionEnthalpy referenceTemperature = suppliedFallbackEnthalpyAt298)
    (hcp_methane : data.heatCapacity methaneGas referenceTemperature = 35)
    (hcp_dioxygen : data.heatCapacity dioxygenGas referenceTemperature = 29)
    (hcp_carbonDioxide : data.heatCapacity carbonDioxideGas referenceTemperature = 37)
    (hcp_water : data.heatCapacity waterGas referenceTemperature = 34)
    (hconstant_heat_capacities : ∀ entity temperature, entity.phase = .gas →
      data.heatCapacity entity temperature = data.heatCapacity entity referenceTemperature)
    (hkirchhoff : ∀ temperature, 0 < temperature →
      data.reactionEnthalpy temperature =
        data.reactionEnthalpy referenceTemperature +
          reactionHeatCapacityChange data temperature *
            (temperature - referenceTemperature) / 1000) :
    data.reactionEnthalpy targetTemperature = -729.576 ∧
      |data.reactionEnthalpy targetTemperature - (-729.6)| < 0.05 := by
  have hcp_methane_target : data.heatCapacity methaneGas targetTemperature = 35 := by
    rw [hconstant_heat_capacities methaneGas targetTemperature (by rfl)]
    exact hcp_methane
  have hcp_dioxygen_target : data.heatCapacity dioxygenGas targetTemperature = 29 := by
    rw [hconstant_heat_capacities dioxygenGas targetTemperature (by rfl)]
    exact hcp_dioxygen
  have hcp_carbonDioxide_target :
      data.heatCapacity carbonDioxideGas targetTemperature = 37 := by
    rw [hconstant_heat_capacities carbonDioxideGas targetTemperature (by rfl)]
    exact hcp_carbonDioxide
  have hcp_water_target : data.heatCapacity waterGas targetTemperature = 34 := by
    rw [hconstant_heat_capacities waterGas targetTemperature (by rfl)]
    exact hcp_water
  have hdeltaCp_target : reactionHeatCapacityChange data targetTemperature = 12 := by
    unfold reactionHeatCapacityChange
    rw [hreaction, hcp_methane_target, hcp_dioxygen_target,
      hcp_carbonDioxide_target, hcp_water_target]
    simp [methaneCombustion, methaneGas, dioxygenGas, carbonDioxideGas, waterGas] ;
      norm_num
  have htarget : data.reactionEnthalpy targetTemperature = -729.576 := by
    calc
      data.reactionEnthalpy targetTemperature =
          data.reactionEnthalpy referenceTemperature +
            reactionHeatCapacityChange data targetTemperature *
              (targetTemperature - referenceTemperature) / 1000 :=
        hkirchhoff targetTemperature (by norm_num [targetTemperature])
      _ = -729.576 := by
        rw [henthalpy_at_298, hdeltaCp_target, suppliedFallbackEnthalpyAt298]
        norm_num [referenceTemperature, targetTemperature]
  exact ⟨htarget, by rw [htarget]; norm_num⟩

end IChO2026Problems
