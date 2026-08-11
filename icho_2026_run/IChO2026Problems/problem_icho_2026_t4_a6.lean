import Mathlib
import CRNT.Basic.Reaction

/-!
# IChO 2026, Theory Problem T4 ("The Nuclear Past of Uzbekistan"), subquestion 4.6

**Source contract.**  The Urtabulak gas-field blowout released burning methane.
Subquestion 4.6 asks for the standard molar reaction enthalpy
`ΔrH°₂₉₈ (kJ mol⁻¹)` of the combustion of **one mole of methane** at 298 K,
assuming **all species are gaseous**, using the thermodynamic data table printed
below the question (T4 page 2):

| quantity                    | value             |
|-----------------------------|-------------------|
| `ΔfH°₂₉₈(CH₄)`              | `−74.8 kJ mol⁻¹`  |
| `ΔfH°₂₉₈(H₂O, gas)`         | `−241.8 kJ mol⁻¹` |
| `ΔfH°₂₉₈(CO₂)`              | `−393.5 kJ mol⁻¹` |
| `C_P(CH₄)`                  | `35 J mol⁻¹ K⁻¹`  |
| `C_P(H₂O, gas)`             | `34 J mol⁻¹ K⁻¹`  |
| `C_P(O₂)`                   | `29 J mol⁻¹ K⁻¹`  |
| `C_P(CO₂)`                  | `37 J mol⁻¹ K⁻¹`  |

The heat capacities are tabulated for the follow-up subquestions (Kirchhoff
correction); they do not enter the 298 K computation of 4.6, but they are part
of the printed dataset and are therefore carried by `sourcedData`.

**Governing relations.**

* Balanced equation (one mole of methane, all species gaseous):
  `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`, with element conservation for
  C, H and O (`methaneCombustion_balanced`).
* Hess's law: `ΔrH°₂₉₈ = Σ_s ν_s · ΔfH°₂₉₈(s)` with signed stoichiometric
  coefficients `ν` (products positive, reactants negative).
* Standard-state convention used by the official marking scheme:
  `ΔfH°₂₉₈(O₂, g) = 0` for the elemental reference state.

**Target.**  `ΔrH°₂₉₈ = −802.3 kJ mol⁻¹`
(official answer: `[−393.5 + 2·(−241.8)] − [−74.8 + 2·0] = −802.3 kJ mol⁻¹`).

The 4.6 question box also prints, in red: *"If you did not get an answer for
4.6, use `ΔH₂₉₈ = −750 kJ mol⁻¹` for further calculations."*  That fallback
serves the follow-up subquestions (4.7 ff.) only; it is not derivable from the
4.6 data, so it is recorded here as a comment, not as a Lean declaration.

**Modelling conventions.**  Following the project convention
(`IChO2026Chem.Kinetics.BelousovZhabotinsky`), thermodynamic quantities are
real numerical readouts in the source units indicated in the docstrings.  The
balanced equation is carried by `CRNT.Reaction` from the pinned chemistry
library, whose `vector` is exactly the signed stoichiometric coefficient
function `s ↦ (target s : ℝ) − (source s : ℝ)`.
-/

namespace IChO2026.T4.A6

/-- The four chemical species of subquestion 4.6.  The problem instructs that
all species are gaseous; the phase is part of each species' identity (it is
load-bearing: `−241.8 kJ mol⁻¹` is the enthalpy of formation of water
*vapour*, not of liquid water). -/
inductive Species where
  /-- Methane, CH₄(g): the fuel, one mole combusted per reaction as written. -/
  | methane
  /-- Dioxygen, O₂(g): the oxidant; elemental reference state. -/
  | dioxygen
  /-- Carbon dioxide, CO₂(g): combustion product. -/
  | carbonDioxide
  /-- Water vapour, H₂O(g): combustion product. -/
  | waterVapour
  deriving DecidableEq, Repr

deriving instance Fintype for Species

/-- The phases referenced by the 4.6 dataset. -/
inductive Phase where
  | gas
  | liquid
  | solid
  deriving DecidableEq, Repr

/-- The elements occurring in the 4.6 species, over which the combustion
equation must balance. -/
inductive Element where
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Repr

/-- The number of atoms of element `e` in one formula unit of species `s`,
from the molecular formulas CH₄, O₂, CO₂ and H₂O. -/
def atomCount : Species → Element → ℕ
  | .methane, .carbon => 1
  | .methane, .hydrogen => 4
  | .dioxygen, .oxygen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .waterVapour, .hydrogen => 2
  | .waterVapour, .oxygen => 1
  | _, _ => 0

/-- The balanced combustion equation `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`,
as a CRNT reaction: the source complex carries the reactant coefficients and
the target complex the product coefficients.  The equation is written per one
mole of methane, which is the normalization requested by the subquestion. -/
def methaneCombustion : CRNT.Reaction Species where
  source := fun
    | .methane => 1
    | .dioxygen => 2
    | _ => 0
  target := fun
    | .carbonDioxide => 1
    | .waterVapour => 2
    | _ => 0

/-- The equation combusts exactly one mole of methane per reaction as written. -/
theorem methaneCombustion_source_methane :
    methaneCombustion.source .methane = 1 := rfl

/-- The reaction is balanced: every element is conserved.  Formally, the
signed stoichiometric sum of atom counts vanishes for each element:
`Σ_s ν_s · (# e-atoms in s) = 0`. -/
theorem methaneCombustion_balanced (e : Element) :
    ∑ s : Species, methaneCombustion.vector s * (atomCount s e : ℝ) = 0 := by
  have huniv : (Finset.univ : Finset Species) =
      {.methane, .dioxygen, .carbonDioxide, .waterVapour} := rfl
  cases e <;>
    simp [methaneCombustion, atomCount, CRNT.Reaction.vector_apply, huniv] <;>
    norm_num

/-- The thermodynamic dataset of subquestion 4.6.

* `phase s` records the phase of species `s`; the problem assumes every
  species is gaseous, and the tabulated values are the gas-phase ones.
* `referenceTemperature` is the numerical readout in kelvin of the
  temperature at which the standard formation enthalpies are tabulated.
* `formationEnthalpy s` is the numerical readout of the standard molar
  enthalpy of formation `ΔfH°₂₉₈(s)` in `kJ mol⁻¹`.
* `heatCapacity s` is the numerical readout of the molar heat capacity
  `C_P(s)` in `J mol⁻¹ K⁻¹` (tabulated for the follow-up subquestions;
  unused by the 298 K computation of 4.6). -/
structure ThermodynamicData where
  phase : Species → Phase
  referenceTemperature : ℝ
  formationEnthalpy : Species → ℝ
  heatCapacity : Species → ℝ

/-- The full dataset printed in the table below subquestion 4.6 (T4 page 2).
The value `ΔfH°₂₉₈(O₂, g) = 0` is not printed but is the standard-state
convention for an element in its reference state, applied as `+0` in the
official marking scheme. -/
def sourcedData : ThermodynamicData where
  phase := fun _ => .gas
  referenceTemperature := 298
  formationEnthalpy := fun
    | .methane => -74.8
    | .dioxygen => 0
    | .carbonDioxide => -393.5
    | .waterVapour => -241.8
  heatCapacity := fun
    | .methane => 35
    | .dioxygen => 29
    | .carbonDioxide => 37
    | .waterVapour => 34

/-- **Hess's law** at the reference temperature: the standard molar reaction
enthalpy is the stoichiometric sum of the standard molar formation
enthalpies,

`ΔrH°₂₉₈ = Σ_s ν_s · ΔfH°₂₉₈(s)`,

where `ν` is the CRNT reaction vector of `methaneCombustion` (products
positive, reactants negative).  The readout is in `kJ mol⁻¹` per mole of
reaction as written, i.e. per mole of methane combusted. -/
def reactionEnthalpy (data : ThermodynamicData) : ℝ :=
  ∑ s : Species, methaneCombustion.vector s * data.formationEnthalpy s

/-- **Subquestion 4.6 (target).**  Assume all species are gaseous at the
reference temperature 298 K, with the tabulated standard molar formation
enthalpies `ΔfH°₂₉₈(CH₄,g) = −74.8 kJ mol⁻¹`,
`ΔfH°₂₉₈(H₂O,g) = −241.8 kJ mol⁻¹` and `ΔfH°₂₉₈(CO₂,g) = −393.5 kJ mol⁻¹`,
and with `ΔfH°₂₉₈(O₂,g) = 0` by the standard-state convention for the
elemental reference state.  Then the standard molar enthalpy of the methane
combustion reaction `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)` at 298 K is

`ΔrH°₂₉₈ = [ΔfH°(CO₂) + 2·ΔfH°(H₂O)] − [ΔfH°(CH₄) + 2·ΔfH°(O₂)]
        = −802.3 kJ mol⁻¹`. -/
theorem combustion_enthalpy_298 (data : ThermodynamicData)
    (hgas : ∀ s, data.phase s = .gas)
    (hT : data.referenceTemperature = 298)
    (hCH4 : data.formationEnthalpy .methane = -74.8)
    (hO2 : data.formationEnthalpy .dioxygen = 0)
    (hCO2 : data.formationEnthalpy .carbonDioxide = -393.5)
    (hH2O : data.formationEnthalpy .waterVapour = -241.8) :
    reactionEnthalpy data = -802.3 := by
  have huniv : (Finset.univ : Finset Species) =
      {.methane, .dioxygen, .carbonDioxide, .waterVapour} := rfl
  unfold reactionEnthalpy
  simp [methaneCombustion, CRNT.Reaction.vector_apply, huniv, hCH4, hO2, hCO2, hH2O]
  norm_num

/-- The recorded answer, instantiated on the printed table:
`ΔrH°₂₉₈(sourcedData) = −802.3 kJ mol⁻¹`. -/
theorem combustion_enthalpy_298_sourced :
    reactionEnthalpy sourcedData = -802.3 :=
  combustion_enthalpy_298 sourcedData (fun _ => rfl) rfl rfl rfl rfl rfl

end IChO2026.T4.A6
