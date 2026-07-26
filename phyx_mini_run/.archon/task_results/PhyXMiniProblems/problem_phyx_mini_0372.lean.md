# Autoformalization result: `problem_phyx_mini_0372.lean`

## Review-gate disposition

The iteration-002 gate reason was evidence-only: it requested a genuine
post-formalization report for the revised Lean model. I preserved the physical
statement after checking it against the source report and the primary bitmap.
The bitmap, rather than the inaccurate auxiliary caption, visibly places state
1 at `V₁ = 100 cm³` and `p₁ = 1 atm`.

The requested `.archon/AGENTS.md` is absent from this checkout. I therefore
followed the injected prover instructions, `.archon/PROGRESS.md`, and
`.archon/prover-modes/physics-formalize.md`; I also consulted the archived
same-project role file at
`../phyx_mini_archives/20260722-review3-rerun/.archon/AGENTS.md`. The assigned
Lean file contains no `/- USER: ... -/` hint.

## Assumption/target split

### Governing laws

- `SatisfiesMassMoleRelation parameters sample` is the material relation
  `m = n M`: gram mass equals mole amount times molar mass in grams per mole.
- `SatisfiesIdealGasEquation parameters sample state` is the mixed-unit ideal
  gas equation `p V = n R T`, with the scalar readouts explicitly named in
  atmospheres, cubic centimetres, moles, and kelvin.
- The theorem assumes the ideal-gas equation at all three labelled states of
  the same fixed sample. `h_amount_positive`, `h_state2_pressure_positive`,
  and `h_state3_volume_positive` retain the relevant physical domains.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Source and figure/data readouts

- Source statement: a `0.10 g` helium sample and the directed process
  `1 → 2 → 3`.
- Material/calibration data used by the textbook law: helium molar mass
  `4 g/mol` and `R = 82.06 atm·cm³/(mol·K)` (`4103 / 50`). These are explicit
  theorem assumptions, not hidden definitions.
- Primary image: `p₁ = 1 atm`, `V₁ = 100 cm³`, `V₂ = 300 cm³`,
  `T₂ = 2926 K`, `p₃ = 2 atm`, and `T₃ = 2438 K`.
- The image leaves `p₂` and `V₃` numerically unspecified. The Lean model keeps
  them as state fields and assumes only positivity; it does not invent values.
- `ThreeStateProcess.transition`, `firstToSecond`, and `secondToThird` retain
  the two arrows in the figure.
- The auxiliary caption incorrectly calls state 1 the origin. The primary
  image clearly shows `(V₁, p₁) = (100 cm³, 1 atm)`, so the theorem follows
  the image as the chapter requires.
- Dataset metadata records answer choice A, `−29 °C`. It is mentioned only in
  comments because it contradicts the stated helium mass and state-1 data.

### Current target conclusion

- `temperatureInDegreesCelsius process.state1.temperature =
  200000 / 4103 - 27315 / 100`.
- From `0.10 = n · 4`, the amount is `n = 1/40 mol`; then the state-1 ideal-gas
  equation gives `T₁ = 200000/4103 K ≈ 48.7448 K`, hence approximately
  `−224.405 °C`. This is the strongest exact numerical conclusion supported
  by the stated helium data, even though it is absent from the answer choices.

## Source/law/answer audit

- Source facts and figure readouts occur in separately named hypotheses.
- Governing laws occur in `SatisfiesMassMoleRelation` and
  `SatisfiesIdealGasEquation`; neither law fixes the requested state-1
  temperature.
- Standard material/calibration values are visible theorem hypotheses.
- The contradicted recorded answer `−29 °C` is neither a hypothesis nor the
  conclusion. No species or mass was silently changed to reproduce it.

## Goal-faithfulness audit

The state-1 Celsius equality appears only as the conclusion of
`stateOneTemperature_from_heliumData`. It is absent from `GasSample`,
`PVState`, `ThreeStateProcess`, `IdealGasParameters`, both governing-law
predicates, and all theorem hypotheses. The helper
`temperatureInDegreesCelsius` is only the general affine readout
`T.toReal - 273.15`; unfolding it does not establish the numerical answer.
The transition fields encode only process incidence/direction. Thus no current
target conclusion is smuggled into a premise structure, law, predicate, or
local definition.

## Declarations and blueprint labels

- `PhyXMini0372.GasSpecies` —
  `def:physics:phyx-mini-0372:phyxmini0372-gasspecies`.
- `PhyXMini0372.GasSample` —
  `def:physics:phyx-mini-0372:phyxmini0372-gassample`.
- `PhyXMini0372.PVState` —
  `def:physics:phyx-mini-0372:phyxmini0372-pvstate`.
- `PhyXMini0372.ThreeStateProcess` —
  `def:physics:phyx-mini-0372:phyxmini0372-threestateprocess`.
- `PhyXMini0372.IdealGasParameters` —
  `def:physics:phyx-mini-0372:phyxmini0372-idealgasparameters`.
- `PhyXMini0372.SatisfiesMassMoleRelation` —
  `def:physics:phyx-mini-0372:phyxmini0372-satisfiesmassmolerelation`.
- `PhyXMini0372.SatisfiesIdealGasEquation` —
  `def:physics:phyx-mini-0372:phyxmini0372-satisfiesidealgasequation`.
- `PhyXMini0372.temperatureInDegreesCelsius` —
  `def:physics:phyx-mini-0372:phyxmini0372-temperatureindegreescelsius`.
- `PhyXMini0372.stateOneTemperature_from_heliumData` —
  `thm:physics:phyx_mini_0372:target`.

All eight helpers are connected directly or indirectly to the target and are
needed to preserve material, unit/readout, state, and process roles.

## LeanExplore queries and candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- Natural language: `ideal gas law pressure volume amount temperature`.
  Relevant results were `IdealGas.ideal_gas_law`, `DimPressure`,
  `Temperature`, and `Temperature.toReal`.
- Likely name: `IdealGas.ideal_gas_law`. Its source, module, and docstring were
  fetched. It fixes a unitless model with `R = 1`, so it is not compatible with
  this problem's mixed atmosphere/cm³/mole/kelvin calibration.
- Natural language: `absolute thermodynamic temperature nonnegative real`.
  Relevant results were `Temperature`, `Temperature.ofNNReal`, and
  `Temperature.toReal`.
- Likely name: `Temperature`. Source/module/docstring lookup confirmed that it
  wraps a nonnegative real and represents absolute temperature.
- Likely name: `Temperature.toReal`. Source/module/docstring lookup confirmed
  the real scalar projection used in the law and readout hypotheses.
- Natural language: `amount of substance mole molar mass physical quantity`
  and likely name `MolarMass`. Results included generic `Dimension`,
  `Dimensionful`, and `MassUnit`, but no compatible mole/molar-mass API.
- Natural language: `pressure measured in standard atmospheres volume in cubic
  centimetres units` and likely name `DimPressure.standardAtmosphere`.
  `DimPressure.standardAtmosphere` was found, but the searches did not expose
  a matching cubic-centimetre/mole ideal-gas interface.
- Natural language: `affine conversion kelvin Celsius temperature` and likely
  name `TemperatureUnit.celsius`. Results exposed `TemperatureUnit.kelvin` and
  scale-only temperature-unit declarations, but no Celsius affine conversion.

## Physlib/Mathlib names grounded

- Used: `Temperature` and `Temperature.toReal` from
  `Physlib.Thermodynamics.Temperature.Basic`.
- Used: Mathlib's `ℝ` and exact field arithmetic for explicitly unit-named
  measurement projections and numerical constants.
- Considered but not used: `IdealGas.ideal_gas_law` from
  `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas`; its fetched
  declaration is unitless and sets `R = 1`.
- Search-grounded near misses: `DimPressure.standardAtmosphere`,
  `TemperatureUnit.kelvin`, `Dimensionful`, and `MassUnit`. They do not provide
  the complete mixed-unit state/law interface required here.

## Local abstractions introduced

- `GasSpecies` and `GasSample` keep the species, gram-mass readout, and mole
  amount tied to one physical sample instead of collapsing the sample to a
  scalar alias.
- `PVState` separates pressure, volume, and absolute temperature. Pressure and
  volume are scalar axis readouts with units in their field names; temperature
  uses Physlib's physical `Temperature` type.
- `ThreeStateProcess` preserves all three labels and both directed arrows.
- `IdealGasParameters` makes the species-indexed molar mass and mixed-unit gas
  constant explicit.
- `SatisfiesMassMoleRelation` and `SatisfiesIdealGasEquation` state governing
  laws directly; neither is defined in terms of the requested answer.
- `temperatureInDegreesCelsius` is a local affine scalar readout because the
  available Physlib temperature units are zero-preserving scales and the
  searches found no Celsius offset API.

## Grounding gaps and redraft requests

- No compatible Physlib declaration was found for amount of substance/molar
  mass, a mixed `atm·cm³/(mol·K)` ideal-gas law, or affine Celsius conversion.
  The local abstractions retain those physical roles explicitly.
- The source should be checked for a transcription error. Its stated helium
  data imply about `−224.405 °C`, while recorded choice A is `−29 °C`. The
  latter would instead be consistent with a molar mass near `20 g/mol`.
- The advertised `archon` executable is not on `PATH`, so the read-only DAG
  query could not run. The chapter itself supplies the target's direct helper
  dependencies.
- No statement redraft is requested in this pass: the exact review-gate reason
  was missing evidence, and the source/image audit found no defect in the
  revised statement.

## Blueprint marker readiness

The target and all topology declarations compile and are ready for statement
`\leanok` markers. I did not edit the blueprint because the active write
permissions and prover-role instructions reserve blueprint changes for the
deterministic sync/coordinator.

## Verification

- `archon-lean-lsp` diagnostics reported no errors and exactly one expected
  warning: the target declaration uses `sorry`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0372.lean` exited `0` with
  the same single expected `sorry` warning.
