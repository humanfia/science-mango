# Autoformalization result: `problem_phyx_mini_0342.lean`

## Assumption/target split

### Governing laws

- The coherent-SI ideal-gas law `p V = n R T` holds at each of states `a`, `b`, and `c`.
- Mayer's relation `C_p = C_v + R` relates the two molar heat capacities.
- For every directed leg, the ideal-gas internal-energy change is `n C_v (T_final - T_initial)`.
- The first-law sign convention is `Q = ΔU + W`, with `Q` heat transferred to the gas and `W` work done by the gas.
- The adiabatic `c → b` leg has zero heat transfer.
- The constant-pressure boundary work on `a → c` is `p_a (V_c - V_a)`.
- The constant-volume `b → a` leg does no work.
- Total cycle work is the sum of the work on the three directed legs.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- The gas amount is `3 mol`, `C_p = 29.1 J/(mol·K)`, and the standard gas-constant readout used for the numerical calculation is `R = 8.31 J/(mol·K)`.
- The Kelvin readings are `T_a = 300`, `T_c = 492`, and `T_b = 600`.
- Primary-image inspection resolves the loop direction as `a → c → b → a`. This corrects the auxiliary caption's erroneous `a → b → c → a` description and agrees with the source phrase “cycle acb.”
- The horizontal axis is volume, the vertical axis is pressure, the origin is labeled `O`, and the plotted states are labeled `a`, `b`, and `c`.
- The `a → c`, `c → b`, and `b → a` legs are respectively horizontal/constant-pressure, curved/adiabatic, and vertical/constant-volume.
- Horizontal and vertical alignment give `p_a = p_c` and `V_b = V_a`.

### Current target conclusion

- The physical total work done by the gas has a joule readout that rounds to `-1.95 × 10^3 J` at nearest-ten-joule precision (answer choice B).
- The explicit rounding relation is used because the supplied `C_p` and standard `R` are finite-precision decimal data; the governing laws give `-1949.4 J`, which reports as `-1.95 × 10^3 J` to three significant figures.

## Goal-faithfulness audit

- The numerical target `-1.95 × 10^3 J`, the corresponding tolerance interval, and answer choice B occur only in the theorem conclusion and its general reporting predicate.
- `RoundsToNearestTenJoules` is a parameterized measurement/rounding relation; it contains no fixed answer and does not make the theorem true by unfolding.
- No premise field asserts the requested total-work value. `totalWorkIsSumOfDirectedLegs` is only the general cycle-additivity law, while all individual-leg relations are standard first-law, ideal-gas, adiabatic, constant-pressure, or constant-volume laws.
- Work, heat, internal energy, pressure, volume, and temperature retain physical types. Reals are used only for named coherent-SI readouts, the measured mole count, molar constants, and numerical observations.
- Sign conventions are explicit, so the negative result means net work is done on the gas during this counterclockwise compression cycle.

## Declarations created and blueprint coverage

- Blueprint label `thm:physics:phyx_mini_0342:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0342.totalWorkDoneByGas_rounds_to_negative_1Point95_kilojoules`.
- Supporting declarations include `GasVolume`, the SI readout functions, the state/leg/figure vocabularies, `ThermodynamicState`, `IdealGasCycleSetup`, `HasPhysicalIdealGasCycleParameters`, `SatisfiesIdealGasCycleLaws`, `HasGivenIdealGasCycleData`, and `RoundsToNearestTenJoules`.
- The theorem statement is ready for a blueprint `\leanok` marker. The blueprint was not edited because this prover's explicit write permissions restrict edits to the assigned Lean file and this result file.

## LeanExplore queries/candidates actually used

- Query `thermodynamic ideal gas state pressure volume temperature work adiabatic process` found `Temperature`, `DimPressure`, `IdealGas.ideal_gas_law`, `adiabatic_relation_log`, and related thermodynamics declarations.
- Query `physical dimensions SI units energy pressure volume temperature amount of substance` found `Dimensionful`, `Dimension`, `UnitChoices.SI`, `DimEnergy.joule`, and `DimPressure`.
- Query `DimVolume volume cubic meter` did not find a ready-made thermodynamic volume type; `Dimensionful` was the relevant generic candidate.
- Query `molar heat capacity joule per mole kelvin` found `CanonicalEnsemble.heatCapacity` and `TemperatureUnit.kelvin`; the former is a canonical-ensemble constant-volume derivative and does not model the supplied molar `C_p` readout.
- Query `Temperature Temperature.toReal TemperatureUnit.kelvin` confirmed `Temperature`, `Temperature.toReal`, `TemperatureUnit`, and `TemperatureUnit.kelvin`.
- Query `Dimensionful WithDim UnitChoices.SI` confirmed the generic dimensionful-quantity representation and the coherent SI choice used by the readout functions.
- Query `DimEnergy DimPressure` confirmed the two ready-made physical quantity types used by the setup.
- Query `amount of substance mole dimensional` did not find a mole/amount-of-substance physical type.
- Query `thermodynamic work energy dimension` found `DimEnergy` but no finite process/cycle-work API.
- Query `adiabatic_relation_UaUbVaVb` found that theorem and `adiabatic_relation_log`; both are near misses for the needed heat/work formulation.
- Source/module/docstring details were fetched for the candidates intended for use or assessed as near misses: `Temperature`, `Temperature.toReal`, `TemperatureUnit`, `TemperatureUnit.kelvin`, `Dimensionful`, `UnitChoices.SI`, `DimEnergy`, `DimEnergy.joule`, `DimPressure`, `IdealGas.ideal_gas_law`, `CanonicalEnsemble.heatCapacity`, `adiabatic_relation_log`, and `adiabatic_relation_UaUbVaVb`.

## Physlib/Mathlib names grounded

- `Temperature` and `Temperature.toReal` from `Physlib.Thermodynamics.Temperature.Basic` represent absolute temperature and its numerical coordinate.
- `TemperatureUnit` and `TemperatureUnit.kelvin` from `Physlib.Thermodynamics.Temperature.TemperatureUnits` record that the supplied readings are Kelvin readings.
- `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and `UnitChoices.SI` from the Physlib units API support the physical volume and coherent SI projections.
- `DimPressure` from `Physlib.Units.WithDim.Pressure` represents pressure.
- `DimEnergy` from `Physlib.Units.WithDim.Energy` represents heat, internal-energy change, leg work, and total work.
- Mathlib supplies `ℝ`, absolute value, decimal notation, exponentiation, conjunctions, and the ordinary algebraic relations used in the declarations.

## Local abstractions introduced

- `GasVolume := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)` uses Physlib's dimensional infrastructure rather than a scalar alias and preserves the length-cubed physical role.
- The small inductive types for states, directed legs, axes, labels, process kinds, leg shapes, and cycle direction preserve the named geometry and qualitative image information without encoding the answer.
- `IdealGasCycleSetup` keeps all energetic quantities dimensionful and makes the sign convention explicit.
- Moles, `C_p`, `C_v`, and `R` are named real SI readouts because the source supplies scalar numerical readings and LeanExplore found no compatible amount-of-substance or molar-heat-capacity quantity type.
- `SatisfiesIdealGasCycleLaws` is a local governing-law interface because the available Physlib ideal-gas result is in a unitsless statistical-mechanics model and is not directly compatible with this finite-state, dimensionful undergraduate cycle.

## Grounding gaps

- Physlib has no ready-made `DimVolume`, amount-of-substance/mole quantity, molar heat-capacity-at-constant-pressure quantity, or finite thermodynamic-process/cycle work API in the searched packages.
- `IdealGas.ideal_gas_law` explicitly uses a unitsless system with `R = 1`, so applying it here would discard the stated SI dimensions and the molar gas constant.
- `adiabatic_relation_log` and `adiabatic_relation_UaUbVaVb` concern entropy/internal-energy-volume relations in real scalar variables; they do not provide the heat/work first-law interface needed for this problem.
- The requested `archon dag-query` navigation could not run because `archon` was not available on `PATH` in this invocation. No blueprint ancestors were needed for this self-contained target.
- The requested project-local `.archon/AGENTS.md` was absent. The injected role instructions, `.archon/prover-modes/physics-formalize.md`, and `.archon/PROGRESS.md` supplied the applicable role and workflow constraints.

## Review-gate resolution and redraft requests

- The exact retry reason was missing post-formalization evidence. This result now records the actual searches, grounded declarations, local abstractions, gaps, assumption/target split, source/figure discrepancy, law audit, answer audit, and verification.
- No Lean-statement redraft is requested. The plan agent should add `\leanok` to the target blueprint environment after reviewing this declaration; this prover did not edit the protected blueprint chapter.

## Verification

- `archon-lean-lsp` diagnostics: success with one expected `sorry` warning.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0342.lean`: exit code 0 with one expected `sorry` warning.
