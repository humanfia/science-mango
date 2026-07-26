# Autoformalization result: `problem_phyx_mini_0470.lean`

## Assumption/target split

### Governing laws

- `SatisfiesPressureVolumeWorkAreaLaw.netWorkEqualsSignedEnclosedArea` states the quasi-static `p`-`V` law that signed enclosed area equals net work done by the system.
- `SatisfiesClosedSystemFirstLaw.internalEnergyChangeIsStateDifference` states that internal energy is a state function by relating the cycle change to final minus initial internal energy.
- `SatisfiesClosedSystemFirstLaw.firstLawForCompleteCycle` uses the explicit sign convention `Q_into = ΔU + W_by`.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- `MatchesProblemStatement` records the route `a → b → a`, equality of the initial and final thermodynamic states, and the given net work readout `W_by = -500 J`.
- `MatchesPrimaryPressureVolumeDiagram` records the `V` and `p` axes; visible labels `a` and `b`; their dimensionful pressure and volume coordinates; the inequalities `V_a < V_b` and `p_b < p_a`; the lower `a → b` and upper `b → a` arrows; counterclockwise orientation; and the negative-work enclosed-area annotation.
- `HasPhysicalStateReadouts` requires positive pressure and volume at each process stage.
- The four displayed scalar answer readouts are `350 J`, `500 J`, `333 J`, and `450 J`, with recorded label B.

### Current target conclusions

- Helper lemma `netInternalEnergyChangeInJoules_eq_zero`: the closed cycle has zero net internal-energy change.
- Main theorem `heatTransferDuringCycle_matches_recordedChoice`: signed net heat into the system is `-500 J`, and its magnitude is `500 J`, the displayed value for recorded choice B.

## Goal-faithfulness audit

The setup keeps pressure, volume, work, heat, and internal energy as dimensionful physical quantities. `netHeatTransferredIntoSystem` is an independent field of `CyclicPVProcess`; neither the setup nor any problem/figure predicate assigns it a numerical value. The only heat constraint is the general first-law relation `Q_into = ΔU + W_by`. The `-500 J` hypothesis is attached solely to the work observable supplied by the problem. The initial/final state equality and state-function law force `ΔU = 0`; only then can the main target infer signed heat `-500 J`. `netHeatTransferMagnitudeInJoules` is merely `abs` of the independent heat readout and does not encode `500` by definition. Thus neither the signed heat conclusion nor the choice-B magnitude is smuggled into a premise, structure field law, or target-specific local definition.

The apparent sign ambiguity in the source was preserved rather than hidden: with heat positive into the system and work positive by the system, the physics gives `Q_into = -500 J`, meaning `500 J` is rejected. The dataset's positive answer B is therefore represented as the magnitude of that transfer.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0470:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0470.heatTransferDuringCycle_matches_recordedChoice`.
- `PhyXMiniProblems.ProblemPhyXMini0470.netInternalEnergyChangeInJoules_eq_zero` is an unlabelled helper declaration for the cyclic state-function step.
- Supporting declarations cover dimensionful quantities/readouts, diagram and cycle vocabulary, the process/setup records, problem and primary-image predicates, governing-law predicates, and answer-choice readouts.
- The theorem environment is ready for `\leanok`. The blueprint was not edited because this prover's write permissions explicitly allow only the assigned Lean file and this task-result file.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- Natural-language query `first law of thermodynamics heat work internal energy cyclic process` returned `MicroHamiltonian.internalU`, `DimEnergy`, and statistical-mechanics declarations, but no general closed-system first-law or cyclic `p`-`V` process interface.
- Likely-name query `thermodynamics FirstLaw internalEnergy heat work` likewise returned `MicroHamiltonian.internalU`, `DimEnergy`, and unrelated/specialized thermodynamics declarations.
- Natural-language query `joule SI unit energy physical quantity` returned `DimEnergy` and `DimEnergy.joule`; their source/module data were inspected.
- Likely-name query `PhysLean thermodynamics` returned statistical-mechanics APIs but no suitable general first-law declaration.
- Likely-name query `DimPressure` returned `DimPressure` and `DimPressure.pascal`; the source and module for `DimPressure` were inspected.
- Natural-language query `dimensionful physical volume length cubed` returned `Dimensionful`, `Dimension.L𝓭`, and related unit infrastructure; `Dimensionful` source/module data were inspected.

`MicroHamiltonian.internalU` was not used because it is a specialized real-valued derivative of a microcanonical partition function with respect to inverse temperature, not a general dimensionful state variable for this macroscopic cycle.

## Physlib/Mathlib names grounded

- `DimEnergy` from `Physlib.Units.WithDim.Energy`, with physical dimension `M L² T⁻²`.
- `DimPressure` from `Physlib.Units.WithDim.Pressure`, with physical dimension `M L⁻¹ T⁻²`.
- `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and `UnitChoices.SI` for the nonnegative `L³` volume carrier and coherent-SI readouts.
- `NNReal` for nonnegative volume magnitudes and `abs` on `ℝ` for the displayed positive heat-transfer magnitude.

## Local abstractions introduced

- `VolumeQuantity` uses `Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)` because no ready-made volume alias appeared in the searches. This preserves both the `L³` dimension and nonnegative physical magnitude.
- `ThermodynamicState`, `PressureVolumeDiagram`, and `CyclicPVProcess` distinguish dimensionful state variables and independent transfer observables from scalar readouts.
- `SatisfiesPressureVolumeWorkAreaLaw` and `SatisfiesClosedSystemFirstLaw` are local governing-law interfaces because the available Physlib search results did not provide general APIs for this macroscopic cycle. They express standard laws only and contain no target heat value.
- Small inductive types preserve the literal figure labels, axes, arrows, curve locations, orientation, work sign, and shaded-area meaning.

## Grounding gaps and redraft requests

- No general Physlib declaration for the closed-system first law or signed work of a cyclic pressure-volume path was found; faithful local law predicates were required.
- No ready-made Physlib volume quantity alias was found; the generic dimension infrastructure was used directly.
- The blueprint should clarify that, under the diagram's stated convention “work done by the system,” `W_by = -500 J` gives signed heat into the system `Q_into = -500 J`; the positive recorded choice `500 J` is the magnitude of heat rejected, not positive heat added.
- The requested `archon dag-query` navigation could not be run because `archon` was not available on `PATH` in this prover environment.
- The requested project file `.archon/AGENTS.md` was absent. The injected prover instructions and `.archon/prover-modes/physics-formalize.md` supplied the operative role rules.

## Verification

- `archon-lean-lsp` diagnostics reported no errors and exactly two expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0470.lean` exited successfully with only the same two expected warnings.
