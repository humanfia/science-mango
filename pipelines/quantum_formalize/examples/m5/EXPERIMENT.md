# M5 auxiliary DAG experiment — 2026-09-15

The repaired live experiment accepted **9/9 auxiliary declarations**, then compiled their assembled proof and checked all axiom dependencies again. The graph still records **28 planned full-M5 obligations** and `m5_formalized=false`.

Configuration: gpt-6-astra / medium, maximum 16 concurrent proof nodes, five attempts per node, Lean 4.34.0-rc1 and the pinned Mathlib in `lean/lake-manifest.json`. Seven targets were initially ready; two dependent targets were unlocked only after their prerequisite proofs passed. Search batches were limited to two at a time.

| Accepted declaration (M5 namespace) | Attempts | Axioms |
|---|---:|---|
| cutoff_gt_period | 3 | propext, Quot.sound |
| packed_range | 1 | propext |
| packed_residue | 1 | propext |
| packed_injective | 1 | propext, Classical.choice, Quot.sound |
| progression_period | 1 | propext |
| recovery_inclusion_positive | 1 | none |
| repair_above_packing | 1 | none |
| repair_no_collision | 1 | propext |
| source_below_birth_bound | 1 | propext |

The model wrote all proof bodies during the live experiment. Targets were frozen before dispatch. `packed_injective` used the accepted `packed_residue` proof; `repair_no_collision` used the accepted `packed_range` and `repair_above_packing` proofs. The cutoff inequality needed three attempts (one nonlinear arithmetic failure and one indentation error); both diagnostics remain archived.

The first run accepted two declarations but stopped five independent nodes because Physlib returned HTTP 500 for their queries; their two descendants were blocked. Its receipt correctly says `experiment_passed=false`. The revised runner retains the original failed query history, tries a configured broader query and still requires successful responses from both libraries. This fixed the retrieval issue without changing any mathematical statement.

- [Accepted assembled Lean proof](experiments/accepted/AcceptedExperiment.lean)
- [Final receipt](experiments/accepted/result.json)
- [Final graph status](experiments/accepted/GRAPH.md)
- [Initial unsuccessful experiment](experiments/initial_retrieval_failure/result.json)

Each archive includes hashes, frozen inputs, dependency receipts, library responses, generated drafts, Lean sources and compiler/axiom diagnostics. Absolute paths in original receipts identify the original run; portable copies are under `node_runs/`. Compiled `.olean` files are not included. To replay the assembled proof, build the pinned project under `lean/`, then run `lake env lean /absolute/path/to/AcceptedExperiment.lean` from that project. This proves only the listed helpers, not character counting, CRT existence, the global birth theorem or complete M5.
