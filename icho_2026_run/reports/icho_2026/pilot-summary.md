# IChO 2026 theory checkpoint

Checkpoint completed on 2026-08-11. All 32 theory-ready subquestions have now
completed autoformalization, proof, deterministic compile checks, hash-bound
source-aware formalization and proof Review, and final Lake builds.
Practical/experimental papers P1--P3 were excluded before target selection;
the verified queue contains only T1--T9 theory entries.

## Representative verified targets

| Target | Formalized and proved conclusion |
| --- | --- |
| `icho_2026_t2_a2` | The Process-A and Process-B steady-state equations give `[HBrO2]A = 6.0e-6 M` and `[HBrO2]B = 5.04e-11 M`. Positivity assumptions make every cancellation explicit. |
| `icho_2026_t2_a3` | Equality of elementary-step rates (1) and (4) gives `[Br⁻]critical = 3.0e-7 M`; no answer from T2-A2 is assumed. |
| `icho_2026_t2_a5` | Process-C neglect and the retained step-(4)/(5) loss terms yield the exact first-order decay formula. The official inputs give `k* = 0.16128 s⁻¹` and a period within half a second of `48 s`; the permitted fallback gives `k* = 0.24064 s⁻¹` and a period within half a second of `37 s`. |
| `icho_2026_t4_a5` | After converting `2 MeV` to `2,000,000 eV`, the cumulative logarithmic-decrement law gives the exact collision-count formula. Certified log-series bounds place the result within `1e-4` of `19.97` and within one half of `20`. Neither number is included in the input predicate. |
| `icho_2026_t4_a6` | The balanced all-gas methane-combustion reaction and formation enthalpies give exactly `-802.3 kJ mol⁻¹` at 298 K. |
| `icho_2026_t4_a7` | The reaction-weighted constant heat-capacities give `ΔCp = 12 J mol⁻¹ K⁻¹` and exactly `-781.876 kJ mol⁻¹` at 2000 K, with `< 0.05` error from the reported `-781.9`. The source-authorized `-750` fallback is kept as a separate conditional theorem. |

The other 26 targets are imported by `IChO2026Problems.lean` and carry the
same compile, source-contract, proof-Review, and axiom-sweep guarantees.

## Automated review history

- T4-A6 and T4-A7 were the initial pilot. Review rejected the first A7 model
  because its stored reaction did not control the heat-capacity expression;
  autoformalization repaired the dependency before the proof passed.
- T2-A2 and T2-A3 were proved and chemistry-reviewed in the next batch, with
  previous-part answers kept out of the hypotheses.
- T4-A5 was proved with explicit rational log bounds rather than an unverified
  decimal evaluation.
- T2-A5 completed its mandatory proof-Review retry in iteration 015. The final
  Review found the two Process-B loss terms, named Process-C approximation,
  exact logarithmic formula, and both official/fallback branches faithful.
- A new source-first Review policy then invalidated every legacy certificate
  and re-audited all 32 targets against the official question, answer, previous
  parts, and every source image. It rejected and forced repairs to T1-A3
  (rounding at the wrong locus), T5-A4 (answer-shaped reagent candidates),
  T6-A4 (answer-shaped ion universe), and T9-A6 (a spurious regioisomer branch).
- The final gates contain 32 formalization passes and 32 solved proof Reviews;
  all stored source-contract hashes match the current files.

Every active target now compiles with zero proof placeholders. The 32-file
axiom sweep and the final post-redraft single-file sweep found no `sorryAx`
laundering or nonstandard axiom, and source audits found no `unsafe` proof
escape. The latest default `lake build` succeeded across 8611 jobs; the
remaining diagnostics are non-blocking style lints.

## Automatically generated shared BZ module

Proof Review identified duplicated BZ kinetics in T2-A2, T2-A3, and T2-A5 and
admitted a shared-infrastructure request. The workflow then:

1. generated and chemistry-reviewed
   `IChO2026Chem/Kinetics/BelousovZhabotinsky.lean`;
2. centralized the concentration/rate aliases, BZ species and state,
   `KineticParameters`, mass-action rates 1--7, and common cancellation/update
   lemmas;
3. migrated all three consumer problem files through automated refactor tasks;
4. rebuilt the shared module and consumers and ran the axiom sweep; and
5. marked the initial module and consumer migrations resolved in iteration
   012; after the API was extended to rates 1--7 and the common helper lemmas,
   reverified the shared contract in iteration 018 and re-solved all three
   consumer Reviews in iteration 019.

This is reusable project infrastructure rather than a theorem copied from any
one target. The problem modules retain their own source-specific data and
requested conclusions.

## Reproducible environment and search

- Lean: `v4.31.0`
- Mathlib: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- Physlib: `1706ae68b63996f1d97717e672e50c9e3933d933`
- crnt-lean: `99137993e729c8add247388718a22a0e0f393dab`

LeanExplore uses the exact package filters `Mathlib`, `Physlib`, and
`Chemistry`. The service configured at `http://127.0.0.1:8765/mcp` composes the
hosted Mathlib/Physlib backend with a local `Chemistry` index built from
`IChO2026Chem/` and `.lake/packages/crnt-lean/CRNT`. This made both upstream
library declarations and newly generated shared BZ declarations available to
agents through one MCP endpoint.

## Verification and rerun commands

Run from the project root:

```bash
# Fetch/build the pinned Lean environment and every umbrella-imported target.
lake exe cache get
lake build

# Verify that active project sources contain no proof placeholders or local axioms.
rg -n '\b(sorry|admit|axiom|sorryAx)\b' IChO2026Chem IChO2026Problems

# Regenerate and serve the Chemistry overlay on top of hosted LeanExplore.
./scripts/rebuild_lean_explore_index.sh
./scripts/start_lean_explore.sh

```

The umbrella imports in `IChO2026Problems.lean` and `IChO2026Run.lean` ensure
that the default build covers the shared BZ module and all 32 problem files.
The index script requires the pinned CRNT source checkout; a fresh Lake setup
obtains it during dependency resolution.

## Current modeling boundary

Concentrations, rate constants, times, temperatures, energies, heat capacities,
and molar enthalpies are real-valued readouts in the units documented beside
each definition. This is appropriate for the conversion-controlled calculations
proved here but does not yet provide universal type-level unit checking. BZ
species/state/rate laws are now shared; a reusable typed thermochemistry layer
remains future infrastructure.
