# M7 formalization status

In progress; complete M7 Lean acceptance is pending. All 56 frozen natural-language source files were hash-checked; `SOURCE.json` records their identities.

Five completed batches contain **43 accepted targets**, each with combined compilation, unchanged environment and exact target/axiom checks:

| Batch | Accepted | Scope |
| --- | ---: | --- |
| [supports](supports/experiment/result.json) | 6 | Actual support polynomials and coefficients |
| [selection](selection/experiment/result.json) | 12 | Pareto/lex selection, all ties, empty answers and winning dominators |
| [factorized](factorized/experiment/result.json) | 6 | Independent-shift arithmetic numerator and partitions |
| [action](action/experiment/result.json) | 13 | Actual unit/exchange/two-shift records and action laws, including N=1 |
| [domain](domain/experiment/result.json) | 6 | Support-to-M6 polynomial, anchored admissibility and shift interfaces |

Active batches: `transport` prepares actual M6 distance and witness transport (7 targets); `orbit_fibers` proves full-stabilizer fiber counts and exact division (7 targets); `presentation` proves factored least-preimage decoding and distinct winning physical outputs (12 targets). `canonical_block` has 13 exact targets prepared and is undergoing definition build/type preflight. The actual group adapter in `group` is prepared but not yet compiled.

Shared-host load caused compilation/startup timeouts in otherwise preserved proof attempts. Replays retain the frozen targets and drafts and adjust execution resources only. A timeout is not an accepted proof or a mathematical counterexample; canonical receipts remain authoritative.

Full signature transport, outer canonicalization, actual M5 prefix arithmetic, compact residual generation, physical labels, complete query integration, replay and original resource bounds remain downstream gates. Generic selector, decoder and numerator lemmas do not close these actual interfaces. No supplied complete transversal or unresolved distance oracle may remain in the final root.

The pipeline ceiling is 16 workers per DAG, with reduced concurrency under shared load. Model: gpt-6-astra / medium; five proof attempts per target; Mathlib/Physlib retrieval; frozen exact targets and Lean/standard-axiom acceptance. Historical scheduler field `m5_formalized` is unrelated to M7 completion. No full-M7 acceptance record has been issued.
