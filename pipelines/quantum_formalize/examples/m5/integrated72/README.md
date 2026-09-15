# M5 checkpoint: 72 accepted lemmas

This checkpoint integrates the 72 accepted named lemmas from stages 1–13. It does not mark the complete M5 theorem as formalized. `M5Accepted.lean` preserves the previous 52-lemma checkpoint; `M5Checkpoint72.lean` adds the 20 accepted declarations from stages 10–13.

`build_checkpoint.py` verifies each accepted receipt, artifact payload, frozen target, candidate source and proof draft against its archived hashes. The current `dag_runner.portable_declaration` transports the exact tactic body, adding a local reducible target alias only when the original proof refers to `QuantumHarnessFrozenTarget`. This includes stage 11's deterministic replay; it does not replace or repair its mathematical proof.

Module reconciliation is limited to imports. Stage 10's support-polynomial definitions are identical to the previous checkpoint's definitions, and its promoted monomial-period lemma is the identical accepted declaration already present there, so `M5QuotientMonomialPeriod` forwards an import. Stage 12 originally imported the 41-lemma checkpoint: every declaration and support module from that checkpoint is verified unchanged within the 52-lemma superset. Stage 13's copied shared modules are verified byte-identical. No old project is modified.

`validate_checkpoint.py` builds the combined module, then independently imports all 72 exact original statements and prints their axiom dependencies. Acceptance permits only `propext`, `Classical.choice`, and `Quot.sound`. See `VALIDATION.json`, `PROVENANCE.json`, and the compiler logs for the result.

To rebuild, use the pinned Lean toolchain and Mathlib revision in `lean/`, run `lake build M5Checkpoint72`, and then `lake env lean Acceptance.lean`. The Python scripts use the documented workspace paths for the isolated validation project and shared Mathlib cache.
