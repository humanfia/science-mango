# Iteration 006 plan

## Decision made

- Advance `prover → polish`: session 5 accepted `1_C_1` and `2_B_1`, so all 22 theory targets now compile with zero placeholders and axiom-clean reviewed proofs.
- Polish the first 10 theory files in source order; the 10-objective cap forces a `10 + 10 + 2` route. Use the stage-default `polish` mode and preserve every reviewed signature and physical contract. Reverse only if direct compilation, axiom verification, or semantic comparison exposes a regression; then return only the affected file to the appropriate earlier stage.
- No blueprint prose changes are needed because no accepted mathematical route changed.

## Doctor deferrals

- `4_B_6`’s missing Physlib import is deferred solely under the standing user pause covering all six E1 targets.
- `def:project:hello` remains isolated intentionally: it is the dependency-free imported bootstrap definition, so inventing a `\uses{}` edge would misstate the graph.

## Subagent skips

- None enabled; classic single-agent loop required.
