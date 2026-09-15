# General weighted character formula accepted

All eight core targets passed exact target checking, Lean kernel compilation and axiom auditing. The combined assembly compiled and the project environment remained unchanged. Canonical evidence is `experiment/` (167 manifest entries), from `character-repair-7wbor4e_`.

For every binary subspace `D` of `Fin m → ZMod 2`, the character sum is its cardinality on the orthogonal set and zero elsewhere. The proof outside the orthogonal set explicitly translates by a subspace word with character −1 and cancels opposite integer sums. The coordinate-product identity then proves the exact general weighted MacWilliams formula over `Polynomial ℤ`:

`C(|D|) * weightedDual D w = weightedTransform D w`.

Weights `w i s` are arbitrary integer polynomials. Thus the formula supports all coordinate pins and signed intermediates without a rational division or an assumed transform formula. The module has no squarefreeness, cyclic-code, stabilizing-order or performance assumption.

The initial live batch accepted five components and failed the two-element `sign_eq_one` tactic, blocking the last two targets. Its complete 151-file evidence is preserved under `experiments/initial_sign_tactic_failure/`. The exact repair first establishes that a binary value equals the actual `ZMod` literal 0 or 1, then substitutes before simplifying; direct `fin_cases` left `Fin` constructors that the simplifier did not normalize. The repair passed independent exact-target/kernel/axiom checking before the full replay. Five accepted proof bodies were replayed unchanged. Orthogonality succeeded on live attempt 3 and weighted MacWilliams on live attempt 1. An independently checked orthogonality backup is retained but did not replace that live success.

Settings remained `gpt-6-astra`, medium effort, concurrency 16, five rounds, with Mathlib and Physlib retrieval. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. `REPAIR_REPLAY.json` records proof origins and live attempts.

The pinned specialization and equal-fiber/cardinality normalization are tracked in `pinned/` and `fibers/`. This core result alone is not a claim that every original M6 clause has been formalized.
