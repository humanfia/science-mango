# Pinned MacWilliams specialization accepted

All four exact targets passed kernel, target and axiom checks; the combined assembly and unchanged-environment checks passed. Canonical evidence is `experiment/` (88 manifest entries), from `pinned-repair-focnyo45`.

The final theorem is

`C((subspaceWords D).card) * M6.Pinned.enumerator (dualWords D) P = pinnedTransform D P`.

It applies to every binary subspace and every shared Option-valued pin assignment, with the exact `M6.Pinned` agreement and nonzero-coordinate weight definitions. Each coordinate boundary factor accepts its pin and contributes the full weight of a pinned one. The character factor is its two-bit signed transform. The proof specializes the accepted general weighted formula, after proving that the product of boundary factors is exactly the pinned weight monomial. For a free coordinate its character factor is `1 + C(sign s) * X`.

The eight core proof imports were verified against their source, frozen target, payload, receipt, original object hashes and combined assembly, then recompiled and audited in this isolated project. No prior pinned-recovery proof was needed: its frozen definitions are shared exactly and their hashes are recorded in `IMPORT_PROVENANCE.json`.

The initial 79-file failure archive is preserved under `experiments/initial_weight_tactic_failure/`. It accepted the free-coordinate formula but exhausted attempts on the weight-as-sum tactic. The exact repair substitutes actual `ZMod` literals 0 or 1 before normalization, and passed independent kernel/target/axiom checks. The successful full replay rechecked that repair and the unchanged accepted free-factor proof; the product bridge then succeeded on live attempt 2 and pinned MacWilliams on live attempt 1. Statements and hypotheses were unchanged.

Settings remained `gpt-6-astra`, medium effort, concurrency 16, five rounds, with Mathlib and Physlib retrieval. All audited axioms lie in `propext`, `Classical.choice`, `Quot.sound`. This proves the pinned transform clause; physical fiber normalization, cycle/boundary identification and the final original-M6 theorem are separate integration work.
