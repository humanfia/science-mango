# Stage47 accepted: concrete arithmetic residue recovery

All eight frozen targets, combined assembly and unchanged-environment checks passed. The concrete oracle is conditionalA applied to the take/drop split of the selected residue prefix; it contains the actual divisor/factor/character arithmetic.

| Target | Final-run attempts | Result |
|---|---:|---|
| M5.ArithmeticResidueRecovery.completion_word_split | 1 | accepted |
| M5.ArithmeticResidueRecovery.completion_prefix_card | 1 | accepted |
| M5.ArithmeticResidueRecovery.oracle_initial | 1 | accepted |
| M5.ArithmeticResidueRecovery.prefix_algebra | 1 | accepted |
| M5.ArithmeticResidueRecovery.completion_feasible | 1 | accepted |
| M5.ArithmeticResidueRecovery.oracle_prefix_count | 1 | accepted |
| M5.ArithmeticResidueRecovery.oracle_partition_terminal | 1 | accepted |
| M5.ArithmeticResidueRecovery.recovery_correct | 1 | accepted |

A completion-pair/full-word bijection and exact conditional count establish the concrete oracle prefix count. Accepted finite prefix partition and terminal identities therefore apply, and the initial oracle value equals actual A. The final recovery_correct theorem instantiates the finite residue algorithm with no abstract oracle-correctness premise: positive A yields a returned word of length 2*(w−1), raw-coordinate gcd1, exact full signature F, and at most 2*(w−1)*signaturePeriod(F) arithmetic candidate tests. Repetitions, cancellations and empty completion lengths remain allowed. This test-count bound does not claim a separate executable-runtime refinement.

The two generic helper drafts were independently checked and then submitted through the same frozen acceptance as the live concrete links; their original checks remain in root_helpers. The initial live oracle_initial and prefix_algebra proofs each succeeded on attempt2 and were preserved unchanged. Local repairs of completion_feasible, oracle_prefix_count and oracle_partition_terminal kept every target, definition and default kernel limit unchanged. In the partition node, live candidates alternated between a missing finite-word type annotation and a missing matching DecidableEq instance, reverting the earlier correction in successive attempts; the verified repair retained both. This is recorded as evidence for future harness feedback retention, not as another M5 completion gate. All prior experiments and successful proofs remain archived under experiments, with repair details in repair/README.md. See [result](experiment/result.json), [combined source](experiment/AcceptedExperiment.lean), [preflight](PREFLIGHT.json) and [manifest](experiment/MANIFEST.json).
