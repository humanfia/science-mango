# Actual compact generator component acceptance

All eight exact targets, combined compilation and unchanged-environment checks passed. All selected proofs are normal live successes; the original drafts and unsuccessful attempts are preserved in experiment/node_runs. No local backup or replay was used.

| Target | Live attempts | Provenance |
| --- | ---: | --- |
| emission_action | 3 | normal live success |
| emission_signature | 4 | normal live success |
| emission_stabilizer | 2 | normal live success |
| emission_trace | 2 | normal live success |
| run_contains | 2 | normal live success |
| run_fold | 2 | normal live success |
| run_length | 2 | normal live success |
| stop | 2 | normal live success |

The accepted components establish the actual emission action/inverse, full signature transport, computed full stabilizer, checked descent path, finite-fuel output length, preservation of initial stored bases, exact fold reconstruction of final bases, and immediate stopping for a nonpositive cached root. The program computes its initial arithmetic root once and passes cached actual roots between calls.

Freshness, correct cache invariants, exclusion of positive fuel exhaustion, complete structural coverage and the original resources remain downstream obligations. This is not a full M7 acceptance receipt.
