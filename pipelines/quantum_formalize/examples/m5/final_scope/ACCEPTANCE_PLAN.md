# Final root acceptance evidence

The final decision concerns the original contract, not the number of successful experiments and not a scheduler flag. Use a separate root acceptance artifact after the actual final theorem/record exists. This proposal does not mark that future root accepted now.

## Evidence to retain

1. **Fixed specification.** Record the reviewed source hash, the final root declaration name, its full elaborated type, and the definitions expanding its contract. Link each original clause to its corresponding theorem/algorithm field. Confirm that no extra physical-witness, residue-pattern or abstract-oracle correctness hypothesis replaced an original conclusion.
2. **Definition correspondence.** Record hashes of the actual A, C, conditional arithmetic counts, period search, birth search and concrete recovery definitions. Check that the public path uses their divisor/character/binomial expressions, with guards, multiplicities, anchors, repetitions and empty cases preserved. Semantic cardinality helpers are permitted proof tools. No separate H-reindexing or runtime implementation requirement is imposed.
3. **Accepted dependency closure.** Promote only actual accepted proofs, verifying each receipt, frozen statement, draft/candidate correspondence and source/compiled hashes. Retain failed attempts and any repair provenance. Hash the final promoted sources and pins. Successful components remain accepted even if a different original clause is unfinished.
4. **Combined kernel check.** Compile the final combined root module against the pinned Lean/Mathlib environment. In a separate import-check module, assert the exact intended root type using the compiled theorem and inspect `#print axioms` for the full root. Allow only the existing standard basis `propext`, `Classical.choice`, `Quot.sound`; reject `sorryAx` or an unproved custom axiom. Check environment/source stability as in existing receipts.
5. **Concrete termination/correctness connection.** Verify actual period search45, actual birth specialization43 and actual arithmetic recovery46/47, including initial count, branch partition, terminal decoding and source decision bounds. Generic recovery theorems alone are insufficient, but no extra codegen benchmark or executable-language refinement is required.
6. **Root outcome.** Produce a root result that identifies the exact checked contract, combined artifact, clause map and remaining-original-obligation list. Set root completion true precisely when every original clause is discharged. If something remains, name that specific clause and missing link; do not substitute a vague “not strong enough” assessment.

A suitable root artifact might have fields:

```json
{
  "scope": "original M5 arithmetic workflow",
  "source_sha256": "a7c0e2ae5f555864340f4b3e6d6674e5b2e74abf382ca5de4d3e5d68da6951a3",
  "root_declaration": "<actual final declaration>",
  "root_type_sha256": "<exact checked contract hash>",
  "combined_compile": "<actual result>",
  "independent_exact_type_import": "<actual result>",
  "root_axioms": "<actual print-axioms output>",
  "definition_correspondence": "<clause/definition evidence>",
  "actual_recovery_wiring": "<46/47 exact proof evidence>",
  "remaining_original_obligations": "<actual list>",
  "original_m5_formalized": "<computed final decision>"
}
```

The placeholders deliberately are not successful results. The final record should be generated from actual evidence, not copied and asserted manually.

## The component `m5_formalized=false` flag

Current `dag.py` and `dag_runner.py` literally emit `m5_formalized: False` for component experiments. Their job is scheduling and verifying the frozen nodes/assembly; they do not inspect a semantic original-M5 root contract. Therefore:

- A component with `experiment_passed=true` and `m5_formalized=false` is not contradictory.
- That fixed flag must not invalidate an actually complete root theorem. Otherwise the controller would prevent success by construction.
- Do not rewrite historical component receipts or flip their flags merely to announce success.
- Add the separate root evidence/result described above. Once the complete actual root passes, its completion result takes precedence for the root question; the old flags retain their original component meaning.

No further stronger target should appear after that decision. Runtime extraction, efficient complexity, distance, optional inherited or anchored ordering, equivalence classes, Tanner-graph reachability, and a new literal H-index representation are not completion gates for this source contract.
