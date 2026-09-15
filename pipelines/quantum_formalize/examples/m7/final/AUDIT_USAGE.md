# Final root evidence audit

From the repository, run:

```sh
/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python pipelines/quantum_formalize/examples/m7/final/audit_root.py
```

Use `--check-only` to suppress the acceptance-file write even when every check passes. Exit 0 means all checks passed; exit 2 means required canonical evidence is still pending; exit 3 means supplied evidence is inconsistent. Only an all-passing ordinary invocation writes `ROOT_ACCEPTANCE.json` with `m7_formalized=true`.

The script starts no model, compiler or new review. It checks canonical manifests and successful batch receipts; the exact `M7.Final.original_m7` target, resolved dependency context, original draft/candidate/frozen-target sources, compiler and axiom receipts, and portable declaration; every selected parent claim’s target identity and closure; original natural-language proof/candidate/decision hashes; and the actual eight-section `M7Final.lean` composition reconstructed from `CLAIM_MAP` and the frozen preparation selection. The final claim source and imported accepted modules must match the root experiment’s frozen environment.

Historical portable rendering before and after the shared-leading-indent fix is supported only when it is exactly reconstructed from the accepted original draft. This preserves old successful batches without accepting arbitrary replacement declarations.

Historical pre-root self-test: the absent final canonical root returns pending and creates no acceptance file. Twenty available parent batches covering 132 dependency-closure targets passed the same receipt/source/portable checks. This is preparation evidence, not final M7 acceptance.

The full root audit has now passed: [ROOT_ACCEPTANCE.json](ROOT_ACCEPTANCE.json), covering all 97 selected clauses.
