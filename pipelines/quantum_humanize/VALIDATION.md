# Import validation — 2026-09-14

This records the original import. Subsequent formalization integration adapts the CLI entry point; current provenance is in SOURCE_MANIFEST.json and the additional checks are in [formalization validation](../quantum_formalize/VALIDATION.md).

Environment: Python 3.12.14, hmz 0.1.0 installed from the required
`48d1559805cbdb083958bf381a2ff57c183f96ab` humanize2 commit.

- All 29 imported adapter files match their hashes in `SOURCE_MANIFEST.json`.
- Existing harness control suite: 88 passed, 66 subtests passed (78.85 seconds).
- New portable-launcher tests: 3 passed. They check external evidence selection,
  research-relative audit paths, dry-run behavior, and incompatible launch modes.
- `python -m pipelines.quantum_humanize doctor`: runtime pin verified.
- Portable `scripts/run_quantum_harness.py --repo RESEARCH --prepare`: the actual
  research workspace's frozen baseline passed all 17 tests (12.83 seconds).
- Publication-checkout probe: correctly rejected README drift against the
  historical archive manifest at research commit
  `753c672d28da4c550078fcb81b93122530ebf4df`. See README for baseline requirements;
  no check was disabled or rewritten to hide this failure.

These checks validate the imported control code and external-checkout boundary.
They do not prove a mathematical result, start live model turns, or integrate
this harness with the existing Lean kernel workflow.

Reproduce the control and launcher tests together from the repository root:

```bash
.venv-quantum-harness/bin/python -m pytest -q pipelines/quantum_humanize
```

The combined expected count is 91 tests plus 66 subtests. Runtime setup and the
separate research baseline command are documented in README.md.
