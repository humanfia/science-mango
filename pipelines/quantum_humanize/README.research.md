# Quantum-code research harness

Adapted from `menik1126/fput-thermalization`, commit
`4c9cb5b86f8d91359824542a66904ebcfdfcbabb`, directory `pipelines/fput_humanize`.
The source was extracted with `git archive`, without copying the dirty local checkout.
The humanize2 runtime stays pinned to `48d1559805cbdb083958bf381a2ff57c183f96ab`.

The eight roles and bounded scheduling, fresh independent dual reviews, repair,
semantic dispatch, hash-bound inputs and evidence records come from that harness.
Quantum obligations and constraints are in `_tasks.py`. SELF must be independently
audited before any dependent theorem is accepted. Other obligations cover birth/lift,
distance laws and the certified selector. No automatic status certifies the full goal.

FPUT-specific analytic coverage/linear-cutoff planning is disabled and rejected by
configuration. Generic proof integration and fresh dual reviews remain enabled.
`docs/` accepts Markdown only; explicit script, test and data inputs retain their
relative paths and hashes. Generated proof documents also use the docs namespace.
Old review votes are never imported. `MANIFEST.json` records baseline source hashes;
run snapshots record the exact selected current files. Changes to frozen sources
halt a live run rather than silently changing its mathematical inputs.

From the repository root:

```bash
.venv-harness/bin/python -m pipelines.quantum_humanize doctor
.venv-harness/bin/python -m pytest -q pipelines/quantum_humanize
.venv-harness/bin/python scripts/run_quantum_harness.py --prepare
.venv-harness/bin/python scripts/run_quantum_harness.py --live
```

The launcher defaults to the local session configuration `gpt-6-astra`, `medium`,
4 concurrent calls, 4 jobs per round, at most 20 rounds and 640 calls, with the
upstream 2,000,000 reported-output-token soft cap. This cap does not bound input
or reasoning tokens or guarantee completion. `--model` and `--effort` are explicit
overrides. The default obligation is `self_audit`; `--obligation` selects the next
research task. Run results live in `.humanize-quantum-runs/` and include requests,
responses, proof candidates, audits, integration and final status.

The upstream tests retained here check flow control using fake agents. Supporting
FPUT test fixtures are marked `__test__ = False`; their domain-specific scenarios
are not quantum-code tests. The actual baseline wrapper separately runs the four
regression modules listed by the roadmap. Only the catalogue JSONL needed for
these checks has been hydrated from Git LFS; other LFS binary certificates remain
unavailable unless explicitly fetched and added to a future evidence snapshot.

Validation on 2026-09-13: 80 control tests and 66 subtests passed; all 17 roadmap
baseline tests passed in the frozen snapshot. Strict static and runtime flow
loading checks passed. These checks validate the adapter and existing evidence,
not SELF or any new mathematical result.

First live SELF audit run: `.humanize-quantum-runs/run-gwvgxbzi`.
Its model, budgets and exact input hashes are recorded in `plan.json` and
`snapshot/_snapshot.json`. Startup passed all baseline checks and entered reader.

## Incomplete-integration audit fix

The generic integration branch previously called reviewers directly and treated
`inconclusive` as a mathematical repair. It now uses the same bounded
`audit_pair` continuation and `assessed` routing as candidate audits. Exhausted
incomplete reviews enqueue the unchanged composition. Only `gap`/`wrong` routes
trigger proof repair. A successfully re-audited selected-obligation composition
finishes directly, without composing it again and discarding that recovery.

Four dedicated regressions cover same-session continuation, bounded audit-only
queueing, successful recovery without reintegration, and genuine-gap repair.
Restart the preserved composition without importing historical votes:

```bash
.venv-harness/bin/python scripts/run_quantum_harness.py --live \
  --audit-input .humanize-quantum-runs/controller/audit-seed.json
```

This audit recovery uses one work slot (the two reviewers still run independently)
and skips strategy review. The task explicitly preserves proof routes as requested.

For a new obligation, canonical drafts from other obligations remain validated
readable evidence but are excluded from the selected obligation's composition
queue. A regression verifies that an old distance draft cannot trigger integration
in a SELF run. Current controller task status explicitly distinguishes completed
external-review work from historical author-time remaining-obligations text.

## Larger composition audits

On 2026-09-14, compositions with 35–39 direct dependencies repeatedly exceeded
the 30-minute reviewer deadline. The launcher now allows 60 minutes per ordinary
call and four same-reviewer continuations. The shared call and token caps still
apply. Reading plans use UTF-8-safe 8 KiB ranges, with at least 16,384 output tokens
requested per read; truncated output still requires smaller replacement reads.
All hashes, complete-source checks, and independent verdict requirements remain.

Use `--audit-only --rounds 1 --audit-input PATH` to review an unchanged seed
without immediately integrating that reviewed sublemma again. It does not mark
the larger mathematical obligation complete. The preserved round-6 seed is
`.humanize-quantum-runs/controller/birth-lift-integration6-audit-seed.json`.

Validation: 87 control tests and 66 subtests pass, including lossless chunking of
large single-line Unicode JSON and an audit finishing on its fourth continuation
without repeating the other reviewer's completed positive verdict.
