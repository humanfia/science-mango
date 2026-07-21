# Humanize-style qcode discovery

`archon qcode-humanize` adds a durable RLCR control layer around the existing
quantum-code pipeline. It follows the useful parts of PolyArch/Humanize without
replacing the domain-specific search engine:

```text
OpenEvolve strategy mutation + MAP-Elites
                  │
                  ▼
        Python rank / BP-OSD screen
                  │
                  ▼
      persistent candidate elite archive
                  │
                  ▼
       diverse top-N candidates → MILP
                  │
                  ▼
 independent read-only Codex review (fresh session)
                  │
                  ├── risks/focus → next search round
                  └── evidence-backed BitLessons → long-term memory
                  │
                  ▼
      Archon formalization → Lean compilation
```

The search model and reviewer are independent invocations. The reviewer cannot
change machine-derived fields. In particular, BP-OSD is always an upper bound,
and a partial MILP run remains an upper bound even if the reviewer recommends
promotion. Exact distance requires every logical direction to be solved to
proven optimality; complete `[[n,k,d]]` verification additionally requires the
generated Lean theorem to compile.

## Full run

```bash
. /root/proposal_for_physic/science-mango/run_env.sh

archon qcode-humanize /root/proposal_for_physic/science-mango \
  --repo-dir /root/proposal_for_physic/science-mango/qcode-discovery \
  --rounds 5 --iterations-per-round 20 \
  --model gpt-5.5 --review-model gpt-5.5 \
  --reasoning-effort xhigh --review-effort xhigh \
  --milp-top 3 --milp-early-stop 0 \
  --formalize --prove --formalize-top 3 \
  --lean-project /root/proposal_for_physic/science-mango/qcode_lean_bridges/qcode_bridge \
  --bridge-dir /root/proposal_for_physic/science-mango/qcode_lean_bridges \
  --lean-jobs 1
```

`--install` (the default) runs `uv sync --group dev --group evolve` in the
vendored qcode tree. Use `--no-install` after the environment is prepared.
OpenEvolve must expose a `reasoning_effort` or generic model-kwargs field;
explicit `xhigh` requests fail loudly if the installed version cannot forward
them.

## Resume and state

Reuse the same `--run-id` to resume a failed run. State updates are atomic and
candidate logs are consumed by byte offset, so finished candidates are not
re-audited. A completed run is idempotent.

```text
qcode-discovery/results/humanize/<run-id>/
  state.json
  events.jsonl
  elite-archive.json
  bitlesson.md
  rounds/round-NNN/
    contract.json
    evolution.log
    candidates.jsonl
    milp.jsonl
    review-request.md
    review.json
    review.log
    summary.md

qcode-discovery/results/evolution/humanize_<run-id>/
  all_codes.jsonl
  best_generate_candidates.py
  checkpoints/

qcode-discovery/results/runs/<run-id>/
  evaluations.jsonl
  run_meta.json
  metrics.json
  metrics.md
```

Lean artifacts use the same location as the baseline pipeline:

```text
qcode_lean_bridges/qcode_bridge/.archon/qcode-runs/<run-id>/
```

## Baseline comparison

Run `archon qcode` with the same MILP timeouts and Lean top-N as the fixed
baseline. Compare `metrics.json` from both run IDs.

| Property | `archon qcode` | `archon qcode-humanize` |
|---|---|---|
| Candidate generator | fixed Python function | LLM-evolved generator |
| Diversity memory | within one candidate batch | OpenEvolve MAP-Elites plus cross-round elite archive |
| Long-term lessons | no | evidence-backed BitLesson file |
| Independent review | no | fresh read-only Codex session each round |
| BP-OSD/MILP semantics | strict upper/exact split | same strict split |
| Lean verification | optional | optional, same trusted bridge |

The key outcome metrics are fully exact MILP rate, BP-OSD agreement on exact
ground truth, Lean objective pass rate, complete-parameter Lean verification
rate, best verified FOM, unique elite cells, wall time, and model/MILP cost.
