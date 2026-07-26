# Archon qcode discovery → Lean verification

`archon qcode` connects the computational discovery cascade to generated Lean
proofs:

```text
GF(2) validation/rank → BP-OSD upper bounds → top-N HiGHS MILP
                     → exact/upper claim split → Lean bridges → Lean check
```

Example:

```bash
. /root/proposal_for_physic/science-mango/run_env.sh

archon qcode /root/proposal_for_physic/science-mango \
  --repo-dir /root/proposal_for_physic/qcode-discovery \
  --no-update-repo --no-install --full \
  --lattices 12,6 --milp-top 3 \
  --milp-timeout-per-logical 300 --milp-total-timeout 7200 \
  --formalize --prove --formalize-top 3 \
  --lean-project /root/proposal_for_physic/science-mango/qcode_lean_bridges/qcode_bridge \
  --bridge-dir /root/proposal_for_physic/science-mango/qcode_lean_bridges \
  --lean-jobs 1
```

Use `--milp-early-stop 0` (the default) when exact MILP certification is
desired. A positive early-stop budget can accelerate discovery, but its result
is kept as an upper bound unless all `2k` logical directions were solved to
proven optimality.

`--formalize` selects MILP-audited candidates when such rows are present and
generates three Lean tiers:

- `css`: CSS orthogonality;
- `upper`: explicit logical witness proving `distance ≤ w`;
- `exact`: block length, dimension, complete logical bases, upper witness, and
  a `bv_decide`/LRAT lower-bound proof yielding `VerifiedParameters code k d`.

`--prove` compiles every generated theorem. Python, BP-OSD, and HiGHS remain
untrusted certificate producers; partial MILP status never becomes an exact
Lean objective. If an upper-bound witness is lighter than the discovery bound,
the generated theorem automatically states the tighter checked bound.

Artifacts are resumably grouped under:

```text
<lean-project>/.archon/qcode-runs/<run-id>/
  catalog.json
  exact-catalog.json
  upper-catalog.json
  objectives.jsonl
  manifest.json
  css/
  exact/
  upper/
  lean-logs/
```

`--no-update-repo` preserves local qcode-discovery changes. `--no-install`
skips dependency installation but still activates an existing repository
virtual environment.
