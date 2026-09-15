# M5 dependency-aware formalization experiment

[EXPERIMENT.md](EXPERIMENT.md) records the completed 9/9 auxiliary experiment.

[ROADMAP.md](ROADMAP.md) maps the reviewed natural-language proof to 28 main obligations and their dependencies. [graph.json](graph.json) is the executable scheduling input: 9 frozen auxiliary targets and the 28 explicitly planned obligations. Auxiliary nodes are linked to their parent proof obligations; they do not discharge those obligations automatically.

The first experiment formalizes packing residue preservation, packed range, packing injectivity, the collision-free shift bound, the cutoff inequality, progression divisibility, the final birth-bound inequality, and the positive recovery-branch arithmetic step. Seven nodes are initially ready and two wait for accepted dependencies. The concurrency ceiling is 16, not a requirement to invent 16 independent tasks.

## Run

Use the pinned Humanize environment described in the parent pipeline README. Copy the files under `lean/` into a dedicated Lean project, install its pinned Lean toolchain, and resolve/build Mathlib with Lake. The development project is `/home/jing/m5-lean-formalization`; cached Mathlib packages are shared locally, while M5 sources and build outputs are separate.

From this repository root:

```bash
python -m pipelines.quantum_humanize formalize-dag \
  --project /path/to/m5-lean-project \
  --graph pipelines/quantum_formalize/examples/m5/graph.json \
  --concurrency 16 --rounds 5 --live
```

Without `--live`, the command validates and prints the plan without making model calls. Live defaults are gpt-6-astra / medium. Lake must be on PATH.

## Execution and acceptance

- Validate duplicate IDs, missing dependencies and cycles before launch; prepare shared imports once.
- Dispatch only ready nodes, at most 16 simultaneously. Per-node proof attempts remain sequential.
- Search both Mathlib and Physlib through LeanExplore. Retrieval is limited to two concurrent batches independently of proof concurrency. Some Physlib queries return HTTP 500; configured broader addition queries can be tried as fallback for these arithmetic helpers. Both the original error and fallback results remain in the node's retrieval history. A failed response is never labeled as an empty successful result.
- Freeze each target. Supply dependency proof bodies only after Lean acceptance, binding them to the compiled candidate and a hash. Compile their actual declarations in downstream contexts; never inject unproved dependency axioms.
- A failure blocks its descendants but independent branches continue. Planned nodes never execute. Receipts are written atomically. Runs use fresh directories; cross-run acceptance reuse is not automatic.
- Assemble all accepted declarations into `AcceptedExperiment.lean`, compile again, and check every theorem's transitive axioms. `experiment_passed` requires every executable target plus the assembly to pass with unchanged project sources. `m5_formalized` remains false because the 28 main obligations are not yet discharged.

Each run lives under `<project>/.humanize-formal-runs/dag-launcher-*/experiment/`. `nodes/state.json` gives current status, `result.json` summarizes the experiment, and node receipts link to each retrieval, draft, compiler diagnostic and axiom audit.

The current shared Lean definitions cover only this experiment's vocabulary. Full period, residue-pattern, character-count and reconstruction definitions and the full root statement remain planned. The compiled project depends on Mathlib; searching Physlib does not silently install or assume its declarations. These experiments do not add distance or optional inherited/anchored obligations to M5.

Cancellation stops scheduling and cancels worker turns. A Lean compiler already running through the synchronous backend remains bounded by its configured compiler timeout; this version does not promise immediate termination of every compiler thread on cancellation.
