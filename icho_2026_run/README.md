# IChO 2026 answer-blind formalizations

This Lake project contains Lean formalizations for 32 selected theory-ready
subquestions from the IChO 2026 theory papers T1--T9. Practical papers P1--P3
and the remaining theory subquestions are outside this release's scope.

The proofs were generated in a fresh answer-blind campaign from commit
`10b04c62`. The solver workspace contained the official problem statements and
images, but not the official solutions. All 32 selected targets passed direct
Lean compilation, source-aware formalization review, proof review, placeholder
scans, the axiom sweep, and the default Lake build.

An independent post-run comparison found all 47 requested outputs equivalent
to the official rubric answers, for an expected 168/168 raw points within this
selected target set. This is not a claim of a full score on the complete IChO
exam. Validation details, rounding notes, and one known auxiliary-carrier
limitation are recorded in [RESULTS.md](RESULTS.md).

## Build

```bash
lake exe cache get
lake build
```

The selected target list is `references/icho_2026_theory_ready.jsonl`.

- [Source code](https://github.com/humanfia/science-mango/tree/chemistry-blind-solver-kimi/icho_2026_run)
- [Dataset](https://huggingface.co/datasets/humanfia-lab/icho-2026)
