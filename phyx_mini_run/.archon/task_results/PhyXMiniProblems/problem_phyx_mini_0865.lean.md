# Prover result: `problem_phyx_mini_0865.lean`

## Status

Complete. The proof obligation
`PhyXMiniProblems.ProblemPhyXMini0865.proton_speed_at_point_B` is closed with
the frozen declaration signature and physical model unchanged. No `sorry`,
`admit`, axiom, or other escape hatch remains in the assigned file.

## Proof summary

- Read the `30 V` and `-10 V` endpoint potentials from the typed figure
  hypotheses.
- Substituted the initial speed and standard proton mass/charge calibration
  into conservation of `K + q V`.
- Used the nonnegativity built into `SpeedQuantity` to select the physical
  speed and proved the exact midpoint bounds
  `79500 < speedAt B < 124500`.
- Converted each absolute-distance comparison to a squared-distance
  comparison with `sq_lt_sq`; the midpoint bounds prove that displayed answer
  D (`100000 m/s`) is uniquely nearest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0865.lean` exits 0 with no
  diagnostics.
- Source scan finds no `sorry`, `admit`, `axiom`, or `sorryAx`.
- `lean_verify` reports only the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint

The target theorem proof environment is ready for deterministic `\leanok`
synchronization. Per prover write permissions, the blueprint chapter was not
edited; the sync phase owns this marker update.

The requested run-local `.archon/AGENTS.md` is absent. I read the
identical-SHA canonical archived `AGENTS.md` referenced by `.archon/PROGRESS.md`
instead.

## Redraft needed

None.
