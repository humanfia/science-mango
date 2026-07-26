# Prover result: `problem_phyx_mini_0344.lean`

## Status

Complete. All three proof placeholders were closed without changing any
declaration signature:

- `internalEnergyChangeAlongABC_eq_1200_joules`
- `workDoneByGasAlongABC_eq_1800_joules`
- `problem_phyx_mini_0344`

The first helper uses the figure-to-process coordinate equalities, the
ideal-gas law, and the monatomic internal-energy law to derive
`U_c - U_a = 1200 J`. The second resolves the two physical leg endpoints,
applies the straight-line trapezoid work law to both path members, and derives
total work `1800 J`. The final theorem combines these values with the stated
first-law convention to obtain positive heat input `3000 J`, matching recorded
answer B.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0344.lean`: success with
  no diagnostics.
- `lake build PhyxMiniRun`: success.
- Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, or `sorryAx`
  occurrence remains in the assigned file.
- Lean axiom verification for both helper lemmas and the final theorem reports
  only `propext`, `Classical.choice`, and `Quot.sound`, with no warnings.

## Redraft needed

None. The frozen statements are faithful and provable from their governing-law
and figure-data hypotheses.

## Blueprint readiness

The proof environments for both helper lemmas and the final theorem are ready
for `\leanok`. The blueprint chapter was not edited because the prover's write
permissions restrict changes to the assigned Lean file and this task-result
file.

The requested project-local `.archon/AGENTS.md` was absent; the injected role
instructions, `.archon/PROGRESS.md`, and `.archon/prover-modes/physics.md`
provided the applicable workflow.
