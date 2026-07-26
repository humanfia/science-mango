# Prover result: `problem_phyx_mini_0202.lean`

## Outcome

Complete. All three assigned proof obligations were closed, reducing the
assigned file's `sorry` count from 3 to 0.

- `initialBulletSpeed_squared_relation`: specialized the stated momentum and
  energy balances to kilograms, metres, and seconds; used the resting block,
  initially uncompressed spring, and zero speed at maximum compression; then
  eliminated the post-impact composite speed algebraically to derive
  `m² v² = (m + M) k x²`.
- `initialBulletSpeed_exact_readout`: proved the Physlib readout conversions
  `grams = 1000 * kilograms` and `centimeters = 100 * meters`, substituted all
  source data into the squared relation, and used positivity to select the
  positive square-root branch.
- `problem_phyx_mini_0202`: bounded the exact square root strictly between
  `26.003` and `26.004`, proving the derived speed lies within `0.05 m/s` of
  `312.6 m/s`; unfolding the answer-table entry then establishes choice D.

All frozen declaration signatures and physical hypotheses were preserved. No
helper declarations, axioms, admissions, or proof-laundering constructs were
introduced.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0202.lean`: exit code 0.
  The only diagnostics are unused-hypothesis linter warnings for `hPhysical`
  in the squared-relation lemma and `hScenario` in the main theorem; their
  frozen binders were preserved.
- Root `lake build`: completed successfully.
- The individual path is not registered as a Lake target
  (`lake build PhyXMiniProblems.problem_phyx_mini_0202` reports
  `unknown target`), so direct file compilation supplied the file-level check.
- Source scan found no `sorry`, `sorryAx`, `admit`, or `axiom`.
- Axiom verification for the final theorem reports only Lean's standard
  foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

The proof environments for `initialBulletSpeed_squared_relation`,
`initialBulletSpeed_exact_readout`, and `problem_phyx_mini_0202` are ready for
`\leanok`. The blueprint was not edited because the explicit prover write
boundary restricts this lane to the assigned Lean file and this result report;
marker synchronization should apply the markers.

The requested run-local `.archon/AGENTS.md` is absent. As recorded in
`.archon/PROGRESS.md`, the matching canonical archive role guide was read as
the fallback. No `/- USER: ... -/` comment occurs in the assigned Lean file.

## Redraft needed

None.
