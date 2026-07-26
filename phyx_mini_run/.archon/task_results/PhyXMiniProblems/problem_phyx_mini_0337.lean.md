# Prover result: `problem_phyx_mini_0337.lean`

## Outcome

Complete. Both assigned proof obligations were closed, reducing the file's
`sorry` count from 2 to 0.

- `workAlongProcessLegs` specializes the stated straight-path boundary-work
  law to `a → b` and `b → c`, rewrites the endpoints using the primary-diagram
  transcription, and normalizes the exact rational calculations. This gives
  work by the gas of `0 J` and `4053/25 J`, respectively; unfolding the
  opposite sign convention gives the corresponding work-on-gas values.
- `problem_phyx_mini_0337` reuses those leg results, substitutes the stated
  `215 J` heat input into the supplied first law, and obtains the exact
  internal-energy change `1322/25 J`. Exact normalization proves that this
  value differs from recorded choice B's `53 J` by less than half a joule.

All frozen declaration signatures and physical hypotheses were preserved. No
helper declarations, axioms, admissions, or proof-laundering constructs were
introduced. The positivity hypothesis `h_physical` is not needed after the
exact figure readouts and governing laws have been supplied.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0337.lean`: exit code 0.
  Its only diagnostic is the linter warning that the frozen `h_physical`
  argument is unused.
- Root `lake build`: completed successfully.
- The individual dotted path is not registered as a Lake target
  (`lake build PhyXMiniProblems.problem_phyx_mini_0337` reports
  `unknown target`), so direct file compilation supplied the file-level check.
- A source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide` occurrence in the assigned file.
- `git diff --check` reported no whitespace errors.

## Blueprint readiness

The proof environments for `workAlongProcessLegs` and
`problem_phyx_mini_0337` are ready for `\leanok`. The blueprint was not edited:
the prover write boundary reserves marker maintenance for deterministic sync.

The run-local `.archon/AGENTS.md` is absent. As stated in `PROGRESS.md`, the
canonical archive copy was read instead, together with the active physics
prover mode. The linked source report is
`reports/phyx_mini/problem_phyx_mini_0337.source.json`. The `archon`
executable was unavailable on `PATH`, but no graph dependency was needed for
this self-contained proof.

The file-specific `/- USER: ... -/` comment only records that the source file
did not exist when autoformalization began; it imposes no additional proof
constraint.

## Redraft needed

None.
