# Prover result: `problem_phyx_mini_0015.lean`

## Outcome

- Closed the sole proof obligation in
  `PhyXMiniProblems.ProblemPhyXMini0015.problem_phyx_mini_0015`.
- Kept the theorem signature, hypotheses, imports, and supporting declarations
  unchanged.
- No `sorry`, `admit`, new axiom, or proof escape hatch remains in the assigned
  file.

## Proof

- Constructed the candidate maximum as the dimensionful SI length
  `d / (2 * tan θc)`.
- Used Snell's law and monotonicity of sine and tangent on the physical angle
  interval to show that every escaping ray at this depth lands under the raft.
- Used the grazing critical ray with refraction angle `π / 2` to show that any
  depth at which the jewel remains unseen is no greater than the candidate.
- Derived `sin θc = 3/4`, `tan² θc = 9/7`, and
  `maximumDepth² = 360703/90000`, which certifies the `0.005 m` tolerance for
  answer C (`2.00 m`).

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0015.lean`: exit code 0.
  The only diagnostic is the fixed but unused
  `h_refractive_indices_positive` hypothesis.
- Lean LSP diagnostics: no errors and no `declaration uses sorry` warning.
- `lean_verify`: only standard logical axioms `propext`,
  `Classical.choice`, and `Quot.sound`; its two source-scan warnings are false
  positives from the physical word/field name `opaque`.
- Source scan found no `sorry`, `admit`, `sorryAx`, or axiom declaration.
- `git diff --check` on the assigned Lean file: clean.

## Blueprint status

- The theorem environment `thm:physics:phyx_mini_0015:target` is ready for
  `\leanok`.
- The blueprint was not edited because the explicit prover write permissions
  restrict changes to the assigned Lean file and this task-result file; the
  deterministic blueprint synchronization step should apply the marker.
- The requested run-local `.archon/AGENTS.md` was absent, as recorded in
  `.archon/PROGRESS.md`; the canonical archived role instructions and the
  injected physics-prover instructions were followed.

## Redraft needed

None.
