# Prover result: `PhyXMiniProblems/problem_phyx_mini_0444.lean`

## Result

The sole placeholder in
`PhyXMiniProblems.ProblemPhyXMini0444.quality_change_in_tank_A_is_choice_D`
was replaced by a complete proof. No declaration header or hypothesis was
changed, and the assigned Lean file now contains no `sorry`, `admit`, axiom,
or `sorryAx`.

## Proof outline

- The initial `20 L` liquid and `180 L` vapor phase volumes, together with
  `V = m v`, give
  `m_liquid = 50000 / 2361 kg` and `m_vapor = 45000 / 3791 kg`.
- The final saturated-vapor contents of the equal `200 L` tank `B` have mass
  `50000 / 3791 kg`. The tank-B balance identifies this with the transferred
  mass.
- The tank-A balance therefore gives a final total mass of
  `177745000 / 8950551 kg`.
- The final tank-A filling equation and the two saturated phase-volume laws
  give a final vapor mass of `1717755000 / 134766259 kg`.
- Substitution into the independently defined vapor qualities yields the exact
  change
  `21132250911000 / 74761085951759`, approximately `0.2826637768`.
  `norm_num` proves that this is within `1/2000` of `0.283`, and case analysis
  over all four answer labels proves that only choice `D` satisfies the
  reporting tolerance.

`hFigure` and `hPhysical` are not needed by the arithmetic derivation; Lean
reports only unused-variable linter warnings for these frozen hypotheses.

## Redraft needed

None. The frozen theorem is faithful and provable.

## Project notes

- The requested `.archon/AGENTS.md` is absent. The injected role contract and
  `.archon/prover-modes/physics.md` were used.
- The assigned Lean file contains no `/- USER: ... -/` hint.
- The source report has no previous-part dependencies.
- The advertised `archon` executable is unavailable on `PATH`, so the optional
  DAG query could not run.
- The blueprint chapter does not contain the promised informal prover proof;
  its target environment still describes autoformalization. The theorem's
  Lean doc comment does state the correct mass/volume calculation route.
- The task explicitly permits writes only to the assigned Lean file and this
  report, so the blueprint was not edited. A blueprint-authorized agent should
  mark `thm:physics:phyx_mini_0444:target` with `\leanok`.

## Verification

- Lean LSP diagnostics: no errors and no `declaration uses sorry` warning.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0444.lean`: exit code `0`.
- `lean_verify` for the fully qualified theorem reports no suspicious source
  patterns and only the standard axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- No-index `git diff --check` scans emit no whitespace diagnostics for either
  permitted output file.
