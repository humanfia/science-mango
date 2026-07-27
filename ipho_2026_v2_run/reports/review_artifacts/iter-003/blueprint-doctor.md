# Blueprint Doctor

## Physics modeling

Physics-aware chapters marked `% archon:physics` should preserve the meaning of load-bearing physical quantities. The Lean targets below either miss the real Mathlib/Physlib import path or introduce self-contained placeholder physics such as local scalar classes, tag-only dimensions, symbolic Taylor/asymptotic enums, fake Jacobian records, or bare `Real`/`ℝ` quantity collapses. Replace them with Mathlib/Physlib-grounded statements or a justified typed local model documented in the blueprint.

- `IPhO2026Problems/problem_IPhO_2026_4_B_6.lean` :: `missing-physlib-import` - physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions

## Malformed annotations

Annotations with an empty argument (`\uses{}`, `\proves{}`, `\label{}`, `\ref{}`, ...) or an empty list item (`\uses{a,,b}`, `\uses{a,}`). plastex emits `Label '' could not be resolved` for each of these and then the leanblueprint depgraph builder enters infinite recursion (`RecursionError`), so the blueprint never finishes building. Fix each one by either filling in the intended label or deleting the empty annotation. Do NOT defer — the next `leanblueprint web` run will crash until these are resolved.

### `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_1.tex`
- `\bare-label{...}` — bare label "thm:physics" in prose — use \cref{thm:physics} or the human-readable number

### `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_5.tex`
- `\bare-label{...}` — bare label "thm:physics" in prose — use \cref{thm:physics} or the human-readable number

