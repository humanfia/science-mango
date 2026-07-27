# Blueprint Doctor

## Physics modeling

Physics-aware chapters marked `% archon:physics` should preserve the meaning of load-bearing physical quantities. The Lean targets below either miss the real Mathlib/Physlib import path or introduce self-contained placeholder physics such as local scalar classes, tag-only dimensions, symbolic Taylor/asymptotic enums, fake Jacobian records, or bare `Real`/`ℝ` quantity collapses. Replace them with Mathlib/Physlib-grounded statements or a justified typed local model documented in the blueprint.

- `IPhO2026Problems/problem_IPhO_2026_2_A_1.lean` :: `missing-physlib-import` - physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions
- `IPhO2026Problems/problem_IPhO_2026_2_C_1.lean` :: `missing-physlib-import` - physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions
- `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean` :: `missing-physlib-import` - physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions
- `IPhO2026Problems/problem_IPhO_2026_4_B_6.lean` :: `missing-physlib-import` - physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions

