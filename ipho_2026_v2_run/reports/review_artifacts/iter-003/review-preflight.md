# Parallel Lean Review Preflight

- Iteration: 003
- Jobs: 22
- Duration: 39.821s
- Result: 22 passed / 0 failed

| Target | Compile | Sorries | Seconds |
| --- | ---: | ---: | ---: |
| `IPhO2026Problems/problem_IPhO_2026_1_A_1.lean` | passed | 0 | 9.397 |
| `IPhO2026Problems/problem_IPhO_2026_1_B_1.lean` | passed | 0 | 9.683 |
| `IPhO2026Problems/problem_IPhO_2026_1_B_2.lean` | passed | 0 | 39.805 |

## `IPhO2026Problems/problem_IPhO_2026_1_B_2.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_1_B_2.lean:282:5: warning: Variable name `hConicParameter` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean` | passed | 1 | 30.073 |

## `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_1_C_1.lean:184:8: warning: declaration uses `sorry`
IPhO2026Problems/problem_IPhO_2026_1_C_1.lean:215:5: warning: Variable name `hThetaNonnegative` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_1_C_1.lean:565:16: warning: `EuclideanSpace.single_apply` has been deprecated: Use `PiLp.single_apply` instead

Note: The updated constant has a different type:
  ∀ (p : ENNReal) (𝕜 : Type u_1) {ι : Type u_2} [inst : DecidableEq ι] [inst_1 : Zero 𝕜] (i : ι) (a : 𝕜) (j : ι),
    (PiLp.single p i a).ofLp j = if j = i then a else 0
instead of
  ∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] [inst_1 : DecidableEq ι] (i : ι) (a : 𝕜) (j : ι),
    (EuclideanSpace.single i a).ofLp j = if j = i then a else 0

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.single_apply` to `PiLp.single_apply x`).
IPhO2026Problems/problem_IPhO_2026_1_C_1.lean:644:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
IPhO2026Problems/problem_IPhO_2026_1_C_1.lean:691:5: warning: Variable name `hThetaNonnegative` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_1_C_1.lean:692:5: warning: Variable name `hThetaAtMostPi` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_1_C_2.lean` | passed | 0 | 28.864 |
| `IPhO2026Problems/problem_IPhO_2026_2_A_1.lean` | passed | 0 | 14.822 |
| `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean` | passed | 0 | 20.374 |

## `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_2_B_1.lean:414:5: warning: Variable name `tangencyLaw` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_2_B_1.lean:415:5: warning: Variable name `thetaMax_is_maximum` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_2_B_1.lean:417:5: warning: Variable name `givenRadiusRelation` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_2_B_2.lean` | passed | 0 | 7.903 |

## `IPhO2026Problems/problem_IPhO_2026_2_B_2.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_2_B_2.lean:198:5: warning: Variable name `hRays` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_2_B_3.lean` | passed | 0 | 8.334 |
| `IPhO2026Problems/problem_IPhO_2026_2_C_1.lean` | passed | 0 | 8.689 |
| `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean` | passed | 0 | 18.060 |

## `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_2_C_2.lean:143:5: warning: Variable name `hθ_pos` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_2_C_2.lean:143:22: warning: Variable name `hθ_lt` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_2_C_2.lean:145:5: warning: Variable name `hA_geometry` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_2_C_2.lean:149:5: warning: Variable name `h_parallel` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_2_C_2.lean:151:5: warning: Variable name `hC1` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_2_C_3.lean` | passed | 0 | 17.416 |

## `IPhO2026Problems/problem_IPhO_2026_2_C_3.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_2_C_3.lean:504:5: warning: Variable name `hAngleWindow` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_2_C_4.lean` | passed | 0 | 15.694 |
| `IPhO2026Problems/problem_IPhO_2026_3_A_1.lean` | passed | 0 | 14.579 |
| `IPhO2026Problems/problem_IPhO_2026_3_A_2.lean` | passed | 0 | 14.169 |
| `IPhO2026Problems/problem_IPhO_2026_3_A_3.lean` | passed | 0 | 8.596 |
| `IPhO2026Problems/problem_IPhO_2026_3_B_1.lean` | passed | 0 | 10.571 |

## `IPhO2026Problems/problem_IPhO_2026_3_B_1.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_3_B_1.lean:292:5: warning: Variable name `initialFieldStrength_nonneg` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_3_B_1.lean:293:5: warning: Variable name `finalFieldStrength_nonneg` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_3_B_2.lean` | passed | 0 | 17.721 |
| `IPhO2026Problems/problem_IPhO_2026_3_C_2.lean` | passed | 0 | 12.331 |
| `IPhO2026Problems/problem_IPhO_2026_3_C_3.lean` | passed | 0 | 16.357 |

## `IPhO2026Problems/problem_IPhO_2026_3_C_3.lean` diagnostics
```text
IPhO2026Problems/problem_IPhO_2026_3_C_3.lean:255:5: warning: Variable name `volumeLaw` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_3_C_3.lean:256:5: warning: Variable name `equationOfState` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_3_C_3.lean:257:5: warning: Variable name `temperaturePattern` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
IPhO2026Problems/problem_IPhO_2026_3_C_3.lean:258:5: warning: Variable name `previousPartC2` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
| `IPhO2026Problems/problem_IPhO_2026_3_C_4.lean` | passed | 0 | 10.757 |
| `IPhO2026Problems/problem_IPhO_2026_3_C_5.lean` | passed | 0 | 9.279 |
