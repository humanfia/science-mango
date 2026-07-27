# Prover result: IPhO 2026 problem 2, B.1

## Status

Partial. The assigned file compiles, but one focused `sorry` remains in
`radiusAtIncidence_from_figure2f`.

The proof body already extracts the path supplied by
`physics.limiting_tangent_path_exists θ hθ`, obtaining:

- `setup.isPhysicalPath path`,
- `setup.isLimitingPathForRadius path (setup.radiusAtIncidence θ)`,
- `setup.isTangentToContainer path (setup.radiusAtIncidence θ)`,
- one reflection, and
- incidence angle `θ`.

No field of `ValidSolarCookerPhysics`, and no field of `Figure2fReadout`,
connects any of those abstract predicates to the claimed numerical identity

```lean
setup.radiusAtIncidence θ =
  scaleLength
    (Real.sin θ - (1 / 2) * Real.sin (2 * θ))
    setup.mirrorRadius
```

`Figure2fReadout.actual_radius_matches_thetaMax` only identifies the actual
container radius with `radiusAtIncidence thetaMax`; it does not determine the
radius response at an arbitrary admissible `θ`.

The downstream theorem `problem_IPhO_2026_2_B_1` has a complete algebraic proof
conditional on the helper: it evaluates the coefficient identity at `π/2` and
`π/4`, uses the standard sine values, and derives `α = R` and `β = -R/2`.
It therefore remains transitively dependent on the helper's `sorry`.

## Verification

Command:

```text
lake env lean IPhO2026Problems/problem_IPhO_2026_2_B_1.lean
```

Result: exit code 0, with exactly the warning
`declaration uses 'sorry'` at the declaration
`radiusAtIncidence_from_figure2f`.

No declaration signature was changed, and no axiom or proof escape hatch was
introduced.

## Redraft needed

- Original problem id: `IPhO_2026_2`, part `B.1`.
- Source report: `reports/ipho_2026/problem_IPhO_2026_2_B_1.source.json`.
- Theorem: `IPhO2026Problems.IPhO2026_2_B_1.radiusAtIncidence_from_figure2f`.
- Reason: the conclusion is not derivable from the frozen contract. The
  radius response and the limiting/tangency predicates are uninterpreted and
  are related only by an existence assertion.
- Smallest faithful repair: add a governing-law projection to
  `ValidSolarCookerPhysics` stating that an admissible, one-reflection limiting
  tangent path of incidence `θ` has radius
  `(sin θ - (1/2) sin (2θ)) R`. The projection should take the six path facts
  already extracted in the partial proof and conclude the displayed
  `radiusAtIncidence` equality. Then the helper closes by applying that
  projection, and the existing final theorem closes without further redraft.

## Blueprint readiness

Neither theorem proof environment is ready for `\leanok`: the helper has the
active `sorry`, and the final theorem depends on it.
