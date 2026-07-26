# Prover result: `problem_phyx_mini_0161.lean`

## Status

Complete. All three `sorry` placeholders were replaced by sound proofs, and the
assigned Lean file compiles.

## Proofs

- `water_side_image_depth_index_relation`: rewrites the water-side image depth
  through the image-depth geometry, plane-mirror equality, mirror-object
  geometry, and air-to-water apparent-object law, then closes the resulting
  polynomial identity with `ring`.
- `final_image_distance_index_relation`: substitutes the final
  distance-from-mirror geometry and combines the return-refraction law with the
  preceding water-side depth relation using `nlinarith`.
- `problem_phyx_mini_0161`: specializes the general relation to centimetres,
  substitutes `d₁ = 250`, `d₂ = 200`, `n_air = 1`, and
  `n_water = 133 / 100`, and derives
  `D = 46650 / 133`. `norm_num` verifies that choice D is within half a
  centimetre and is strictly closer than A, B, and C; the D-versus-D branch is
  eliminated by the competing-choice hypothesis.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0161.lean`: succeeded.
- LSP diagnostics: no errors; one harmless unused-variable warning for the
  frozen `physical` parameter of `water_side_image_depth_index_relation`.
- Source scan: no `sorry`, `admit`, user-defined `axiom`, `native_decide`, or
  `sorryAx`-style escape.
- Axiom verification for
  `PhyXMiniProblems.ProblemPhyXMini0161.problem_phyx_mini_0161`: only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint and role-file notes

The blueprint chapter exists and was read before proof work. It was not edited
to add `\leanok`, because the task's explicit write permissions restrict edits
to the assigned Lean file and this task-result file. The chapter still lacks a
problem-specific informal proof; a plan agent may document the derivation
`n_water D = n_water d₁ + (2 n_air - n_water) d₂` and the numerical
specialization.

The requested `.archon/AGENTS.md` is absent in this checkout. `.archon/PROGRESS.md`
explicitly records that the run-local file is absent and that the canonical
archived instructions supply the active role.

## Redraft needed

None.
