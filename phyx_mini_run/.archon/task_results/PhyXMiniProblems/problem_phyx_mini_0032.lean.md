# Prover result: `problem_phyx_mini_0032.lean`

## Status

Complete. All three `sorry` placeholders were replaced by checked proofs while preserving every declaration signature.

## Closed declarations

- `mirror_stage_values`: derives the mirror focal length and object distance from the radius and midpoint geometry, proves the image distance is nonzero, solves the signed mirror equation, and obtains magnification `-4`.
- `return_lens_stage_values`: links the mirror image position to the return-lens virtual-object distance, proves the return image distance is nonzero, solves the signed lens equation, and obtains magnification `-167 / 83`.
- `problem_phyx_mini_0032`: composes the exact stage magnifications to obtain `668 / 83` and verifies the nearest-hundredth tolerance for answer D (`8.05`).

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0032.lean` succeeds with no diagnostics.
- `lake build` succeeds (`Build completed successfully (4 jobs)`).
- Source audit found no `sorry`, `admit`, `axiom`, `native_decide`, or `sorryAx` in the assigned file.
- No file-specific `/- USER: ... -/` comment was present.

## Blueprint readiness

The target and both supporting lemmas are fully proved and ready for `\leanok` synchronization. The blueprint was not edited because the prover write-permission rule makes it read-only.

## Redraft needed

None.
