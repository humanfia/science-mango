# Project Status

## Knowledge Base

### Proof Patterns (reusable across targets)

- Local approximation contract: use `=O[𝓝 0]` with an explicit remainder order, `Tendsto` on a punctured neighborhood, or `HasDerivAt`; do not state a local expansion as a global exact equality.
- Physics-law split: keep figure/data readouts, governing laws, licensed previous-part results, and the current conclusion in separate predicates/structures.
- Fixed-SI readouts: real components are acceptable only when their structures/field names retain explicit units and roles and governing equations connect them.
- Experimental algebra: establish positivity/nonzero factors before division cancellation; then normalize algebra and discharge uncertainty intervals separately.
- Natural-language prerequisites: permitted previous-part results may be restated locally, but an inconsistent prerequisite blocks the descendant target.

### Source and modeling corrections (do not regress)

- `1_C_1`: fragment conservation forces a factor `2` under both threshold square roots.
- `1_C_2`: the corrected C.1 formula gives approximately `2.0296693e-11 eV`, consistent with the recorded `2.03e-11 eV`.
- Figure 2 optics: physical lengths should use `Dimensionful (WithDim L𝓭 ℝ)` and one named `UnitChoices` projection for all coordinate readouts.
- `4_A_1`: Figure 17 gives inner diameter `33.7 mm`; with air height `9.5 cm`, the inventory is about `85 mL` and `0.094 g`. Printed `0.94 g` is a factor-ten typo.
- Import gates cleared in iter 002: `2_A_1`, `2_C_2`, and `2_C_3` use Physlib/PhysLean; `3_C_3` and `4_A_1` use explicit Mathlib imports. The current doctor has no live modeling or grounding blocker.

### Review infrastructure

- Review telemetry: `attempts_raw.jsonl` code-change events currently lose file and text payloads; do not infer unrecorded tactics.

## Last Updated

2026-07-26T18:46:29Z
