# iter-001 Review

- Scope: 28/28 listed autoformalization targets; direct preflight 28 passed, 0 failed; 85 expected open sorries; no recompilation.
- Formalization Review: 21 passed, 7 failed.
- Doctor-blocked: `2_A_1`, `2_C_1`, `2_C_2`, `4_B_6` (`missing-physlib-import`).
- Modeling-blocked: `4_A_1` (missing numerical/error premises), `4_A_5` (fixed output band, no uncertainty propagation), `4_C_6` (disconnected official sample).
- Passing statements have explicit governing-law/elimination carriers, uncertainty treatment where applicable, and branch/orientation constraints.
- Blueprint: no orphan/broken-ref findings. Correct the missing factor `2` in C.1/C.2 recorded text and add target `\lean{...}` mappings.
- Grounding: all 28 logs structurally complete; no dedicated physics-reviewer report because the subagent is disabled.
- Marker sync: current-objectives scope, all 28 checked, 0 added/removed; no manual marker edits.

