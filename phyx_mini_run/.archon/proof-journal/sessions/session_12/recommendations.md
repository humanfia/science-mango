# Iter-013 Recommendations

## Blockers first

- Do not reassign any of the 32 iter-012 objectives; all are directly elaborated, sorry-free, grounded, and semantically certified.
- Route the two live doctor findings through an authorized structural Lean-writing lane:
  - `PhyXMiniProblems/problem_phyx_mini_0206.lean` — add a real Mathlib import and verify the target in the Lake/Mathlib environment.
  - `PhyXMiniProblems/problem_phyx_mini_0472.lean` — add a real Mathlib import and verify the target in the Lake/Mathlib environment.
- Keep the global project verdict blocked until both exact doctor entries disappear. Their shared reason is: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”.

## Next proof wave

- Select new proof objectives only from the formalization-review-passed, grounded frontier. After this batch, the reviewed count is approximately 888 sorry-bearing files.
- Preserve the source-honest correction in `0043`: the two-lens combination has overall magnification `+2` and final signed height `+16 cm`; recorded answer B = `-1` describes only the second stage.
- Preserve the source-text interpretation in `0049`: the parallel glass sheet gives outgoing direction `60°`, answer B; the auxiliary mirror-room image is unrelated and must not supply data.
- Retain exact or symbolic physical results before rounding. In particular, do not replace `0047`'s supported symbolic slit-width formula with an assumed displayed number.

## Reusable proof patterns

- For local paraxial ray claims, attach derivatives to the actual image/ray functions with `HasDerivAt`, and transport them through an exact neighborhood relation before using derivative uniqueness (`0040`, `0041`, `0055`).
- For signed multi-stage optics, solve each imaging stage first and compose signed magnifications only afterward (`0031`, `0032`, `0043`).
- For lensmaker problems, derive signed curvature radii from surface orientation before specializing the governing equation (`0056`, `0057`, `0064`).
- For numerical optics, derive an exact trigonometric expression and retain physical branch hypotheses before applying certified bounds or nearest-choice comparisons (`0028`, `0036`, `0037`, `0050`, `0051`, `0063`).
- Keep PhysLean/Physlib dimensions through the physical derivation and expose scalars only at named unit readouts (`0038`, `0047`, `0048`, `0052`, `0054`, `0056`).

## Evidence and controls

- Continue requiring every physics target's grounding log to include actual queries/candidates, grounded names, local abstractions, and explicit gaps. Compilation alone does not establish semantic faithfulness.
- Preserve the current iter-012 sync attribution: `current-objectives` scope, exactly 32 checked targets, 0 additions, and 0 removals.
- Treat unused-hypothesis linter warnings as review prompts, not automatic failures. Retain source/figure parameters when they capture physical context, but ensure the current answer remains derived from an independent governing law.
