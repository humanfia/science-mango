# Iteration 008 Review

- Prover: 26/32 certified; six no-`sorry` proof bodies fail direct elaboration: `0061`, `0303`, `0333`, `0346`, `0380`, `0458`.
- Textual sorries fell 2,207 → 2,175 and sorry-bearing files 978 → 946, but those counts overstate proof closure by six. Root build passes because standalone generated files are not Lake targets.
- Manual grounding, anti-fake, governing-law, parameter, and answer-as-assumption audits pass all 32 statements. No dedicated `physics-reviewer` was enabled.
- Global verdict **BLOCKED**: doctor retains `missing-mathlib-import` on `0206`/`0472`; other doctor structural/grounding lists are empty.
- Fresh graph: 0 unknown `\uses`/gaps, 106 unmatched Lean helpers across 28 chapters, and 29 known isolated declarations.
- Markers: added 52 statement/proof `\leanok` markers for the 26 certified targets; left six broken targets unmarked; restored 32 valid markers for 16 earlier targets removed by the current sync false negative.
- Control gap persists: run-local `AGENTS.md` and `prompts/review.md` are absent; canonical identical-SHA copies supplied the review contract.
