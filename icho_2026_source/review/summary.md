# IChO 2026 Archon Input Review

- Items: 95 (68 theory + 27 experiment)
- By paper: {'IChO_2026_T1': 6, 'IChO_2026_T2': 7, 'IChO_2026_T3': 7, 'IChO_2026_T4': 9, 'IChO_2026_T5': 6, 'IChO_2026_T6': 7, 'IChO_2026_T7': 7, 'IChO_2026_T8': 10, 'IChO_2026_T9': 9, 'IChO_2026_P1': 10, 'IChO_2026_P2': 8, 'IChO_2026_P3': 9}
- Formalization-ready subset: 36
- Items with explicit previous-part dependencies: 44
- Unique rendered input pages: 74

## Compatibility

- Every Archon row has exactly the same 29 top-level fields as `hipho_ipho_2024_2025_archon.jsonl`.
- Theory papers map to problem numbers 1–9; practical papers P1–P3 map to 10–12.
- `previous_parts` are explicit natural-language prerequisites and never import Lean output.
- The first image is always the current official question page; blank answer sheets never contain solutions.

## Source caveats

- Raw per-subquestion rubric points are stored. Competition percentages remain in `processed/manifest.json`.
- The official overview says T4=24 and T7=60 raw points, while each paper's own grid and per-item rubrics sum to T4=22 and T7=54. This dataset follows the per-item rubrics.
- PDF plain text omits some vector structures, ticks, and tables. Affected answers are flagged and retain exact solution-page provenance; selected experimental visuals were manually transcribed.
- P3.3 has no universal numeric official answer: the official rubric uses local master-value placeholders. No value was invented.

## Primary inputs

- `icho_2026_source/icho_2026_archon.jsonl`
- `icho_2026_source/icho_2026_archon_pipeline.jsonl`
