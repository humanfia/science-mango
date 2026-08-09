# IChO 2026 dataset

This directory contains the official English 2026 International Chemistry
Olympiad exam materials organized with the same two-layer data model used by
the repository's IPhO datasets.

## Dataset outputs

| File | Rows | Purpose |
|---|---:|---|
| `icho_2026_archon.jsonl` | 95 | Complete strict 29-field HiPhO/Archon-compatible dataset |
| `icho_2026_archon_pipeline.jsonl` | 36 | Conservative formalization-ready subset |
| `processed/icho_2026_all.jsonl` | 95 | Provenance-rich native records |
| `processed/icho_2026_theory.jsonl` | 68 | Theory-only native records |
| `processed/icho_2026_experiment.jsonl` | 27 | Practical-only native records |
| `processed/icho_2026_pipeline.jsonl` | 36 | Native form of the pipeline subset |

Theory papers T1–T9 map to canonical problem numbers 1–9. Practical papers
P1–P3 map to canonical problem numbers 10–12, avoiding ID collisions. Every
canonical row has exactly the same 29 top-level fields as
`hipho_ipho_2024_2025/hipho_ipho_2024_2025_archon.jsonl`; its category is
`chemistry`.

## Source layout

- `raw/`: four combined English problem/solution PDFs.
- `text/`: deterministic page-marked plain-text extraction used by the builder.
- `image/`: official question-page renders and blank practical answer sheets.
- `processed/`: native JSONL, JSON array, hashes, counts, and provenance.
- `review/`: a TSV preview, representative full rows, schema manifest, and
  human-review summary.

The organizer's source index is <https://www.icho2026.uz/problems>. The local
combined PDFs are verified copies from the [Dutch Chemistry Olympiad
mirror](https://scheikundeolympiade.science.ru.nl/internationaal/2026/index.html);
their exact download URLs and SHA-256 hashes are recorded in
`processed/manifest.json`.

## Rebuild

From the repository root:

```bash
python scripts/build_icho_2026_dataset.py
```

The builder uses only Python's standard library. It validates all 95 question
markers, point totals, problem/solution prompt pairs, asset paths, dependency
counts, unique IDs, answer-array alignment, and the exact 29-field contract.

## Interpretation notes

- `points` stores raw per-subquestion rubric points. Paper percentage weights
  are kept separately in `processed/manifest.json`.
- The official overview table reports T4=24 and T7=60 raw points, while the
  corresponding paper grids and per-item rubrics sum to 22 and 54. The dataset
  follows the per-item rubrics and records both reported values.
- Some official answers are vector drawings, tick matrices, or graphs and
  therefore are incomplete in PDF plain-text extraction. Affected rows carry a
  visual-answer notice and exact solution-page provenance. Selected practical
  matrices and ticks were manually transcribed from the official solution.
- P3.3 depends on local experimental master values; the official rubric itself
  uses placeholders. The dataset does not invent a universal numeric answer.
- Solution pages are never included among model-input images. Practical answer
  sheet images are blank official templates and are explicitly marked as such.
