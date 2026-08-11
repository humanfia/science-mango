# References

<!-- references-summary -->
<!-- One row per file. Agents append/update rows as they discover what -->
<!-- actually works. The `How to read` column is a LIVING LOG, not a -->
<!-- static cheat-sheet — fill it in the first time you successfully -->
<!-- ingest a file, and correct it if a later attempt finds a better way. -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `icho_2026_theory_ready.jsonl` | Extracted official IChO 2026 theory questions and marking-scheme answers | `jq -c 'select(.id == "<target-id>") | {id, current_question, answer, previous_parts, images}' references/icho_2026_theory_ready.jsonl` |
| `../icho_2026_source/raw/theory_solution.pdf` | Official theory marking scheme (solutions + rubrics), PDF page numbering | Answer-page PNGs exist only for P1–P3 (practical); theory answer pages must be rendered: `pdftoppm -f <pdfpage> -l <pdfpage> -r 400 -png ../icho_2026_source/raw/theory_solution.pdf out` (poppler installed), then Read the PNG; 400 dpi + PIL crop/2–3x LANCZOS upscale resolves red pathway highlights (confirmed on p.58, the 6.7 electron-count figure). |
| `../icho_2026_source/image/T<n>_page-<k>.png` | Problem-statement page PNGs (primary visual evidence) | Read directly. Structure figures resolve well; for fine bond-highlight detail render the matching `../icho_2026_source/raw/theory_problem.pdf` page at 400 dpi and crop. |
<!-- Example row (delete once you have real entries):                   -->
<!-- | `paper.pdf` | Source paper for chapter 3 | `Read` with `pages: "1-12"` (poppler installed); for the appendix tables, `pdftotext paper.pdf - \| sed -n '120,180p'` was clearer. |  -->

<!-- Rules of thumb when filling in `How to read`:                       -->
<!--   * If `Read` worked out of the box, write `Read` (and any options   -->
<!--     you needed, e.g. `pages: "1-5"` for long PDFs).                  -->
<!--   * If `Read` failed and you fell back to a shell command, record   -->
<!--     the exact command (e.g. `pdftotext file.pdf -`, `pandoc … -t    -->
<!--     markdown`, `unzip -p archive.zip path/inside.tex`).             -->
<!--   * If a file is binary / opaque (e.g. a Mathematica notebook with  -->
<!--     no useful plain-text export), say so — that saves the next      -->
<!--     agent from trying.                                              -->
<!--   * When in doubt, prefer the cheapest tool that gives you the part -->
<!--     you actually need (a page range, a single table) over loading   -->
<!--     the whole file.                                                 -->
