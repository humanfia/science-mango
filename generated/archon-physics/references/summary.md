# References

<!-- archon:references-summary -->
<!-- One row per file. Agents append/update rows as they discover what -->
<!-- actually works. The `How to read` column is a LIVING LOG, not a -->
<!-- static cheat-sheet — fill it in the first time you successfully -->
<!-- ingest a file, and correct it if a later attempt finds a better way. -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `Thermal_physics_README.md` | Source-checked roadmap; SHA-256 `d17e30d980e7f398522371973d047b6c85aaed55f02036ab06ef4d5c2df6260d`. | Plain UTF-8 Markdown; read by section with `sed`. |
| `WangFuZhangZhao_2019_arXiv1903.09502v2.pdf` | Primary arXiv v2 artifact; SHA-256 `026e100f6dc3fe567463f9712bcd01727493a2b4d6a8a380adb07d015841ea66`. | Retained byte-for-byte; use the arXiv rendering with the recorded page/equation locators because this image lacks `pdftotext`. |
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
