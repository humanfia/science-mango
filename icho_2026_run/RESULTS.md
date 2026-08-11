# Validation results

## Scope

This release covers 32 selected theory-ready subquestions from IChO 2026
papers T1--T9. Practical papers P1--P3 are excluded. Accordingly, “32/32” below
means all selected targets passed; it does not mean a full score on the complete
competition exam.

The formalizations were rerun from the `chemistry` parent branch with
`kimi-k3[1m]` through a Claude Code harness. No prior GPT-produced problem proof
files were imported. The run was independent at the proof-file input boundary,
but it did not enforce strict per-target filesystem isolation: a small number of
K3 workers consulted sibling K3 files from the same run for formatting patterns.

## Checks

| Check | Result |
| --- | --- |
| Selected targets | 32/32 |
| Lean preflight | 32/32 passed |
| Source-bound statement audit | 32/32 fresh passes in run 6 |
| Source-bound proof audit | 32/32 fresh and solved: 27 in run 4, 5 revalidated in run 7 |
| Active placeholders and escape hatches | None: `sorry`, `admit`, custom axioms, `native_decide`, and `unsafe` all absent |
| Final all-declaration axiom sweep | 32/32 passed; 0 findings, laundering cases, or custom axioms |
| Default `lake build` | Passed; 8,611 jobs completed successfully |
| Python test suite | 863 passed, including 95 subtests; 3 deprecation warnings |
| Blueprint consistency check | Clean |

## T8-A6 source discrepancy

The official answer for T8-A6 states 1.94%. The unrounded value is approximately
1.9334888%, while the printed-checkpoint route gives
`474 / 245 ≈ 1.9346939%`. Under standard rounding to two decimal places, both
values give 1.93%, not 1.94%.

The Lean development proves 1.93% and records this as a source inconsistency;
it does not alter the mathematics to force the official 1.94% value.

## Audit limitations

Four of the five supplemental proof checks consulted generated context before
finishing their source-only assessment. Those checks still compared the
official source material and images, but they should not be described as
strictly access-isolated two-stage audits. T9-A3 followed the intended order.

Two audit notes also contain non-semantic wording limitations. The T9-A3 note
says that 35 occurs only in the final answer, although a derived ring-length
helper also contains 35. The T4-A9 note identifies an intermediate typo in the
official material but does not encode it as a structured conflict. Neither
issue changes the Lean statements, proofs, conclusions, or pass status.

## Release links

- [Source code](https://github.com/humanfia/science-mango/tree/chemistry-K3/icho_2026_run)
- [Dataset](https://huggingface.co/datasets/humanfia-lab/icho-2026-lean4-formalizations)
