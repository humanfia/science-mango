# Iter-009 Recommendations

## Blockers first

- Reconcile the fresh graph’s 106 unmatched Lean helper declarations across 28 chapters before claiming graph completeness. Do not invent dependency edges; add faithful blueprint declaration coverage or an authorized structural mapping. There are 0 unknown `\uses` targets and 29 separately known isolated declarations.
- Repair and directly recheck the six iter-008 proof bodies that no longer contain `sorry` but do not elaborate:
  - `0061`: rewrite point/readout hypotheses before changing the angle representation; normalize the final `9 - 0 = 9`.
  - `0303`: replace unknown `Real.pi_gt_d2`/`Real.pi_lt_d4` with verified Mathlib pi bounds.
  - `0333`: fix the malformed term at line 316.
  - `0346`: remove/restructure the redundant trailing tactic that runs after the goal is closed.
  - `0380`: remove or target the progress-demanding `simp` at line 275.
  - `0458`: establish common-pressure rewriting in the correct orientation and supply the missing nonzero/positive cancellation fact.
- Global physics review remains BLOCKED:
  - `PhyXMiniProblems/problem_phyx_mini_0206.lean` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”.
  - `PhyXMiniProblems/problem_phyx_mini_0472.lean` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”.
- Route `0206`/`0472` through an authorized structural Lean-writing lane, not an ordinary prover retry. Repair current evidence for the other 35 formalization-gate failures and refresh stale `0117`/`0629` reports before dispatch.

## Next proof wave

- Do not reassign the 26 certified iter-008 targets: `0014`, `0030`, `0035`, `0046`, `0060`, `0083`, `0085`, `0093`, `0157`, `0171`, `0200`, `0363`, `0367`, `0372`, `0373`, `0376`, `0408`, `0424`, `0471`, `0510`, `0523`, `0642`, `0748`, `0794`, `0843`, `0856`.
- Give the six broken no-`sorry` files an explicit repair list; a sorry-based target selector can otherwise lose them.
- After structural and repair routing, 909 other gate-passed open files remain. Select new targets only from that accepted set and retain the earlier decomposition rule for optics targets that already exhausted a monolithic pass.

## Reusable Lean details

- Dimensionful scalarization: rewrite `CarriesDimension.toDimensionful_apply_apply`, derive exact SI/readout equalities, and only then call `norm_num`/`nlinarith`.
- Rounded physics answers: derive an exact relation plus explicit sign/square/trig bounds, then use `round_eq_iff` or an answer tolerance. This worked for `0046`, `0083`, `0085`, and `0200`.
- Thermodynamic path comparisons: expand each work law and apply the first law to common endpoints; eliminate the shared internal-energy change (`0408`, `0471`).
- Direct `lake env lean <file>` is mandatory for these generated files. Root `lake build` can pass while standalone targets contain syntax errors, unknown constants, unsolved goals, or an extra tactic after closure.
- A file with no textual `sorry` is not necessarily proved. Require elaboration before adding target/proof `\leanok`.

## Doctor, markers, and controls

- Doctor structural findings are otherwise clean: 0 orphans, broken/malformed refs, axioms, and physics-grounding problems.
- Preserve the 84 manual marker additions/restorations from this review. Fix `sync_leanok` or register standalone generated modules before relying on its Lake-module verdict.
- Restore run-local `.archon/AGENTS.md` and `.archon/prompts/{plan,review}.md` from the known identical-SHA canonical copies through an authorized control-file route.
