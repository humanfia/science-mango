# Session 1 Summary

## Metadata

- Iteration/session: `iter-001` / `session_1`; stage `autoformalize`; runner `codex` (model ID was not recorded).
- Scope: 1,000 physics targets. The run created 1,000 Lean files containing 2,233 textual `sorry` occurrences; no target proof is complete.
- The preprocessed attempt journal was read first and in full: 47,967 events plus its summary, including 2,523 Edit events, 15,724 shell events, 1,178 LSP-diagnostic events, and 8,235 LeanExplore searches. It contains no goal-state events and erases Edit paths/bodies, so statement review used the resulting Lean sources, task reports, original lane logs, blueprints, and source excerpts.
- Formalization gate: **473 passed / 527 failed**. Passed targets are `partial` because their proofs remain sorry-bodied; failed targets are `blocked`. The authoritative per-target verdict and evidence are in `milestones.jsonl`.

## Gate accounting

The 527 failures use disjoint primary reasons:

- 237 have live `blueprint-doctor` physics-modeling blockers.
- 162 are doctor-clean but lack a genuine post-formalization, actual-used grounding report.
- 128 are doctor-clean and have grounding evidence, but fail independent source/figure/units/laws/statement review. Of these, 36 globalize a local approximation as an exact equality; the other 92 have target-specific source, data, governing-law, dimensional, or answer-selection defects recorded verbatim in the ledger.

There are 220 targets without a genuine post-formalization report in total; 58 already fail under the doctor category, leaving the 162 additional missing-evidence failures above. Generic `physics-grounding-*` preflight files predate the Lean model and cannot establish which candidates or local abstractions were actually used.

## Attempts, grounding, and compilation

- Genuine post-formalization reports cover 780 distinct targets (81 `problem_phyx_mini_NNNN.lean.md` names and 699 `PhyXMiniProblems_problem_phyx_mini_NNNN[.lean].md` names). All 780 contain a LeanExplore section and a local-abstractions section, with queries/candidates used, grounded names, introduced abstractions, gaps, and source/model notes. Heading wording varies, so exact-filename or exact-heading counting substantially undercounts them.
- An independent sweep ran `lake env lean` on every target file: **1,000 passed, 0 failed**. Compilation verifies elaboration only; every file still has at least one `sorry`, and compilation does not override a semantic or grounding failure.
- The anti-escape/anti-fake sweep found no target theorem replaced by `True`, `exists _, True`, a reflexive equality, `axiom`, `admit`, or `native_decide`. Independent statement review nevertheless found substantive modeling failures.
- No dedicated `physics-reviewer` report exists because that subagent is disabled. The required physics checklist was applied directly.

## Independent physics review

The 36 doctor-clean globalized-approximation blockers are: `0040`, `0041`, `0055`, `0110`, `0121`, `0122`, `0175`, `0203`, `0229`, `0232`, `0234`, `0238`, `0248`, `0249`, `0262`, `0263`, `0264`, `0265`, `0266`, `0270`, `0274`, `0276`, `0308`, `0507`, `0520`, `0533`, `0557`, `0615`, `0623`, `0655`, `0719`, `0911`, `0967`, `0971`, `0975`, `0978`. Their statements encode first-order, paraxial, small-angle, low-speed, far-field, or similar approximations as global exact equalities without a derivative, limit, neighborhood, asymptotic relation, or remainder/error contract. Targets `0137` and `0596`, already blocked primarily for missing report and doctor findings respectively, have the same secondary defect.

Representative non-approximation failures include:

- `0104`: the source uses the `E1/E2` eccentricity ratio, while the Lean setup reverses it; the exact value at `n = 1.62` also does not round to the printed `0.449`.
- `0346`: the encoded heat bars and `Cp - Cv = R` imply approximately `28 C`, but the theorem targets `20 C`.
- `0463`: an exact steam-table value is uncited/unverified and tightly determines the requested numerical answer.
- `0697`: the source does not choose a point on the rotating rod; the model selects the endpoint because it produces the answer choice.
- `0983`: the conclusion has an extra factor of `b`, inconsistent with the encoded Maxwell/Faraday laws and dimensions.
- `0990`: the source asks for inductance but supplies ohm-valued choices and no numerical data; the Lean theorem changes this to a symbolic-only result.

Positive controls confirm that the gate did not reject approximations mechanically: `0267` uses `HasDerivAt`, `0268`/`0269` use explicit neighborhoods, `0546` uses a limit contract, `0658` connects the claim to `deriv`, and `0997` uses `IsLittleO`. Target `0525` now states an exact longitudinal-reflector law and was not assigned the earlier approximation defect.

## Blueprint doctor

- Structural results: 1,001/1,001 chapters included; 0 orphan chapters, broken references, malformed references, new axioms, or cover problems. `physics_grounding_problems` is empty.
- Live `physics_modeling_problems` contain 237 blockers, which therefore cannot receive a passing review.
- `missing-physlib-import` (38), reason: “physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions”: `0006`, `0007`, `0008`, `0009`, `0014`, `0016`, `0017`, `0019`, `0021`, `0024`, `0036`, `0037`, `0050`, `0060`, `0061`, `0068`, `0069`, `0073`, `0074`, `0091`, `0093`, `0096`, `0097`, `0098`, `0099`, `0100`, `0103`, `0142`, `0143`, `0146`, `0147`, `0164`, `0502`, `0541`, `0542`, `0574`, `0791`, `0792`.
- `missing-mathlib-import` (199), reason: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”: `0027`, `0029`, `0031`, `0032`, `0033`, `0034`, `0035`, `0038`, `0039`, `0042`, `0043`, `0044`, `0045`, `0052`, `0053`, `0054`, `0056`, `0057`, `0058`, `0059`, `0064`, `0065`, `0066`, `0067`, `0076`, `0077`, `0078`, `0092`, `0108`, `0109`, `0111`, `0112`, `0116`, `0118`, `0119`, `0123`, `0129`, `0130`, `0133`, `0134`, `0136`, `0139`, `0140`, `0144`, `0148`, `0149`, `0151`, `0152`, `0157`, `0159`, `0161`, `0165`, `0166`, `0167`, `0171`, `0176`, `0177`, `0178`, `0179`, `0181`, `0182`, `0183`, `0184`, `0185`, `0190`, `0193`, `0194`, `0195`, `0196`, `0197`, `0199`, `0200`, `0201`, `0204`, `0207`, `0210`, `0211`, `0213`, `0214`, `0215`, `0217`, `0222`, `0223`, `0224`, `0226`, `0231`, `0239`, `0242`, `0244`, `0245`, `0247`, `0250`, `0257`, `0258`, `0259`, `0271`, `0275`, `0279`, `0280`, `0282`, `0286`, `0291`, `0306`, `0310`, `0314`, `0318`, `0319`, `0320`, `0327`, `0328`, `0332`, `0337`, `0339`, `0340`, `0344`, `0349`, `0352`, `0358`, `0373`, `0376`, `0384`, `0386`, `0391`, `0402`, `0403`, `0404`, `0405`, `0408`, `0409`, `0412`, `0413`, `0418`, `0419`, `0421`, `0442`, `0448`, `0470`, `0471`, `0474`, `0475`, `0477`, `0494`, `0504`, `0509`, `0510`, `0512`, `0513`, `0515`, `0519`, `0523`, `0525`, `0527`, `0528`, `0529`, `0547`, `0552`, `0559`, `0572`, `0577`, `0586`, `0591`, `0592`, `0596`, `0599`, `0604`, `0607`, `0619`, `0627`, `0639`, `0649`, `0664`, `0723`, `0732`, `0749`, `0761`, `0776`, `0780`, `0787`, `0795`, `0801`, `0802`, `0810`, `0813`, `0814`, `0819`, `0821`, `0826`, `0830`, `0840`, `0846`, `0848`, `0852`, `0872`, `0878`, `0919`, `0923`, `0937`, `0979`, `0999`.

## Blueprint, DAG, and marker status

- `sync_leanok-state.json` is current for iteration 001 and changed no chapters. All 1,000 physics chapters contain no `\lean{...}`, `\leanok`, `\mathlibok`, or `\notready`; no manual marker override was made.
- `archon dag-query unmatched --json` returned the complete set of 31,436 unmatched `lean_aux` nodes, all with `chapter=""` and `dep_count=0`. This is systemic blueprint-to-Lean linkage debt, not an isolated helper list.
- Run-local `.archon/AGENTS.md` and `.archon/prompts/review.md` are missing. Identical-SHA canonical copies from the same-project archive/template supplied the review rules; restore the local control files before iteration 002.

## Blueprint markers updated (manual)

- None.
