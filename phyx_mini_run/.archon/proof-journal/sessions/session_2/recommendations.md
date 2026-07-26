# Recommendations — iter-003 plan

## 1. Restore the 170 missing retry reports before proof work

Generate a genuine post-formalization report for each target below. Each report must describe the revised statement, not the generic preflight, and must include actual LeanExplore queries/candidates, names adopted, local abstractions, grounding gaps, and a governing-law/data/current-target split.

0001, 0002, 0005, 0006, 0009, 0010, 0014, 0018, 0019, 0021, 0024, 0027, 0029, 0030, 0031, 0032, 0033, 0034, 0035, 0036, 0038, 0039, 0041, 0043, 0044, 0050, 0052, 0053, 0055, 0061, 0064, 0083, 0090, 0093, 0098, 0101, 0102, 0118, 0120, 0126, 0129, 0130, 0131, 0136, 0138, 0151, 0152, 0157, 0161, 0168, 0170, 0176, 0177, 0178, 0181, 0182, 0184, 0186, 0194, 0196, 0201, 0205, 0213, 0217, 0222, 0223, 0231, 0234, 0242, 0245, 0246, 0255, 0263, 0278, 0279, 0281, 0282, 0284, 0287, 0292, 0296, 0313, 0315, 0326, 0336, 0340, 0342, 0351, 0362, 0372, 0374, 0377, 0385, 0402, 0403, 0413, 0426, 0438, 0440, 0442, 0451, 0468, 0471, 0474, 0475, 0481, 0486, 0500, 0504, 0519, 0529, 0533, 0535, 0541, 0543, 0549, 0552, 0554, 0561, 0569, 0595, 0598, 0600, 0605, 0615, 0616, 0619, 0629, 0632, 0647, 0679, 0688, 0693, 0699, 0707, 0712, 0731, 0740, 0749, 0762, 0765, 0766, 0768, 0791, 0792, 0793, 0801, 0802, 0829, 0836, 0847, 0854, 0862, 0871, 0877, 0878, 0882, 0885, 0890, 0906, 0907, 0911, 0922, 0924, 0937, 0939, 0945, 0976, 0984, 0989.

For 0629, a report alone is insufficient: replace the unsupported exact `0.006 A` conclusion with the symbolic Shockley/Ohm characterization, or add genuinely sourced input voltage and resistance data.

## 2. Clear all nine deterministic doctor blockers

Repair the direct Mathlib import/grounding path and rerun the doctor for these exact blocking entries:

> `0165` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0197` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0384` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0418` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0519` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0541` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0547` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0627` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

> `0776` — `missing-mathlib-import`: “physics target does not import Mathlib; autoformalization must be checked in a real Lake/Mathlib environment, not as a standalone Lean smoke file”

Targets 0519 and 0541 also need genuine post-formalization reports.

## 3. Redraft the 40 report-bearing semantic failures

- Replace exact global approximation laws with honest local contracts in 0075, 0078, 0115, 0137, 0227, 0478, and 0596. Use `HasDerivAt`/`HasFDerivAt`, a limit or neighborhood, or a finite remainder/error bound tied to the operating point.
- Correct non-derivable, ambiguous, or disconnected targets in 0117, 0206, 0325, 0441, 0513, 0786, 0790, 0941, 0954, and 0980. In particular, do not attach the 0954 sigma threshold to the apparatus until sigma is physically defined and connected to energy/trajectory equations.
- Supply traceable empirical data or weaken the target to a symbolic theorem in 0135, 0150, 0158, 0195, 0308, 0330, 0331, 0388, 0435, 0439, 0455, 0462, 0463, 0465, 0466, 0467, 0472, 0483, 0488, 0498, 0514, 0611, and 0663. A premise named `Calibration`, `Previous...`, or `Uses...` is not evidence when the source/table/previous-part link is absent.
- Preserve the accepted corrections: 0016 = B/about 27.5 degrees; 0104 = `E2/E1` and about 0.44818; 0346 = A/about 28 C; 0983 has one `b`; 0990 remains symbolic.

Do not retry proofs on any failed target until its statement and report pass review. The current review is attempt 2 of the configured three-review ceiling.

## 4. Keep proof and formalization progress separate

- All 1,000 files still contain `sorry` (2,247 occurrences), so no theorem should be presented as proved.
- After statement repair, re-run `lake env lean <file>` directly; the root build does not substitute for independent target elaboration.
- Reuse the accepted approximation patterns already present in this corpus: derivative plus finite remainder, exact finite geometry, `Tendsto`, `IsLittleO`, and explicit error budgets. Do not reintroduce selector-only `paraxial`, `smallAngle`, or `lowSpeed` exact equalities.

## 5. Repair blueprint coverage and local review infrastructure

- The working venv CLI reports 31,067 unmatched declarations, `frontier = 1000`, and `gaps = 0`. Add declaration-specific links for the stabilized 527 retry targets, then map their supporting laws/helpers rather than leaving them as chapterless `lean_aux` nodes.
- Restore `.archon/AGENTS.md` and `.archon/prompts/review.md` from the known identical canonical copies. Put the venv `archon` executable on the loop's `PATH` so future agents can query the DAG without manual discovery.
- Leave `\leanok` absent while every target is sorry-bodied; iter-002 sync was current and no manual override was warranted.
