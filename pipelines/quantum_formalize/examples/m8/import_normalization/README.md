The read-only audit verified that `M6FinalDependencies` supplies all 105 theorems needed by the complete `M6ActualCSSAccepted` closure with exactly identical declaration types and proof bodies. All 13 definition source files are byte-identical. The remaining `M6ActualCSS` module contains imports only and introduces no definitions. Fourteen canonical batches and the original receipt/candidate/target provenance were checked. See `CSS_SUPERSET_AUDIT.json`.

The physical bridge carries a later superset of the original M6 final dependency file: its import header changed and additional accepted declarations were appended. The helper checks that all 225 declarations from the original recorded promotion remain identical, then checks each of the 105 required declarations against its exact accepted receipt and portable declaration. It does not infer equivalence from theorem names.

For a new child, first promote the physical bridge and diagonal/polynomial parents normally. Before freezing any proof environment, run:

```python
from pathlib import Path
import runpy
helper = runpy.run_path(str(repo / 'pipelines/quantum_formalize/examples/m8/import_normalization/css_superset.py'))
helper['normalize_child'](repo, project, stage / 'lean', stage / 'CSS_IMPORT_NORMALIZATION.json')
```

This rechecks all sources and replaces only the new child's `M6ActualCSSAccepted.lean` with `import M6FinalDependencies`. It preserves the original source hash in the report. No canonical parent or frozen proof source is edited. The child must then pass its ordinary full build, exact target preflight and harness acceptance. The helper refuses missing or differing definitions/types/proof bodies, mismatched child superset sources, or an already frozen child environment.

To repeat the read-only audit alone, call `helper['audit'](repo)`. No model worker or additional mathematical acceptance gate is introduced.
