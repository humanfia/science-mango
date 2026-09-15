# Final resource composition acceptance

All six exact targets passed combined compilation, axiom/payload/target checks and unchanged-environment checks. The canonical receipt is `experiment/result.json`. This component does not establish the full M7 root.

Five targets passed their first live attempts. `generation` exhausted five attempts due to tactic syntax/argument mismatches; an isolated exact verification then accepted the local `GeneratedFamily.size` unfold and canonical `generate_card`/`generate_count` composition. Definitions and targets were unchanged. All six proof drafts subsequently passed normal replay and full batch acceptance. The original five failed attempts and successful live proofs are preserved under `experiments/replay_history`; the exact repair and receipt are under `repairs/generation`. Replay attempt counts do not replace original attempt history.
