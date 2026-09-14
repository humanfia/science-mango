# Third-Party Notices

This project is licensed under Apache License 2.0. Some bundled components are derived from third-party projects under the MIT License.

## 1) lean4-skills (modified fork)

- Upstream: https://github.com/cameronfreer/lean4-skills
- License: MIT License
- Copyright: Copyright (c) 2025 Lean 4 Theorem Proving Skill Contributors
- Local path in this repository: `.claude/skills/lean4/`
- Local license file: `.claude/skills/lean4/LICENSE`
- Notes: This repository contains a modified fork.

## 2) lean-lsp-mcp (modified fork)

- Upstream: https://github.com/oOo0oOo/lean-lsp-mcp
- License: MIT License
- Copyright: Copyright (c) 2025 Oliver Dressler
- Local path in this repository: `.claude/tools/lean-lsp-mcp/`
- Local license file: `.claude/tools/lean-lsp-mcp/LICENSE`
- Notes: This repository contains a modified fork.

## MIT License Requirement Reminder

For MIT-licensed portions, the above copyright notice and permission notice must be included in all copies or substantial portions of those portions.

## Quantum research harness provenance

`pipelines/quantum_humanize` is imported from the quantum-code research adapter
in https://github.com/ShuxiangCao/quantum_code_discovery_proof. It derives from
`pipelines/fput_humanize` in https://github.com/menik1126/fput-thermalization at
commit `4c9cb5b86f8d91359824542a66904ebcfdfcbabb`. The separately installed
`humanfia/humanize2` runtime is pinned to
`48d1559805cbdb083958bf381a2ff57c183f96ab`; its source is not vendored here.
Exact imported file hashes and the portable launcher adjustment are recorded in
`pipelines/quantum_humanize/SOURCE_MANIFEST.json`.
