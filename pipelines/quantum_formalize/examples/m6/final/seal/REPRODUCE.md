# Reproduce the complete theorem

Use the pinned Lean toolchain and Mathlib revision in `lean/`. From that directory, run `lake build`; its default target is `M6OriginalAccepted`. The source module contains the three final declarations including `M6.Final.original_m6`. `M6FinalClaims.lean` exposes its full proposition, and `M6FinalDependencies.lean` preserves the exact accepted component proofs.

The supplied Mathlib cache can be restored with `lake exe cache get` before building. No model or retrieval service is needed to check the exported proofs. The proof-generation DAG and receipts remain in the parent directories. `LEAN_SOURCE_MANIFEST.json` hashes every exported file; the dedicated root receipt and independent audit record exact-target and standard-axiom verification.
