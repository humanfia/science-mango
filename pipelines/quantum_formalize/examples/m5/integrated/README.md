# Integrated M5 Lean checkpoints

The current checkpoint composes the 52 accepted results of stages 1–9 in one Lean environment. Thirteen declarations are imported from byte-preserved, receipt-verified modules; 39 are declared in `M5Accepted.lean`. No proof or definition is changed. See [validation](VALIDATION.json), [provenance](PROVENANCE.json), and [Lean source](lean/M5Accepted.lean).

The earlier [checkpoint 41](checkpoint41/VALIDATION.json) is frozen independently, retaining its original 41 statements, source, import audit and provenance.

Both checkpoints verify original payload digests, frozen target and candidate source hashes, exact compiled proof drafts, surviving original object hashes, and promoted proof bodies. Global compilation and a separate exact-type import audit check composition and axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. This is a component integration checkpoint, not a claim of full M5 formalization. The noncomputable period definition still requires a separate executable algorithm refinement.

To compile a portable copy of `lean/`, install the pinned Lean toolchain, resolve the pinned Mathlib dependency using Lake, and run `lake build M5Accepted` followed by `lake env lean Acceptance.lean`. The assembly/provenance scripts additionally use this workspace's accepted archives and shared Mathlib cache; their original object-file verification is conditional on those historical files still being available.
