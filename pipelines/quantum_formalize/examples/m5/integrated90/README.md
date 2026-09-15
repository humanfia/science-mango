# M5 checkpoint: 90 accepted lemmas

This checkpoint integrates the exact accepted declarations from stages 1–15, 17, and 18: the immutable 72-lemma checkpoint plus 18 lemmas about subset characters, tuple characters, finite exclusion, and residual-factor products. It does not mark the complete M5 theorem as formalized. Stage19 and subsequent experiments are deliberately outside this fixed checkpoint.

`build_checkpoint.py` verifies every archived accepted receipt, payload hash, frozen target, candidate source, exact tactic draft and portable declaration. It also verifies the full immutable72 manifest and preserves every source module there byte for byte. The only new import reconciliation is `M5BinaryDivisibility.lean`: stage18's two promoted proofs are verified identical to the already accepted declarations in checkpoint72, so the module forwards an import instead of redeclaring them. No theorem statement or mathematical proof is changed.

`M5Checkpoint90.lean` imports the preserved earlier modules and adds the 18 accepted declarations. `validate_checkpoint.py` compiles the combined module, independently imports each of the 90 exact original statements, and audits every theorem's axioms against the allowed set `propext`, `Classical.choice`, and `Quot.sound`. See `VALIDATION.json`, `PROVENANCE.json`, and the compiler logs. Counts alone do not constitute integration acceptance.

The isolated project is `/home/jing/m5-lean-integrated90-formalization`; older projects remain unchanged. To rebuild the portable Lean sources with the pinned toolchain and Mathlib revision, run `lake build M5Checkpoint90`, followed by `lake env lean Acceptance.lean` in `lean/`. The Python reconstruction and audit scripts use the documented workspace paths.
