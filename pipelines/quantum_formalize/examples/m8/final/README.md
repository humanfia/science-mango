# Original M8 root closure

Root acceptance is pending. A successful component or natural-language review is not the complete Lean result.

The [original main claim](PRIMARY_CLAIM.json) fixes the completion scope. The gated [preparer](prepare.py) copies exact accepted, frozen statements into seven explicit groups: algorithm outcomes, physical parameters, sequential time, sequential storage, measured-program projection, admitted families and excluded families. The eighth target is their closed conjunction, `M8.Final.original_m8`. No correctness proposition becomes an input to this theorem.

The root includes the original time exponent 12 and space exponent 4. Sharper intermediate discovery estimates are optional follow-ups, not additional completion requirements. Physical witnesses, all even orders and repeated-factor multiplicities remain included. The mixed family retains the separate actual cycle-space nonproduct conclusion. Unrestricted all-input M9 and machine-code extraction are outside the accepted M8 claim.

[The audit](audit_root.py) checks original natural-language source hashes, the root statement composition, canonical batch manifests, exact frozen target compilation, accepted draft transport, source and payload hashes, and printed axioms. It writes `ROOT_ACCEPTANCE.json` only after all evidence checks pass. Until then it reports pending without writing acceptance.

From the repository root, using the harness Python environment:

```sh
python pipelines/quantum_formalize/examples/m8/final/audit_root.py --check-only
```

After root acceptance, a fresh Lean rebuild can be requested in a new directory:

```sh
python pipelines/quantum_formalize/examples/m8/final/replay_lean.py --project /tmp/m8-root-replay --cache
```

The rebuild checks the recorded evidence first, copies the pinned source closure to a fresh project, builds the accepted proof, and asks Lean for the root's exact type and axioms. It does not invoke a proof model. The original canonical experiment remains the acceptance evidence; this optional rebuild is a reproduction aid.
