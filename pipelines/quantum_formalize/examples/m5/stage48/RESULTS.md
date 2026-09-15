# Original M5 root accepted

The fixed theorem `M5.Final.original_m5` is accepted with exactly the original positive-weight assumptions: `0 < w`, `F.Monic` and `F.coeff 0 = 1`. It proves the unchanged `M5.Final.OriginalM5Spec w F` using actual arithmetic definitions and actual recovery procedures.

All four Core nodes and all three final nodes passed on their first attempts. Both experiments passed combined assembly and unchanged-environment checks. The final root was promoted into `M5OriginalRootAccepted` and rebuilt (3,103 jobs). A separate `RootAcceptance.lean` checks the exact public type. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`.

The original source hash and all 14 frozen primary definition hashes match. Actual stage46/47 recovery proofs were verified and imported; no original obligations or proof gates remain. The root includes finite period search, exact order counting, global occurrence, bounded progression, least birth, later-order exceptions, normalization, the weight-one boundary, and both concrete arithmetic recovery procedures.

`ROOT_ACCEPTANCE.json` is the dedicated final result. Historical receipts retain the scheduler constant `m5_formalized=false`; it does not reject the independently accepted exact root. No runtime/codegen, distance, sorting or stronger target was added.
