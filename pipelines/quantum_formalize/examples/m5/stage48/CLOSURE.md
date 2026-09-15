# Root dependency closure collection

The root project is independent of all live component projects. Definition files are copied verbatim and recorded in IMPORT_PROVENANCE.json. Accepted assembly imports are promoted only after receipt, frozen-target, candidate/draft, payload, source and original compiled hash verification, including allowed axiom checks.

Some component projects package the same accepted declarations differently. For example, stage46's composite OrderCount dependency module expands polynomial indicator declarations which stage43 imports through canonical modules. Importing both composites would redeclare the same Lean names. The collector retains the stage43 canonical dependency module and verifies every theorem block in the expanded alternative occurs verbatim in the canonical source closure. This changes module packaging, not mathematical statements or proof bodies. Alternate source hashes and the correspondence are recorded.

The root-local M5PhysicalRecoveryDependencies is an adapter importing canonical accepted27/34/36/44 modules. The actual M5PhysicalRecovery definition file is unchanged. This avoids importing duplicate theorem definitions while retaining the exact same names/types needed by accepted recovery proofs. Fresh combined compilation and exact-type/axiom auditing remain required after promotion.

The pending residue-recovery dependency adapter imports the actual conditional-residue definitions and contributes no proofs. It is not an accepted42 receipt. When47's closure is ready, verify its accepted receipts, copy only missing verified modules, normalize any identical duplicate composites with recorded correspondence, and replace the definition-only adapter with actual accepted proof imports. Do not weaken a gate into an assumed theorem.

Before promoting46/47, compare their actual public definition files against the root snapshot. Any material definition change requires correspondence/type rechecking of the root; it must not silently change the public OriginalM5Spec meaning. Pure proof-module packaging changes are recorded and recompiled.
