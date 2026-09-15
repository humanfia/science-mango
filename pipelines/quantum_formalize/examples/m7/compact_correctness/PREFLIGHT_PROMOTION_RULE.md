# Unimported preflight modules

The promotion controller still verifies every canonical manifest entry and every promoted source against its frozen environment. When combining parents, `GraphPreflight.lean` and `Preflight.lean` may have the same filename but different lists of closed target-type checks. They are not mathematical dependency modules.

A preflight file is omitted from child imports only after its frozen hash has been checked and the controller has checked that no frozen source or AcceptedExperiment imports that module. If such an import exists, promotion stops. Each omission, original hash and reason is recorded in IMPORT_PROVENANCE. All actual definition and accepted-proof source collisions still stop promotion. Parent archives and proofs remain unchanged; the child always runs a fresh full build and its own exact closed target-type preflight.
