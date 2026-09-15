# Definition imports for the deduplicated root

The owned definition bodies do not reference accepted pipeline theorems. Their current broad imports are convenient project dependencies, not extra logical assumptions in the definitions. In a separate root packaging project, retain each body verbatim and replace only import lines according to `DEFINITION_IMPORT_AUDIT.json`; verify the body hash after doing so. Do not rewrite the frozen source files themselves.

Direct accepted imports to remove from the owned definitions:

- `M6TransferPartialResources`: remove CoefficientsAccepted and ResourcesAccepted; Scatter supplies all names used by arrayMass/eventMass.
- `M6TransferActualResources`: remove ResourcesAccepted; Scatter already imports the Resources definitions.
- `M6QueryResources`: replace ActualResourcesAccepted with ActualResources.
- `M6Postprocessing`: remove NormalizeAccepted; its definitions use ActualTransfer trace/Q interfaces only.
- `M6SolveResources`: remove PinnedAccepted; retain ActualTransfer, QueryResources and Euclid definitions.
- `M6SolveStorage`: replace QueryResourcesAccepted with QueryResources; retain ActualTransfer and EuclidStorage.
- `M6RecoveryLayout`: replace QueryResourcesAccepted with QueryResources; its allocation definition uses no theorem.

`M6TransferFactorBounds`, `M6WeightResources`, `M6PostSafety` and the Ready modules are import-only wrappers. They introduce no mathematical definitions and can be omitted when canonical proof payloads are deduplicated. The other primary resource modules import only definition modules already.

The external ActualTransfer/Euclid/EuclidStorage definition imports need their owners' corresponding audit. This resource audit does not claim that external modules have no local proof obligations. The canonical resource payload sources and acceptance receipts are enumerated in ACCEPTED_CLOSURES.json.
