import M8WholeResourcesAccepted
import M8SequentialStoreAccepted
namespace M8.SequentialResources
/-- A standard indexed-bit primitive has bounded fan-in/out: two reads, one
write, and finite cursor/control steps. Eight scan-plus-control allowances
cover this fixed primitive alphabet; no gate-level extraction is required. -/
noncomputable def primitiveCharge (N : ℕ) : ℕ :=
  8*(M8.SequentialStore.accessCharge N+1)
noncomputable def sequentialCharge {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ℕ :=
  M8.SequentialStore.tagSetupCharge N +
    M8.SequentialStore.prefixCharge (primitiveCharge N) (M8.WholeResources.run c).charges
end M8.SequentialResources
