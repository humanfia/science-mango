import M8WholeResourcesAccepted
import M8BankLayoutAccepted
import M8TaggedStoreAccepted

namespace M8.SequentialResources
noncomputable def slots (N : ℕ) : ℕ := M8.BankLayout.payloadSlots N
noncomputable def addressBits (N : ℕ) : ℕ := (slots N).size
/-- Substitute the real allocated size/width into the proved concrete scan bound. -/
noncomputable def accessCharge (N : ℕ) : ℕ :=
  slots N * (4*(addressBits N+1)) + 1
/-- Actual indexed-bit upper charges are simulated one primitive at a time.
This accumulates the proved sequential scan allowance, not an n^12 formula. -/
def repeatCharge (unit : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => repeatCharge unit k + unit
def prefixCharge (unit : ℕ) (segments : List ℕ) : ℕ :=
  segments.foldl (fun total k => total + repeatCharge unit k) 0
/-- Build each actual binary address tag and its record, with standard binary
increment, delimiter/copy and cursor-control allowances per visited address. -/
noncomputable def tagSetupCharge (N : ℕ) : ℕ :=
  (List.range (slots N)).foldl
    (fun total i => total + 16*((M8.TaggedStore.address i).length+1)) 0 + 32
/-- Two addresses, a buffered record tag and scan-position counter, plus flags. -/
noncomputable def scratchSlots (N : ℕ) : ℕ := 4*(addressBits N+1)+32
noncomputable def storeSpace (N : ℕ) (mem : List Bool) : ℕ :=
  (M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom 0 mem)).length + scratchSlots N
noncomputable def sequentialCharge {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ℕ :=
  tagSetupCharge N + prefixCharge (accessCharge N) (M8.WholeResources.run c).charges
end M8.SequentialResources
