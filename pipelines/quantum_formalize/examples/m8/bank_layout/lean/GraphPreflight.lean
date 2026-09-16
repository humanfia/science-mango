import M8BankLayout
def M8.BankTarget.workspace_monotone : Prop := ∀ R S N slots : ℕ, R ≤ S → M6.Transfer.solveStorage R N slots ≤ M6.Transfer.solveStorage S N slots
def M8.BankTarget.payload_bound : Prop := ∀ (N : ℕ) [NeZero N], M8.BankLayout.payloadSlots N ≤ 20000*(N+1)^3
def M8.BankTarget.actual_workspace_fits : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualSolveStorage N a b ≤ M8.BankLayout.bankSlots N
def M8.BankTarget.address_bits_bound : Prop := ∀ (N : ℕ) [NeZero N], (M8.BankLayout.payloadSlots N).size ≤ 32*(N+1)
