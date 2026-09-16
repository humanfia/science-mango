import M8Cutoff

def M8.CutoffTarget.limit_bounds : Prop :=
  ∀ N : ℕ, M8.Cutoff.limit N ≤ N-1 ∧ M8.Cutoff.limit N ≤ Nat.log 2 (N+1) ∧ (0 < N → M8.Cutoff.limit N < N)

def M8.CutoffTarget.bit_length_limit : Prop :=
  ∀ N : ℕ, M8.Cutoff.limit N = min (N-1) (Nat.log2 (N+1))

def M8.CutoffTarget.state_bound : Prop :=
  ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2^R ≤ N+1

def M8.CutoffTarget.state_square : Prop :=
  ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 4^R ≤ (N+1)^2

def M8.CutoffTarget.indexed_work_envelopes : Prop :=
  ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N^3 * 4^R ≤ (N+1)^5 ∧ N^4 * 4^R ≤ (N+1)^6

def M8.CutoffTarget.indexed_storage_envelope : Prop :=
  ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N^2 * 2^R ≤ (N+1)^3

def M8.CutoffTarget.coefficient_capacity : Prop :=
  ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2^R * 8^N < 2^(4*(N+1))

def M8.CutoffTarget.anchor_trial_envelope : Prop :=
  ∀ (N a b : ℕ), a ≤ N → b ≤ N → 2*N*a*b ≤ 2*N^3

