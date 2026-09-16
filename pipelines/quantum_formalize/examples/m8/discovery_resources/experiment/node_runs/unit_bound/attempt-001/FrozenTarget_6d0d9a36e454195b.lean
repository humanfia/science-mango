import M8DiscoveryResources

theorem M8.DiscoveryResources.fold_charges : ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)), M8.DiscoveryResources.memberCharge A ≤ 4*N*(N+1) ∧ M8.DiscoveryResources.spanCharge A ≤ 16*N*(N+1)^2 := by
  change ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)), M8.DiscoveryResources.memberCharge A ≤ 4*N*(N+1) ∧ M8.DiscoveryResources.spanCharge A ≤ 16*N*(N+1)^2
  intro N inst A
  have hcard : A.card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ A
  constructor
  · calc
      M8.DiscoveryResources.memberCharge A = A.card * (4 * (N + 1)) := by
        simp [M8.DiscoveryResources.memberCharge]
      _ ≤ N * (4 * (N + 1)) := Nat.mul_le_mul_right _ hcard
      _ = 4 * N * (N + 1) := by ring
  · calc
      M8.DiscoveryResources.spanCharge A = A.card * (16 * (N + 1)^2) := by
        simp [M8.DiscoveryResources.spanCharge]
      _ ≤ N * (16 * (N + 1)^2) := Nat.mul_le_mul_right _ hcard
      _ = 16 * N * (N + 1)^2 := by ring

theorem M8.DiscoveryResources.leaf_bound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.DiscoveryResources.leafCharge c k ≤ 128*(N+1)^3 := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.DiscoveryResources.leafCharge c k ≤ 128 * (N + 1)^3
  intro N inst c k
  obtain ⟨hlm, hls⟩ := M8.DiscoveryResources.fold_charges N (M8.Anchor.left c k.exchange)
  obtain ⟨hrm, hrs⟩ := M8.DiscoveryResources.fold_charges N (M8.Anchor.right c k.exchange)
  have htotal :
      64 * (N + 1)^2 +
        (4 * N * (N + 1) +
          (4 * N * (N + 1) +
            (16 * N * (N + 1)^2 + 16 * N * (N + 1)^2))) ≤
        128 * (N + 1)^3 := by
    nlinarith [Nat.zero_le (N^2), Nat.zero_le (N^3)]
  unfold M8.DiscoveryResources.leafCharge
  split_ifs <;> omega

theorem M8.DiscoveryResources.right_bound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t a : Fin N), M8.DiscoveryResources.charged N (M8.DiscoveryResources.rightRun c e t a) ≤ 136*(N+1)^4 := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t a : Fin N), M8.DiscoveryResources.charged N (M8.DiscoveryResources.rightRun c e t a) ≤ 136 * (N + 1)^4
  intro N inst c e t a
  have h := M8.WeightedSearch.total_bound N (M8.Discovery.Choice N)
    (fun b : Fin N =>
      (if M8.Discovery.test c ⟨e,t,a,b⟩ then some ⟨e,t,a,b⟩ else none,
        M8.DiscoveryResources.leafCharge c ⟨e,t,a,b⟩))
    (128 * (N + 1)^3) (M8.DiscoveryResources.control N)
    (fun b => M8.DiscoveryResources.leaf_bound N c ⟨e,t,a,b⟩)
  calc
    M8.DiscoveryResources.charged N (M8.DiscoveryResources.rightRun c e t a)
        ≤ N * (M8.DiscoveryResources.control N + 128 * (N + 1)^3) := by
          simpa only [M8.DiscoveryResources.charged, M8.DiscoveryResources.rightRun,
            Nat.add_comm] using h
    _ ≤ 136 * (N + 1)^4 := by
      unfold M8.DiscoveryResources.control
      nlinarith [Nat.zero_le (N^2), Nat.zero_le (N^3), Nat.zero_le (N^4)]

theorem M8.DiscoveryResources.left_bound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t : Fin N), M8.DiscoveryResources.charged N (M8.DiscoveryResources.leftRun c e t) ≤ 144*(N+1)^5 := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t : Fin N), M8.DiscoveryResources.charged N (M8.DiscoveryResources.leftRun c e t) ≤ 144 * (N + 1)^5
  intro N inst c e t
  have h := M8.WeightedSearch.total_bound N (M8.Discovery.Choice N)
    (fun a : Fin N =>
      let r := M8.DiscoveryResources.rightRun c e t a
      (r.selected.map Prod.snd, M8.DiscoveryResources.charged N r))
    (136 * (N + 1)^4) (M8.DiscoveryResources.control N)
    (fun a => M8.DiscoveryResources.right_bound N c e t a)
  calc
    M8.DiscoveryResources.charged N (M8.DiscoveryResources.leftRun c e t)
        ≤ N * (M8.DiscoveryResources.control N + 136 * (N + 1)^4) := by
          simpa only [M8.DiscoveryResources.charged, M8.DiscoveryResources.leftRun,
            Nat.add_comm] using h
    _ ≤ 144 * (N + 1)^5 := by
      unfold M8.DiscoveryResources.control
      nlinarith [Nat.zero_le (N^2), Nat.zero_le (N^3), Nat.zero_le (N^4), Nat.zero_le (N^5)]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ e : Bool, M8.DiscoveryResources.charged N (M8.DiscoveryResources.unitRun c e) ≤ 152*(N+1)^6
