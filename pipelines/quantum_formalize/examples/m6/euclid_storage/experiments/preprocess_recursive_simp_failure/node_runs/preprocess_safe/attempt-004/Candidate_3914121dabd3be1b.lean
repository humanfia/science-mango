import FrozenTarget_3914121dabd3be1b
theorem M6.EuclidStorage.preprocess_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N a b M ha hb hM
  have hwidth : 0 < N + 1 := by omega
  have rank_bound (p : M6.Euclid.BP) (hp : p.natDegree ≤ N) :
      M6.Euclid.rank p ≤ N + 1 := by
    unfold M6.Euclid.rank
    split <;> omega
  have hra := rank_bound a ha
  have hrb := rank_bound b hb
  have hrM := rank_bound M hM
  have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
    simp [M6.Euclid.rank]
  have bounds (p q : M6.Euclid.BP)
      (hp : M6.Euclid.rank p ≤ N + 1)
      (hq : M6.Euclid.rank q ≤ N + 1) :
      (M6.Euclid.euclid p q).cancellations ≤ 2 * (N + 1) ∧
      (M6.Euclid.euclid p q).rounds ≤ N + 1 ∧
      (M6.Euclid.euclid p q).passes ≤ 9 * (N + 1) := by
    have hc := (M6.Euclid.euclid_correct p q).2.1
    have he := (M6.Euclid.euclid_correct p q).2.2
    have ht := M6.Euclid.euclid_passes p q
    constructor
    · omega
    constructor <;> omega
  rcases bounds a b hra hrb with ⟨hc₁, he₁, ht₁⟩
  have hout : M6.Euclid.rank (M6.Euclid.euclid a b).value ≤ N + 1 := by
    have h := M6.Euclid.euclid_output_width (M6.Euclid.rank b + 1) a b
    have hm : max (M6.Euclid.rank a) (M6.Euclid.rank b) ≤ N + 1 :=
      max_le hra hrb
    simpa [M6.Euclid.euclid] using le_trans h hm
  rcases bounds (M6.Euclid.euclid a b).value M hout hrM with ⟨hc₂, he₂, ht₂⟩
  rcases M6.EuclidStorage.gcd_start_refines a b M 0 0 0 with
    ⟨hsaved, hwork, href⟩
  have hv := congrArg (fun r : M6.Euclid.Run => r.value) href
  have hc := congrArg (fun r : M6.Euclid.Run => r.cancellations) href
  have he := congrArg (fun r : M6.Euclid.Run => r.rounds) href
  have ht := congrArg (fun r : M6.Euclid.Run => r.passes) href
  simp only [M6.EuclidStorage.toRun, M6.EuclidStorage.offset,
    Nat.zero_add, Nat.add_zero] at hv hc he ht
  unfold M6.EuclidStorage.preprocessSafe
  dsimp only
  simp only [hsaved, hwork, hv, hc, he, ht]
  repeat' first
    | assumption
    | apply And.intro
    | apply M6.EuclidStorage.gcd_start_safe
  all_goals
    simp only [M6.EuclidStorage.slotsFit, hsaved, hwork, hv, hc, he, ht,
      hz, Nat.zero_add, Nat.add_zero] at *
  all_goals first | assumption | rfl | omega
