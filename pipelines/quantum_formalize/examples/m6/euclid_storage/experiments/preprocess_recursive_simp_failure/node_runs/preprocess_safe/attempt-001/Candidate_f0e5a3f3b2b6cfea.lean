import FrozenTarget_f0e5a3f3b2b6cfea
theorem M6.EuclidStorage.preprocess_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N a b M ha hb hM
  have rank_bound (p : M6.Euclid.BP) (hp : p.natDegree ≤ N) :
      M6.Euclid.rank p ≤ N + 1 := by
    unfold M6.Euclid.rank
    split <;> omega
  have ha' := rank_bound a ha
  have hb' := rank_bound b hb
  have hM' := rank_bound M hM
  have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
    simp [M6.Euclid.rank]
  have bounds (p q : M6.Euclid.BP)
      (hp : M6.Euclid.rank p ≤ N + 1)
      (hq : M6.Euclid.rank q ≤ N + 1) :
      (M6.Euclid.euclid p q).cancellations ≤ 2 * (N + 1) ∧
      (M6.Euclid.euclid p q).rounds ≤ N + 1 ∧
      (M6.Euclid.euclid p q).passes ≤ 9 * (N + 1) := by
    have h := M6.Euclid.euclid_correct p q
    have ht := M6.Euclid.euclid_passes p q
    omega
  have hfirst := bounds a b ha' hb'
  have hout : M6.Euclid.rank (M6.Euclid.euclid a b).value ≤ N + 1 := by
    have h := M6.Euclid.euclid_output_width (M6.Euclid.rank b + 1) a b
    have hm : max (M6.Euclid.rank a) (M6.Euclid.rank b) ≤ N + 1 :=
      max_le ha' hb'
    simpa only [M6.Euclid.euclid] using h.trans hm
  have hsecond := bounds (M6.Euclid.euclid a b).value M hout hM'
  have hr := M6.EuclidStorage.gcd_start_refines a b M 0 0 0
  have hs := hr.1
  have hv := congrArg (fun r : M6.Euclid.Run => r.value) hr.2.2
  have hc := congrArg (fun r : M6.Euclid.Run => r.cancellations) hr.2.2
  have he := congrArg (fun r : M6.Euclid.Run => r.rounds) hr.2.2
  have ht := congrArg (fun r : M6.Euclid.Run => r.passes) hr.2.2
  simp only [M6.EuclidStorage.toRun, M6.EuclidStorage.offset,
    Nat.zero_add, Nat.add_zero] at hv hc he ht
  unfold M6.EuclidStorage.preprocessSafe
  dsimp only
  simp only [hs, hv, hc, he, ht]
  repeat' first
    | assumption
    | apply And.intro
    | apply M6.EuclidStorage.gcd_start_safe
  all_goals simp only [hz, Nat.zero_add, Nat.add_zero]
  all_goals omega
