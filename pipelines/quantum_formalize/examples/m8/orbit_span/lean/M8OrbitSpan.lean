import M8AnchorAccepted

namespace M8.OrbitSpan
/-- Analysis-only finite set, not materialized by the discovery algorithm. -/
noncomputable def spans {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun g : M7.Action.Record N => M8.Anchor.Anchored (M7.Action.act g c))).image
    (fun g => M8.Anchor.span (M7.Action.act g c))
noncomputable def value {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ℕ :=
  if h : (spans c).Nonempty then (spans c).min' h else 0
end M8.OrbitSpan
