import FrozenTarget_ed29961d1794e6bf
theorem M7.QueryRebase.presentation_images : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves placed
  have himages (bs : M7.GlobalQuery.Family H N) :
      (∃ x : M7.GlobalQuery.Index H N,
        M7.GlobalQuery.present q bs x ∧ M7.GlobalQuery.realize bs x = placed) ↔
      (∃ x ∈ M7.GlobalQuery.winners q bs,
        M7.GlobalQuery.realize bs x = placed) := by
    constructor
    · rintro ⟨x, hx, hp⟩
      exact ⟨x, (M7.GlobalQuery.presentation_sound H N q bs x hx).1, hp⟩
    · rintro ⟨x, hx, hp⟩
      obtain ⟨g, ⟨hg, heq⟩, _⟩ :=
        M7.GlobalQuery.same_class_presentation H N q bs x hx
      refine ⟨(x.1, g), hg, ?_⟩
      change M7.Action.act g (bs x.1) = placed
      exact heq.trans hp
  exact (himages (M7.QueryRebase.rebase bases moves)).trans
    ((M7.QueryRebase.winner_images H N q bases moves placed).trans
      (himages bases).symm)
