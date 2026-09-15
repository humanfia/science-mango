import FrozenTarget_16dc87af495ac747
theorem M7.GlobalQuery.physical_presentation : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases hsep x hx
  classical
  rcases M7.GlobalQuery.same_class_presentation H N q bases x hx with ⟨g, hg, huniq⟩
  refine ⟨(x.1, g), hg, ?_⟩
  intro y hy
  have hclass : y.1 = x.1 := by
    unfold M7.GlobalQuery.separated at hsep
    first
    | exact hsep y x hy.2
    | exact hsep y.1 x.1 y.2 x.2 hy.2
    | exact hsep y.1 y.2 x.1 x.2 hy.2
  rcases y with ⟨j, h⟩
  change j = x.1 at hclass
  subst j
  exact congrArg (fun a : M7.Action.Record N => (x.1, a)) (huniq h hy)
