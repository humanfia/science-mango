import FrozenTarget_6b0a8cf7895ce8a4
theorem M7.PrefixOrbit.emitted_class_valid : QuantumHarnessFrozenTarget := by
  intro N inst w E A B WA WB hbase y hy
  classical
  have hv : M7.PrefixOrbit.ClassValid w y :=
    ((M7.PrefixOrbit.membership N w E A B WA WB hbase y).mp hy).1
  have ho : M7.CanonicalOuter.canonical y ∈ M7.ActualOrbit.orbit y :=
    (M7.CanonicalClasses.orbit_membership N y (M7.CanonicalOuter.canonical y)).mpr
      (M7.CanonicalClasses.idempotent N y)
  obtain ⟨g, hg, heq⟩ := Finset.mem_image.mp ho
  rw [← heq]
  exact M7.PrefixOrbit.class_action N w y g hv
