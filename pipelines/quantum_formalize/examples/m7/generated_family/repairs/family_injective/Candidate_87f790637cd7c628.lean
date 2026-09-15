import FrozenTarget_87f790637cd7c628
theorem M7.GeneratedFamily.family_injective : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  classical
  have hn := (M7.CompactCorrectness.generate_exact N w E hE).2.2.2
  have hl := List.Nodup.of_map (fun e : M7.CompactGeneration.Emission N => e.representative) hn
  intro i j hij
  apply hl.injective_get
  exact List.inj_on_of_nodup_map hn
    (List.get_mem (M7.CompactGeneration.generate (N := N) w E).emitted i)
    (List.get_mem (M7.CompactGeneration.generate (N := N) w E).emitted j) hij
