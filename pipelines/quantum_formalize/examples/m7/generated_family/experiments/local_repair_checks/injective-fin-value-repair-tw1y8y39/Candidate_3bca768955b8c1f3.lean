import FrozenTarget_3bca768955b8c1f3
theorem M7.GeneratedFamily.family_injective : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  classical
  have hex := M7.CompactCorrectness.generate_exact N w E hE
  have hn : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).Nodup := by
    tauto
  intro i j hij
  let i' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length := ⟨i.val, by simpa [M7.GeneratedFamily.size] using i.isLt⟩
  let j' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length := ⟨j.val, by simpa [M7.GeneratedFamily.size] using j.isLt⟩
  have heq : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get i' = ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get j' := by
    simpa only [M7.GeneratedFamily.family, List.get_eq_getElem, List.getElem_map, i', j'] using hij
  have hidx := hn.injective_get heq
  have hv : i'.val = j'.val := congrArg (fun k : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length => k.val) hidx
  exact Fin.ext hv
