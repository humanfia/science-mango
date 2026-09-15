import FrozenTarget_b52fd2e4b18ac0b2
theorem M7.GeneratedFamily.family_injective : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  have hn : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).Nodup := by
    have hs := M7.CompactCorrectness.generate_exact N w E hE
    tauto
  intro i j hij
  change ((M7.CompactGeneration.generate (N := N) w E).emitted.get i).representative = ((M7.CompactGeneration.generate (N := N) w E).emitted.get j).representative at hij
  let i' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length := ⟨i.val, by simpa [M7.GeneratedFamily.size] using i.isLt⟩
  let j' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length := ⟨j.val, by simpa [M7.GeneratedFamily.size] using j.isLt⟩
  have he : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get i' = ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get j' := by
    simpa only [List.get_eq_getElem, List.getElem_map] using hij
  have hidx : i' = j' := hn.injective_get he
  have hv : i'.val = j'.val := congrArg (fun k => k.val) hidx
  apply Fin.ext
  exact hv
