import FrozenTarget_2c58f4d26e215854
theorem M7.GeneratedFamily.family_injective : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  classical
  have hn : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).Nodup := by
    have h := M7.CompactCorrectness.generate_exact N w E hE
    tauto
  intro i j hij
  let i' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length :=
    ⟨i.val, by simpa [M7.GeneratedFamily.size] using i.isLt⟩
  let j' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length :=
    ⟨j.val, by simpa [M7.GeneratedFamily.size] using j.isLt⟩
  have he : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get i' =
      ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get j' := by
    simpa [i', j', M7.GeneratedFamily.family] using hij
  have hidx := (List.nodup_iff_injective_get.mp hn) he
  apply Fin.ext
  exact congrArg Fin.val hidx
