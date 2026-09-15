import FrozenTarget_e3442d2f6cbbda62
theorem M7.GeneratedFamily.family_injective : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  classical
  have hexact := M7.CompactCorrectness.generate_exact N w E hE
  have hn : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).Nodup := by
    tauto
  intro i j hij
  let i' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length :=
    ⟨i.val, by simpa [M7.GeneratedFamily.size] using i.isLt⟩
  let j' : Fin ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).length :=
    ⟨j.val, by simpa [M7.GeneratedFamily.size] using j.isLt⟩
  have hget : ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get i' =
      ((M7.CompactGeneration.generate (N := N) w E).emitted.map (fun e => e.representative)).get j' := by
    simpa [i', j', M7.GeneratedFamily.family] using hij
  have heq : i' = j' := (List.nodup_iff_injective_get.mp hn) hget
  apply Fin.ext
  exact congrArg Fin.val heq
