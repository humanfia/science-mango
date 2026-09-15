import FrozenTarget_860f9a11713a36ef
theorem M7.GeneratedFamily.family_injective : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  classical
  let l := (M7.CompactGeneration.generate (N := N) w E).emitted
  have hn : (l.map (fun e => e.representative)).Nodup := by
    have hex := M7.CompactCorrectness.generate_exact N w E hE
    dsimp [l]
    tauto
  intro i j hij
  let i' : Fin (l.map (fun e => e.representative)).length :=
    ⟨i.val, by simpa [l, M7.GeneratedFamily.size] using i.isLt⟩
  let j' : Fin (l.map (fun e => e.representative)).length :=
    ⟨j.val, by simpa [l, M7.GeneratedFamily.size] using j.isLt⟩
  have heq : i' = j' := hn.injective_get (by
    simpa [List.get_eq_getElem, i', j', l, M7.GeneratedFamily.family] using hij)
  apply Fin.ext
  exact congrArg (fun k : Fin (l.map (fun e => e.representative)).length => k.val) heq
