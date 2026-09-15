import FrozenTarget_5c4cd86056731716
theorem M7.Transport.action_isometry : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst g c
  classical
  have ht := M6.RecipeIsometries.translation_isometry N
  have hm := M6.RecipeIsometries.multiplier_isometry N
  have he := M6.RecipeIsometries.exchange_isometry N
  have hc : ∀ (f h : M6.Pinned.Vector (2*N) → M6.Pinned.Vector (2*N)),
      Function.Bijective f → Function.Bijective h →
      Function.Bijective (fun v => f (h v)) := by
    intro f h hf hh
    exact hf.comp hh
  simp only [M7.Transport.Xmap, M7.Transport.BX, M7.Transport.CX,
    M7.Action.act]
  split_ifs <;>
    (try simp only [M7.Transport.affine_indicator]) <;>
    grind only
