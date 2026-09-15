import M7GenerationReplay

theorem M7.GenerationReplay.fresh_nodup : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (es : List (M7.CompactGeneration.Emission N)), M7.GenerationReplay.FreshFrom w E bases es → (es.map (fun e => e.representative)).Nodup ∧ ∀ e ∈ es, e.representative ∉ bases := by
  classical
  intro N inst w E bases es
  induction es generalizing bases with
  | nil =>
      intro h
      simp
  | cons e es ih =>
      intro h
      change e.representative ∉ bases ∧ _ ∧ _ ∧ M7.GenerationReplay.FreshFrom w E (insert e.representative bases) es at h
      rcases h with ⟨hfresh, _, _, htail⟩
      obtain ⟨hnd, hdisjoint⟩ := ih (insert e.representative bases) htail
      constructor
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hnd⟩
        intro hm
        obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
        exact hdisjoint a ha (by simp [heq])
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hfresh
        · intro hb
          exact hdisjoint a ha (Finset.mem_insert_of_mem hb)

theorem M7.GenerationReplay.replay_terminal_fold : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases final : Finset (M7.Action.Recipe N)) (es : List (M7.CompactGeneration.Emission N)), M7.GenerationReplay.replay w E bases es = some final → M7.CompactGeneration.residual w E final [] = 0 ∧ final = es.foldl (fun acc e => insert e.representative acc) bases := by
  classical
  intro N inst w E bases final es
  induction es generalizing bases final with
  | nil =>
      intro h
      unfold M7.GenerationReplay.replay at h
      split at h
      · rename_i hz
        have heq : bases = final := Option.some.inj h
        subst final
        exact ⟨hz, rfl⟩
      · simp at h
  | cons e es ih =>
      intro h
      unfold M7.GenerationReplay.replay at h
      split at h
      · exact ih (insert e.representative bases) final h
      · simp at h

theorem M7.GenerationReplay.step_exact : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (e : M7.CompactGeneration.Emission N), M7.GenerationReplay.stepPass w E bases e = true ↔ 0 < M7.CompactGeneration.residual w E bases [] ∧ e = M7.CompactGeneration.emission w E bases := by
  classical
  intro N inst w E bases e
  change M7.GenerationReplay.stepPass w E bases e = true ↔ _
  constructor
  · intro h
    simp only [M7.GenerationReplay.stepPass, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hpos, hcheck⟩, hdepth, hleaf, hrep, haction, hleafSig, hrepSig, hstab⟩
    have hpath := M7.DescentTrace.check_unique
      (M7.CompactGeneration.residual w E bases) [] e.path hcheck
    rw [hdepth] at hpath
    refine ⟨hpos, ?_⟩
    cases e
    dsimp only at *
    simp_all [M7.CompactGeneration.emission, M7.DescentTrace.endpoint_recover]
  · rintro ⟨hpos, rfl⟩
    simp [M7.GenerationReplay.stepPass, M7.CompactGeneration.emission,
      M7.DescentTrace.trace_length, M7.DescentTrace.check_trace,
      M7.DescentTrace.endpoint_recover, hpos]

theorem M7.GenerationReplay.replay_sound : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases final : Finset (M7.Action.Recipe N)) (es : List (M7.CompactGeneration.Emission N)), M7.RecoveryInstance.GoodBases w bases → M7.GenerationReplay.replay w E bases es = some final → M7.RecoveryInstance.GoodBases w final ∧ M7.GenerationReplay.FreshFrom w E bases es := by
  classical
  intro N inst w E hE bases final es
  induction es generalizing bases final with
  | nil =>
      intro hb hr
      simp only [M7.GenerationReplay.replay] at hr
      split at hr
      · cases Option.some.inj hr
        exact ⟨hb, trivial⟩
      · cases hr
  | cons e es ih =>
      intro hb hr
      simp only [M7.GenerationReplay.replay] at hr
      split at hr
      · rename_i hs
        rcases (M7.GenerationReplay.step_exact N w E bases e).mp hs with ⟨hp, rfl⟩
        have hp' : 0 < M7.RecoveryInstance.count w E bases [] := by
          simpa only [M7.CompactCorrectness.residual_eq] using hp
        have he := M7.CompactCorrectness.emission_eq N w E bases
        have hg := M7.RecoveryInstance.insert_good N w E bases hE hb hp'
        have hb' : M7.RecoveryInstance.GoodBases w
            (insert (M7.CompactGeneration.emission w E bases).representative bases) := by
          rw [he.2]
          exact hg.1
        have hn : (M7.CompactGeneration.emission w E bases).representative ∉ bases := by
          change M7.CanonicalOuter.canonical (M7.CompactGeneration.emission w E bases).leaf ∉ bases
          rw [he.1]
          exact hg.2
        have hv : M7.PrefixOrbit.ClassValid w
            (M7.CompactGeneration.emission w E bases).representative := by
          have hh := hb'
          unfold M7.RecoveryInstance.GoodBases at hh
          rcases hh with ⟨h₁, h₂⟩
          first
          | exact h₂ _ (Finset.mem_insert_self _ _)
          | exact h₁ _ (Finset.mem_insert_self _ _)
        have hl : (M7.CompactGeneration.emission w E bases).leaf ∈
            M7.RecoveryPrefix.completed N w E [] := by
          rw [he.1]
          have hf := (M7.RecoveryInstance.fresh_leaf N w E bases hE hb hp').1
          simp only [M7.RecoveryInstance.remaining, M7.OrbitResidual.remaining,
            Finset.mem_sdiff, Finset.mem_filter] at hf
          exact hf.1
        obtain ⟨hfinal, htail⟩ := ih _ _ hb' hr
        exact ⟨hfinal, hn, hv, hl, htail⟩
      · cases hr

theorem M7.GenerationReplay.run_replay : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), root = M7.CompactGeneration.residual w E bases [] → (M7.CompactGeneration.run w E fuel bases root).finalResidual = 0 → M7.GenerationReplay.replay w E bases (M7.CompactGeneration.run w E fuel bases root).emitted = some (M7.CompactGeneration.run w E fuel bases root).finalBases := by
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero =>
      intro hroot hzero
      by_cases hpos : 0 < root
      · simp_all [M7.CompactGeneration.run, M7.GenerationReplay.replay,
          not_le_of_gt hpos]
      · simp_all [M7.CompactGeneration.run, M7.GenerationReplay.replay,
          le_of_not_gt hpos]
  | succ fuel ih =>
      intro hroot hzero
      by_cases hpos : 0 < root
      · have hstep : M7.GenerationReplay.stepPass w E bases
            (M7.CompactGeneration.emission w E bases) = true :=
          (M7.GenerationReplay.step_exact N w E bases _).2
            ⟨hroot ▸ hpos, rfl⟩
        simp only [M7.CompactGeneration.run, if_pos hpos,
          if_neg (not_le_of_gt hpos)] at hzero ⊢
        simp only [M7.GenerationReplay.replay, hstep, if_true]
        exact ih _ _ rfl hzero
      · have hstop := M7.CompactGeneration.stop N w E bases
          (fuel + 1) root (le_of_not_gt hpos)
        rw [hstop.1, hstop.2.1]
        have hres : M7.CompactGeneration.residual w E bases [] = 0 :=
          hroot.symm.trans (hstop.2.2.1.symm.trans hzero)
        simp [M7.GenerationReplay.replay, hres]

theorem M7.GenerationReplay.checked_coverage : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → 0 < w → ∀ o : M7.CompactGeneration.Output N, M7.GenerationReplay.check w E o = true → M7.RecoveryInstance.GoodBases w o.finalBases ∧ M7.GenerationReplay.FreshFrom w E ∅ o.emitted ∧ (o.emitted.map (fun e => e.representative)).Nodup ∧ (∀ y ∈ M7.RecoveryPrefix.completed N w E [], y ∈ M7.OrbitResidual.covered o.finalBases) ∧ (∀ c : M7.Action.Recipe N, M7.RawCoverage.Queried w E c → M7.CanonicalOuter.canonical c ∈ o.finalBases ∧ ∃ b ∈ o.finalBases, ∃ g : M7.Action.Record N, M7.Action.act g b = c) := by
  classical
  intro N inst w E hE hw o hc
  have hr : M7.GenerationReplay.replay w E ∅ o.emitted = some o.finalBases := by
    unfold M7.GenerationReplay.check at hc
    cases he : M7.GenerationReplay.replay w E ∅ o.emitted with
    | none => simp [he] at hc
    | some bases =>
        simp only [he, decide_eq_true_eq] at hc
        exact congrArg some hc.1
  obtain ⟨hb, hf⟩ := M7.GenerationReplay.replay_sound N w E hE ∅ o.finalBases o.emitted
    (M7.CompactCorrectness.initial N w E hE).1 hr
  have hn := (M7.GenerationReplay.fresh_nodup N w E ∅ o.emitted hf).1
  have hz := (M7.GenerationReplay.replay_terminal_fold N w E ∅ o.finalBases o.emitted hr).1
  have hz' : M7.RecoveryInstance.count w E o.finalBases [] = 0 := by
    simpa only [M7.CompactCorrectness.residual_eq] using hz
  have hcov := (M7.RecoveryInstance.root_zero N w E o.finalBases hE hb).mp hz'
  refine ⟨hb, hf, hn, ?_, ?_⟩
  · intro y hy
    exact hcov hy
  · have hrem : M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) o.finalBases = ∅ := by
      change M7.RecoveryInstance.remaining w E o.finalBases [] = ∅
      apply Finset.card_eq_zero.mp
      have hcard := (M7.RecoveryInstance.count_card N w E o.finalBases hE hb []).2.1
      simpa only [hz', Int.toNat_zero] using hcard.symm
    apply M7.RawCoverage.remaining_coverage N w E o.finalBases hw
    · first | exact hb.1 | exact hb.2
    · first | exact hb.2 | exact hb.1
    · exact hrem

theorem M7.GenerationReplay.generate_checked : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → M7.GenerationReplay.check w E (M7.CompactGeneration.generate (N := N) w E) = true := by
  classical
  intro N inst w E hE
  have hex := M7.CompactCorrectness.generate_exact N w E hE
  have hz : (M7.CompactGeneration.generate (N := N) w E).finalResidual = 0 := by
    tauto
  have hf : (M7.CompactGeneration.generate (N := N) w E).fuelExhausted = false := by
    tauto
  have hr : M7.GenerationReplay.replay w E ∅
      (M7.CompactGeneration.generate (N := N) w E).emitted =
      some (M7.CompactGeneration.generate (N := N) w E).finalBases := by
    unfold M7.CompactGeneration.generate
    apply M7.GenerationReplay.run_replay N w E ∅
    · rfl
    · exact hz
  simp [M7.GenerationReplay.check, hr, hz, hf]
#print axioms M7.GenerationReplay.fresh_nodup
#print axioms M7.GenerationReplay.replay_terminal_fold
#print axioms M7.GenerationReplay.step_exact
#print axioms M7.GenerationReplay.replay_sound
#print axioms M7.GenerationReplay.checked_coverage
#print axioms M7.GenerationReplay.run_replay
#print axioms M7.GenerationReplay.generate_checked
