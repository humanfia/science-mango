import M7CanonicalOuter

theorem M7.CanonicalOuter.normalize_act_shifts : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.normalizePair (M7.Action.act g c) = M7.CanonicalOuter.normalizePair (M7.Action.act (⟨g.unit,g.exchange,0,0⟩ : M7.Action.Record N) c) := by
    intro N inst g c
    classical
    have h (u : (ZMod N)ˣ) (s : ZMod N) (A : Finset (ZMod N)) :
        M7.CanonicalBlock.normalize (A.image (M7.Action.affine u s)) =
          M7.CanonicalBlock.normalize (A.image (M7.Action.affine u 0)) := by
      have he : A.image (M7.Action.affine u s) =
          M7.CanonicalBlock.shift s (A.image (M7.Action.affine u 0)) := by
        unfold M7.CanonicalBlock.shift
        rw [Finset.image_image]
        congr 1
        funext i
        simp [M7.Action.affine, Function.comp_def]
      rw [he]
      exact M7.CanonicalBlock.normalize_shift N s (A.image (M7.Action.affine u 0))
    rcases g with ⟨u, e, s, t⟩
    cases e <;> simp [M7.CanonicalOuter.normalizePair, M7.Action.act, h]

theorem M7.CanonicalOuter.pair_key_injective : ∀ (N : ℕ) [NeZero N], Function.Injective (M7.CanonicalOuter.pairKey (N := N)) := by
  change ∀ (N : ℕ) [NeZero N], Function.Injective (M7.CanonicalOuter.pairKey (N := N))
  intro N inst a b h
  apply Prod.ext
  · have hk : M7.CanonicalBlock.key a.1 = M7.CanonicalBlock.key b.1 :=
      congrArg (fun k : M7.CanonicalOuter.PairKey => (ofLex k).1) h
    have hd := congrArg (M7.CanonicalBlock.decode N) hk
    simpa only [M7.CanonicalBlock.decode_key] using hd
  · have hk : M7.CanonicalBlock.key a.2 = M7.CanonicalBlock.key b.2 :=
      congrArg (fun k : M7.CanonicalOuter.PairKey => (ofLex k).2) h
    have hd := congrArg (M7.CanonicalBlock.decode N) hk
    simpa only [M7.CanonicalBlock.decode_key] using hd

theorem M7.CanonicalOuter.realizer_correct : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.CanonicalOuter.realizer c) c = M7.CanonicalOuter.canonical c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.CanonicalOuter.realizer c) c = M7.CanonicalOuter.canonical c
  intro N _ c
  classical
  have hs (s : ZMod N) (A : M7.CanonicalBlock.Support N) :
      A.image (M7.Action.affine 1 s) = M7.CanonicalBlock.shift s A := by
    unfold M7.Action.affine M7.CanonicalBlock.shift
    simp [add_comm]
  have hn (r : M7.Action.Recipe N) :
      M7.Action.act
        (M7.Action.translate (-M7.CanonicalBlock.bestAnchor r.1)
          (-M7.CanonicalBlock.bestAnchor r.2)) r =
        M7.CanonicalOuter.normalizePair r := by
    change
      (r.1.image (M7.Action.affine 1 (-M7.CanonicalBlock.bestAnchor r.1)),
        r.2.image (M7.Action.affine 1 (-M7.CanonicalBlock.bestAnchor r.2))) =
      (M7.CanonicalBlock.shift (-M7.CanonicalBlock.bestAnchor r.1) r.1,
        M7.CanonicalBlock.shift (-M7.CanonicalBlock.bestAnchor r.2) r.2)
    exact Prod.ext (hs _ _) (hs _ _)
  unfold M7.CanonicalOuter.realizer
  rw [M7.Action.act_compose]
  exact hn _

theorem M7.CanonicalOuter.unit_index : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (e : Bool), ∃ i ∈ M7.CanonicalOuter.indices N, M7.CanonicalOuter.outerRecord i = (⟨u,e,0,0⟩ : M7.Action.Record N) := by
   classical
   intro N inst u e
   let i : M7.CanonicalOuter.OuterIndex N :=
     toLex (⟨(u : ZMod N).val, ZMod.val_lt (u : ZMod N)⟩, e)
   have hv : (((ofLex i).1.val : ℕ) : ZMod N) = (u : ZMod N) := by
     simp [i]
   have hi : IsUnit (((ofLex i).1.val : ℕ) : ZMod N) := by
     rw [hv]
     exact u.isUnit
   refine ⟨i, ?_, ?_⟩
   · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
   · have hu : M7.CanonicalOuter.outerUnit i = u := by
       unfold M7.CanonicalOuter.outerUnit
       rw [dif_pos hi]
       apply Units.ext
       exact hi.unit_spec.trans hv
     change (⟨M7.CanonicalOuter.outerUnit i, (ofLex i).2, 0, 0⟩ : M7.Action.Record N) = ⟨u, e, 0, 0⟩
     rw [hu]
     rfl

theorem M7.CanonicalOuter.indices_nonempty : ∀ (N : ℕ) [NeZero N], (M7.CanonicalOuter.indices N).Nonempty := by
  change ∀ (N : ℕ) [NeZero N], (M7.CanonicalOuter.indices N).Nonempty
  intro N inst
  obtain ⟨i, hi, _⟩ := M7.CanonicalOuter.unit_index N (1 : (ZMod N)ˣ) false
  exact ⟨i, hi⟩

theorem M7.CanonicalOuter.keyset_all_records : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.keyset c = (Finset.univ : Finset (M7.Action.Record N)).image (fun g => M7.CanonicalOuter.pairKey (M7.CanonicalOuter.normalizePair (M7.Action.act g c))) := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.keyset c = (Finset.univ : Finset (M7.Action.Record N)).image (fun g => M7.CanonicalOuter.pairKey (M7.CanonicalOuter.normalizePair (M7.Action.act g c)))
  intro N inst c
  classical
  unfold M7.CanonicalOuter.keyset M7.CanonicalOuter.candidate
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, hik⟩
    exact Finset.mem_image.mpr ⟨M7.CanonicalOuter.outerRecord i, Finset.mem_univ _, hik⟩
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨g, hg, hgk⟩
    rcases M7.CanonicalOuter.unit_index N g.unit g.exchange with ⟨i, hi, hir⟩
    refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
    rw [hir, ← M7.CanonicalOuter.normalize_act_shifts N g c]
    exact hgk

theorem M7.CanonicalOuter.realizer_inverse : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.inverse (M7.CanonicalOuter.realizer c)) (M7.CanonicalOuter.canonical c) = c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.inverse (M7.CanonicalOuter.realizer c)) (M7.CanonicalOuter.canonical c) = c
  intro N _ c
  rw [← M7.CanonicalOuter.realizer_correct N c]
  exact M7.Action.act_inverse N (M7.CanonicalOuter.realizer c) c

theorem M7.CanonicalOuter.choices_nonempty : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.CanonicalOuter.choices c).Nonempty := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.CanonicalOuter.choices c).Nonempty
  intro N inst c
  obtain ⟨i, hi⟩ := M7.CanonicalOuter.indices_nonempty N
  unfold M7.CanonicalOuter.choices
  exact ⟨_, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

theorem M7.CanonicalOuter.keyset_action : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.keyset (M7.Action.act g c) = M7.CanonicalOuter.keyset c := by
  change ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.keyset (M7.Action.act g c) = M7.CanonicalOuter.keyset c
  intro N inst g c
  classical
  rw [M7.CanonicalOuter.keyset_all_records N (M7.Action.act g c), M7.CanonicalOuter.keyset_all_records N c]
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨h, _, hkey⟩
    refine Finset.mem_image.mpr ⟨M7.Action.compose h g, Finset.mem_univ _, ?_⟩
    rw [M7.Action.act_compose N h g c]
    exact hkey
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨h, _, hkey⟩
    refine Finset.mem_image.mpr ⟨M7.Action.compose h (M7.Action.inverse g), Finset.mem_univ _, ?_⟩
    rw [M7.Action.act_compose N h (M7.Action.inverse g) (M7.Action.act g c), M7.Action.act_inverse N g c]
    exact hkey

theorem M7.CanonicalOuter.canonical_key_agrees : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (ofLex (M7.CanonicalOuter.best c)).1 = M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c) := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (ofLex (M7.CanonicalOuter.best c)).1 = M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c)
  intro N inst c
  have h := M7.CanonicalOuter.choices_nonempty N c
  have hb : M7.CanonicalOuter.best c ∈ M7.CanonicalOuter.choices c := by
    unfold M7.CanonicalOuter.best
    rw [dif_pos h]
    exact Finset.min'_mem _ _
  unfold M7.CanonicalOuter.choices at hb
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hb
  change (ofLex (M7.CanonicalOuter.best c)).1 = M7.CanonicalOuter.pairKey (M7.CanonicalOuter.candidate c (ofLex (M7.CanonicalOuter.best c)).2)
  rw [← he]
  rfl

theorem M7.CanonicalOuter.chosen_outer_member : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.chosenOuter c ∈ M7.CanonicalOuter.indices N := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.chosenOuter c ∈ M7.CanonicalOuter.indices N
  intro N inst c
  have h := M7.CanonicalOuter.choices_nonempty N c
  have hb : M7.CanonicalOuter.best c ∈ M7.CanonicalOuter.choices c := by
    simpa only [M7.CanonicalOuter.best, dif_pos h] using (M7.CanonicalOuter.choices c).min'_mem h
  unfold M7.CanonicalOuter.choices at hb
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hb
  unfold M7.CanonicalOuter.chosenOuter
  rw [← he]
  exact hi

theorem M7.CanonicalOuter.canonical_key_member : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c) ∈ M7.CanonicalOuter.keyset c := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c) ∈ M7.CanonicalOuter.keyset c
  intro N inst c
  unfold M7.CanonicalOuter.keyset M7.CanonicalOuter.canonical
  exact Finset.mem_image.mpr ⟨M7.CanonicalOuter.chosenOuter c, M7.CanonicalOuter.chosen_outer_member N c, rfl⟩

theorem M7.CanonicalOuter.canonical_minimal : ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) k, k ∈ M7.CanonicalOuter.keyset c → M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c) ≤ k := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) k, k ∈ M7.CanonicalOuter.keyset c → M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c) ≤ k
  intro N inst c k hk
  unfold M7.CanonicalOuter.keyset at hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  have hc : toLex (M7.CanonicalOuter.pairKey (M7.CanonicalOuter.candidate c i), i) ∈ M7.CanonicalOuter.choices c := by
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hm : M7.CanonicalOuter.best c ≤ toLex (M7.CanonicalOuter.pairKey (M7.CanonicalOuter.candidate c i), i) := by
    unfold M7.CanonicalOuter.best
    rw [dif_pos (M7.CanonicalOuter.choices_nonempty N c)]
    exact Finset.min'_le _ _ hc
  have hf := Prod.Lex.monotone_fst _ _ hm
  rw [M7.CanonicalOuter.canonical_key_agrees N c] at hf
  exact hf

theorem M7.CanonicalOuter.canonical_invariant : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.canonical (M7.Action.act g c) = M7.CanonicalOuter.canonical c := by
  change ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.canonical (M7.Action.act g c) = M7.CanonicalOuter.canonical c
  intro N inst g c
  apply M7.CanonicalOuter.pair_key_injective N
  apply le_antisymm
  · apply M7.CanonicalOuter.canonical_minimal N (M7.Action.act g c)
    rw [M7.CanonicalOuter.keyset_action N g c]
    exact M7.CanonicalOuter.canonical_key_member N c
  · apply M7.CanonicalOuter.canonical_minimal N c
    rw [← M7.CanonicalOuter.keyset_action N g c]
    exact M7.CanonicalOuter.canonical_key_member N (M7.Action.act g c)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c d : M7.Action.Recipe N, (∃ g : M7.Action.Record N, M7.Action.act g c = d) ↔ M7.CanonicalOuter.canonical c = M7.CanonicalOuter.canonical d
