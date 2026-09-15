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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.keyset (M7.Action.act g c) = M7.CanonicalOuter.keyset c
