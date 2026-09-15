import M7PrefixOrbit

theorem M7.PrefixOrbit.class_action : ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), M7.PrefixOrbit.ClassValid w c → M7.PrefixOrbit.ClassValid w (M7.Action.act g c) := by
  intro N inst w c g h
  change c.1.card = w ∧ c.2.card = w ∧ M7.Connectivity.connected c at h
  change (M7.Action.act g c).1.card = w ∧ (M7.Action.act g c).2.card = w ∧ M7.Connectivity.connected (M7.Action.act g c)
  have hc := (M7.Connectivity.connected_action N g c).mpr h.2.2
  first
  | have hcards := M7.Action.support_cards N g c
  | have hcards := M7.Action.support_cards N c g
  all_goals
    aesop

theorem M7.PrefixOrbit.gcd_bridge : ∀ (N : ℕ) [NeZero N], ∀ y : M7.Action.Recipe N, M7.Domain.connectivityGcd y.1 y.2 = M5.Connectivity.supportGcd N (M7.ResiduePrefix.encode y.1) (M7.ResiduePrefix.encode y.2) := by
  intro N _ y
  rw [M7.ResiduePrefix.gcd_union]
  rfl

theorem M7.PrefixOrbit.prefix_anchors : ∀ (N : ℕ) [NeZero N], ∀ (A B WA WB : Finset ℕ) (y : M7.Action.Recipe N), M7.PrefixCompleted.Base N A B WA WB → M7.PrefixOrbit.Within A WA y.1 → M7.PrefixOrbit.Within B WB y.2 → (0 : ZMod N) ∈ y.1 ∧ (0 : ZMod N) ∈ y.2 := by
  intro N inst A B WA WB y hbase hA hB
  classical
  have hzero : 0 ∈ A ∧ 0 ∈ B := by
    unfold M7.PrefixCompleted.Base at hbase
    tauto
  have hleft : 0 ∈ M7.ResiduePrefix.encode y.1 := hA.1 hzero.1
  have hright : 0 ∈ M7.ResiduePrefix.encode y.2 := hB.1 hzero.2
  constructor
  · rw [← M7.ResiduePrefix.residue_roundtrip N y.1]
    unfold M7.ResiduePrefix.decode
    exact Finset.mem_image.mpr ⟨0, hleft, by simp⟩
  · rw [← M7.ResiduePrefix.residue_roundtrip N y.2]
    unfold M7.ResiduePrefix.decode
    exact Finset.mem_image.mpr ⟨0, hright, by simp⟩

theorem M7.PrefixOrbit.membership : ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ y : M7.Action.Recipe N, y ∈ M7.ResiduePrefix.completed N w E A B WA WB ↔ M7.PrefixOrbit.ClassValid w y ∧ M7.RecipeSignature.signature y ∈ E ∧ M7.PrefixOrbit.Within A WA y.1 ∧ M7.PrefixOrbit.Within B WB y.2 := by
  intro N inst w E A B WA WB hbase y
  classical
  have hs : M5.completeSignature
      (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode y.1))
      (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode y.2)) N =
      M7.RecipeSignature.signature y :=
    M7.ResiduePrefix.signature_bridge N y.1 y.2
  have hm := M7.ResiduePrefix.completed_membership N w E A B WA WB hbase y
  simp only [M7.PrefixCompleted.Within, M7.PrefixCompleted.Valid,
    M7.ResiduePrefix.encodePair, M7.ResiduePrefix.encode_card, hs,
    ← M7.PrefixOrbit.gcd_bridge N y] at hm
  constructor
  · intro hy
    have hp := hm.mp hy
    have hA : M7.PrefixOrbit.Within A WA y.1 := by
      unfold M7.PrefixOrbit.Within
      tauto
    have hB : M7.PrefixOrbit.Within B WB y.2 := by
      unfold M7.PrefixOrbit.Within
      tauto
    obtain ⟨ha, hb⟩ := M7.PrefixOrbit.prefix_anchors N A B WA WB y hbase hA hB
    have hc := M7.Connectivity.anchored_gcd N y.1 y.2 ha hb
    change M7.Connectivity.connected y ↔ M7.Domain.connectivityGcd y.1 y.2 = 1 at hc
    unfold M7.PrefixOrbit.ClassValid
    tauto
  · intro hy
    obtain ⟨hv, hs', hA, hB⟩ := hy
    obtain ⟨ha, hb⟩ := M7.PrefixOrbit.prefix_anchors N A B WA WB y hbase hA hB
    have hc := M7.Connectivity.anchored_gcd N y.1 y.2 ha hb
    change M7.Connectivity.connected y ↔ M7.Domain.connectivityGcd y.1 y.2 = 1 at hc
    unfold M7.PrefixOrbit.ClassValid at hv
    unfold M7.PrefixOrbit.Within at hA hB
    apply hm.mpr
    tauto
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ c : M7.Action.Recipe N, M7.PrefixOrbit.ClassValid w c → M7.PrefixOrbit.orbitCount E A B WA WB c = M7.ActualOrbit.distinctCount c (fun y => y ∈ M7.ResiduePrefix.completed N w E A B WA WB)
