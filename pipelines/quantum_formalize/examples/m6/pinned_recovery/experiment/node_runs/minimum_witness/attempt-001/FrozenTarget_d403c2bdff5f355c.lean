import M6Pinned

theorem M6.Pinned.agrees_pin : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Pinned.Vector m) (i : Fin m) (b : ZMod 2), P i = none → (M6.Pinned.agrees (M6.Pinned.pin P i b) v ↔ M6.Pinned.agrees P v ∧ v i = b) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Pinned.Vector m) (i : Fin m) (b : ZMod 2), P i = none → (M6.Pinned.agrees (M6.Pinned.pin P i b) v ↔ M6.Pinned.agrees P v ∧ v i = b)
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro m P v i b hP
  unfold M6.Pinned.agrees
  constructor
  · intro h
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simp [hP]
      · simpa [M6.Pinned.pin, Function.update, hji, Ne.symm hji] using h j
    · simpa [M6.Pinned.pin, Function.update] using h i
  · rintro ⟨h, hv⟩ j
    by_cases hji : j = i
    · subst j
      simp [M6.Pinned.pin, Function.update, hv]
    · simpa [M6.Pinned.pin, Function.update, hji, Ne.symm hji] using h j

theorem M6.Pinned.choose_properties : ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (i : Fin m), M6.Pinned.refines P (M6.Pinned.choose c P i).1 ∧ (M6.Pinned.choose c P i).1 i ≠ none ∧ (M6.Pinned.choose c P i).2 ≤ 1 := by
  classical
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (i : Fin m), M6.Pinned.refines P (M6.Pinned.choose c P i).1 ∧ (M6.Pinned.choose c P i).1 i ≠ none ∧ (M6.Pinned.choose c P i).2 ≤ 1
  intro m c P i
  cases h : P i with
  | none =>
      have hr (b : ZMod 2) : M6.Pinned.refines P (M6.Pinned.pin P i b) := by
        unfold M6.Pinned.refines
        intro j
        by_cases hj : j = i
        · subst j
          simp [h]
        · simp [M6.Pinned.pin, hj]
      have hn (b : ZMod 2) : M6.Pinned.pin P i b i ≠ none := by
        simp [M6.Pinned.pin]
      simp only [M6.Pinned.choose, h]
      split <;> simp_all
  | some b =>
      simp [M6.Pinned.choose, h, M6.Pinned.refines]

theorem M6.Pinned.count_nonnegative_positive : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), 0 ≤ M6.Pinned.count L P d ∧ (0 < M6.Pinned.count L P d ↔ ∃ v ∈ L, M6.Pinned.agrees P v ∧ M6.Pinned.weight v = d) := by
  classical
  intro m L P d
  unfold M6.Pinned.count
  constructor
  · exact Int.natCast_nonneg _
  · simp [Int.natCast_pos, Finset.card_pos, Finset.Nonempty, and_assoc]

theorem M6.Pinned.decode_unique : ∀ (m : ℕ) (P : M6.Pinned.Pins m), M6.Pinned.assigned P → ∀ v : M6.Pinned.Vector m, (M6.Pinned.agrees P v ↔ v = M6.Pinned.decode P) := by
  intro m P hP v
  unfold M6.Pinned.assigned at hP
  constructor
  · intro hv
    unfold M6.Pinned.agrees at hv
    funext i
    have ha := hP i
    have hv' := hv i
    cases hi : P i <;> simp_all [M6.Pinned.decode]
  · intro hv
    subst v
    unfold M6.Pinned.agrees
    intro i
    cases hi : P i <;> simp [M6.Pinned.decode, hi]

theorem M6.Pinned.distance_spec : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), (M6.Pinned.distance L = none ↔ L = ∅) ∧ ∀ d : ℕ, (M6.Pinned.distance L = some d ↔ (∃ v ∈ L, M6.Pinned.weight v = d) ∧ ∀ v ∈ L, d ≤ M6.Pinned.weight v) := by
  classical
  intro m L
  by_cases h : L.Nonempty
  · have hi : (L.image M6.Pinned.weight).Nonempty := h.image M6.Pinned.weight
    constructor
    · simp [M6.Pinned.distance, h, h.ne_empty]
    · intro d
      change (if h : L.Nonempty then
        some ((L.image M6.Pinned.weight).min' (h.image M6.Pinned.weight))
        else none) = some d ↔ _
      rw [dif_pos h, Option.some.injEq]
      constructor
      · intro hd
        obtain ⟨v, hv, hw⟩ := Finset.mem_image.mp
          (Finset.min'_mem (L.image M6.Pinned.weight) hi)
        constructor
        · exact ⟨v, hv, hw.trans hd⟩
        · intro w hw
          rw [← hd]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
      · rintro ⟨⟨v, hv, hvd⟩, hleast⟩
        apply le_antisymm
        · rw [← hvd]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        · obtain ⟨w, hw, hweight⟩ := Finset.mem_image.mp
            (Finset.min'_mem (L.image M6.Pinned.weight) hi)
          rw [← hweight]
          exact hleast w hw
  · have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst L
    simp [M6.Pinned.distance]

theorem M6.Pinned.enumerator_coeff : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d := by
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d
  intro m L P d
  classical
  simp only [M6.Pinned.enumerator, M6.Pinned.count,
    Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hrev : (d = M6.Pinned.weight v) ↔ (M6.Pinned.weight v = d) := eq_comm
  by_cases ha : M6.Pinned.agrees P v <;>
    by_cases hw : M6.Pinned.weight v = d <;>
    simp [ha, hw, Polynomial.coeff_X_pow, eq_comm]
  all_goals omega

theorem M6.Pinned.recover_positive : ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ), M6.Pinned.partitions c → ∀ (P : M6.Pinned.Pins m) (xs : List (Fin m)), 0 < c P → 0 < c (M6.Pinned.recover c P xs).1 := by
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ), M6.Pinned.partitions c → ∀ (P : M6.Pinned.Pins m) (xs : List (Fin m)), 0 < c P → 0 < c (M6.Pinned.recover c P xs).1
  intro m c hc
  unfold M6.Pinned.partitions at hc
  have hchoose : ∀ (P : M6.Pinned.Pins m) (i : Fin m), 0 < c P → 0 < c (M6.Pinned.choose c P i).1 := by
    intro P i hP
    unfold M6.Pinned.choose
    split
    all_goals
      first
      | exact hP
      | (split <;> dsimp only <;>
          first
          | assumption
          | (have hsum := hc P i (by assumption)
             omega))
  intro P xs
  induction xs generalizing P with
  | nil =>
      simpa only [M6.Pinned.recover] using (fun h : 0 < c P => h)
  | cons i xs ih =>
      intro hP
      simpa only [M6.Pinned.recover] using
        (ih (M6.Pinned.choose c P i).1 (hchoose P i hP))

theorem M6.Pinned.weight_bound : ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m := by
  change ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m
  intro m v
  classical
  unfold M6.Pinned.weight
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp

theorem M6.Pinned.count_pin_partition : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ), M6.Pinned.partitions (fun P => M6.Pinned.count L P d) := by
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ), M6.Pinned.partitions (fun P => M6.Pinned.count L P d)
  classical
  intro m L d
  unfold M6.Pinned.partitions
  intro P i hP
  have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  induction L using Finset.induction_on with
  | empty =>
      simp [M6.Pinned.count, M6.Pinned.enumerator]
  | @insert v L hv ih =>
      rcases hbits (v i) with hb | hb <;>
        by_cases ha : M6.Pinned.agrees P v <;>
        by_cases hw : M6.Pinned.weight v = d <;>
        simp_all [M6.Pinned.count, M6.Pinned.enumerator,
          M6.Pinned.agrees_pin, Finset.filter_insert,
          Finset.sum_insert, Polynomial.coeff_sum,
          Polynomial.coeff_monomial] <;> omega

theorem M6.Pinned.first_positive_distance : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), M6.Pinned.firstPositive m (M6.Pinned.enumerator L (M6.Pinned.free m)) = M6.Pinned.distance L := by
  classical
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), M6.Pinned.firstPositive m (M6.Pinned.enumerator L (M6.Pinned.free m)) = M6.Pinned.distance L
  intro m L
  have hc : ∀ d : ℕ, (0 < (M6.Pinned.enumerator L (M6.Pinned.free m)).coeff d) ↔ ∃ v ∈ L, M6.Pinned.weight v = d := by
    intro d
    rw [M6.Pinned.enumerator_coeff]
    simpa [M6.Pinned.agrees, M6.Pinned.free] using
      (M6.Pinned.count_nonnegative_positive m L (M6.Pinned.free m) d).2
  cases hd : M6.Pinned.distance L with
  | none =>
      have he : L = ∅ := (M6.Pinned.distance_spec m L).1.mp hd
      simp [M6.Pinned.firstPositive, he, M6.Pinned.enumerator]
  | some d =>
      obtain ⟨hwitness, hleast⟩ := (M6.Pinned.distance_spec m L).2 d |>.mp hd
      have hbound : d < m + 1 := by
        obtain ⟨v, hv, hweight⟩ := hwitness
        have hb := M6.Pinned.weight_bound m v
        omega
      have hn : ∀ j < d, ¬ ∃ v ∈ L, M6.Pinned.weight v = j := by
        intro j hj
        rintro ⟨v, hv, hw⟩
        have hl := hleast v hv
        omega
      simp only [M6.Pinned.firstPositive, List.find?_range_eq_some, decide_eq_true_eq, List.mem_range, hc]
      refine ⟨hwitness, hbound, ?_⟩
      intro j hj
      simpa using hn j hj

theorem M6.Pinned.recover_properties : ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (xs : List (Fin m)), M6.Pinned.refines P (M6.Pinned.recover c P xs).1 ∧ (∀ i ∈ xs, (M6.Pinned.recover c P xs).1 i ≠ none) ∧ (M6.Pinned.recover c P xs).2 ≤ xs.length := by
  classical
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (xs : List (Fin m)), M6.Pinned.refines P (M6.Pinned.recover c P xs).1 ∧ (∀ i ∈ xs, (M6.Pinned.recover c P xs).1 i ≠ none) ∧ (M6.Pinned.recover c P xs).2 ≤ xs.length
  intro m c P xs
  have trans_refines (A B C : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (hBC : M6.Pinned.refines B C) :
      M6.Pinned.refines A C := by
    unfold M6.Pinned.refines at hAB hBC ⊢
    intro j b hj
    exact hBC j b (hAB j b hj)
  have preserve (A B : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (j : Fin m)
      (hj : A j ≠ none) : B j ≠ none := by
    unfold M6.Pinned.refines at hAB
    cases h : A j with
    | none => exact False.elim (hj h)
    | some b =>
        rw [hAB j b h]
        simp
  induction xs generalizing P with
  | nil =>
      simp [M6.Pinned.recover, M6.Pinned.refines]
  | cons i xs ih =>
      have hcprop := M6.Pinned.choose_properties m c P i
      cases hc : M6.Pinned.choose c P i with
      | mk Q k =>
          have hrprop := ih Q
          cases hr : M6.Pinned.recover c Q xs with
          | mk R n =>
              simp only [hc, Prod.fst, Prod.snd] at hcprop
              simp only [hr, Prod.fst, Prod.snd] at hrprop
              simp only [M6.Pinned.recover, hc, hr, Prod.fst, Prod.snd]
              refine ⟨trans_refines P Q R hcprop.1 hrprop.1, ?_, ?_⟩
              · intro j hj
                rcases List.mem_cons.mp hj with hji | hj
                · rw [hji]
                  exact preserve Q R hrprop.1 i hcprop.2.1
                · exact hrprop.2.1 j hj
              · have hk := hcprop.2.2
                have hn := hrprop.2.2
                simp only [List.length_cons]
                omega

theorem M6.Pinned.recover_from_counts : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ) (c : M6.Pinned.Pins m → ℤ), (∀ P, c P = M6.Pinned.count L P d) → 0 < c (M6.Pinned.free m) → let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m); M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ) (c : M6.Pinned.Pins m → ℤ), (∀ P, c P = M6.Pinned.count L P d) → 0 < c (M6.Pinned.free m) → let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m); M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro m L d c hc hpos
  let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m)
  change M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m
  have heq : c = fun P => M6.Pinned.count L P d := funext hc
  have hpart : M6.Pinned.partitions c := by
    rw [heq]
    exact M6.Pinned.count_pin_partition m L d
  have hp := M6.Pinned.recover_positive m c hpart (M6.Pinned.free m) (List.finRange m) hpos
  change 0 < c r.1 at hp
  rw [hc r.1] at hp
  have hr := M6.Pinned.recover_properties m c (M6.Pinned.free m) (List.finRange m)
  have ha : M6.Pinned.assigned r.1 := by
    intro i
    exact hr.2.1 i (by simp)
  obtain ⟨v, hvL, hvA, hvW⟩ := (M6.Pinned.count_nonnegative_positive m L r.1 d).2.mp hp
  have hv : v = M6.Pinned.decode r.1 := (M6.Pinned.decode_unique m r.1 ha v).mp hvA
  refine ⟨hv ▸ hvL, hv ▸ hvW, ?_⟩
  simpa only [List.length_finRange] using hr.2.2

theorem M6.Pinned.solve_exact : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (Q : M6.Pinned.Pins m → Polynomial ℤ), (∀ P, Q P = M6.Pinned.enumerator L P) → (M6.Pinned.solve Q = none ↔ L = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve Q = some (d, v, k) → v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (Q : M6.Pinned.Pins m → Polynomial ℤ), (∀ P, Q P = M6.Pinned.enumerator L P) → (M6.Pinned.solve Q = none ↔ L = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve Q = some (d, v, k) → v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro m L Q hQ
  have hf : M6.Pinned.firstPositive m (Q (M6.Pinned.free m)) = M6.Pinned.distance L := by
    rw [hQ]
    exact M6.Pinned.first_positive_distance m L
  cases hd : M6.Pinned.distance L with
  | none =>
      have he : L = ∅ := (M6.Pinned.distance_spec m L).1.mp hd
      have hs : M6.Pinned.solve Q = none := by
        simp [M6.Pinned.solve, hf, hd]
      simp [hs, he]
  | some d =>
      obtain ⟨hwitness, hleast⟩ := (M6.Pinned.distance_spec m L).2 d |>.mp hd
      have hn : L ≠ ∅ := by
        intro he
        have hh := (M6.Pinned.distance_spec m L).1.mpr he
        rw [hd] at hh
        cases hh
      let c : M6.Pinned.Pins m → ℤ := fun P => (Q P).coeff d
      have hc : ∀ P, c P = M6.Pinned.count L P d := by
        intro P
        dsimp [c]
        rw [hQ, M6.Pinned.enumerator_coeff]
      have hp : 0 < c (M6.Pinned.free m) := by
        rw [hc]
        apply (M6.Pinned.count_nonnegative_positive m L (M6.Pinned.free m) d).2.mpr
        obtain ⟨v, hv, hw⟩ := hwitness
        exact ⟨v, hv, by simp [M6.Pinned.agrees, M6.Pinned.free], hw⟩
      let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m)
      have hr := M6.Pinned.recover_from_counts m L d c hc hp
      change M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m at hr
      have hs : M6.Pinned.solve Q = some (d, M6.Pinned.decode r.1, r.2) := by
        simp [M6.Pinned.solve, hf, hd, r, c]
      constructor
      · simp [hs, hn]
      · intro d' v k h
        have he := hs.symm.trans h
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl, rfl⟩
        exact ⟨hr.1, hr.2.1, hleast, hr.2.2⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), L.Nonempty → ∃ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve (M6.Pinned.enumerator L) = some (d, v, k) ∧ v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m
