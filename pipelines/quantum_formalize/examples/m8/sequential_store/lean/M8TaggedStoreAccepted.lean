import M8TaggedStore

theorem M8.TaggedStore.address_representation : Function.Injective M8.TaggedStore.address ∧ ∀ i : ℕ, (M8.TaggedStore.address i).length = i.size := by
  change Function.Injective M8.TaggedStore.address ∧ ∀ i : ℕ, (M8.TaggedStore.address i).length = i.size
  constructor
  · intro a b h
    change a.bits = b.bits at h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]
  · intro i
    change i.bits.length = i.size
    exact Nat.size_eq_bits_len i

theorem M8.TaggedStore.comparison_exact : ∀ a b : M8.TaggedStore.Tag, (M8.TaggedStore.compare a b).1 = decide (a=b) ∧ (M8.TaggedStore.compare a b).2 ≤ a.length+1 := by
  change ∀ a b : M8.TaggedStore.Tag, (M8.TaggedStore.compare a b).1 = decide (a = b) ∧ (M8.TaggedStore.compare a b).2 ≤ a.length + 1
  intro a
  induction a with
  | nil =>
      intro b
      cases b <;> simp [M8.TaggedStore.compare]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [M8.TaggedStore.compare]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simpa [M8.TaggedStore.compare] using ih ys
          · simp [M8.TaggedStore.compare, h]

theorem M8.TaggedStore.write_layout : ∀ (key : M8.TaggedStore.Tag) (bit : Bool) (s : M8.TaggedStore.Store), ((M8.TaggedStore.write key bit s).1.map Prod.fst) = s.map Prod.fst ∧ (M8.TaggedStore.tapeBits (M8.TaggedStore.write key bit s).1).length = (M8.TaggedStore.tapeBits s).length := by
  change ∀ (key : M8.TaggedStore.Tag) (bit : Bool) (s : M8.TaggedStore.Store), _
  intro key bit s
  induction s with
  | nil =>
      simp [M8.TaggedStore.write, M8.TaggedStore.tapeBits]
  | cons r rs ih =>
      simp only [M8.TaggedStore.write]
      split
      · simp [M8.TaggedStore.tapeBits, M8.TaggedStore.recordBits]
      · constructor
        · simpa using congrArg (List.cons r.1) ih.1
        · change (M8.TaggedStore.recordBits r ++ M8.TaggedStore.tapeBits (M8.TaggedStore.write key bit rs).1).length = (M8.TaggedStore.recordBits r ++ M8.TaggedStore.tapeBits rs).length
          simpa only [List.length_append] using congrArg (fun n : ℕ => (M8.TaggedStore.recordBits r).length + n) ih.2

theorem M8.TaggedStore.indexed_read : ∀ (start i : ℕ) (mem : List Bool), (M8.TaggedStore.read (M8.TaggedStore.address (start+i)) (M8.TaggedStore.packFrom start mem)).1 = mem[i]? := by
  change ∀ (start i : ℕ) (mem : List Bool), (M8.TaggedStore.read (M8.TaggedStore.address (start + i)) (M8.TaggedStore.packFrom start mem)).1 = mem[i]?
  intro start i mem
  induction mem generalizing start i with
  | nil =>
      simp [M8.TaggedStore.packFrom, M8.TaggedStore.read]
  | cons b bs ih =>
      cases i with
      | zero =>
          have hc : (M8.TaggedStore.compare (M8.TaggedStore.address start) (M8.TaggedStore.address start)).1 = true := by
            simpa using (M8.TaggedStore.comparison_exact (M8.TaggedStore.address start) (M8.TaggedStore.address start)).1
          simp [M8.TaggedStore.packFrom, M8.TaggedStore.read, hc]
      | succ i =>
          have hne : M8.TaggedStore.address (start + Nat.succ i) ≠ M8.TaggedStore.address start := by
            intro h
            have := M8.TaggedStore.address_representation.1 h
            omega
          have hc : (M8.TaggedStore.compare (M8.TaggedStore.address (start + Nat.succ i)) (M8.TaggedStore.address start)).1 = false := by
            simpa [hne] using (M8.TaggedStore.comparison_exact (M8.TaggedStore.address (start + Nat.succ i)) (M8.TaggedStore.address start)).1
          have ht : (M8.TaggedStore.read (M8.TaggedStore.address (start + Nat.succ i)) (M8.TaggedStore.packFrom (start + 1) bs)).1 = bs[i]? := by
            rw [show start + Nat.succ i = (start + 1) + i by omega]
            exact ih (start + 1) i
          simpa [M8.TaggedStore.packFrom, M8.TaggedStore.read, hc] using ht

theorem M8.TaggedStore.indexed_write : ∀ (start i : ℕ) (bit : Bool) (mem : List Bool), (M8.TaggedStore.write (M8.TaggedStore.address (start+i)) bit (M8.TaggedStore.packFrom start mem)).1 = M8.TaggedStore.packFrom start (mem.set i bit) := by
  change ∀ (start i : ℕ) (bit : Bool) (mem : List Bool), (M8.TaggedStore.write (M8.TaggedStore.address (start + i)) bit (M8.TaggedStore.packFrom start mem)).1 = M8.TaggedStore.packFrom start (mem.set i bit)
  intro start i bit mem
  induction mem generalizing start i with
  | nil =>
      simp [M8.TaggedStore.packFrom, M8.TaggedStore.write]
  | cons b bs ih =>
      cases i with
      | zero =>
          simp [M8.TaggedStore.packFrom, M8.TaggedStore.write,
            (M8.TaggedStore.comparison_exact (M8.TaggedStore.address start) (M8.TaggedStore.address start)).1]
      | succ i =>
          have hne : M8.TaggedStore.address (start + Nat.succ i) ≠ M8.TaggedStore.address start := by
            intro h
            have he := M8.TaggedStore.address_representation.1 h
            omega
          have hc : (M8.TaggedStore.compare (M8.TaggedStore.address (start + Nat.succ i)) (M8.TaggedStore.address start)).1 = false := by
            rw [(M8.TaggedStore.comparison_exact _ _).1]
            simp [hne]
          have hshift : start + Nat.succ i = (start + 1) + i := by omega
          simpa [M8.TaggedStore.packFrom, M8.TaggedStore.write, hc, ← hshift] using
            congrArg (fun s : M8.TaggedStore.Store => (M8.TaggedStore.address start, b) :: s) (ih (start + 1) i)

theorem M8.TaggedStore.packed_layout : ∀ (start : ℕ) (mem : List Bool), (M8.TaggedStore.packFrom start mem).length = mem.length ∧ (∀ r ∈ M8.TaggedStore.packFrom start mem, r.1.length ≤ (start+mem.length).size) ∧ (M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom start mem)).length ≤ mem.length*(2*(start+mem.length).size+2) := by
  change ∀ (start : ℕ) (mem : List Bool), (M8.TaggedStore.packFrom start mem).length = mem.length ∧ (∀ r ∈ M8.TaggedStore.packFrom start mem, r.1.length ≤ (start + mem.length).size) ∧ (M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom start mem)).length ≤ mem.length * (2 * (start + mem.length).size + 2)
  have hrecord : ∀ (tag : List Bool) (bit : Bool), (M8.TaggedStore.recordBits (tag, bit)).length = 2 * tag.length + 2 := by
    intro tag bit
    induction tag with
    | nil => simp [M8.TaggedStore.recordBits]
    | cons a tag ih =>
      simp only [M8.TaggedStore.recordBits, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
      omega
  intro start mem
  induction mem generalizing start with
  | nil => simp [M8.TaggedStore.packFrom, M8.TaggedStore.tapeBits]
  | cons b bs ih =>
    rcases ih (start + 1) with ⟨hlen, htags, htape⟩
    have he : start + (bs.length + 1) = (start + 1) + bs.length := by omega
    have hs : start.size ≤ (start + (bs.length + 1)).size := Nat.size_le_size (by omega)
    constructor
    · simpa only [M8.TaggedStore.packFrom, List.length_cons] using congrArg Nat.succ hlen
    constructor
    · intro r hr
      simp only [M8.TaggedStore.packFrom, List.mem_cons] at hr
      rcases hr with hr | hr
      · subst r
        change (M8.TaggedStore.address start).length ≤ (start + (bs.length + 1)).size
        rw [M8.TaggedStore.address_representation.2]
        exact hs
      · simpa only [List.length_cons, he] using htags r hr
    · change (M8.TaggedStore.recordBits (M8.TaggedStore.address start, b) ++ M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom (start + 1) bs)).length ≤ (bs.length + 1) * (2 * (start + (bs.length + 1)).size + 2)
      rw [List.length_append, hrecord, M8.TaggedStore.address_representation.2]
      rw [← he] at htape
      nlinarith

theorem M8.TaggedStore.read_work : ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.read key s).2 ≤ s.length*(4*(B+1))+1 := by
  change ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.read key s).2 ≤ s.length * (4 * (B + 1)) + 1
  have hflat : ∀ t : List Bool, (t.flatMap (fun b => [true, b])).length = 2 * t.length := by
    intro t
    induction t with
    | nil => simp
    | cons b bs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
        omega
  intro B key s hk
  induction s with
  | nil => simp [M8.TaggedStore.read]
  | cons r rs ih =>
      intro hs
      have hr : r.1.length ≤ B := hs r (by simp)
      have ht : ∀ t ∈ rs, t.1.length ≤ B := by
        intro t ht
        exact hs t (by simp [ht])
      have hrest := ih ht
      have hc := (M8.TaggedStore.comparison_exact key r.1).2
      have hl : (M8.TaggedStore.recordBits r).length = 2 * r.1.length + 2 := by
        simp [M8.TaggedStore.recordBits, hflat]
      have hcharge : (M8.TaggedStore.recordBits r).length + (M8.TaggedStore.compare key r.1).2 + 1 ≤ 4 * (B + 1) := by
        omega
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      simp only [M8.TaggedStore.read]
      split <;> simp only [Prod.snd] <;> omega

theorem M8.TaggedStore.write_work : ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (bit : Bool) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.write key bit s).2 ≤ s.length*(4*(B+1))+1 := by
  change ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (bit : Bool) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.write key bit s).2 ≤ s.length * (4 * (B + 1)) + 1
  intro B key bit s hk
  have hflat : ∀ t : List Bool, (t.flatMap (fun b => [true, b])).length = 2 * t.length := by
    intro t
    induction t with
    | nil => simp
    | cons b t ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
        omega
  induction s with
  | nil =>
      intro hs
      simp [M8.TaggedStore.write]
  | cons r rs ih =>
      intro hs
      have hr : r.1.length ≤ B := hs r (by simp)
      have ht : ∀ x ∈ rs, x.1.length ≤ B := by
        intro x hx
        exact hs x (by simp [hx])
      have hi := ih ht
      have hc := (M8.TaggedStore.comparison_exact key r.1).2
      have hl : (M8.TaggedStore.recordBits r).length = 2 * r.1.length + 2 := by
        simp [M8.TaggedStore.recordBits, hflat]
      have hcharge : (M8.TaggedStore.recordBits r).length + (M8.TaggedStore.compare key r.1).2 + 1 ≤ 4 * (B + 1) := by
        omega
      simp only [M8.TaggedStore.write, List.length_cons, Nat.add_mul, Nat.one_mul]
      split <;> dsimp only <;> omega
#print axioms M8.TaggedStore.address_representation
#print axioms M8.TaggedStore.comparison_exact
#print axioms M8.TaggedStore.indexed_read
#print axioms M8.TaggedStore.indexed_write
#print axioms M8.TaggedStore.packed_layout
#print axioms M8.TaggedStore.read_work
#print axioms M8.TaggedStore.write_layout
#print axioms M8.TaggedStore.write_work
