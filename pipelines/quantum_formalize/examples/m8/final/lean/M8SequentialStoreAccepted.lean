import M8SequentialStore

theorem M8.SequentialStore.access_envelope : ∀ (N : ℕ) [NeZero N], M8.SequentialStore.accessCharge N ≤ 3000000*(N+1)^6 := by
  change ∀ (N : ℕ) [NeZero N], M8.SequentialStore.accessCharge N ≤ 3000000 * (N + 1)^6
  intro N _
  let n := N + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hs : M8.SequentialStore.slots N ≤ 20000 * n^3 := by
    exact M8.BankLayout.payload_bound N
  have hb : M8.SequentialStore.addressBits N ≤ 32 * n := by
    exact M8.BankLayout.address_bits_bound N
  have hf : 4 * (M8.SequentialStore.addressBits N + 1) ≤ 132 * n := by
    omega
  have h2 : 1 ≤ n^2 := by
    have h := pow_pos hn 2
    omega
  have h4 : 1 ≤ n^4 := by
    have h := pow_pos hn 4
    omega
  have h46 : n^4 ≤ n^6 := by
    calc
      n^4 = n^4 * 1 := by simp
      _ ≤ n^4 * n^2 := Nat.mul_le_mul_left _ h2
      _ = n^6 := by ring
  change M8.SequentialStore.slots N * (4 * (M8.SequentialStore.addressBits N + 1)) + 1 ≤ 3000000 * n^6
  calc
    M8.SequentialStore.slots N * (4 * (M8.SequentialStore.addressBits N + 1)) + 1
        ≤ (20000 * n^3) * (132 * n) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul hs hf) 1
    _ = 2640000 * n^4 + 1 := by ring
    _ ≤ 3000000 * n^6 := by omega

theorem M8.SequentialStore.allocation_access : ∀ (N : ℕ) [NeZero N], ∀ (mem : List Bool), mem.length = M8.SequentialStore.slots N → ∀ (i : Fin (M8.SequentialStore.slots N)) (bit : Bool), (M8.TaggedStore.read (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem)).1 = mem[i.val]? ∧ (M8.TaggedStore.write (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem)).1 = M8.TaggedStore.packFrom 0 (mem.set i.val bit) ∧ (M8.TaggedStore.read (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem)).2 ≤ M8.SequentialStore.accessCharge N ∧ (M8.TaggedStore.write (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem)).2 ≤ M8.SequentialStore.accessCharge N := by
  intro N inst mem hmem i bit
  have layout := M8.TaggedStore.packed_layout 0 mem
  have hkey : (M8.TaggedStore.address i.val).length ≤ (M8.SequentialStore.slots N).size := by
    rw [M8.TaggedStore.address_representation.2]
    exact Nat.size_le_size (Nat.le_of_lt i.isLt)
  have htags : ∀ r ∈ M8.TaggedStore.packFrom 0 mem, r.1.length ≤ (M8.SequentialStore.slots N).size := by
    simpa only [Nat.zero_add, hmem] using layout.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using M8.TaggedStore.indexed_read 0 i.val mem
  · simpa only [Nat.zero_add] using M8.TaggedStore.indexed_write 0 i.val bit mem
  · simpa only [M8.SequentialStore.accessCharge, M8.SequentialStore.addressBits, layout.1, hmem] using
      M8.TaggedStore.read_work (M8.SequentialStore.slots N).size (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem) hkey htags
  · simpa only [M8.SequentialStore.accessCharge, M8.SequentialStore.addressBits, layout.1, hmem] using
      M8.TaggedStore.write_work (M8.SequentialStore.slots N).size (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem) hkey htags

theorem M8.SequentialStore.store_space : ∀ (N : ℕ) [NeZero N], ∀ mem : List Bool, mem.length = M8.SequentialStore.slots N → M8.SequentialStore.storeSpace N mem ≤ 2000000*(N+1)^4 := by
  intro N inst mem hmem
  have hp : M8.SequentialStore.slots N ≤ 20000 * (N + 1)^3 := by
    simpa only [M8.SequentialStore.slots] using M8.BankLayout.payload_bound N
  have ha : M8.SequentialStore.addressBits N ≤ 32 * (N + 1) := by
    simpa only [M8.SequentialStore.addressBits, M8.SequentialStore.slots] using M8.BankLayout.address_bits_bound N
  have ht : (M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom 0 mem)).length ≤
      M8.SequentialStore.slots N * (2 * M8.SequentialStore.addressBits N + 2) := by
    simpa only [Nat.zero_add, hmem, M8.SequentialStore.addressBits] using
      (M8.TaggedStore.packed_layout 0 mem).2.2
  change (M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom 0 mem)).length +
      (4 * (M8.SequentialStore.addressBits N + 1) + 32) ≤ 2000000 * (N + 1)^4
  calc
    _ ≤ M8.SequentialStore.slots N * (2 * M8.SequentialStore.addressBits N + 2) +
        (4 * (M8.SequentialStore.addressBits N + 1) + 32) := Nat.add_le_add_right ht _
    _ ≤ (20000 * (N + 1)^3) * (2 * (32 * (N + 1)) + 2) +
        (4 * (32 * (N + 1) + 1) + 32) := by
      gcongr <;> assumption
    _ ≤ 2000000 * (N + 1)^4 := by
      nlinarith only [Nat.zero_le N, Nat.zero_le (N^2), Nat.zero_le (N^3), Nat.zero_le (N^4)]

theorem M8.SequentialStore.tag_setup_bound : ∀ (N : ℕ) [NeZero N], M8.SequentialStore.tagSetupCharge N ≤ 11000000*(N+1)^6 := by
  change ∀ (N : ℕ) [NeZero N], M8.SequentialStore.tagSetupCharge N ≤ 11000000 * (N + 1)^6
  intro N inst
  let n := N + 1
  let S := M8.SequentialStore.slots N
  let B := S.size
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hs : S ≤ 20000 * n^3 := M8.BankLayout.payload_bound N
  have hb : B ≤ 32 * n := M8.BankLayout.address_bits_bound N
  have hfold : ∀ (l : List ℕ) (total : ℕ),
      (∀ i ∈ l, (M8.TaggedStore.address i).length ≤ B) →
      l.foldl (fun total i => total + 16 * ((M8.TaggedStore.address i).length + 1)) total ≤
        total + l.length * (16 * (B + 1)) := by
    intro l
    induction l with
    | nil =>
        intro total h
        simp
    | cons i l ih =>
        intro total h
        have hi := h i (by simp)
        have ht := ih (total + 16 * ((M8.TaggedStore.address i).length + 1))
          (by
            intro j hj
            exact h j (by simp [hj]))
        simp only [List.foldl_cons, List.length_cons]
        nlinarith
  have hcharge : M8.SequentialStore.tagSetupCharge N ≤ S * (16 * (B + 1)) + 32 := by
    have h := hfold (List.range S) 0 (by
      intro i hi
      rw [M8.TaggedStore.address_representation.2 i]
      exact Nat.size_le_size (Nat.le_of_lt (List.mem_range.mp hi)))
    simp only [List.length_range, zero_add] at h
    exact Nat.add_le_add_right h 32
  have hprod : S * (16 * (B + 1)) ≤ (20000 * n^3) * (16 * (32 * n + 1)) := by
    apply Nat.mul_le_mul hs
    omega
  have h34 : n^3 ≤ n^4 := by
    calc
      n^3 = n^3 * 1 := by simp
      _ ≤ n^3 * n := Nat.mul_le_mul_left _ hn
      _ = n^4 := by ring
  have h46 : n^4 ≤ n^6 := by
    have h2 : 1 ≤ n^2 := by nlinarith
    calc
      n^4 = n^4 * 1 := by simp
      _ ≤ n^4 * n^2 := Nat.mul_le_mul_left _ h2
      _ = n^6 := by ring
  have h6 : 1 ≤ n^6 := by
    have hp : 0 < n^6 := pow_pos (by omega) _
    omega
  change M8.SequentialStore.tagSetupCharge N ≤ 11000000 * n^6
  nlinarith [hcharge, hprod, h34, h46, h6]
#print axioms M8.SequentialStore.access_envelope
#print axioms M8.SequentialStore.allocation_access
#print axioms M8.SequentialStore.store_space
#print axioms M8.SequentialStore.tag_setup_bound
