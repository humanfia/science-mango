import M6EuclidAccepted
import M6EuclidStorage

theorem M6.EuclidStorage.control_encoding : ∀ (width v : ℕ), v ≤ 32*width → v < 2 ^ (M6.EuclidStorage.registerBits width) := by
  change ∀ (width v : ℕ), v ≤ 32 * width → v < 2 ^ (M6.EuclidStorage.registerBits width)
  intro width v hv
  have h : width < 2 ^ width := Nat.lt_two_pow_self
  change v < 2 ^ (width + 5)
  rw [pow_add]
  norm_num
  omega

theorem M6.EuclidStorage.layout_bound : ∀ N : ℕ, M6.EuclidStorage.polynomialSlots.length = 4 ∧ M6.EuclidStorage.controlSlots.length = 16 ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512*(N+1)^2 := by
  change ∀ N : ℕ, M6.EuclidStorage.polynomialSlots.length = 4 ∧ M6.EuclidStorage.controlSlots.length = 16 ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512 * (N + 1) ^ 2
  intro N
  refine ⟨rfl, rfl, ?_⟩
  norm_num [M6.EuclidStorage.actualPreprocessStorage, M6.EuclidStorage.registerBits, M6.EuclidStorage.polynomialSlots, M6.EuclidStorage.controlSlots] <;> nlinarith [Nat.zero_le (N * N)]

theorem M6.EuclidStorage.rem_loop_refines : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t
      simp [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
  | succ fuel ih =>
      intro s c t
      simp only [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
      split <;> simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem M6.EuclidStorage.slots_encoding : ∀ (N : ℕ) (s u : M6.EuclidStorage.Slots), M6.EuclidStorage.slotsFit (N+1) s → M6.EuclidStorage.slotsFit (N+1) u → M6.Euclid.dense N s.p = M6.Euclid.dense N u.p → M6.Euclid.dense N s.q = M6.Euclid.dense N u.q → M6.Euclid.dense N s.work = M6.Euclid.dense N u.work → M6.Euclid.dense N s.saved = M6.Euclid.dense N u.saved → s = u := by
  intro N s u hs hu hp hq hw hm
  rcases hs with ⟨hsp, hsq, hsw, hsm⟩
  rcases hu with ⟨hup, huq, huw, hum⟩
  have ep := M6.Euclid.dense_injective N s.p u.p hsp hup hp
  have eq := M6.Euclid.dense_injective N s.q u.q hsq huq hq
  have ew := M6.Euclid.dense_injective N s.work u.work hsw huw hw
  have em := M6.Euclid.dense_injective N s.saved u.saved hsm hum hm
  cases s
  cases u
  simp_all

theorem M6.EuclidStorage.control_values_fit : ∀ (width : ℕ) (s : M6.EuclidStorage.Slots) (fuel c e t : ℕ), M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c ≤ 32*width → e ≤ 32*width → t ≤ 32*width → ∀ v ∈ M6.EuclidStorage.controlValues s fuel c e t, v < 2 ^ (M6.EuclidStorage.registerBits width) := by
  change ∀ (width : ℕ) (s : M6.EuclidStorage.Slots) (fuel c e t : ℕ), M6.EuclidStorage.slotsFit width s → fuel ≤ 32 * width → c ≤ 32 * width → e ≤ 32 * width → t ≤ 32 * width → ∀ v ∈ M6.EuclidStorage.controlValues s fuel c e t, v < 2 ^ M6.EuclidStorage.registerBits width
  intro width s fuel c e t hs hf hc he ht v hv
  apply M6.EuclidStorage.control_encoding width v
  simp only [M6.EuclidStorage.slotsFit, M6.Euclid.rank] at hs
  simp only [M6.EuclidStorage.controlValues, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, M6.Euclid.rank] at hv
  split_ifs at hs hv <;> simp_all <;> omega

theorem M6.EuclidStorage.gcd_loop_refines : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t : ℕ), s.work = 0 → let r := M6.EuclidStorage.gcdLoop fuel s c e t; r.slots.saved = s.saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclidAux fuel s.p s.q) c e t := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t : ℕ), s.work = 0 → let r := M6.EuclidStorage.gcdLoop fuel s c e t; r.slots.saved = s.saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclidAux fuel s.p s.q) c e t
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t hw
      simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
        M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hw]
  | succ fuel ih =>
      intro s c e t hw
      by_cases hq : s.q = 0
      · simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hq, hw]
      · have hr := fun (c t : ℕ) =>
          M6.EuclidStorage.rem_loop_refines (M6.Euclid.rank s.p)
            (⟨0, s.q, s.p, s.saved⟩ : M6.EuclidStorage.Slots) c t
        dsimp only at hr
        simp only [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          hq, if_false]
        simp only [M6.Euclid.remainder, hr, ih]
        simp [M6.EuclidStorage.offset, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]

theorem M6.EuclidStorage.gcd_start_refines : ∀ (p q saved : M6.Euclid.BP) (c e t : ℕ), let r := M6.EuclidStorage.gcdStart p q saved c e t; r.slots.saved = saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclid p q) c e t := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (p q saved : M6.Euclid.BP) (c e t : ℕ), let r := M6.EuclidStorage.gcdStart p q saved c e t; r.slots.saved = saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclid p q) c e t
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro p q saved c e t
  simpa [M6.EuclidStorage.gcdStart, M6.Euclid.euclid,
    M6.EuclidStorage.offset, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (M6.EuclidStorage.gcd_loop_refines (M6.Euclid.rank q + 1)
      (⟨p, q, 0, saved⟩ : M6.EuclidStorage.Slots) c e (t + 1) rfl)

theorem M6.EuclidStorage.preprocess_refines : ∀ a b M : M6.Euclid.BP, M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ a b M : M6.Euclid.BP, M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro a b M
  have hfirst := M6.EuclidStorage.gcd_start_refines a b M 0 0 0
  have hs := hfirst.1
  have hv := congrArg M6.Euclid.Run.value hfirst.2.2
  have hc := congrArg M6.Euclid.Run.cancellations hfirst.2.2
  have he := congrArg M6.Euclid.Run.rounds hfirst.2.2
  have ht := congrArg M6.Euclid.Run.passes hfirst.2.2
  simp only [M6.EuclidStorage.toRun, M6.EuclidStorage.offset,
    Nat.zero_add, Nat.add_zero] at hv hc he ht
  have hsecond := fun p q saved c e t =>
    (M6.EuclidStorage.gcd_start_refines p q saved c e t).2.2
  dsimp only [M6.EuclidStorage.preprocess]
  rw [hsecond]
  simp [M6.Euclid.preprocess, M6.EuclidStorage.offset,
    hs, hv, hc, he, ht, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
#print axioms M6.EuclidStorage.control_encoding
#print axioms M6.EuclidStorage.control_values_fit
#print axioms M6.EuclidStorage.layout_bound
#print axioms M6.EuclidStorage.rem_loop_refines
#print axioms M6.EuclidStorage.gcd_loop_refines
#print axioms M6.EuclidStorage.gcd_start_refines
#print axioms M6.EuclidStorage.preprocess_refines
#print axioms M6.EuclidStorage.slots_encoding
