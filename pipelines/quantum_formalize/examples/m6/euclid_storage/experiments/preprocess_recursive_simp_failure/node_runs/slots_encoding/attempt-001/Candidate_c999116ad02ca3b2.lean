import FrozenTarget_c999116ad02ca3b2
theorem M6.EuclidStorage.slots_encoding : QuantumHarnessFrozenTarget := by
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
