import FrozenTarget_024155abab2eab0b
theorem M5.Packing.packed_value_injective : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r)
  intro w T r i j h
  have hrval : (r i).val = (r j).val := by
    have hm := congrArg (fun n : ℕ => n % T) h
    simpa only [M5.Packing.packed_value_mod] using hm
  have hr : r i = r j := Fin.ext hrval
  have hT : 0 < T := lt_of_le_of_lt (Nat.zero_le _) (r i).isLt
  have hmul : T * M5.Packing.occurrenceTag r i = T * M5.Packing.occurrenceTag r j := by
    unfold M5.Packing.packedValue at h
    nlinarith [hrval]
  have htag : M5.Packing.occurrenceTag r i = M5.Packing.occurrenceTag r j :=
    Nat.eq_of_mul_eq_mul_left hT hmul
  rcases lt_trichotomy i j with hij | hij | hji
  · have hs := M5.Packing.equal_residue_tag_strict w T r i j hij hr
    omega
  · exact hij
  · have hs := M5.Packing.equal_residue_tag_strict w T r j i hji hr.symm
    omega
