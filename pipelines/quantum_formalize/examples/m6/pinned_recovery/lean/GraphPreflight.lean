import M6Pinned

noncomputable def M6.PinnedTarget.weight_bound : Prop :=
  ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m

#check M6.PinnedTarget.weight_bound

noncomputable def M6.PinnedTarget.agrees_pin : Prop :=
  ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Pinned.Vector m) (i : Fin m) (b : ZMod 2), P i = none → (M6.Pinned.agrees (M6.Pinned.pin P i b) v ↔ M6.Pinned.agrees P v ∧ v i = b)

#check M6.PinnedTarget.agrees_pin

noncomputable def M6.PinnedTarget.enumerator_coeff : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d

#check M6.PinnedTarget.enumerator_coeff

noncomputable def M6.PinnedTarget.count_nonnegative_positive : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), 0 ≤ M6.Pinned.count L P d ∧ (0 < M6.Pinned.count L P d ↔ ∃ v ∈ L, M6.Pinned.agrees P v ∧ M6.Pinned.weight v = d)

#check M6.PinnedTarget.count_nonnegative_positive

noncomputable def M6.PinnedTarget.count_pin_partition : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ), M6.Pinned.partitions (fun P => M6.Pinned.count L P d)

#check M6.PinnedTarget.count_pin_partition

noncomputable def M6.PinnedTarget.decode_unique : Prop :=
  ∀ (m : ℕ) (P : M6.Pinned.Pins m), M6.Pinned.assigned P → ∀ v : M6.Pinned.Vector m, (M6.Pinned.agrees P v ↔ v = M6.Pinned.decode P)

#check M6.PinnedTarget.decode_unique

noncomputable def M6.PinnedTarget.distance_spec : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), (M6.Pinned.distance L = none ↔ L = ∅) ∧ ∀ d : ℕ, (M6.Pinned.distance L = some d ↔ (∃ v ∈ L, M6.Pinned.weight v = d) ∧ ∀ v ∈ L, d ≤ M6.Pinned.weight v)

#check M6.PinnedTarget.distance_spec

noncomputable def M6.PinnedTarget.first_positive_distance : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), M6.Pinned.firstPositive m (M6.Pinned.enumerator L (M6.Pinned.free m)) = M6.Pinned.distance L

#check M6.PinnedTarget.first_positive_distance

noncomputable def M6.PinnedTarget.choose_properties : Prop :=
  ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (i : Fin m), M6.Pinned.refines P (M6.Pinned.choose c P i).1 ∧ (M6.Pinned.choose c P i).1 i ≠ none ∧ (M6.Pinned.choose c P i).2 ≤ 1

#check M6.PinnedTarget.choose_properties

noncomputable def M6.PinnedTarget.recover_properties : Prop :=
  ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (xs : List (Fin m)), M6.Pinned.refines P (M6.Pinned.recover c P xs).1 ∧ (∀ i ∈ xs, (M6.Pinned.recover c P xs).1 i ≠ none) ∧ (M6.Pinned.recover c P xs).2 ≤ xs.length

#check M6.PinnedTarget.recover_properties

noncomputable def M6.PinnedTarget.recover_positive : Prop :=
  ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ), M6.Pinned.partitions c → ∀ (P : M6.Pinned.Pins m) (xs : List (Fin m)), 0 < c P → 0 < c (M6.Pinned.recover c P xs).1

#check M6.PinnedTarget.recover_positive

noncomputable def M6.PinnedTarget.recover_from_counts : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ) (c : M6.Pinned.Pins m → ℤ), (∀ P, c P = M6.Pinned.count L P d) → 0 < c (M6.Pinned.free m) → let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m); M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m

#check M6.PinnedTarget.recover_from_counts

noncomputable def M6.PinnedTarget.solve_exact : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (Q : M6.Pinned.Pins m → Polynomial ℤ), (∀ P, Q P = M6.Pinned.enumerator L P) → (M6.Pinned.solve Q = none ↔ L = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve Q = some (d, v, k) → v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m

#check M6.PinnedTarget.solve_exact

noncomputable def M6.PinnedTarget.minimum_witness : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), L.Nonempty → ∃ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve (M6.Pinned.enumerator L) = some (d, v, k) ∧ v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m

#check M6.PinnedTarget.minimum_witness

