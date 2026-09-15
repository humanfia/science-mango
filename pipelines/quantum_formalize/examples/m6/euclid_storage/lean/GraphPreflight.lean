import M6EuclidStorage
import M6EuclidAccepted

noncomputable def M6.EuclidStorageTarget.rem_loop_refines : Prop :=
  ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes

#check M6.EuclidStorageTarget.rem_loop_refines

noncomputable def M6.EuclidStorageTarget.gcd_loop_refines : Prop :=
  ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t : ℕ), s.work = 0 → let r := M6.EuclidStorage.gcdLoop fuel s c e t; r.slots.saved = s.saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclidAux fuel s.p s.q) c e t

#check M6.EuclidStorageTarget.gcd_loop_refines

noncomputable def M6.EuclidStorageTarget.gcd_start_refines : Prop :=
  ∀ (p q saved : M6.Euclid.BP) (c e t : ℕ), let r := M6.EuclidStorage.gcdStart p q saved c e t; r.slots.saved = saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclid p q) c e t

#check M6.EuclidStorageTarget.gcd_start_refines

noncomputable def M6.EuclidStorageTarget.preprocess_refines : Prop :=
  ∀ a b M : M6.Euclid.BP, M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M

#check M6.EuclidStorageTarget.preprocess_refines

noncomputable def M6.EuclidStorageTarget.rem_loop_safe : Prop :=
  ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ≤ 32*width → t + (M6.Euclid.remainderAux fuel s.work s.q).passes ≤ 32*width → M6.EuclidStorage.remSafe fuel s c t width

#check M6.EuclidStorageTarget.rem_loop_safe

noncomputable def M6.EuclidStorageTarget.gcd_loop_safe : Prop :=
  ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → s.work = 0 → fuel ≤ 32*width → c + (M6.Euclid.euclidAux fuel s.p s.q).cancellations ≤ 32*width → e + (M6.Euclid.euclidAux fuel s.p s.q).rounds ≤ 32*width → t + (M6.Euclid.euclidAux fuel s.p s.q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe fuel s c e t width

#check M6.EuclidStorageTarget.gcd_loop_safe

noncomputable def M6.EuclidStorageTarget.gcd_start_safe : Prop :=
  ∀ (p q saved : M6.Euclid.BP) (c e t width : ℕ), 0 < width → M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.rank saved ≤ width → c + (M6.Euclid.euclid p q).cancellations ≤ 32*width → e + (M6.Euclid.euclid p q).rounds ≤ 32*width → t + (M6.Euclid.euclid p q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe (M6.Euclid.rank q+1) ⟨p,q,0,saved⟩ c e (t+1) width

#check M6.EuclidStorageTarget.gcd_start_safe

noncomputable def M6.EuclidStorageTarget.preprocess_safe : Prop :=
  ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → M6.EuclidStorage.preprocessSafe (N+1) a b M

#check M6.EuclidStorageTarget.preprocess_safe

noncomputable def M6.EuclidStorageTarget.slots_encoding : Prop :=
  ∀ (N : ℕ) (s u : M6.EuclidStorage.Slots), M6.EuclidStorage.slotsFit (N+1) s → M6.EuclidStorage.slotsFit (N+1) u → M6.Euclid.dense N s.p = M6.Euclid.dense N u.p → M6.Euclid.dense N s.q = M6.Euclid.dense N u.q → M6.Euclid.dense N s.work = M6.Euclid.dense N u.work → M6.Euclid.dense N s.saved = M6.Euclid.dense N u.saved → s = u

#check M6.EuclidStorageTarget.slots_encoding

noncomputable def M6.EuclidStorageTarget.control_encoding : Prop :=
  ∀ (width v : ℕ), v ≤ 32*width → v < 2 ^ (M6.EuclidStorage.registerBits width)

#check M6.EuclidStorageTarget.control_encoding

noncomputable def M6.EuclidStorageTarget.control_values_fit : Prop :=
  ∀ (width : ℕ) (s : M6.EuclidStorage.Slots) (fuel c e t : ℕ), M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c ≤ 32*width → e ≤ 32*width → t ≤ 32*width → ∀ v ∈ M6.EuclidStorage.controlValues s fuel c e t, v < 2 ^ (M6.EuclidStorage.registerBits width)

#check M6.EuclidStorageTarget.control_values_fit

noncomputable def M6.EuclidStorageTarget.layout_bound : Prop :=
  ∀ N : ℕ, M6.EuclidStorage.polynomialSlots.length = 4 ∧ M6.EuclidStorage.controlSlots.length = 16 ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512*(N+1)^2

#check M6.EuclidStorageTarget.layout_bound

noncomputable def M6.EuclidStorageTarget.preprocess_storage : Prop :=
  ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M ∧ M6.EuclidStorage.preprocessSafe (N+1) a b M ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512*(N+1)^2

#check M6.EuclidStorageTarget.preprocess_storage

