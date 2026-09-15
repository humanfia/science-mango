import M7QuerySectors

noncomputable def M7.QuerySectorsTarget.all_sound : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N → F.Monic ∧ F ∣ M6.Cyclic.modulus N

noncomputable def M7.QuerySectorsTarget.all_complete : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → F ∈ M7.QuerySectors.allSectors N

noncomputable def M7.QuerySectorsTarget.all_membership : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N ↔ F.Monic ∧ F ∣ M6.Cyclic.modulus N

noncomputable def M7.QuerySectorsTarget.effective_valid : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ q : M7.DefaultQuery.Query, M7.DefaultQuery.valid N q → M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q)

noncomputable def M7.QuerySectorsTarget.signature_allowed : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (q : M7.DefaultQuery.Query) (c : M7.Action.Recipe N), M7.DefaultQuery.signature c ∈ M7.QuerySectors.effective N q ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature c)

