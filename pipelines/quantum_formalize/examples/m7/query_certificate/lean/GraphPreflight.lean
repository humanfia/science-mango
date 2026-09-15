import M7QueryCertificate
import M7GlobalQueryAccepted

noncomputable def M7.QueryCertificateTarget.winner_pass_spec : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W : Finset (M7.GlobalQuery.Index H N)) (dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N)), (M7.QueryCertificate.winnerPass q bases W dominator = true ↔ (∀ x ∈ W, M7.GlobalQuery.feasible q bases x ∧ ∀ y : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases y → ¬ M7.QueryCertificate.strictBetter q bases y x) ∧ (∀ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases x → x ∉ W → ∃ y : M7.GlobalQuery.Index H N, dominator x = some y ∧ y ∈ W ∧ M7.QueryCertificate.strictBetter q bases y x))

#check M7.QueryCertificateTarget.winner_pass_spec

noncomputable def M7.QueryCertificateTarget.winner_pass_sound : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W : Finset (M7.GlobalQuery.Index H N)) (dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N)), M7.QueryCertificate.winnerPass q bases W dominator = true → W = M7.GlobalQuery.winners q bases

#check M7.QueryCertificateTarget.winner_pass_sound

noncomputable def M7.QueryCertificateTarget.winner_pass_complete : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∃ dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N), M7.QueryCertificate.winnerPass q bases (M7.GlobalQuery.winners q bases) dominator = true

#check M7.QueryCertificateTarget.winner_pass_complete

noncomputable def M7.QueryCertificateTarget.presentation_pass_spec : Prop :=
  ∀ (H N : ℕ) [NeZero N] (bases : M7.GlobalQuery.Family H N) (W P : Finset (M7.GlobalQuery.Index H N)), (M7.QueryCertificate.presentationPass bases W P = true ↔ ∀ x : M7.GlobalQuery.Index H N, x ∈ P ↔ x ∈ W ∧ M7.QueryCertificate.isLeast bases x)

#check M7.QueryCertificateTarget.presentation_pass_spec

noncomputable def M7.QueryCertificateTarget.invalid_rule : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : M7.QueryCertificate.Certificate H N), (M7.QueryCertificate.check q bases certificate = Except.error M7.DefaultQuery.QueryError.invalidSignature ↔ ¬ M7.DefaultQuery.valid N q) ∧ (M7.DefaultQuery.valid N q → M7.QueryCertificate.check q bases certificate = Except.ok (M7.QueryCertificate.winnerPass q bases certificate.winners certificate.dominator && M7.QueryCertificate.presentationPass bases certificate.winners certificate.presentations))

#check M7.QueryCertificateTarget.invalid_rule

noncomputable def M7.QueryCertificateTarget.check_sound : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : M7.QueryCertificate.Certificate H N), M7.QueryCertificate.check q bases certificate = Except.ok true → M7.DefaultQuery.valid N q ∧ certificate.winners = M7.GlobalQuery.winners q bases ∧ certificate.presentations = M7.QueryCertificate.allPresentations q bases

#check M7.QueryCertificateTarget.check_sound

noncomputable def M7.QueryCertificateTarget.check_complete : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), M7.DefaultQuery.valid N q → ∃ dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N), M7.QueryCertificate.check q bases (⟨M7.GlobalQuery.winners q bases, M7.QueryCertificate.allPresentations q bases, dominator⟩ : M7.QueryCertificate.Certificate H N) = Except.ok true

#check M7.QueryCertificateTarget.check_complete

noncomputable def M7.QueryCertificateTarget.check_exact : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W P : Finset (M7.GlobalQuery.Index H N)), ((∃ dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N), M7.QueryCertificate.check q bases (⟨W, P, dominator⟩ : M7.QueryCertificate.Certificate H N) = Except.ok true) ↔ M7.DefaultQuery.valid N q ∧ W = M7.GlobalQuery.winners q bases ∧ P = M7.QueryCertificate.allPresentations q bases)

#check M7.QueryCertificateTarget.check_exact

