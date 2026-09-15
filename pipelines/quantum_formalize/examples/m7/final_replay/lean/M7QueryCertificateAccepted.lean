import M7GlobalQueryAccepted
import M7QueryCertificate

theorem M7.QueryCertificate.invalid_rule : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : M7.QueryCertificate.Certificate H N), (M7.QueryCertificate.check q bases certificate = Except.error M7.DefaultQuery.QueryError.invalidSignature ↔ ¬ M7.DefaultQuery.valid N q) ∧ (M7.DefaultQuery.valid N q → M7.QueryCertificate.check q bases certificate = Except.ok (M7.QueryCertificate.winnerPass q bases certificate.winners certificate.dominator && M7.QueryCertificate.presentationPass bases certificate.winners certificate.presentations)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : M7.QueryCertificate.Certificate H N), (M7.QueryCertificate.check q bases certificate = Except.error M7.DefaultQuery.QueryError.invalidSignature ↔ ¬ M7.DefaultQuery.valid N q) ∧ (M7.DefaultQuery.valid N q → M7.QueryCertificate.check q bases certificate = Except.ok (M7.QueryCertificate.winnerPass q bases certificate.winners certificate.dominator && M7.QueryCertificate.presentationPass bases certificate.winners certificate.presentations))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases certificate
  classical
  by_cases h : M7.DefaultQuery.valid N q
  <;> simp [M7.QueryCertificate.check, h]

theorem M7.QueryCertificate.presentation_pass_spec : ∀ (H N : ℕ) [NeZero N] (bases : M7.GlobalQuery.Family H N) (W P : Finset (M7.GlobalQuery.Index H N)), (M7.QueryCertificate.presentationPass bases W P = true ↔ ∀ x : M7.GlobalQuery.Index H N, x ∈ P ↔ x ∈ W ∧ M7.QueryCertificate.isLeast bases x) := by
  intro H N inst bases W P
  classical
  simp only [M7.QueryCertificate.presentationPass, M7.QueryCertificate.allOn,
    Bool.and_eq_true, List.all_eq_true, Finset.mem_toList, decide_eq_true_eq]
  change ((∀ x, x ∈ P → x ∈ W ∧ M7.QueryCertificate.isLeast bases x) ∧
    (∀ x, x ∈ W → M7.QueryCertificate.isLeast bases x → x ∈ P)) ↔
    ∀ x, x ∈ P ↔ x ∈ W ∧ M7.QueryCertificate.isLeast bases x
  constructor
  · rintro ⟨hP, hW⟩ x
    exact ⟨hP x, fun h => hW x h.1 h.2⟩
  · intro h
    constructor
    · intro x hx
      exact (h x).mp hx
    · intro x hx hl
      exact (h x).mpr ⟨hx, hl⟩

theorem M7.QueryCertificate.winner_pass_spec : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W : Finset (M7.GlobalQuery.Index H N)) (dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N)), (M7.QueryCertificate.winnerPass q bases W dominator = true ↔ (∀ x ∈ W, M7.GlobalQuery.feasible q bases x ∧ ∀ y : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases y → ¬ M7.QueryCertificate.strictBetter q bases y x) ∧ (∀ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases x → x ∉ W → ∃ y : M7.GlobalQuery.Index H N, dominator x = some y ∧ y ∈ W ∧ M7.QueryCertificate.strictBetter q bases y x)) := by
  classical
  intro H N inst q bases W dominator
  simp only [M7.QueryCertificate.winnerPass, M7.QueryCertificate.allOn,
    List.all_eq_true, Finset.mem_toList, Bool.and_eq_true,
    decide_eq_true_eq, Finset.mem_univ, forall_const]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro x
  by_cases hf : M7.GlobalQuery.feasible q bases x
  · by_cases hw : x ∈ W
    · simp [hf, hw]
    · cases hd : dominator x <;> simp [hf, hw, hd]
  · simp [hf]

theorem M7.QueryCertificate.winner_pass_complete : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∃ dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N), M7.QueryCertificate.winnerPass q bases (M7.GlobalQuery.winners q bases) dominator = true := by
  classical
  intro H N inst q bases
  have hd : ∀ x : M7.GlobalQuery.Index H N,
      M7.GlobalQuery.feasible q bases x ∧ x ∉ M7.GlobalQuery.winners q bases →
      ∃ y ∈ M7.GlobalQuery.winners q bases, M7.QueryCertificate.strictBetter q bases y x := by
    intro x hx
    exact M7.GlobalQuery.strict_dominator H N q bases x hx.1 hx.2
  let dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N) :=
    fun x => if hx : M7.GlobalQuery.feasible q bases x ∧ x ∉ M7.GlobalQuery.winners q bases
      then some (Classical.choose (hd x hx)) else none
  refine ⟨dominator, ?_⟩
  apply (M7.QueryCertificate.winner_pass_spec H N q bases
    (M7.GlobalQuery.winners q bases) dominator).2
  constructor
  · intro x hx
    exact ((M7.GlobalQuery.winners_exact H N q bases).1 x).1 hx
  · intro x hf hw
    have hx : M7.GlobalQuery.feasible q bases x ∧ x ∉ M7.GlobalQuery.winners q bases := ⟨hf, hw⟩
    refine ⟨Classical.choose (hd x hx), ?_, Classical.choose_spec (hd x hx)⟩
    simp only [dominator, dif_pos hx]

theorem M7.QueryCertificate.winner_pass_sound : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W : Finset (M7.GlobalQuery.Index H N)) (dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N)), M7.QueryCertificate.winnerPass q bases W dominator = true → W = M7.GlobalQuery.winners q bases := by
  classical
  intro H N inst q bases W dominator hpass
  rcases (M7.QueryCertificate.winner_pass_spec H N q bases W dominator).mp hpass with ⟨hclaimed, hdominator⟩
  have hexact := (M7.GlobalQuery.winners_exact H N q bases).1
  apply Finset.ext
  intro x
  constructor
  · intro hx
    apply (hexact x).mpr
    simpa only [M7.QueryCertificate.strictBetter] using hclaimed x hx
  · intro hx
    by_contra hmissing
    have hwin := (hexact x).mp hx
    rcases hdominator x hwin.1 hmissing with ⟨y, hlookup, hy, hbetter⟩
    apply hwin.2 y (hclaimed y hy).1
    simpa only [M7.QueryCertificate.strictBetter] using hbetter

theorem M7.QueryCertificate.check_complete : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), M7.DefaultQuery.valid N q → ∃ dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N), M7.QueryCertificate.check q bases (⟨M7.GlobalQuery.winners q bases, M7.QueryCertificate.allPresentations q bases, dominator⟩ : M7.QueryCertificate.Certificate H N) = Except.ok true := by
  classical
  intro H N inst q bases hvalid
  obtain ⟨dominator, hwin⟩ := M7.QueryCertificate.winner_pass_complete H N q bases
  have hpres : M7.QueryCertificate.presentationPass bases
      (M7.GlobalQuery.winners q bases)
      (M7.QueryCertificate.allPresentations q bases) = true := by
    apply (M7.QueryCertificate.presentation_pass_spec H N bases
      (M7.GlobalQuery.winners q bases)
      (M7.QueryCertificate.allPresentations q bases)).2
    intro x
    simp [M7.QueryCertificate.allPresentations, M7.GlobalQuery.present,
      M7.QueryCertificate.isLeast,
      (M7.ActualPresentation.leastAction_spec N (bases x.1)
        (M7.GlobalQuery.realize bases x)).1,
      M7.GlobalQuery.realize]
  refine ⟨dominator, ?_⟩
  simp [M7.QueryCertificate.check, hvalid, hwin, hpres]

theorem M7.QueryCertificate.check_sound : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : M7.QueryCertificate.Certificate H N), M7.QueryCertificate.check q bases certificate = Except.ok true → M7.DefaultQuery.valid N q ∧ certificate.winners = M7.GlobalQuery.winners q bases ∧ certificate.presentations = M7.QueryCertificate.allPresentations q bases := by
  intro H N inst q bases certificate hcheck
  classical
  by_cases hv : M7.DefaultQuery.valid N q
  · have hpasses := hcheck
    simp [M7.QueryCertificate.check, hv, Bool.and_eq_true] at hpasses
    have hW : certificate.winners = M7.GlobalQuery.winners q bases :=
      M7.QueryCertificate.winner_pass_sound H N q bases certificate.winners _ hpasses.1
    refine ⟨hv, hW, ?_⟩
    have hP := (M7.QueryCertificate.presentation_pass_spec H N bases
      certificate.winners certificate.presentations).mp hpasses.2
    apply Finset.ext
    intro x
    simpa [M7.QueryCertificate.allPresentations, M7.GlobalQuery.present,
      M7.QueryCertificate.isLeast, hW] using hP x
  · simp [M7.QueryCertificate.check, hv] at hcheck

theorem M7.QueryCertificate.check_exact : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W P : Finset (M7.GlobalQuery.Index H N)), ((∃ dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N), M7.QueryCertificate.check q bases (⟨W, P, dominator⟩ : M7.QueryCertificate.Certificate H N) = Except.ok true) ↔ M7.DefaultQuery.valid N q ∧ W = M7.GlobalQuery.winners q bases ∧ P = M7.QueryCertificate.allPresentations q bases) := by
  intro H N inst q bases W P
  constructor
  · rintro ⟨dominator, hcheck⟩
    exact M7.QueryCertificate.check_sound H N q bases
      (⟨W, P, dominator⟩ : M7.QueryCertificate.Certificate H N) hcheck
  · rintro ⟨hvalid, hW, hP⟩
    rw [hW, hP]
    exact M7.QueryCertificate.check_complete H N q bases hvalid
#print axioms M7.QueryCertificate.invalid_rule
#print axioms M7.QueryCertificate.presentation_pass_spec
#print axioms M7.QueryCertificate.winner_pass_spec
#print axioms M7.QueryCertificate.winner_pass_complete
#print axioms M7.QueryCertificate.check_complete
#print axioms M7.QueryCertificate.winner_pass_sound
#print axioms M7.QueryCertificate.check_sound
#print axioms M7.QueryCertificate.check_exact
