import M7GlobalQueryAccepted
import M7QueryCertificate

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : M7.QueryCertificate.Certificate H N), M7.QueryCertificate.check q bases certificate = Except.ok true → M7.DefaultQuery.valid N q ∧ certificate.winners = M7.GlobalQuery.winners q bases ∧ certificate.presentations = M7.QueryCertificate.allPresentations q bases
