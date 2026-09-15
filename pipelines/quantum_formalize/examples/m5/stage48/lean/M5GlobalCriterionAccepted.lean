import M5GlobalCriterionReady

theorem M5.GlobalCriterion.physical_implies_A_positive : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (S U : Finset ℕ), 0 < w → F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F S U → 0 < M5.ResidueCount.A w F := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (S U : Finset ℕ), 0 < w → F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F S U → 0 < M5.ResidueCount.A w F
  intro N w F S U hw hF hF0 hphys
  rcases M5.ResidueNecessity.period_necessity N w F S U hw hF hF0 hphys with ⟨r, s, hr, hs, hgcd, hsig⟩
  apply (M5.ResidueCount.period_A_exact w F hw hF hF0).2.2.mpr
  exact M5.GlobalCriterion.full_to_tail w (M5.signaturePeriod F) F r s hw (M5.Period.period_law F hF hF0).1 hr hs hgcd hsig

theorem M5.GlobalCriterion.positive_bounded_progression : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ (S U : Finset ℕ) (N E : ℕ), 0 < E ∧ N < M5.birthBound w (M5.signaturePeriod F) ∧ ∀ j : ℕ, M5.PhysicalOrder.realizes (N + j * E) w F S U := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ (S U : Finset ℕ) (N E : ℕ), 0 < E ∧ N < M5.birthBound w (M5.signaturePeriod F) ∧ ∀ j : ℕ, M5.PhysicalOrder.realizes (N + j * E) w F S U
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro w F hw hF hF0 hA
  cases w with
  | zero => omega
  | succ k =>
    have hT := (M5.Period.period_law F hF hF0).1
    have htails := (M5.ResidueCount.period_A_exact (k + 1) F (by omega) hF hF0).2.2.mp hA
    change ∃ a b : Fin k → Fin (M5.signaturePeriod F), M5.ResidueCount.feasible F a b at htails
    obtain ⟨a, b, hab⟩ := htails
    let r := M5.ResidueTailBridge.anchored hT a
    let s := M5.ResidueTailBridge.anchored hT b
    have hr : M5.BoundedConstruction.anchoredTuple r := by
      exact M5.ResidueTailBridge.anchor_zero (M5.signaturePeriod F) k hT a
    have hs : M5.BoundedConstruction.anchoredTuple s := by
      exact M5.ResidueTailBridge.anchor_zero (M5.signaturePeriod F) k hT b
    have hg : M5.BoundedConstruction.tupleSupportGcd r s = 1 := by
      simpa [M5.BoundedConstruction.tupleSupportGcd, r, s,
        M5.ResidueCount.residueSupport, Finset.gcd_union, Finset.gcd_image,
        Function.comp_def, M5.ResidueTailBridge.gcd_cons] using hab.1
    have hp : M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r)
        (M5.SupportPolynomial.ofResidueTuple s) (M5.signaturePeriod F) = F := by
      simpa [r, s, M5.ResidueTailBridge.polynomial_cons,
        M5.ResidueCount.tailPolynomial] using hab.2
    obtain ⟨S, N, E, hE, hN, hprogress⟩ :=
      M5.FeasibleSource.same_support_infinite_progression (k + 1)
        (M5.signaturePeriod F) r s F hw hT hr hs hg hp
    exact ⟨S, M5.Packing.packedSupport s, N, E, hE, hN, hprogress⟩

theorem M5.GlobalCriterion.global_occurrence_criterion : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U) ∧ (M5.ResidueCount.A w F = 0 ↔ ¬ (∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U) ∧ (M5.ResidueCount.A w F = 0 ↔ ¬ (∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro w F hw hF hF0
  have hwpos : 0 < w := by omega
  have hnonneg := (M5.ResidueCount.period_A_exact w F hwpos hF hF0).2.1
  have hiff : 0 < M5.ResidueCount.A w F ↔ ∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U := by
    constructor
    · intro hA
      obtain ⟨S, U, N, E, hE, hN, hprogress⟩ :=
        M5.GlobalCriterion.positive_bounded_progression w F hw hF hF0 hA
      refine ⟨N, S, U, ?_⟩
      simpa only [Nat.zero_mul, Nat.add_zero] using hprogress 0
    · rintro ⟨N, S, U, hphys⟩
      exact M5.GlobalCriterion.physical_implies_A_positive N w F S U hwpos hF hF0 hphys
  refine ⟨hnonneg, hiff, ?_⟩
  constructor
  · intro hzero hexists
    have hpos := hiff.mpr hexists
    omega
  · intro hnone
    have hnotpos : ¬ 0 < M5.ResidueCount.A w F := fun hpos => hnone (hiff.mp hpos)
    omega
#print axioms M5.GlobalCriterion.physical_implies_A_positive
#print axioms M5.GlobalCriterion.positive_bounded_progression
#print axioms M5.GlobalCriterion.global_occurrence_criterion
