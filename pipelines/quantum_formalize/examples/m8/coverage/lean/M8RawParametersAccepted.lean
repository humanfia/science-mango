import M8RawParameters

theorem M8.RawParameters.encoded_dimension : ∀ (N w : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → M6.Final.encodedQubits N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) = 2*(M8.PhysicalBridge.signature c).natDegree := by
  intro N w inst c hw hc
  have ha : (M7.Supports.polynomial c.1).degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast M7.Supports.degree_lt N c.1
  have hb : (M7.Supports.polynomial c.2).degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast M7.Supports.degree_lt N c.2
  simpa only [M6.Final.encodedQubits, M6.ActualCounts.f,
    M8.PhysicalBridge.signature, M7.RecipeSignature.signature,
    M7.Domain.signature] using
    (M6.ActualCounts.encoded_dimension N
      (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ha hb)

theorem M8.RawParameters.raw_anchor : ∀ (N w : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → ∃ g : M7.Action.Record N, M8.PhysicalBridge.Anchored (M7.Action.act g c) := by
  intro N w inst c hw hv
  classical
  rcases hv with ⟨hA, hB, hconn⟩
  have hApos : 0 < c.1.card := by omega
  have hBpos : 0 < c.2.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hApos
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hBpos
  refine ⟨M8.Anchor.record false 1 a b, ?_⟩
  have he : M8.Anchor.Eligible c false a b := by
    simpa [M8.Anchor.Eligible, M8.Anchor.left, M8.Anchor.right] using And.intro ha hb
  exact M8.Anchor.anchored N c false 1 a b he

theorem M8.RawParameters.raw_noLogical : ∀ (N w : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → (M7.Transport.distance c = none ↔ M8.PhysicalBridge.signature c = 1) ∧ (M7.Transport.LX c = ∅ ↔ M8.PhysicalBridge.signature c = 1) := by
  intro N w inst c hw hv
  classical
  obtain ⟨g, hg⟩ := M8.RawParameters.raw_anchor N w c hw hv
  have hp := M8.PhysicalBridge.pointwise_optimizer N c g w hv hg
  have hn := M8.PhysicalBridge.noLogical N c g w hv hg
  have hi := M7.Transport.distance_invariant N g c
  have hsolve : M8.PhysicalBridge.solve (M7.Action.act g c) = none ↔ M7.Transport.distance (M7.Action.act g c) = none := by
    unfold M8.PhysicalBridge.solve M7.Transport.distance
    simp only [M6.Final.PointwiseCorrect, M6.Final.AnswerCorrect] at hp
    first
    | aesop
    | cases hs : M6.ActualTransfer.solve N (M7.Supports.polynomial (M7.Action.act g c).1) (M7.Supports.polynomial (M7.Action.act g c).2) with
      | none => aesop
      | some result =>
        rcases result with ⟨d, v, k⟩
        aesop
  have hd : M7.Transport.distance c = none ↔ M8.PhysicalBridge.signature c = 1 := by
    rw [← hi]
    exact hsolve.symm.trans hn
  refine ⟨hd, ?_⟩
  have hc := M6.ActualCSS.common_quantum_distance N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2)
  have he : M7.Transport.distance c = M6.Pinned.distance (M7.Transport.LX c) := by
    simpa only [M7.Transport.distance, M7.Transport.LX, M7.Transport.BX, M7.Transport.CX, M6.Final.quantumDistance, M6.Final.BX, M6.Final.CX, M6.Final.BZ, M6.Final.CZ, M7.Domain.coefficients_indicator, M6.Spaces.logicalWords] using hc
  have hs := (M6.Pinned.distance_spec (2 * N) (M7.Transport.LX c)).1
  apply Iff.trans hs.symm
  rw [← he]
  exact hd
#print axioms M8.RawParameters.encoded_dimension
#print axioms M8.RawParameters.raw_anchor
#print axioms M8.RawParameters.raw_noLogical
