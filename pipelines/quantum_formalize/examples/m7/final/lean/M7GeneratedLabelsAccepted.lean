import M7GeneratedLabels

theorem M7.GeneratedLabels.arrays : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ (i : Fin (M7.GeneratedFamily.size N w E)) (g : M7.Action.Record N), (M7.QualityTable.leftTable (M7.GeneratedFamily.family N w E i) (g.unit,g.exchange)).size = N ∧ (M7.QualityTable.rightTable (M7.GeneratedFamily.family N w E i) (g.unit,g.exchange)).size = N ∧ M7.QualityTable.placedScores (M7.GeneratedFamily.family N w E i) g = (M7.DefaultQuery.locality (M7.Action.act g (M7.GeneratedFamily.family N w E i)), M7.DefaultQuery.radius (M7.Action.act g (M7.GeneratedFamily.family N w E i))) := by
  intro N w inst E hw hwN hE i g
  exact M7.QualityTable.array_scores N (M7.GeneratedFamily.family N w E i) g

theorem M7.GeneratedLabels.cache : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ (i : Fin (M7.GeneratedFamily.size N w E)) (g : M7.Action.Record N), (M7.DefaultQuery.dimension (M7.Action.act g (M7.GeneratedFamily.family N w E i)), M7.DefaultQuery.distance (M7.Action.act g (M7.GeneratedFamily.family N w E i))) = M7.QualityTable.cache (M7.GeneratedFamily.family N w E i) := by
  intro N w inst E hw hwN hE i g
  have hvalid := (M7.GeneratedFamily.family_good N w E hw hwN hE i).1
  obtain ⟨hleft, hright⟩ := M7.GeneratedFamily.family_anchored N w E hw hwN hE i
  unfold M7.PrefixOrbit.ClassValid at hvalid
  apply M7.QualityTable.cache_action N w (M7.GeneratedFamily.family N w E i) _ _ hleft hright _ g
  all_goals aesop

theorem M7.GeneratedLabels.pointwise : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ i : Fin (M7.GeneratedFamily.size N w E), M6.Final.PointwiseCorrect N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) := by
  intro N w inst E hw hwN hE i
  have hgood := (M7.GeneratedFamily.family_good N w E hw hwN hE i).1
  have hanchored := M7.GeneratedFamily.family_anchored N w E hw hwN hE i
  apply M7.ClosedSolve.closed_pointwise N w (M7.GeneratedFamily.family N w E i)
  all_goals
    simp_all [M7.PrefixOrbit.ClassValid]

theorem M7.GeneratedLabels.witness : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ (i : Fin (M7.GeneratedFamily.size N w E)) (g : M7.Action.Record N) (d k : ℕ) (v : M6.Pinned.Vector (2*N)), M6.ActualTransfer.solve N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) = some (d,v,k) → M7.Transport.distance (M7.Action.act g (M7.GeneratedFamily.family N w E i)) = some d ∧ M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g (M7.GeneratedFamily.family N w E i)) ∧ M6.Pinned.weight (M7.Transport.Xmap g v) = d ∧ M6.Flatten.J N (M7.Transport.Xmap g v) ∈ M7.Transport.LZ (M7.Action.act g (M7.GeneratedFamily.family N w E i)) ∧ M6.Pinned.weight (M6.Flatten.J N (M7.Transport.Xmap g v)) = d ∧ k ≤ 2*N := by
  intro N w inst E hw hwN hE i g d k v hsolve
  have hgood := (M7.GeneratedFamily.family_good N w E hw hwN hE i).1
  have hanchor := M7.GeneratedFamily.family_anchored N w E hw hwN hE i
  simp only [M7.PrefixOrbit.ClassValid] at hgood
  have hconn : M7.Connectivity.connected (M7.GeneratedFamily.family N w E i) := by
    aesop
  have hgcd := (M7.Connectivity.anchored_gcd N
    (M7.GeneratedFamily.family N w E i).1
    (M7.GeneratedFamily.family N w E i).2
    hanchor.1 hanchor.2).mp hconn
  apply M7.Transport.actual_witness N w g (M7.GeneratedFamily.family N w E i) d k v
  · aesop
  · aesop
  · exact hanchor.1
  · exact hanchor.2
  · exact hgcd
  · exact hsolve
#print axioms M7.GeneratedLabels.arrays
#print axioms M7.GeneratedLabels.cache
#print axioms M7.GeneratedLabels.pointwise
#print axioms M7.GeneratedLabels.witness
