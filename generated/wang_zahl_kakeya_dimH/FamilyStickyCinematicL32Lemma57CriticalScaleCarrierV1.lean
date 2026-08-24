import FamilyStickyCinematicL32Lemma57CanonicalMaximizerV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1

open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32Lemma57CanonicalMaximizerV1

noncomputable section

/-!
# Finite critical-scale carrier for PYZ Lemma 5.7

For a finite family, a closed-ball cardinality changes only when its radius
crosses one of the finitely many pairwise distances.  Consequently the
weighted ball score on the full compact scale interval `[delta,K]` is
controlled by its values at `delta` and the pairwise distances lying in that
interval.  This removes the need to place each later test radius into a
hand-chosen finite carrier.
-/

variable {alpha : Type*}

/-- The lower endpoint together with all pairwise distance values in the
requested compact scale interval. -/
noncomputable def finiteCriticalScaleCarrier
    (family : Finset alpha) (distance : alpha -> alpha -> Real)
    (delta K : Real) : Finset Real := by
  classical
  exact insert delta
    (((family ×ˢ family).image fun pair => distance pair.1 pair.2).filter
      fun radius => delta <= radius ∧ radius <= K)

/-- The critical carrier is nonempty because it contains `delta`. -/
theorem finiteCriticalScaleCarrier_nonempty
    (family : Finset alpha) (distance : alpha -> alpha -> Real)
    (delta K : Real) :
    (finiteCriticalScaleCarrier family distance delta K).Nonempty := by
  classical
  exact ⟨delta, by simp [finiteCriticalScaleCarrier]⟩

/-- Every critical scale belongs to the requested interval. -/
theorem finiteCriticalScaleCarrier_bounds
    (family : Finset alpha) (distance : alpha -> alpha -> Real)
    {delta K radius : Real} (hdeltaK : delta <= K)
    (hradius : radius ∈ finiteCriticalScaleCarrier family distance delta K) :
    delta <= radius ∧ radius <= K := by
  classical
  rw [finiteCriticalScaleCarrier, Finset.mem_insert] at hradius
  rcases hradius with rfl | hradius
  · exact ⟨le_rfl, hdeltaK⟩
  · exact (Finset.mem_filter.mp hradius).2

/-- At every radius in `[delta,K]`, one critical radius no larger than it has
the same closed-ball cardinality and at least as large a weighted score. -/
theorem exists_criticalScale_with_score_ge
    (family : Finset alpha) (distance : alpha -> alpha -> Real)
    {delta K exponent radius : Real} (center : alpha)
    (hcenter : center ∈ family)
    (hself : distance center center <= delta)
    (hdelta : 0 < delta) (hradiusLower : delta <= radius)
    (hradiusUpper : radius <= K) (hexponent : 0 <= exponent) :
    exists criticalRadius,
      criticalRadius ∈
        finiteCriticalScaleCarrier family distance delta K ∧
      finiteTwoEndsScore family distance exponent radius center <=
        finiteTwoEndsScore family distance exponent criticalRadius center := by
  classical
  let ball := family.filter fun point => distance point center <= radius
  have hcenterBall : center ∈ ball := by
    change center ∈ family.filter fun point => distance point center <= radius
    rw [Finset.mem_filter]
    exact ⟨hcenter, hself.trans hradiusLower⟩
  have hball : ball.Nonempty := ⟨center, hcenterBall⟩
  obtain ⟨point, hpoint, hmaximum⟩ :=
    Finset.exists_mem_eq_sup' hball (fun point => distance point center)
  have hpointFamily : point ∈ family :=
    (Finset.mem_filter.mp hpoint).1
  have hpointRadius : distance point center <= radius :=
    (Finset.mem_filter.mp hpoint).2
  have hdistanceMax : forall testPoint, testPoint ∈ ball ->
      distance testPoint center <= distance point center := by
    intro testPoint htestPoint
    calc
      distance testPoint center <=
          ball.sup' hball (fun candidate => distance candidate center) :=
        Finset.le_sup' (fun candidate => distance candidate center) htestPoint
      _ = distance point center := hmaximum
  by_cases hsmall : distance point center <= delta
  · have hcount : finiteBallCount family distance radius center =
        finiteBallCount family distance delta center := by
      apply congrArg Finset.card
      ext testPoint
      simp only [Finset.mem_filter]
      constructor
      · intro htest
        refine ⟨htest.1, ?_⟩
        exact (hdistanceMax testPoint (by
          change testPoint ∈
            family.filter fun point => distance point center <= radius
          rw [Finset.mem_filter]
          exact htest)).trans hsmall
      · intro htest
        exact ⟨htest.1, htest.2.trans hradiusLower⟩
    refine ⟨delta, by simp [finiteCriticalScaleCarrier], ?_⟩
    have hpower : radius ^ (-exponent) <= delta ^ (-exponent) :=
      Real.rpow_le_rpow_of_nonpos hdelta hradiusLower
        (neg_nonpos.mpr hexponent)
    simp only [finiteTwoEndsScore]
    rw [hcount]
    exact mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _)
  · have hcriticalLower : delta <= distance point center :=
      le_of_not_ge hsmall
    have hcriticalMem : distance point center ∈
        finiteCriticalScaleCarrier family distance delta K := by
      rw [finiteCriticalScaleCarrier, Finset.mem_insert]
      right
      rw [Finset.mem_filter]
      refine ⟨?_, hcriticalLower, hpointRadius.trans hradiusUpper⟩
      rw [Finset.mem_image]
      exact ⟨(point, center),
        Finset.mem_product.mpr ⟨hpointFamily, hcenter⟩, rfl⟩
    have hcount : finiteBallCount family distance radius center =
        finiteBallCount family distance (distance point center) center := by
      apply congrArg Finset.card
      ext testPoint
      simp only [Finset.mem_filter]
      constructor
      · intro htest
        exact ⟨htest.1, hdistanceMax testPoint (by
          change testPoint ∈
            family.filter fun point => distance point center <= radius
          rw [Finset.mem_filter]
          exact htest)⟩
      · intro htest
        exact ⟨htest.1, htest.2.trans hpointRadius⟩
    refine ⟨distance point center, hcriticalMem, ?_⟩
    have hcriticalPos : 0 < distance point center :=
      hdelta.trans_le hcriticalLower
    have hpower : radius ^ (-exponent) <=
        (distance point center) ^ (-exponent) :=
      Real.rpow_le_rpow_of_nonpos hcriticalPos hpointRadius
        (neg_nonpos.mpr hexponent)
    simp only [finiteTwoEndsScore]
    rw [hcount]
    exact mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _)

/-- The canonical maximizer on the critical carrier dominates the weighted
score at every real radius in `[delta,K]`. -/
theorem canonicalCriticalMaximizer_dominates_on_Icc
    (family : Finset alpha) (distance : alpha -> alpha -> Real)
    {delta K exponent : Real}
    (hfamily : family.Nonempty)
    (hself : forall center, center ∈ family ->
      distance center center <= delta)
    (hdelta : 0 < delta) (_hdeltaK : delta <= K)
    (hexponent : 0 <= exponent) :
    forall radius, delta <= radius -> radius <= K ->
      forall center, center ∈ family ->
        finiteTwoEndsScore family distance exponent radius center <=
          finiteTwoEndsScore family distance exponent
            (canonicalMaximizerData family
              (finiteCriticalScaleCarrier family distance delta K)
              distance exponent
              (finiteCriticalScaleCarrier_nonempty
                family distance delta K) hfamily).scale
            (canonicalMaximizerData family
              (finiteCriticalScaleCarrier family distance delta K)
              distance exponent
              (finiteCriticalScaleCarrier_nonempty
                family distance delta K) hfamily).center := by
  intro radius hradiusLower hradiusUpper center hcenter
  obtain ⟨criticalRadius, hcriticalRadius, hscore⟩ :=
    exists_criticalScale_with_score_ge family distance center hcenter
      (hself center hcenter) hdelta hradiusLower hradiusUpper hexponent
  exact hscore.trans
    (canonicalMaximizerData_dominates family
      (finiteCriticalScaleCarrier family distance delta K)
      distance exponent
      (finiteCriticalScaleCarrier_nonempty family distance delta K)
      hfamily criticalRadius hcriticalRadius center hcenter)

#print axioms finiteCriticalScaleCarrier
#print axioms finiteCriticalScaleCarrier_nonempty
#print axioms finiteCriticalScaleCarrier_bounds
#print axioms exists_criticalScale_with_score_ge
#print axioms canonicalCriticalMaximizer_dominates_on_Icc

end

end FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1
