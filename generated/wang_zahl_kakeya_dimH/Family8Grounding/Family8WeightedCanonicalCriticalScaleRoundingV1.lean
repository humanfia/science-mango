import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped BigOperators ENNReal

namespace Family8WeightedCanonicalCriticalScaleRoundingV1

open Family8Family7NativeHighWeightedCriticalBallV1
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1

noncomputable section

universe u

/-- Every real-radius weighted score in the canonical interval is dominated
by the score at a literal member of the finite critical-scale carrier. -/
theorem exists_criticalScale_with_weighted_score_ge
    {alpha : Type u} (family : Finset alpha)
    (distance : alpha → alpha → Real) (weight : alpha → ENNReal)
    {delta ceiling exponent radius : Real} (center : alpha)
    (hcenter : center ∈ family)
    (hself : distance center center ≤ delta)
    (_hdelta : 0 < delta) (hradiusLower : delta ≤ radius)
    (hradiusUpper : radius ≤ ceiling) (hexponent : 0 ≤ exponent) :
    ∃ criticalRadius,
      criticalRadius ∈
        finiteCriticalScaleCarrier family distance delta ceiling ∧
      finiteWeightedTwoEndsScore family distance weight exponent radius center ≤
        finiteWeightedTwoEndsScore family distance weight exponent
          criticalRadius center := by
  classical
  let ball := family.filter fun point => distance point center ≤ radius
  have hcenterBall : center ∈ ball := by
    change center ∈ family.filter fun point => distance point center ≤ radius
    rw [Finset.mem_filter]
    exact ⟨hcenter, hself.trans hradiusLower⟩
  have hball : ball.Nonempty := ⟨center, hcenterBall⟩
  obtain ⟨point, hpoint, hmaximum⟩ :=
    Finset.exists_mem_eq_sup' hball (fun point => distance point center)
  have hpointFamily : point ∈ family :=
    (Finset.mem_filter.mp hpoint).1
  have hpointRadius : distance point center ≤ radius :=
    (Finset.mem_filter.mp hpoint).2
  have hdistanceMax : ∀ testPoint, testPoint ∈ ball →
      distance testPoint center ≤ distance point center := by
    intro testPoint htestPoint
    calc
      distance testPoint center ≤
          ball.sup' hball (fun candidate => distance candidate center) :=
        Finset.le_sup' (fun candidate => distance candidate center) htestPoint
      _ = distance point center := hmaximum
  by_cases hsmall : distance point center ≤ delta
  · have hfilter :
        family.filter (fun testPoint => distance testPoint center ≤ radius) =
          family.filter (fun testPoint => distance testPoint center ≤ delta) := by
      ext testPoint
      simp only [Finset.mem_filter]
      constructor
      · intro htest
        refine ⟨htest.1, ?_⟩
        exact (hdistanceMax testPoint (by
          change testPoint ∈
            family.filter fun point => distance point center ≤ radius
          rw [Finset.mem_filter]
          exact htest)).trans hsmall
      · intro htest
        exact ⟨htest.1, htest.2.trans hradiusLower⟩
    have hmass :
        finiteWeightedBallMass family distance weight radius center =
          finiteWeightedBallMass family distance weight delta center := by
      unfold finiteWeightedBallMass
      rw [hfilter]
    refine ⟨delta, by simp [finiteCriticalScaleCarrier], ?_⟩
    have hpower :
        (ENNReal.ofReal radius) ^ (-exponent) ≤
          (ENNReal.ofReal delta) ^ (-exponent) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hradiusLower) hexponent
    unfold finiteWeightedTwoEndsScore
    rw [hmass]
    exact mul_le_mul' le_rfl hpower
  · have hcriticalLower : delta ≤ distance point center :=
      le_of_not_ge hsmall
    have hcriticalMem : distance point center ∈
        finiteCriticalScaleCarrier family distance delta ceiling := by
      rw [finiteCriticalScaleCarrier, Finset.mem_insert]
      right
      rw [Finset.mem_filter]
      refine ⟨?_, hcriticalLower, hpointRadius.trans hradiusUpper⟩
      rw [Finset.mem_image]
      exact ⟨(point, center),
        Finset.mem_product.mpr ⟨hpointFamily, hcenter⟩, rfl⟩
    have hfilter :
        family.filter (fun testPoint => distance testPoint center ≤ radius) =
          family.filter
            (fun testPoint => distance testPoint center ≤
              distance point center) := by
      ext testPoint
      simp only [Finset.mem_filter]
      constructor
      · intro htest
        exact ⟨htest.1, hdistanceMax testPoint (by
          change testPoint ∈
            family.filter fun point => distance point center ≤ radius
          rw [Finset.mem_filter]
          exact htest)⟩
      · intro htest
        exact ⟨htest.1, htest.2.trans hpointRadius⟩
    have hmass :
        finiteWeightedBallMass family distance weight radius center =
          finiteWeightedBallMass family distance weight
            (distance point center) center := by
      unfold finiteWeightedBallMass
      rw [hfilter]
    refine ⟨distance point center, hcriticalMem, ?_⟩
    have hpower :
        (ENNReal.ofReal radius) ^ (-exponent) ≤
          (ENNReal.ofReal (distance point center)) ^ (-exponent) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hpointRadius) hexponent
    unfold finiteWeightedTwoEndsScore
    rw [hmass]
    exact mul_le_mul' le_rfl hpower

end

end Family8WeightedCanonicalCriticalScaleRoundingV1
