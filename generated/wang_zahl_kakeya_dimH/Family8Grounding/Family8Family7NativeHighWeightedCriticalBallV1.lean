import Family8Grounding.Family8Family7NativeHighCriticalBallDatumV1
import FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighWeightedCriticalBallV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

/-!
# A mass-weighted canonical critical ball

The existing canonical norm ball maximizes cardinality times a scale weight.
That choice cannot retain first-hit or shading mass.  This additive successor
keeps the same literal finite critical-scale carrier and coefficient metric,
but permits an arbitrary nonnegative `ENNReal` weight on each tube occurrence.
The selected ball is therefore a genuine upstream weighted choice rather than
a desired-conclusion callback.
-/

variable {alpha : Type*}

/-- Literal weight in a closed finite ball. -/
def finiteWeightedBallMass (family : Finset alpha)
    (distance : alpha → alpha → Real) (weight : alpha → ENNReal)
    (ballRadius : Real) (center : alpha) : ENNReal :=
  ∑ i ∈ family.filter fun j => distance j center ≤ ballRadius, weight i

/-- Weighted two-ends score on one ball. -/
def finiteWeightedTwoEndsScore (family : Finset alpha)
    (distance : alpha → alpha → Real) (weight : alpha → ENNReal)
    (exponent ballRadius : Real) (center : alpha) : ENNReal :=
  finiteWeightedBallMass family distance weight ballRadius center *
    (ENNReal.ofReal ballRadius) ^ (-exponent)

/-- Finite scales and centres have an exact maximizer for arbitrary
`ENNReal` occurrence weights. -/
theorem exists_finiteWeightedTwoEndsScore_maximizer
    (family : Finset alpha) (scales : Finset Real)
    (distance : alpha → alpha → Real) (weight : alpha → ENNReal)
    (exponent : Real) (hscales : scales.Nonempty)
    (hfamily : family.Nonempty) :
    ∃ chosenScale, chosenScale ∈ scales ∧
      ∃ chosenCenter, chosenCenter ∈ family ∧
        ∀ testScale, testScale ∈ scales →
          ∀ testCenter, testCenter ∈ family →
            finiteWeightedTwoEndsScore family distance weight exponent
                testScale testCenter ≤
              finiteWeightedTwoEndsScore family distance weight exponent
                chosenScale chosenCenter := by
  let candidates := scales ×ˢ family
  let score : Real × alpha → ENNReal := fun pair =>
    finiteWeightedTwoEndsScore family distance weight exponent
      pair.1 pair.2
  have hcandidates : candidates.Nonempty := hscales.product hfamily
  obtain ⟨chosen, hchosen, hmax⟩ :=
    Finset.exists_mem_eq_sup' hcandidates score
  have hchosenMem := Finset.mem_product.mp hchosen
  refine ⟨chosen.1, hchosenMem.1, chosen.2, hchosenMem.2, ?_⟩
  intro testScale htestScale testCenter htestCenter
  have hcandidate : (testScale, testCenter) ∈ candidates :=
    Finset.mem_product.mpr ⟨htestScale, htestCenter⟩
  have hle : score (testScale, testCenter) ≤
      candidates.sup' hcandidates score :=
    Finset.le_sup' score hcandidate
  rw [hmax] at hle
  exact hle

/-- Inputs for the mass-weighted canonical norm choice. -/
structure WeightedCanonicalNormBallData (alpha : Type*) where
  family : Finset alpha
  distance : alpha → alpha → Real
  weight : alpha → ENNReal
  delta : Real
  ceiling : Real
  exponent : Real
  family_nonempty : family.Nonempty
  self_le_delta : ∀ center, center ∈ family →
    distance center center ≤ delta
  delta_pos : 0 < delta
  delta_le_ceiling : delta ≤ ceiling
  exponent_nonneg : 0 ≤ exponent

namespace WeightedCanonicalNormBallData

/-- A bundled exact weighted maximizer on the literal critical carrier. -/
structure CriticalChoice (D : WeightedCanonicalNormBallData alpha) where
  scale : Real
  scale_mem : scale ∈ finiteCriticalScaleCarrier D.family D.distance
    D.delta D.ceiling
  center : alpha
  center_mem : center ∈ D.family
  dominates : ∀ testScale,
    testScale ∈ finiteCriticalScaleCarrier D.family D.distance
      D.delta D.ceiling →
    ∀ testCenter, testCenter ∈ D.family →
      finiteWeightedTwoEndsScore D.family D.distance D.weight D.exponent
          testScale testCenter ≤
        finiteWeightedTwoEndsScore D.family D.distance D.weight D.exponent
          scale center

theorem criticalChoice_nonempty (D : WeightedCanonicalNormBallData alpha) :
    Nonempty D.CriticalChoice := by
  obtain ⟨scale, hscale, center, hcenter, hmax⟩ :=
    exists_finiteWeightedTwoEndsScore_maximizer
      D.family (finiteCriticalScaleCarrier D.family D.distance
        D.delta D.ceiling) D.distance D.weight D.exponent
      (finiteCriticalScaleCarrier_nonempty D.family D.distance
        D.delta D.ceiling) D.family_nonempty
  exact ⟨⟨scale, hscale, center, hcenter, hmax⟩⟩

/-- The exact finite weighted maximizer, stored only by classical choice from
the proved finite maximization theorem. -/
noncomputable def criticalChoice (D : WeightedCanonicalNormBallData alpha) :
    D.CriticalChoice :=
  Classical.choice D.criticalChoice_nonempty

def criticalScale (D : WeightedCanonicalNormBallData alpha) : Real :=
  D.criticalChoice.scale

def criticalCenter (D : WeightedCanonicalNormBallData alpha) : alpha :=
  D.criticalChoice.center

/-- The literal filter associated to the weighted maximizing pair. -/
noncomputable def criticalBall (D : WeightedCanonicalNormBallData alpha) :
    Finset alpha :=
  D.family.filter fun i => D.distance i D.criticalCenter ≤ D.criticalScale

theorem criticalScale_bounds (D : WeightedCanonicalNormBallData alpha) :
    D.delta ≤ D.criticalScale ∧ D.criticalScale ≤ D.ceiling := by
  apply finiteCriticalScaleCarrier_bounds D.family D.distance
    D.delta_le_ceiling
  exact D.criticalChoice.scale_mem

theorem criticalCenter_mem_family
    (D : WeightedCanonicalNormBallData alpha) :
    D.criticalCenter ∈ D.family :=
  D.criticalChoice.center_mem

theorem criticalCenter_mem_criticalBall
    (D : WeightedCanonicalNormBallData alpha) :
    D.criticalCenter ∈ D.criticalBall := by
  rw [criticalBall, Finset.mem_filter]
  exact ⟨D.criticalCenter_mem_family,
    (D.self_le_delta D.criticalCenter D.criticalCenter_mem_family).trans
      D.criticalScale_bounds.1⟩

theorem criticalBall_nonempty (D : WeightedCanonicalNormBallData alpha) :
    D.criticalBall.Nonempty :=
  ⟨D.criticalCenter, D.criticalCenter_mem_criticalBall⟩

theorem criticalBall_subset_family
    (D : WeightedCanonicalNormBallData alpha) :
    D.criticalBall ⊆ D.family := by
  exact Finset.filter_subset _ _

theorem criticalBall_distance_to_center
    (D : WeightedCanonicalNormBallData alpha)
    {i : alpha} (hi : i ∈ D.criticalBall) :
    D.distance i D.criticalCenter ≤ D.criticalScale := by
  exact (Finset.mem_filter.mp hi).2

/-- The chosen ball has exactly the literal occurrence-weight sum. -/
theorem finiteWeightedBallMass_criticalScale
    (D : WeightedCanonicalNormBallData alpha) :
    finiteWeightedBallMass D.family D.distance D.weight D.criticalScale
        D.criticalCenter =
      ∑ i ∈ D.criticalBall, D.weight i := by
  rfl

/-- The weighted choice dominates every candidate ball on the same literal
critical-scale carrier. -/
theorem weighted_score_dominates_on_criticalCarrier
    (D : WeightedCanonicalNormBallData alpha)
    {testScale : Real}
    (hscale : testScale ∈ finiteCriticalScaleCarrier D.family D.distance
      D.delta D.ceiling)
    {testCenter : alpha} (hcenter : testCenter ∈ D.family) :
    finiteWeightedTwoEndsScore D.family D.distance D.weight D.exponent
        testScale testCenter ≤
      finiteWeightedTwoEndsScore D.family D.distance D.weight D.exponent
        D.criticalScale D.criticalCenter := by
  exact D.criticalChoice.dominates testScale hscale testCenter hcenter

end WeightedCanonicalNormBallData

universe u

/-- Native-high specialization with an arbitrary honest occurrence weight.
Taking `weight i = volume (Y.carrier i)` gives a shading-mass maximizer;
taking an E2 first-hit occurrence weight gives the paper's weighted choice. -/
noncomputable def nativeHighWeightedNormData
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (weight : iota → ENNReal) : WeightedCanonicalNormBallData iota := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  exact
    { family := N.family
      distance := N.distance
      weight := weight
      delta := N.delta
      ceiling := N.ceiling
      exponent := N.exponent
      family_nonempty := N.family_nonempty
      self_le_delta := N.self_le_delta
      delta_pos := N.delta_pos
      delta_le_ceiling := N.delta_le_ceiling
      exponent_nonneg := N.exponent_nonneg }

noncomputable def nativeHighWeightedCriticalBall
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (weight : iota → ENNReal) : Finset iota :=
  (nativeHighWeightedNormData D c weight).criticalBall

theorem nativeHighWeightedCriticalBall_nonempty
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (weight : iota → ENNReal) :
    (nativeHighWeightedCriticalBall D c weight).Nonempty :=
  (nativeHighWeightedNormData D c weight).criticalBall_nonempty

theorem nativeHighWeightedCriticalBall_subset_physicalAmbient
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (weight : iota → ENNReal) :
    nativeHighWeightedCriticalBall D c weight ⊆ D.physical.ambient := by
  intro i hi
  have hiFamily : i ∈
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).family :=
    (nativeHighWeightedNormData D c weight).criticalBall_subset_family hi
  rw [positiveCenterHighPayloadGlobalNormData_family] at hiFamily
  exact (mem_actualGlobalNormIndexFamily_iff D.S.family D.physical
    D.globalScale c.1.1).mp hiFamily |>.1

#print axioms finiteWeightedBallMass
#print axioms finiteWeightedTwoEndsScore
#print axioms exists_finiteWeightedTwoEndsScore_maximizer
#print axioms WeightedCanonicalNormBallData
#print axioms WeightedCanonicalNormBallData.criticalBall
#print axioms WeightedCanonicalNormBallData.weighted_score_dominates_on_criticalCarrier
#print axioms nativeHighWeightedNormData
#print axioms nativeHighWeightedCriticalBall_nonempty
#print axioms nativeHighWeightedCriticalBall_subset_physicalAmbient

end

end Family8Family7NativeHighWeightedCriticalBallV1
