import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Family8Grounding.Family8StickyFiberSubtypeAverageBridgeV1
import FamilyStickyGrounding.FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
import Mathlib.Tactic

/-!
# Parent aggregation controlled by actual fibre averages

The usual cardinality transport from fine shading to parent-aggregated
shading is too coarse for the first Section 8 factor.  This file records the
exact sharper transport: a uniform bound for the actual average
multiplicity of every literal Sticky fibre is the multiplicative loss.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyParentAggregatedFiberAverageV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal source-fibre shaded union is the corresponding carrier of
the parent-aggregated shading. -/
theorem stickyFiberSourceShading_shadedUnion_eq_parentCarrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberSourceShading S Y k.1).shadedUnion =
      (parentAggregatedShading S Y).carrier k := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hiFiber :
        ⟨i.1, (S.mem_fiber i.1 k.1).mp i.2 |>.1⟩ ∈
          (activeIndexFactorization S).fiber k := by
      rw [IndexFactorization.mem_fiber]
      exact ⟨Finset.mem_univ _, Subtype.ext ((S.mem_fiber i.1 k.1).mp i.2).2⟩
    exact Set.mem_iUnion.mpr ⟨⟨i.1, (S.mem_fiber i.1 k.1).mp i.2 |>.1⟩,
      Set.mem_iUnion.mpr ⟨hiFiber, hxi⟩⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hiFiber, hxiY⟩ := Set.mem_iUnion.mp hxi
    have hi := (IndexFactorization.mem_fiber
      (activeIndexFactorization S) i k).mp hiFiber
    have hiSticky : i.1 ∈ S.fiber k.1 :=
      (S.mem_fiber i.1 k.1).mpr
        ⟨i.2, congrArg Subtype.val hi.2⟩
    exact Set.mem_iUnion.mpr ⟨⟨i.1, hiSticky⟩, hxiY⟩

/-- Exact regrouping of active fine shading mass by the actual literal
Sticky fibre shadings. -/
theorem activeFineShading_shadingMass_eq_sum_stickyFibers
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (activeFineShading S Y).shadingMass =
      ∑ k : {k // k ∈ S.activeCoarse},
        (stickyFiberSourceShading S Y k.1).shadingMass := by
  rw [activeFineShading_shadingMass_eq_sum_fibers S Y]
  apply Finset.sum_congr rfl
  intro k _hk
  unfold Shading.shadingMass
  classical
  let e : {i // i ∈ (activeIndexFactorization S).fiber k} ≃
      {i // i ∈ S.fiber k.1} :=
    { toFun := fun i =>
        ⟨i.1.1, (S.mem_fiber i.1.1 k.1).mpr
          ⟨i.1.2, congrArg Subtype.val
            ((IndexFactorization.mem_fiber
              (activeIndexFactorization S) i.1 k).mp i.2).2⟩⟩
      invFun := fun i =>
        ⟨⟨i.1, (S.mem_fiber i.1 k.1).mp i.2 |>.1⟩, by
          rw [IndexFactorization.mem_fiber]
          exact ⟨Finset.mem_univ _, Subtype.ext
            ((S.mem_fiber i.1 k.1).mp i.2).2⟩⟩
      left_inv := by intro i; exact Subtype.ext (Subtype.ext rfl)
      right_inv := by intro i; exact Subtype.ext rfl }
  calc
    ∑ i ∈ (activeIndexFactorization S).fiber k,
        volume (Y.carrier i.1) =
      ∑ i : {i // i ∈ (activeIndexFactorization S).fiber k},
        volume (Y.carrier i.1.1) := by
          rw [← Finset.attach_eq_univ]
          exact (Finset.sum_attach
            ((activeIndexFactorization S).fiber k)
            (fun i => volume (Y.carrier i.1))).symm
    _ = ∑ i : {i // i ∈ S.fiber k.1},
        volume ((stickyFiberSourceShading S Y k.1).carrier i) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- A uniform actual fibre-average estimate transports through parent
aggregation without replacing the fibre by its cardinality. -/
theorem activeFineShading_averageMultiplicity_le_mul_parent_of_fiberAverage
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (M : ENNReal)
    (hM : ∀ k : {k // k ∈ S.activeCoarse},
      (stickyFiberSourceShading S Y k.1).averageMultiplicity ≤ M) :
    (activeFineShading S Y).averageMultiplicity ≤
      M * (parentAggregatedShading S Y).averageMultiplicity := by
  have hfiberMass : ∀ k : {k // k ∈ S.activeCoarse},
      (stickyFiberSourceShading S Y k.1).shadingMass ≤
        M * volume ((parentAggregatedShading S Y).carrier k) := by
    intro k
    let Z := stickyFiberSourceShading S Y k.1
    have hunion : Z.shadedUnion =
        (parentAggregatedShading S Y).carrier k :=
      stickyFiberSourceShading_shadedUnion_eq_parentCarrier S Y k
    change Z.shadingMass ≤
      M * volume ((parentAggregatedShading S Y).carrier k)
    by_cases hmass : Z.shadingMass = 0
    · rw [hmass]
      exact bot_le
    · have hvolume : volume Z.shadedUnion ≠ 0 :=
        volume_shadedUnion_ne_zero_of_shadingMass_ne_zero Z hmass
      have hbound : Z.shadingMass ≤ M * volume Z.shadedUnion :=
        (ENNReal.div_le_iff_le_mul (Or.inl hvolume)
          (Or.inl (volume_shadedUnion_ne_top Z))).mp (hM k)
      simpa only [hunion] using hbound
  have hmass : (activeFineShading S Y).shadingMass ≤
      M * (parentAggregatedShading S Y).shadingMass := by
    rw [activeFineShading_shadingMass_eq_sum_stickyFibers S Y]
    unfold Shading.shadingMass
    calc
      ∑ k : {k // k ∈ S.activeCoarse},
          (stickyFiberSourceShading S Y k.1).shadingMass ≤
        ∑ k : {k // k ∈ S.activeCoarse},
          M * volume ((parentAggregatedShading S Y).carrier k) :=
        Finset.sum_le_sum fun k _hk => hfiberMass k
      _ = M * ∑ k : {k // k ∈ S.activeCoarse},
          volume ((parentAggregatedShading S Y).carrier k) := by
        rw [Finset.mul_sum]
  unfold Shading.averageMultiplicity
  calc
    (activeFineShading S Y).shadingMass /
        volume (activeFineShading S Y).shadedUnion ≤
      (M * (parentAggregatedShading S Y).shadingMass) /
        volume (activeFineShading S Y).shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ = (M * (parentAggregatedShading S Y).shadingMass) /
        volume (parentAggregatedShading S Y).shadedUnion := by
      rw [parentAggregatedShading_shadedUnion S Y]
    _ = M * ((parentAggregatedShading S Y).shadingMass /
        volume (parentAggregatedShading S Y).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms stickyFiberSourceShading_shadedUnion_eq_parentCarrier
#print axioms activeFineShading_shadingMass_eq_sum_stickyFibers
#print axioms
  activeFineShading_averageMultiplicity_le_mul_parent_of_fiberAverage

end
end Family8StickyParentAggregatedFiberAverageV1
