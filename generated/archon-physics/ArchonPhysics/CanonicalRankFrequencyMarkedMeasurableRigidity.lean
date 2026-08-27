import ArchonPhysics.CanonicalRankFrequencyMarkedBalanceRigidity
import ArchonPhysics.MeasurableThreeWaveBalanceRigidity

/-!
# Measurable marked graph rigidity from equivalent child trace

This module removes continuity from both the marked weight and its IDS graph.
A measurable scalar graph profile in `Lp Real ∞` is classified by the
measurable interval Cauchy theorem.  Bidirectional absolute continuity of the
child-pair trace transfers the balance law to planar Lebesgue measure and the
resulting classification back to every collision leg.
-/

namespace ArchonPhysics.CanonicalRankFrequencyMarkedMeasurableRigidity

open Set MeasureTheory
open ArchonPhysics.AdditiveTriangleMeasureSupport
open ArchonPhysics.CanonicalRankFrequencyMarkedBalanceRigidity
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.MeasurableThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal

noncomputable section

variable (collision : ResonantThreeWaveMeasure RankFrequencyMark)

/-- Measurable graph concentration descends to the collision reference measure.
This version uses measurability of the equality predicate instead of closedness
of the graph, so neither `F` nor `weight` needs to be continuous. -/
theorem measurableWeight_eq_graphProfile_ae_collisionReferenceMeasure
    (F : Real -> Real) (hF : Measurable F)
    (hfrequencyProjection : forall mark,
      collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    {weight : RankFrequencyMark -> Real} (hweight : Measurable weight) :
    ∀ᵐ mark ∂collisionReferenceMeasure collision,
      weight mark = rankFrequencyGraphProfile F weight
        (collision.frequency mark) := by
  have hprofile : Measurable (rankFrequencyGraphProfile F weight) :=
    measurable_rankFrequencyGraphProfile hF hweight
  have hset : MeasurableSet {mark |
      weight mark = rankFrequencyGraphProfile F weight
        (collision.frequency mark)} :=
    measurableSet_eq_fun hweight (hprofile.comp collision.measurable_frequency)
  have htriad := weight_eq_graphProfile_on_triad_legs_ae collision F
    hfrequencyProjection hgraph weight
  have hleg (leg : Fin 3) :
      ∀ᵐ mark ∂legMarginal collision leg,
        weight mark = rankFrequencyGraphProfile F weight
          (collision.frequency mark) := by
    unfold legMarginal
    exact (ae_map_iff (measurable_triadLeg leg).aemeasurable hset).2 (by
      filter_upwards [htriad] with triad ht
      exact ht leg)
  rw [collisionReferenceMeasure, ae_add_measure_iff, ae_add_measure_iff]
  exact ⟨⟨hleg 0, hleg 1⟩, hleg 2⟩

/-- A measurable marked balance weight is frequency-linear reference-a.e. once
its scalar graph profile is essentially bounded on the frequency interval and
the child-pair trace has the same null sets as planar Lebesgue measure on the
additive triangle. -/
theorem measurableMarkedWeight_linear_ae_of_graph_equivalentVolumeTrace
    (F : Real -> Real) (hF : Measurable F)
    (hfrequencyProjection : forall mark,
      collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    {weight : RankFrequencyMark -> Real}
    (hweight : Measurable weight)
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        weight (triad 0) = weight (triad 1) + weight (triad 2))
    {W : Real} (hW : 0 < W)
    (hfrequencyCollision :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    (hprofileMemLp : MemLp (rankFrequencyGraphProfile F weight) ∞
      (volume.restrict (Icc (0 : Real) W)))
    (hlower : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W))
    (hupper : (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W) ≪
      volume.restrict (additiveFrequencyTriangle W)) :
    exists beta : Real,
      ∀ᵐ mark ∂collisionReferenceMeasure collision,
        weight mark = beta * collision.frequency mark := by
  have hprofile : Measurable (rankFrequencyGraphProfile F weight) :=
    measurable_rankFrequencyGraphProfile hF hweight
  have hprofileBalance := graphProfile_balance_ae_of_weight_balance
    collision F hfrequencyProjection hgraph weight hbalance
  obtain ⟨beta, hlinear⟩ :=
    measurableFrequencyProfile_ae_proportional_of_memLp_top_equivalentTrace
      collision hW hfrequencyCollision hprofile hprofileMemLp
      hprofileBalance hlower hupper
  refine ⟨beta, ?_⟩
  have hfactor := measurableWeight_eq_graphProfile_ae_collisionReferenceMeasure
    collision F hF hfrequencyProjection hgraph hweight
  filter_upwards [hfactor, hlinear] with mark hmark hmarkLinear
  rw [hmark]
  exact hmarkLinear

end

end ArchonPhysics.CanonicalRankFrequencyMarkedMeasurableRigidity
