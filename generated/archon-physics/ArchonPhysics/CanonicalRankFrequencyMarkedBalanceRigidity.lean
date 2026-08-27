import ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
import ArchonPhysics.ContinuousThreeWaveBalanceAEBounded

/-!
# Balance rigidity on the canonical rank--frequency graph

The canonical marked limit identifies every collision leg with the graph

`rank = 1 - F (omega ^ 2)`.

Consequently an arbitrary marked weight has a canonical scalar representative
on every collision leg: evaluate the weight on the graph lift at frequency
`omega`.  This module proves that factorization almost everywhere for each leg
and for the canonical collision reference measure.  It also transports a
triad almost-everywhere balance law to the scalar representative.

For continuous `F` and a continuous marked weight the representative is
continuous.  The positive-volume-trace rigidity theorem can therefore be
applied without separately assuming that the marked weight factors through
frequency.
-/

namespace ArchonPhysics.CanonicalRankFrequencyMarkedBalanceRigidity

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ContinuousThreeWaveBalanceVolumeTrace
open ArchonPhysics.ContinuousThreeWaveBalanceAEBounded
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

noncomputable section

/-- The scalar representative obtained by evaluating a marked weight on the
canonical one-leg rank--frequency graph. -/
def rankFrequencyGraphProfile (F : Real -> Real)
    (weight : RankFrequencyMark -> Real) (omega : Real) : Real :=
  weight (1 - F (omega ^ 2), omega)

@[simp]
theorem rankFrequencyGraphProfile_apply (F : Real -> Real)
    (weight : RankFrequencyMark -> Real) (omega : Real) :
    rankFrequencyGraphProfile F weight omega =
      weight (1 - F (omega ^ 2), omega) := by
  rfl

/-- Evaluation after the three-leg graph lift is exactly evaluation of the
scalar graph profile at the corresponding frequency. -/
theorem weight_liftRankFrequencyTriple_eq_profile
    (F : Real -> Real) (weight : RankFrequencyMark -> Real)
    (frequencies : Fin 3 -> Real) (leg : Fin 3) :
    weight (liftRankFrequencyTriple F frequencies leg) =
      rankFrequencyGraphProfile F weight (frequencies leg) := by
  rfl

/-- A measurable marked weight and measurable IDS give a measurable scalar
graph profile. -/
theorem measurable_rankFrequencyGraphProfile
    {F : Real -> Real} {weight : RankFrequencyMark -> Real}
    (hF : Measurable F) (hweight : Measurable weight) :
    Measurable (rankFrequencyGraphProfile F weight) := by
  unfold rankFrequencyGraphProfile
  fun_prop

/-- A continuous marked weight and continuous IDS give a continuous scalar
graph profile. -/
theorem continuous_rankFrequencyGraphProfile
    {F : Real -> Real} {weight : RankFrequencyMark -> Real}
    (hF : Continuous F) (hweight : Continuous weight) :
    Continuous (rankFrequencyGraphProfile F weight) := by
  unfold rankFrequencyGraphProfile
  fun_prop

/-- On one point of the canonical graph, a marked weight agrees with its
explicit scalar profile.  No regularity of the weight is needed. -/
theorem weight_eq_rankFrequencyGraphProfile_of_eq
    (F : Real -> Real) (weight : RankFrequencyMark -> Real)
    (mark : RankFrequencyMark)
    (hmark : mark.1 = 1 - F (mark.2 ^ 2)) :
    weight mark = rankFrequencyGraphProfile F weight mark.2 := by
  unfold rankFrequencyGraphProfile
  congr 1
  exact Prod.ext hmark rfl

variable (collision : ResonantThreeWaveMeasure RankFrequencyMark)

/-- Graph concentration of the triad measure factors an arbitrary marked
weight on every triad leg. -/
theorem weight_eq_graphProfile_on_triad_legs_ae
    (F : Real -> Real)
    (hfrequency : forall mark, collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    (weight : RankFrequencyMark -> Real) :
    ∀ᵐ triad ∂(collision.collisionMeasure :
        Measure (Fin 3 -> RankFrequencyMark)),
      forall leg : Fin 3,
        weight (triad leg) =
          rankFrequencyGraphProfile F weight
            (collision.frequency (triad leg)) := by
  filter_upwards [hgraph] with triad htriad
  intro leg
  rw [hfrequency]
  exact weight_eq_rankFrequencyGraphProfile_of_eq F weight
    (triad leg) (htriad leg)

/-- Graph concentration descends through a collision-leg pushforward.  The
weight itself is arbitrary; continuity of `F` is used only to make the
one-leg graph a measurable set. -/
theorem weight_eq_graphProfile_ae_legMarginal
    (F : Real -> Real) (hF : Continuous F)
    (hfrequency : forall mark, collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    (weight : RankFrequencyMark -> Real) (leg : Fin 3) :
    ∀ᵐ mark ∂legMarginal collision leg,
      weight mark =
        rankFrequencyGraphProfile F weight (collision.frequency mark) := by
  have hclosed : IsClosed {mark : RankFrequencyMark |
      mark.1 = 1 - F (mark.2 ^ 2)} := by
    exact isClosed_eq continuous_fst
      (continuous_const.sub (hF.comp (continuous_snd.pow 2)))
  have hlegGraph :
      ∀ᵐ mark ∂legMarginal collision leg,
        mark.1 = 1 - F (mark.2 ^ 2) := by
    unfold legMarginal
    apply (ae_map_iff
      (measurable_triadLeg leg).aemeasurable hclosed.measurableSet).2
    filter_upwards [hgraph] with triad htriad
    exact htriad leg
  filter_upwards [hlegGraph] with mark hmark
  rw [hfrequency]
  exact weight_eq_rankFrequencyGraphProfile_of_eq F weight mark hmark

/-- The sum of the three leg marginals inherits the canonical graph
factorization. -/
theorem weight_eq_graphProfile_ae_collisionReferenceMeasure
    (F : Real -> Real) (hF : Continuous F)
    (hfrequency : forall mark, collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    (weight : RankFrequencyMark -> Real) :
    ∀ᵐ mark ∂collisionReferenceMeasure collision,
      weight mark =
        rankFrequencyGraphProfile F weight (collision.frequency mark) := by
  rw [collisionReferenceMeasure, ae_add_measure_iff, ae_add_measure_iff]
  exact ⟨⟨weight_eq_graphProfile_ae_legMarginal collision F hF
      hfrequency hgraph weight 0,
    weight_eq_graphProfile_ae_legMarginal collision F hF
      hfrequency hgraph weight 1⟩,
    weight_eq_graphProfile_ae_legMarginal collision F hF
      hfrequency hgraph weight 2⟩

/-- A marked balance law transports to the explicit scalar profile on the
same triad measure.  Neither the IDS nor the weight needs regularity here. -/
theorem graphProfile_balance_ae_of_weight_balance
    (F : Real -> Real)
    (hfrequency : forall mark, collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    (weight : RankFrequencyMark -> Real)
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        weight (triad 0) = weight (triad 1) + weight (triad 2)) :
    ∀ᵐ triad ∂(collision.collisionMeasure :
        Measure (Fin 3 -> RankFrequencyMark)),
      rankFrequencyGraphProfile F weight
          (collision.frequency (triad 0)) =
        rankFrequencyGraphProfile F weight
            (collision.frequency (triad 1)) +
          rankFrequencyGraphProfile F weight
            (collision.frequency (triad 2)) := by
  filter_upwards [hgraph, hbalance] with triad htriad hbalanced
  have hleg (leg : Fin 3) :
      weight (triad leg) =
        rankFrequencyGraphProfile F weight
          (collision.frequency (triad leg)) := by
    rw [hfrequency]
    exact weight_eq_rankFrequencyGraphProfile_of_eq F weight
      (triad leg) (htriad leg)
  rw [← hleg 0, ← hleg 1, ← hleg 2]
  exact hbalanced

/-- Positive volume trace rigidity for continuous marked weights on the
canonical graph.  The usual frequency-only factorization hypothesis is not an
input: graph concentration proves it on the collision reference measure. -/
theorem continuousMarkedWeight_linear_ae_of_graph_positive_volumeTrace
    (F : Real -> Real) (hF : Continuous F)
    (hfrequencyProjection : forall mark,
      collision.frequency mark = mark.2)
    (hgraph :
      ∀ᵐ triad ∂(collision.collisionMeasure :
          Measure (Fin 3 -> RankFrequencyMark)),
        triad ∈ rankFrequencyTripleGraph F)
    {weight : RankFrequencyMark -> Real}
    (hweight : Continuous weight)
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
    (hfrequencyReference :
      ∀ᵐ mark ∂collisionReferenceMeasure collision,
        collision.frequency mark ∈ Icc (0 : Real) W)
    {density : Real × Real -> ENNReal}
    (hdensity : AEMeasurable density
      (volume.restrict (additiveFrequencyTriangle W)))
    (hdensity_ne_zero :
      ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
        density pair ≠ 0)
    (hpair :
      (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W) =
        (volume.restrict (additiveFrequencyTriangle W)).withDensity density) :
    exists beta : Real,
      (forall omega, omega ∈ Icc (0 : Real) W ->
        rankFrequencyGraphProfile F weight omega = beta * omega) ∧
      (∀ᵐ mark ∂collisionReferenceMeasure collision,
        weight mark = beta * collision.frequency mark) := by
  have hprofile : ContinuousOn (rankFrequencyGraphProfile F weight)
      (Icc (0 : Real) W) :=
    (continuous_rankFrequencyGraphProfile hF hweight).continuousOn
  have hprofileBalance := graphProfile_balance_ae_of_weight_balance
    collision F hfrequencyProjection hgraph weight hbalance
  have hfullSupport := fullSupport_of_restrict_eq_withDensity hW
    hdensity hdensity_ne_zero hpair
  obtain ⟨beta, hlinear⟩ :=
    continuousFrequencyProfile_linear_of_collision_ae_bounds
      collision hW hfrequencyCollision hprofile hprofileBalance hfullSupport
  refine ⟨beta, hlinear, ?_⟩
  have hfactor := weight_eq_graphProfile_ae_collisionReferenceMeasure
    collision F hF hfrequencyProjection hgraph weight
  filter_upwards [hfactor, hfrequencyReference] with mark hmark hmarkFrequency
  rw [hmark, hlinear _ hmarkFrequency]

end

end ArchonPhysics.CanonicalRankFrequencyMarkedBalanceRigidity
