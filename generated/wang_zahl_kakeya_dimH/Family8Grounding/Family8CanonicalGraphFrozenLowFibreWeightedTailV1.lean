import Family8Grounding.Family8PyzCarrierGraphStripVolumeV1
import Family8Grounding.Family8CanonicalGraphFrozenLowerBucketGraphStripSupportV1
import Family8Grounding.Family8ProjectedActiveShadingMassMeasureV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenLowFibreWeightedTailV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ProjectedTubeImageGraphStripSupportV1
open Family8PyzCarrierGraphStripVolumeV1
open Family8ShadingAwareProjectedPhysicalImageSupportV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u

variable {iota : Type u} {G : ConvexFamily iota}

/-- The post-truncation projected datum.  Positivity is kept explicitly so
that level zero never activates a zero-mass fibre. -/
noncomputable def positiveLowerFibreProjectedPhysical
    [DecidableEq iota]
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal) :
    FiniteProjectedShading ProjectionSpace iota where
  ambient := active
  base := Set.univ
  carrier := fun i =>
    {u | 0 < shadingFiberMass Y f i u ∧
      level ≤ shadingFiberMass Y f i u}
  measurable_base := MeasurableSet.univ
  measurable_carrier := by
    intro i _hi
    have hmass := measurable_shadingFiberMass Y f hf i
    exact (measurableSet_lt measurable_const hmass).inter
      (measurableSet_le measurable_const hmass)

@[simp]
theorem mem_activeAtPoint_positiveLowerFibreProjectedPhysical
    [DecidableEq iota]
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal)
    (u : ProjectionSpace) (i : iota) :
    i ∈ (positiveLowerFibreProjectedPhysical
      Y active f hf level).activeAtPoint u ↔
      i ∈ active ∧ 0 < shadingFiberMass Y f i u ∧
        level ≤ shadingFiberMass Y f i u := by
  rw [FiniteProjectedShading.mem_activeAtPoint]
  rfl

/-- Weighted contribution of fibres strictly below the truncation level. -/
noncomputable def lowFibreWeightedMultiplicity
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (level : ENNReal)
    (u : ProjectionSpace) : ENNReal :=
  ∑ i ∈ active,
    if shadingFiberMass Y f i u < level then
      shadingFiberMass Y f i u
    else 0

/-- Weighted contribution of positive fibres at or above the level. -/
noncomputable def highFibreWeightedMultiplicity
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (level : ENNReal)
    (u : ProjectionSpace) : ENNReal :=
  ∑ i ∈ active,
    if 0 < shadingFiberMass Y f i u ∧
        level ≤ shadingFiberMass Y f i u then
      shadingFiberMass Y f i u
    else 0

theorem measurable_lowFibreWeightedMultiplicity
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal) :
    Measurable (lowFibreWeightedMultiplicity Y active f level) := by
  classical
  unfold lowFibreWeightedMultiplicity
  exact Finset.measurable_fun_sum active fun i _hi ↦
    Measurable.ite
      (measurableSet_lt (measurable_shadingFiberMass Y f hf i)
        measurable_const)
      (measurable_shadingFiberMass Y f hf i) measurable_const

theorem measurable_highFibreWeightedMultiplicity
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal) :
    Measurable (highFibreWeightedMultiplicity Y active f level) := by
  classical
  unfold highFibreWeightedMultiplicity
  exact Finset.measurable_fun_sum active fun i _hi ↦
    Measurable.ite
      ((measurableSet_lt measurable_const
        (measurable_shadingFiberMass Y f hf i)).inter
        (measurableSet_le measurable_const
          (measurable_shadingFiberMass Y f hf i)))
      (measurable_shadingFiberMass Y f hf i) measurable_const

/-- Low and positive-high fibres exactly partition the weighted projected
multiplicity, including at level zero. -/
theorem projectedActiveMultiplicity_eq_low_add_high
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal)
    (u : ProjectionSpace) :
    projectedActiveMultiplicity Y active f u =
      lowFibreWeightedMultiplicity Y active f level u +
        highFibreWeightedMultiplicity Y active f level u := by
  classical
  rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
    Y active f hf u]
  unfold lowFibreWeightedMultiplicity highFibreWeightedMultiplicity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let mass := shadingFiberMass Y f i u
  by_cases hlow : mass < level
  · have hnle : ¬ level ≤ mass := not_le_of_gt hlow
    simp only [mass, if_pos hlow, hnle, and_false, if_false, add_zero]
  · have hle : level ≤ mass := le_of_not_gt hlow
    by_cases hzero : mass = 0
    · simp [mass, hzero]
    · have hpos : 0 < mass := pos_iff_ne_zero.mpr hzero
      simp only [mass, if_neg hlow, zero_add, hpos, hle, and_self,
        if_true]

/-- Integrated low-fibre weighted mass on a projected set. -/
noncomputable def lowFibreWeightedMass
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (level : ENNReal)
    (E : Set ProjectionSpace) : ENNReal :=
  ∫⁻ u in E, lowFibreWeightedMultiplicity Y active f level u
    ∂(volume : Measure ProjectionSpace)

/-- Integrated positive-high-fibre weighted mass on a projected set. -/
noncomputable def highFibreWeightedMass
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (level : ENNReal)
    (E : Set ProjectionSpace) : ENNReal :=
  ∫⁻ u in E, highFibreWeightedMultiplicity Y active f level u
    ∂(volume : Measure ProjectionSpace)

theorem projectedActiveShadingMassMeasure_eq_low_add_high
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f) (level : ENNReal)
    (E : Set ProjectionSpace) (hE : MeasurableSet E) :
    projectedActiveShadingMassMeasure Y active f E =
      lowFibreWeightedMass Y active f level E +
        highFibreWeightedMass Y active f level E := by
  rw [projectedActiveShadingMassMeasure,
    MeasureTheory.withDensity_apply _ hE]
  unfold lowFibreWeightedMass highFibreWeightedMass
  rw [← lintegral_add_left
    (measurable_lowFibreWeightedMultiplicity Y active f hf level) _]
  apply lintegral_congr
  intro u
  exact projectedActiveMultiplicity_eq_low_add_high
    Y active f hf level u

/-- If every positive fibre carrier has planar volume at most `V`, the
total weighted mass discarded below `level` is at most
`active.card * level * V`. -/
theorem lowFibreWeightedMass_univ_le_card_mul_level_mul_volume
    (Y : Shading G) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (level V : ENNReal)
    (hvolume : ∀ i, i ∈ active →
      volume {u : ProjectionSpace | 0 < shadingFiberMass Y f i u} ≤ V) :
    lowFibreWeightedMass Y active f level Set.univ ≤
      (active.card : ENNReal) * (level * V) := by
  classical
  unfold lowFibreWeightedMass lowFibreWeightedMultiplicity
  simp only [Measure.restrict_univ]
  rw [lintegral_finsetSum active]
  · calc
      (∑ i ∈ active, ∫⁻ u,
          if shadingFiberMass Y f i u < level then
            shadingFiberMass Y f i u
          else 0 ∂(volume : Measure ProjectionSpace)) ≤
          ∑ _i ∈ active, level * V := by
        apply Finset.sum_le_sum
        intro i hi
        let mass : ProjectionSpace → ENNReal :=
          fun u ↦ shadingFiberMass Y f i u
        have hpositive :
            MeasurableSet {u : ProjectionSpace | 0 < mass u} :=
          measurableSet_lt measurable_const
            (measurable_shadingFiberMass Y f hf i)
        calc
          (∫⁻ u, if mass u < level then mass u else 0
              ∂(volume : Measure ProjectionSpace)) ≤
              ∫⁻ u, {v : ProjectionSpace | 0 < mass v}.indicator
                (fun _ ↦ level) u
                ∂(volume : Measure ProjectionSpace) := by
            apply lintegral_mono
            intro u
            by_cases hlow : mass u < level
            · by_cases hzero : mass u = 0
              · simp [hzero]
              · have hpos : 0 < mass u := pos_iff_ne_zero.mpr hzero
                simp only [if_pos hlow, Set.indicator,
                  Set.mem_ofPred_eq, hpos, if_true]
                exact hlow.le
            · simp [hlow]
          _ = level * volume {u : ProjectionSpace | 0 < mass u} :=
            lintegral_indicator_const hpositive level
          _ ≤ level * V := by
            gcongr
            simpa only [mass] using hvolume i hi
      _ = (active.card : ENNReal) * (level * V) := by
        simp [nsmul_eq_mul]
  · intro i _hi
    exact Measurable.ite
      (measurableSet_lt (measurable_shadingFiberMass Y f hf i)
        measurable_const)
      (measurable_shadingFiberMass Y f hf i) measurable_const

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

theorem sameGraph_zeroWindow_positiveCarrier_volume_le_24_tau
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (i : fineIndex)
    (hi : i ∈ verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      (firstCrossingFamilyVerticalSource R.axis F P R.k) R.label) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let positive := shadingAwareProjectedPhysical Z graph f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    volume (positive.carrier i) ≤ 24 * (tau : ENNReal) := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let positive := shadingAwareProjectedPhysical Z graph f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let Q := Classical.choice R.graphCertificate
  have hiSource : i ∈ VS.source :=
    (mem_verticalSourceGraphCBucketFiber_iff
      ((tau : Real) / 2) VS R.label i).mp (by
        simpa only [graph] using hi) |>.1
  have hvertical : (1 / 2 : Real) ≤
      |(VS.family.tubes i).axis.direction 2| :=
    VS.source_direction_final_half i hiSource
  have hB2 : (VS.family.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 2 := by
    simpa only [VS, graph] using Q.vertical_b2 i hi
  have hsupport : positive.carrier i ⊆
      pyzCarrierGraphStrip (-2) 2
        (projectedTubeCinematicTrace f0 (VS.family.tubes i))
        (3 * (tau : Real)) := by
    intro u hu
    have himage : u ∈ projectedTubeImageCarrier f0
        (VS.family.tubes i) := by
      apply shadingAwareProjectedPhysical_carrier_subset_projectedTubeImageCarrier
        VS.family Z graph f0 measurable_const Set.univ MeasurableSet.univ
          Set.univ MeasurableSet.univ i
      simpa only [positive] using hu
    simpa only [f0] using
      (projectedTubeImageCarrier_subset_pyzGraphStrip_negTwo_two_three
        (VS.family.tubes i) hvertical hB2 (by
          simpa only [f0] using himage))
  calc
    volume (positive.carrier i) ≤
        volume (pyzCarrierGraphStrip (-2) 2
          (projectedTubeCinematicTrace f0 (VS.family.tubes i))
          (3 * (tau : Real))) := measure_mono hsupport
    _ ≤ 24 * (tau : ENNReal) := by
      apply volume_pyzCarrierGraphStrip_negTwo_two_three_mul_le
      exact (continuous_projectedTubeCinematicTrace f0
        continuous_const (VS.family.tubes i)).measurable

/-- On the frozen canonical graph, discarding every fibre below `level`
costs at most `24 * tau * graph.card * level` in genuine projected
weighted mass. -/
theorem sameGraph_zeroWindow_lowFibreWeightedMass_le
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (level : ENNReal) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    lowFibreWeightedMass Yw graph f0 level Set.univ ≤
      24 * (tau : ENNReal) * (graph.card : ENNReal) * level := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  have hvolume : ∀ i, i ∈ graph →
      volume {u : ProjectionSpace |
        0 < shadingFiberMass Yw f0 i u} ≤ 24 * (tau : ENNReal) := by
    intro i hi
    have hsupport :=
      sameGraph_zeroWindow_positiveCarrier_volume_le_24_tau
        (R := R) i (by simpa only [graph] using hi)
    have hset :
        {u : ProjectionSpace | 0 < shadingFiberMass Yw f0 i u} =
          (shadingAwareProjectedPhysical Z graph f0 measurable_const
            Set.univ MeasurableSet.univ Set.univ
              MeasurableSet.univ).carrier i := by
      ext u
      simp [shadingAwareProjectedPhysical, Yw]
    rw [hset]
    simpa only [VS, graph, Z, f0] using hsupport
  calc
    lowFibreWeightedMass Yw graph f0 level Set.univ ≤
        (graph.card : ENNReal) *
          (level * (24 * (tau : ENNReal))) :=
      lowFibreWeightedMass_univ_le_card_mul_level_mul_volume
        Yw graph f0 measurable_const level
          (24 * (tau : ENNReal)) hvolume
    _ = 24 * (tau : ENNReal) * (graph.card : ENNReal) * level := by
      ac_rfl

end
end Family8CanonicalGraphFrozenLowFibreWeightedTailV1
