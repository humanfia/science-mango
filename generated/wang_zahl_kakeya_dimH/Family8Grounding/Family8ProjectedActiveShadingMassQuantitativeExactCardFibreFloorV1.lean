import Family8Grounding.Family8ProjectedActiveShadingMassPositiveExactCardBandV5
import Family8Grounding.Family8Family7QuantitativeFibreFloorSelectionV2
import Mathlib.Tactic

/-!
# Quantitative projected-mass exact-card and fibre-floor selection

The earlier projected-mass selector retained only positivity of one exact
active-card band.  Here the same finite pigeonhole is run without discarding
its quantitative conclusion.  Thus one exact-card band retains at least the
reciprocal of the actual number of possible positive card values of the
literal window-restricted shading mass.

The second selector stays on that very band and on the same shading, active
set, graph and windows.  A dyadic lower-fibre exhaustion retains half of its
projected shading-mass measure.  We deliberately retain the intersection
with the original exact-card band: this prevents the lower cut from silently
admitting points with additional small positive fibres.

The final sandwich is the honest same-object conclusion.  On the selected
intersection every one of the `n` positive fibres has the displayed floor,
while the projected weighted mass is bounded above by `n` times planar
volume when the fibre window has volume at most one.  A reverse estimate by
`fibreFloor * volume` with a floor-independent coefficient would require a
two-sided fibre-mass bucket, and is not asserted here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7FiniteProjectedPositiveExactCardBandV1
open Family8Family7PositiveBandLowerFibreFloorV1
open Family8Family7QuantitativeFibreFloorSelectionV2
open Family8Family7ShadingMassPositiveProjectedActiveRegionV1
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ProjectedActiveShadingMassPositiveExactCardBandV5
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

/-- The literal region on which the shading-aware projected active pattern is
nonempty. -/
def projectedPositiveActiveRegion
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) : Set ProjectionSpace :=
  let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
  {u | u ∈ Z.base ∧ (Z.activeAtPoint u).Nonempty}

theorem measurableSet_projectedPositiveActiveRegion
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) :
    MeasurableSet
      (projectedPositiveActiveRegion Y active f hf X hX I hI) := by
  let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
  have hcardMeasurable : Measurable fun u : ProjectionSpace ↦
      (Z.activeAtPoint u).card :=
    Z.measurable_activeValue fun s ↦ s.card
  have hnonempty : MeasurableSet
      {u : ProjectionSpace | (Z.activeAtPoint u).Nonempty} := by
    have hpreimage := hcardMeasurable
      (Set.to_countable {n : Nat | 1 ≤ n}).measurableSet
    convert hpreimage using 1
    ext u
    simp [Finset.one_le_card]
  exact Z.measurable_base.inter hnonempty

/-- The projected weighted measure of the nonempty active region is exactly
the literal mass of the same window-restricted active shading. -/
theorem projectedActiveShadingMassMeasure_activeRegion_eq_activeWindowMass
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) :
    projectedActiveShadingMassMeasure
        (shadingWindowRestriction Y f hf X hX I hI) active f
        (projectedPositiveActiveRegion Y active f hf X hX I hI) =
      ∑ i ∈ active,
        volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i) := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let g : ProjectionSpace → ENNReal := fun u ↦
    projectedActiveMultiplicity Yw active f u
  let R : Set ProjectionSpace :=
    projectedPositiveActiveRegion Y active f hf X hX I hI
  let mu : Measure ProjectionSpace :=
    projectedActiveShadingMassMeasure Yw active f
  have hg : Measurable g := by
    have hsum : Measurable fun u : ProjectionSpace ↦
        ∑ i ∈ active, shadingFiberMass Yw f i u := by
      refine Finset.measurable_fun_sum active fun i _hi ↦ ?_
      exact measurable_shadingFiberMass Yw f hf i
    simpa only [g, projectedActiveMultiplicity_eq_sum_shadingFiberMass
      Yw active f hf] using hsum
  have hsupport : Function.support g ∩ X = R := by
    ext u
    simp only [Function.mem_support, ne_eq, Set.mem_inter_iff]
    change (g u ≠ 0 ∧ u ∈ X) ↔
      (u ∈ X ∧ (Z.activeAtPoint u).Nonempty)
    constructor
    · rintro ⟨hgu, huX⟩
      have hsumPos : 0 < ∑ i ∈ active, shadingFiberMass Yw f i u := by
        rw [← projectedActiveMultiplicity_eq_sum_shadingFiberMass
          Yw active f hf u]
        exact pos_iff_ne_zero.mpr hgu
      obtain ⟨i, hi, himass⟩ := Finset.sum_pos_iff.mp hsumPos
      refine ⟨huX, ⟨i, ?_⟩⟩
      exact (mem_activeAtPoint_shadingAwareProjectedPhysical
        Y active f hf X hX I hI u i).mpr ⟨hi, huX, himass⟩
    · rintro ⟨huX, ⟨i, hi⟩⟩
      have hidata := (mem_activeAtPoint_shadingAwareProjectedPhysical
        Y active f hf X hX I hI u i).mp hi
      refine ⟨?_, huX⟩
      apply ne_of_gt
      change 0 < projectedActiveMultiplicity Yw active f u
      rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
        Yw active f hf u, Finset.sum_pos_iff]
      exact ⟨i, hidata.1, hidata.2.2⟩
  have hRsubset : R ⊆ X := by
    intro u hu
    exact hu.1
  have hdiffZero : mu (X \ R) = 0 := by
    change (volume.withDensity g) (X \ R) = 0
    apply (MeasureTheory.withDensity_apply_eq_zero hg).2
    have hempty : {u : ProjectionSpace | g u ≠ 0} ∩ (X \ R) = ∅ := by
      rw [show {u : ProjectionSpace | g u ≠ 0} = Function.support g by rfl]
      rw [← Set.inter_sdiff_assoc, hsupport, Set.sdiff_self]
    rw [hempty, measure_empty]
  have hmuRX : mu R = mu X :=
    measure_eq_measure_of_null_sdiff hRsubset hdiffZero
  calc
    projectedActiveShadingMassMeasure Yw active f R = mu R := rfl
    _ = mu X := hmuRX
    _ = ∑ i ∈ active, restrictedMass Yw
        (twistedProjection f ⁻¹' X) i := by
      simpa only [mu] using
        (projectedActiveShadingMassMeasure_apply Yw active f hf hX)
    _ = ∑ i ∈ active, volume (Yw.carrier i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact restrictedMass_shadingWindowRestriction_projectedBase
        Y f hf X hX I hI i

/-- Weighted-mass-first exact-card selection.  The denominator is the actual
number of possible positive active-card values, namely `ambient.card`. -/
theorem exists_exactCard_projectedActiveShadingMassBand_ge_average
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hmass : 0 < ∑ i ∈ active,
      volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i)) :
    let Yw := shadingWindowRestriction Y f hf X hX I hI
    let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
    let mu := projectedActiveShadingMassMeasure Yw active f
    ∃ n : Nat, 1 ≤ n ∧ n ≤ Z.ambient.card ∧
      (∑ i ∈ active, volume (Yw.carrier i)) /
          (Z.ambient.card : ENNReal) ≤
        mu (Z.multiplicityBand n n) := by
  dsimp only
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let mu : Measure ProjectionSpace :=
    projectedActiveShadingMassMeasure Yw active f
  let R : Set ProjectionSpace :=
    projectedPositiveActiveRegion Y active f hf X hX I hI
  let cardAt : ProjectionSpace → Nat := fun u ↦ (Z.activeAtPoint u).card
  let labels : Finset Nat := Finset.Icc 1 Z.ambient.card
  have hR : MeasurableSet R := by
    exact measurableSet_projectedPositiveActiveRegion
      Y active f hf X hX I hI
  have hmuR : mu R = ∑ i ∈ active, volume (Yw.carrier i) := by
    simpa only [mu, R, Yw] using
      projectedActiveShadingMassMeasure_activeRegion_eq_activeWindowMass
        Y active f hf X hX I hI
  have hpositive : 0 < mu R := by
    rw [hmuR]
    simpa only [Yw] using hmass
  have hRnonempty : R.Nonempty := nonempty_of_measure_ne_zero hpositive.ne'
  obtain ⟨u, huR⟩ := hRnonempty
  have huActive : (Z.activeAtPoint u).Nonempty := huR.2
  have hambientCard : 1 ≤ Z.ambient.card := by
    exact (Finset.one_le_card.mpr huActive).trans
      (Finset.card_le_card
        (finiteIncidenceActiveAtPoint_subset Z.ambient
          (fun i x ↦ x ∈ Z.carrier i) u))
  have hlabels : labels.Nonempty := by
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hambientCard⟩⟩
  have hcardMeasurable : Measurable cardAt :=
    Z.measurable_activeValue fun s ↦ s.card
  have hrange : ∀ u, u ∈ R → cardAt u ∈ labels := by
    intro u hu
    apply Finset.mem_Icc.mpr
    refine ⟨Finset.one_le_card.mpr hu.2, ?_⟩
    exact Finset.card_le_card
      (finiteIncidenceActiveAtPoint_subset Z.ambient
        (fun i x ↦ x ∈ Z.carrier i) u)
  obtain ⟨n, hn, haverage⟩ :=
    exists_measurableLabelCell_measure_ge_average
      mu labels hlabels hR hcardMeasurable hrange
  have hcellEq : measurableLabelCell R cardAt n =
      Z.multiplicityBand n n := by
    ext u
    rw [FiniteProjectedShading.mem_multiplicityBand]
    simp only [measurableLabelCell, R, projectedPositiveActiveRegion,
      cardAt, Z, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨huBase, _huPos⟩, huCard⟩
      exact ⟨huBase, by omega, by omega⟩
    · rintro ⟨huBase, hnLower, hnUpper⟩
      have huCard :
          ((shadingAwareProjectedPhysical
            Y active f hf X hX I hI).activeAtPoint u).card = n := by
        omega
      have hnPos : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have huOne : 1 ≤
          ((shadingAwareProjectedPhysical
            Y active f hf X hX I hI).activeAtPoint u).card := by
        rw [huCard]
        exact hnPos
      exact ⟨⟨huBase, Finset.one_le_card.mp huOne⟩, huCard⟩
  have hlabelsCard : labels.card = Z.ambient.card := by
    simp [labels]
  refine ⟨n, (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2, ?_⟩
  rw [← hcellEq, ← hmuR, ← hlabelsCard]
  exact haverage

/-! ## A genuine fibre floor on the same weighted exact-card band -/

/-- A dyadic lower-fibre cut retains half of the projected shading mass of
the fixed exact-card band.  The retained set is explicitly intersected with
the original band, so no additional positive fibres can enter after the
cut. -/
theorem exists_dyadic_fibreFloor_half_projectedMass_exactCardBand
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (n : Nat)
    (hband : 0 < projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f
      ((shadingAwareProjectedPhysical
        Y active f hf X hX I hI).multiplicityBand n n))
    (hbandFinite : projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f
      ((shadingAwareProjectedPhysical
        Y active f hf X hX I hI).multiplicityBand n n) ≠ ∞) :
    ∃ level : Nat,
      0 < dyadicFibreFloor level ∧
      projectedActiveShadingMassMeasure
          (shadingWindowRestriction Y f hf X hX I hI) active f
          ((shadingAwareProjectedPhysical
            Y active f hf X hX I hI).multiplicityBand n n) ≤
        fibreLevelBinLoss *
          projectedActiveShadingMassMeasure
            (shadingWindowRestriction Y f hf X hX I hI) active f
            ((shadingAwareProjectedPhysical
                Y active f hf X hX I hI).multiplicityBand n n ∩
              (shadingAwareProjectedPhysicalLowerBucket
                Y active f hf X hX I hI
                  (dyadicFibreFloor level)).multiplicityBand n n) := by
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lowerAt := fun level : Nat ↦ shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI (dyadicFibreFloor level)
  let mu : Measure ProjectionSpace :=
    projectedActiveShadingMassMeasure Yw active f
  let E := positive.multiplicityBand n n
  let kept := fun level : Nat ↦ E ∩ (lowerAt level).multiplicityBand n n
  have hband' : 0 < mu E := by
    simpa only [mu, E, positive, Yw] using hband
  have hbandFinite' : mu E ≠ ∞ := by
    simpa only [mu, E, positive, Yw] using hbandFinite
  have hactiveMono (l m : Nat) (hlm : l ≤ m) (u : ProjectionSpace) :
      (lowerAt l).activeAtPoint u ⊆ (lowerAt m).activeAtPoint u := by
    intro i hi
    have hiData :=
      (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI (dyadicFibreFloor l) u i).mp (by
          simpa only [lowerAt] using hi)
    have hiNext : i ∈
        (shadingAwareProjectedPhysicalLowerBucket
          Y active f hf X hX I hI (dyadicFibreFloor m)).activeAtPoint u := by
      apply (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI (dyadicFibreFloor m) u i).mpr
      exact ⟨hiData.1, hiData.2.1,
        (dyadicFibreFloor_antitone hlm).trans hiData.2.2⟩
    simpa only [lowerAt] using hiNext
  have hactivePositive (level : Nat) (u : ProjectionSpace) :
      (lowerAt level).activeAtPoint u ⊆ positive.activeAtPoint u := by
    simpa only [lowerAt, positive] using
      (activeAtPoint_lowerBucket_subset_positive
        Y active f hf X hX I hI (dyadicFibreFloor_pos level) u)
  have hkeptMono : Monotone kept := by
    intro l m hlm u hu
    rcases hu with ⟨huE, huL⟩
    have huEData := positive.mem_multiplicityBand.mp (by
      simpa only [E] using huE)
    have huLData := (lowerAt l).mem_multiplicityBand.mp huL
    refine ⟨huE, (lowerAt m).mem_multiplicityBand.mpr ?_⟩
    refine ⟨huLData.1, ?_, ?_⟩
    · exact huLData.2.1.trans
        (Finset.card_le_card (hactiveMono l m hlm u))
    · exact (Finset.card_le_card (hactivePositive m u)).trans
        huEData.2.2
  have hkeptUnion : (⋃ level : Nat, kept level) = E := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun _level ↦ Set.inter_subset_left
    · intro u huE
      have huEData := positive.mem_multiplicityBand.mp (by
        simpa only [E] using huE)
      have hmassPos : ∀ i, i ∈ positive.activeAtPoint u →
          0 < shadingFiberMass Yw f i u := by
        intro i hi
        exact (mem_activeAtPoint_shadingAwareProjectedPhysical
          Y active f hf X hX I hI u i).mp hi |>.2.2
      obtain ⟨pointFloor, hpointFloor, hpointLower⟩ :=
        exists_common_pos_lowerBound_on_finset
          (positive.activeAtPoint u) (fun i ↦ shadingFiberMass Yw f i u)
          hmassPos
      obtain ⟨level, hlevel⟩ :=
        ENNReal.exists_inv_two_pow_lt (ne_of_gt hpointFloor)
      have hactiveEq : (lowerAt level).activeAtPoint u =
          positive.activeAtPoint u := by
        ext i
        constructor
        · intro hi
          exact hactivePositive level u hi
        · intro hi
          have hiData := (mem_activeAtPoint_shadingAwareProjectedPhysical
            Y active f hf X hX I hI u i).mp hi
          have hiLower : i ∈
              (shadingAwareProjectedPhysicalLowerBucket
                Y active f hf X hX I hI
                  (dyadicFibreFloor level)).activeAtPoint u := by
            apply (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
              Y active f hf X hX I hI (dyadicFibreFloor level) u i).mpr
            exact ⟨hiData.1, hiData.2.1,
              (le_of_lt hlevel).trans (hpointLower i hi)⟩
          simpa only [lowerAt] using hiLower
      apply Set.mem_iUnion.mpr
      refine ⟨level, huE, ?_⟩
      apply (lowerAt level).mem_multiplicityBand.mpr
      refine ⟨huEData.1, ?_, ?_⟩
      · rw [hactiveEq]
        exact huEData.2.1
      · rw [hactiveEq]
        exact huEData.2.2
  have hmeasureTendsto :
      Tendsto (fun level : Nat ↦ mu (kept level)) atTop (𝓝 (mu E)) := by
    have h := tendsto_measure_iUnion_atTop (μ := mu) hkeptMono
    rw [hkeptUnion] at h
    simpa only [Function.comp_def] using h
  have hhalf : mu E / 2 < mu E := by
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    simpa only [one_mul, mul_comm] using
      ENNReal.mul_lt_mul_left hband'.ne' hbandFinite' ENNReal.one_lt_two
  obtain ⟨level, hlevel⟩ :=
    ((tendsto_order.1 hmeasureTendsto).1 _ hhalf).exists
  have hhalfSelected : mu E / 2 ≤ mu (kept level) := le_of_lt hlevel
  have hretention : mu E ≤ mu (kept level) * 2 :=
    (ENNReal.div_le_iff_le_mul (by norm_num) (by norm_num)).mp hhalfSelected
  refine ⟨level, dyadicFibreFloor_pos level, ?_⟩
  simpa only [mu, E, kept, positive, lowerAt, Yw, fibreLevelBinLoss,
    mul_comm] using hretention

/-- On the retained intersection the projected weighted mass has both the
literal `n * fibreFloor` lower density and the exact-card upper density `n`,
provided the fibre window has volume at most one. -/
theorem projectedMass_exactCard_dyadicFibreFloor_sandwich
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (hIone : volume I ≤ 1)
    (n level : Nat) :
    let Yw := shadingWindowRestriction Y f hf X hX I hI
    let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
    let lower := shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI (dyadicFibreFloor level)
    let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
    let mu := projectedActiveShadingMassMeasure Yw active f
    (dyadicFibreFloor level * (n : ENNReal)) * volume E ≤ mu E ∧
      mu E ≤ (n : ENNReal) * volume E := by
  dsimp only
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI (dyadicFibreFloor level)
  let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
  let g : ProjectionSpace → ENNReal := fun u ↦
    projectedActiveMultiplicity Yw active f u
  have hEmeasurable : MeasurableSet E :=
    (positive.measurableSet_multiplicityBand n n).inter
      (lower.measurableSet_multiplicityBand n n)
  have hlowerPoint : ∀ u, u ∈ E →
      dyadicFibreFloor level * (n : ENNReal) ≤ g u := by
    intro u hu
    have huLower := lower.mem_multiplicityBand.mp hu.2
    have hcard : (lower.activeAtPoint u).card = n := by omega
    have h := level_mul_activeAtPoint_card_le_projectedActiveMultiplicity
      Y active f hf X hX I hI (dyadicFibreFloor level) u
    simpa only [lower, Yw, g, hcard] using h
  have hupperPoint : ∀ u, u ∈ E → g u ≤ (n : ENNReal) := by
    intro u hu
    have huPositive := positive.mem_multiplicityBand.mp hu.1
    have hcard : (positive.activeAtPoint u).card = n := by omega
    have h :=
      projectedActiveMultiplicity_shadingWindowRestriction_le_activeAtPoint_card
        Y active f hf X hX I hI hIone u huPositive.1
    simpa only [positive, Yw, g, hcard] using h
  constructor
  · calc
      (dyadicFibreFloor level * (n : ENNReal)) * volume E =
          ∫⁻ _u in E, dyadicFibreFloor level * (n : ENNReal)
            ∂(volume : Measure ProjectionSpace) := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace) :=
        setLIntegral_mono' hEmeasurable hlowerPoint
      _ = projectedActiveShadingMassMeasure Yw active f E := by
        rw [projectedActiveShadingMassMeasure,
          MeasureTheory.withDensity_apply _ hEmeasurable]
  · calc
      projectedActiveShadingMassMeasure Yw active f E =
          ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace) := by
        rw [projectedActiveShadingMassMeasure,
          MeasureTheory.withDensity_apply _ hEmeasurable]
      _ ≤ ∫⁻ _u in E, (n : ENNReal)
          ∂(volume : Measure ProjectionSpace) :=
        setLIntegral_mono' hEmeasurable hupperPoint
      _ = (n : ENNReal) * volume E := by
        rw [setLIntegral_const]

#print axioms projectedActiveShadingMassMeasure_activeRegion_eq_activeWindowMass
#print axioms exists_exactCard_projectedActiveShadingMassBand_ge_average
#print axioms exists_dyadic_fibreFloor_half_projectedMass_exactCardBand
#print axioms projectedMass_exactCard_dyadicFibreFloor_sandwich

end
end Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1
