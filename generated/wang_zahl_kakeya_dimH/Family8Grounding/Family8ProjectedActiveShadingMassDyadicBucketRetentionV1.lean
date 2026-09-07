import Family8Grounding.Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1
import Family8Grounding.Family8ShadingAwareProjectedPhysicalDyadicFibreBucketV1
import Family8Grounding.Family8UniformTubeZeroFibreMassCapV1
import FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 5000000

open Set MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Family8ProjectedActiveShadingMassDyadicBucketRetentionV1

/-!
# Same-object upward dyadic retention for projected shading mass

After a positive exact-card band has been intersected with the same lower-floor
+exact-card band, each positive fibre is at least `floor`.  The upward levels
+`floor * 2^k` therefore partition every finite fibre without any finite-window
+or `volume I ≤ 1` assumption.  Finiteness is needed only almost everywhere and
+is obtained from finiteness of the literal source weighted mass.
-/

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalDyadicFibreBucketV1
open Family8UniformTubeZeroFibreMassCapV1
open Family8Family7QuantitativeFibreFloorSelectionV2
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section
universe u
variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {F : ConvexFamily iota}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def upwardDyadicFibreLevel (floor : ENNReal) (k : Nat) : ENNReal :=
  floor * (2 : ENNReal) ^ k

def InUpwardDyadicFibreBucket (floor : ENNReal) (k : Nat) (x : ENNReal) : Prop :=
  upwardDyadicFibreLevel floor k ≤ x ∧
    x < 2 * upwardDyadicFibreLevel floor k

theorem upwardDyadicFibreLevel_zero (floor : ENNReal) :
    upwardDyadicFibreLevel floor 0 = floor := by
  simp [upwardDyadicFibreLevel]

theorem two_mul_upwardDyadicFibreLevel (floor : ENNReal) (k : Nat) :
    2 * upwardDyadicFibreLevel floor k =
      upwardDyadicFibreLevel floor (k + 1) := by
  simp only [upwardDyadicFibreLevel, pow_succ]
  ac_rfl

theorem upwardDyadicFibreLevel_monotone (floor : ENNReal) :
    Monotone (upwardDyadicFibreLevel floor) := by
  intro k l hkl
  unfold upwardDyadicFibreLevel
  gcongr
  norm_num

theorem upwardDyadicFibreLevel_pos {floor : ENNReal} (hfloor : 0 < floor)
    (k : Nat) : 0 < upwardDyadicFibreLevel floor k := by
  exact ENNReal.mul_pos hfloor.ne' (by simp)

theorem upwardDyadicFibreLevel_ne_top {floor : ENNReal} (hfloor : floor ≠ ∞)
    (k : Nat) : upwardDyadicFibreLevel floor k ≠ ∞ := by
  apply ENNReal.mul_ne_top hfloor
  exact ENNReal.pow_ne_top (by norm_num)

theorem exists_upwardDyadicFibreBucket
    {floor mass : ENNReal}
    (hfloorPos : 0 < floor)
    (hlower : floor ≤ mass) (hmassFinite : mass ≠ ∞) :
    ∃ k : Nat, InUpwardDyadicFibreBucket floor k mass := by
  have hex : ∃ k : Nat, mass < 2 * upwardDyadicFibreLevel floor k := by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hfloorPos.ne' hmassFinite
    refine ⟨n, hn.trans_le ?_⟩
    calc
      (n : ENNReal) * floor ≤ ((2 ^ n : Nat) : ENNReal) * floor := by
        gcongr
        exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self))
      _ = upwardDyadicFibreLevel floor n := by
        simp [upwardDyadicFibreLevel, Nat.cast_pow]
        ac_rfl
      _ = 1 * upwardDyadicFibreLevel floor n := by simp
      _ ≤ 2 * upwardDyadicFibreLevel floor n := by
        gcongr
        norm_num
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_cases hzero : Nat.find hex = 0
  · rw [hzero, upwardDyadicFibreLevel_zero]
    exact hlower
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hnot : ¬ mass < 2 * upwardDyadicFibreLevel floor j :=
      Nat.find_min hex (by omega)
    rw [hj, ← two_mul_upwardDyadicFibreLevel]
    exact le_of_not_gt hnot

theorem upwardDyadicFibreBucket_unique
    {floor mass : ENNReal} {k l : Nat}
    (hk : InUpwardDyadicFibreBucket floor k mass)
    (hl : InUpwardDyadicFibreBucket floor l mass) : k = l := by
  apply le_antisymm
  · by_contra hnot
    have hlevels : 2 * upwardDyadicFibreLevel floor l ≤
        upwardDyadicFibreLevel floor k := by
      rw [two_mul_upwardDyadicFibreLevel]
      exact upwardDyadicFibreLevel_monotone floor (by omega)
    exact (not_lt_of_ge (hlevels.trans hk.1)) hl.2
  · by_contra hnot
    have hlevels : 2 * upwardDyadicFibreLevel floor k ≤
        upwardDyadicFibreLevel floor l := by
      rw [two_mul_upwardDyadicFibreLevel]
      exact upwardDyadicFibreLevel_monotone floor (by omega)
    exact (not_lt_of_ge (hlevels.trans hl.1)) hk.2

def upwardDyadicFibreBucketTerm
    (floor : ENNReal) (k : Nat) (x : ENNReal) : ENNReal :=
  if InUpwardDyadicFibreBucket floor k x then x else 0

theorem tsum_upwardDyadicFibreBucketTerm_eq
    {floor x : ENNReal} (hfloorPos : 0 < floor)
    (hx : x = 0 ∨ floor ≤ x) (hxFinite : x ≠ ∞) :
    (∑' k : Nat, upwardDyadicFibreBucketTerm floor k x) = x := by
  rcases hx with rfl | hxLower
  · have hnone : ∀ k : Nat, ¬ InUpwardDyadicFibreBucket floor k 0 := by
      intro k hk
      exact (not_le_of_gt (upwardDyadicFibreLevel_pos hfloorPos k)) hk.1
    simp [upwardDyadicFibreBucketTerm, hnone]
  · obtain ⟨k, hk⟩ :=
      exists_upwardDyadicFibreBucket hfloorPos hxLower hxFinite
    rw [tsum_eq_single k]
    · simp [upwardDyadicFibreBucketTerm, hk]
    · intro l hlk
      have hlnot : ¬ InUpwardDyadicFibreBucket floor l x := by
        intro hl
        exact hlk (upwardDyadicFibreBucket_unique hl hk)
      simp [upwardDyadicFibreBucketTerm, hlnot]

def upwardDyadicFibreLevelWeightedIntegrand
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (k : Nat) (u : ProjectionSpace) : ENNReal :=
  ∑ i ∈ active, upwardDyadicFibreBucketTerm floor k
    (shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u)

theorem measurable_upwardDyadicFibreLevelWeightedIntegrand
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (k : Nat) :
    Measurable (upwardDyadicFibreLevelWeightedIntegrand
      Y active f hf X hX I hI floor k) := by
  classical
  unfold upwardDyadicFibreLevelWeightedIntegrand
    upwardDyadicFibreBucketTerm InUpwardDyadicFibreBucket
  apply Finset.measurable_fun_sum active
  intro i _hi
  let mass : ProjectionSpace → ENNReal := fun u ↦
    shadingFiberMass (shadingWindowRestriction Y f hf X hX I hI) f i u
  have hmass : Measurable mass := measurable_shadingFiberMass
    (shadingWindowRestriction Y f hf X hX I hI) f hf i
  exact Measurable.ite
    ((measurableSet_le measurable_const hmass).inter
      (measurableSet_lt hmass measurable_const)) hmass measurable_const

theorem dyadicFibreBucketWeightedMultiplicity_eq_upwardIntegrand
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (k : Nat) (u : ProjectionSpace) (huX : u ∈ X) :
    dyadicFibreBucketWeightedMultiplicity Y active f hf X hX I hI
        (upwardDyadicFibreLevel floor k) u =
      upwardDyadicFibreLevelWeightedIntegrand
        Y active f hf X hX I hI floor k u := by
  classical
  have hactive :
      (shadingAwareProjectedPhysicalDyadicFibreBucket
        Y active f hf X hX I hI
          (upwardDyadicFibreLevel floor k)).activeAtPoint u =
      active.filter fun i ↦ InUpwardDyadicFibreBucket floor k
        (shadingFiberMass
          (shadingWindowRestriction Y f hf X hX I hI) f i u) := by
    ext i
    constructor
    · intro hi
      have hiData :=
        (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI
            (upwardDyadicFibreLevel floor k) u i).mp hi
      exact Finset.mem_filter.mpr
        ⟨hiData.1, hiData.2.2.1, hiData.2.2.2⟩
    · intro hi
      have hiData := Finset.mem_filter.mp hi
      exact
        (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI
            (upwardDyadicFibreLevel floor k) u i).mpr
          ⟨hiData.1, huX, hiData.2.1, hiData.2.2⟩
  unfold dyadicFibreBucketWeightedMultiplicity
  rw [hactive]
  simp only [upwardDyadicFibreLevelWeightedIntegrand,
    upwardDyadicFibreBucketTerm, Finset.sum_filter]

theorem tsum_upwardIntegrand_eq_projectedActiveMultiplicity
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (hfloorPos : 0 < floor)
    (n : Nat) (u : ProjectionSpace)
    (hu : u ∈
      (shadingAwareProjectedPhysical Y active f hf X hX I hI).multiplicityBand n n ∩
      (shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI floor).multiplicityBand n n)
    (hfinite : projectedActiveMultiplicity
      (shadingWindowRestriction Y f hf X hX I hI) active f u ≠ ∞) :
    (∑' k : Nat, upwardDyadicFibreLevelWeightedIntegrand
      Y active f hf X hX I hI floor k u) =
      projectedActiveMultiplicity
        (shadingWindowRestriction Y f hf X hX I hI) active f u := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI floor
  let mass : iota → ENNReal := fun i ↦ shadingFiberMass Yw f i u
  have huPositive := positive.mem_multiplicityBand.mp (by
    simpa only [positive] using hu.1)
  have huLower := lower.mem_multiplicityBand.mp (by
    simpa only [lower] using hu.2)
  have hactiveSubset : lower.activeAtPoint u ⊆ positive.activeAtPoint u := by
    simpa only [lower, positive] using activeAtPoint_lowerBucket_subset_positive
      Y active f hf X hX I hI hfloorPos u
  have hactiveEq : lower.activeAtPoint u = positive.activeAtPoint u := by
    apply Finset.eq_of_subset_of_card_le hactiveSubset
    omega
  rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass Yw active f hf u]
  change _ = ∑ i ∈ active, mass i
  unfold upwardDyadicFibreLevelWeightedIntegrand
  rw [Summable.tsum_finsetSum (fun _i _hi ↦ ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro i hi
  have hsumFinite : (∑ j ∈ active, mass j) ≠ ∞ := by
    rw [← projectedActiveMultiplicity_eq_sum_shadingFiberMass
      Yw active f hf u]
    exact hfinite
  have hmassFinite : mass i ≠ ∞ := by
    apply ne_of_lt
    have hsingle : mass i ≤ ∑ j ∈ active, mass j := by
      exact Finset.single_le_sum (fun _j _hj ↦ bot_le) hi
    exact hsingle.trans_lt (lt_top_iff_ne_top.mpr hsumFinite)
  by_cases hmassZero : mass i = 0
  · exact tsum_upwardDyadicFibreBucketTerm_eq hfloorPos
      (Or.inl hmassZero) hmassFinite
  · have hmassPos : 0 < mass i := pos_iff_ne_zero.mpr hmassZero
    have hiPositive : i ∈ positive.activeAtPoint u := by
      apply (mem_activeAtPoint_shadingAwareProjectedPhysical
        Y active f hf X hX I hI u i).mpr
      exact ⟨hi, huPositive.1, by simpa only [mass, Yw] using hmassPos⟩
    have hiLower : i ∈ lower.activeAtPoint u := by
      rw [hactiveEq]
      exact hiPositive
    have hmassLower : floor ≤ mass i := by
      have h := (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI floor u i).mp (by
          simpa only [lower] using hiLower)
      simpa only [mass, Yw] using h.2.2
    exact tsum_upwardDyadicFibreBucketTerm_eq hfloorPos
      (Or.inr hmassLower) hmassFinite

theorem tsum_upwardDyadicFibreBucketWeightedMass_eq_source
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (hfloorPos : 0 < floor)
    (n : Nat)
    (hsourceFinite : projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f
      ((shadingAwareProjectedPhysical Y active f hf X hX I hI).multiplicityBand n n ∩
       (shadingAwareProjectedPhysicalLowerBucket
         Y active f hf X hX I hI floor).multiplicityBand n n) ≠ ∞) :
    (∑' k : Nat, dyadicFibreBucketWeightedMass
      Y active f hf X hX I hI (upwardDyadicFibreLevel floor k)
      ((shadingAwareProjectedPhysical Y active f hf X hX I hI).multiplicityBand n n ∩
       (shadingAwareProjectedPhysicalLowerBucket
         Y active f hf X hX I hI floor).multiplicityBand n n)) =
      projectedActiveShadingMassMeasure
        (shadingWindowRestriction Y f hf X hX I hI) active f
        ((shadingAwareProjectedPhysical Y active f hf X hX I hI).multiplicityBand n n ∩
         (shadingAwareProjectedPhysicalLowerBucket
           Y active f hf X hX I hI floor).multiplicityBand n n) := by
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI floor
  let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
  let g : ProjectionSpace → ENNReal := fun u ↦
    projectedActiveMultiplicity Yw active f u
  have hE : MeasurableSet E :=
    (positive.measurableSet_multiplicityBand n n).inter
      (lower.measurableSet_multiplicityBand n n)
  have hEX : E ⊆ X := fun _u hu ↦
    (positive.mem_multiplicityBand.mp hu.1).1
  have hg : Measurable g := by
    rw [show g = fun u ↦ ∑ i ∈ active, shadingFiberMass Yw f i u by
      funext u
      exact projectedActiveMultiplicity_eq_sum_shadingFiberMass
        Yw active f hf u]
    exact Finset.measurable_fun_sum active fun i _hi ↦
      measurable_shadingFiberMass Yw f hf i
  have hsourceEq :
      projectedActiveShadingMassMeasure Yw active f E =
        ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace) := by
    rw [projectedActiveShadingMassMeasure,
      MeasureTheory.withDensity_apply _ hE]
  have hfiniteAE : ∀ᵐ u ∂(volume.restrict E), g u < ∞ := by
    apply ae_lt_top hg
    rw [← hsourceEq]
    simpa only [Yw, E, positive, lower] using hsourceFinite
  have hterm (k : Nat) :
      dyadicFibreBucketWeightedMass Y active f hf X hX I hI
          (upwardDyadicFibreLevel floor k) E =
        ∫⁻ u in E, upwardDyadicFibreLevelWeightedIntegrand
          Y active f hf X hX I hI floor k u
          ∂(volume : Measure ProjectionSpace) := by
    unfold dyadicFibreBucketWeightedMass
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hE] with u hu
    exact dyadicFibreBucketWeightedMultiplicity_eq_upwardIntegrand
      Y active f hf X hX I hI floor k u (hEX hu)
  calc
    (∑' k : Nat, dyadicFibreBucketWeightedMass
      Y active f hf X hX I hI (upwardDyadicFibreLevel floor k) E) =
        ∑' k : Nat, ∫⁻ u in E,
          upwardDyadicFibreLevelWeightedIntegrand
            Y active f hf X hX I hI floor k u
          ∂(volume : Measure ProjectionSpace) := by
      apply tsum_congr
      exact hterm
    _ = ∫⁻ u in E, ∑' k : Nat,
          upwardDyadicFibreLevelWeightedIntegrand
            Y active f hf X hX I hI floor k u
          ∂(volume : Measure ProjectionSpace) := by
      rw [lintegral_tsum]
      intro k
      exact (measurable_upwardDyadicFibreLevelWeightedIntegrand
        Y active f hf X hX I hI floor k).aemeasurable
    _ = ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hE, hfiniteAE] with u hu hfin
      exact tsum_upwardIntegrand_eq_projectedActiveMultiplicity
        Y active f hf X hX I hI floor hfloorPos n u hu hfin.ne
    _ = projectedActiveShadingMassMeasure Yw active f E := hsourceEq.symm
    _ = _ := by rfl





theorem exists_upwardDyadicFibreBucket_of_between
    (floor : ENNReal) (hfloorPos : 0 < floor)
    (cutoff : Nat) {mass : ENNReal}
    (hlower : floor ≤ mass)
    (hupper : mass < 2 * upwardDyadicFibreLevel floor cutoff) :
    ∃ k : Nat, k ≤ cutoff ∧ InUpwardDyadicFibreBucket floor k mass := by
  induction cutoff with
  | zero =>
      refine ⟨0, le_rfl, ?_, ?_⟩
      · simpa only [upwardDyadicFibreLevel_zero] using hlower
      · simpa only using hupper
  | succ cutoff ih =>
      by_cases hprev : mass < 2 * upwardDyadicFibreLevel floor cutoff
      · obtain ⟨k, hk, hkBucket⟩ := ih hprev
        exact ⟨k, hk.trans (Nat.le_succ cutoff), hkBucket⟩
      · refine ⟨cutoff + 1, le_rfl, ?_, hupper⟩
        rw [← two_mul_upwardDyadicFibreLevel]
        exact le_of_not_gt hprev

theorem projectedActiveMultiplicity_le_sum_upwardIntegrand_of_upper
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (hfloorPos : 0 < floor)
    (cutoff n : Nat) (u : ProjectionSpace)
    (hu : u ∈
      (shadingAwareProjectedPhysical Y active f hf X hX I hI).multiplicityBand n n ∩
      (shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI floor).multiplicityBand n n)
    (hmassUpper : ∀ i ∈ active,
      shadingFiberMass (shadingWindowRestriction Y f hf X hX I hI) f i u <
        2 * upwardDyadicFibreLevel floor cutoff) :
    projectedActiveMultiplicity
        (shadingWindowRestriction Y f hf X hX I hI) active f u ≤
      ∑ k ∈ Finset.range (cutoff + 1),
        upwardDyadicFibreLevelWeightedIntegrand
          Y active f hf X hX I hI floor k u := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI floor
  let mass : iota → ENNReal := fun i ↦ shadingFiberMass Yw f i u
  let levels := Finset.range (cutoff + 1)
  have huPositive := positive.mem_multiplicityBand.mp (by
    simpa only [positive] using hu.1)
  have huLower := lower.mem_multiplicityBand.mp (by
    simpa only [lower] using hu.2)
  have hactiveSubset : lower.activeAtPoint u ⊆ positive.activeAtPoint u := by
    simpa only [lower, positive] using activeAtPoint_lowerBucket_subset_positive
      Y active f hf X hX I hI hfloorPos u
  have hactiveEq : lower.activeAtPoint u = positive.activeAtPoint u := by
    apply Finset.eq_of_subset_of_card_le hactiveSubset
    omega
  rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass Yw active f hf u]
  change (∑ i ∈ active, mass i) ≤ _
  calc
    (∑ i ∈ active, mass i) ≤
        ∑ i ∈ active, ∑ k ∈ levels,
          upwardDyadicFibreBucketTerm floor k (mass i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hmassZero : mass i = 0
      · simp [hmassZero, upwardDyadicFibreBucketTerm]
      · have hmassPos : 0 < mass i := pos_iff_ne_zero.mpr hmassZero
        have hiPositive : i ∈ positive.activeAtPoint u := by
          apply (mem_activeAtPoint_shadingAwareProjectedPhysical
            Y active f hf X hX I hI u i).mpr
          exact ⟨hi, huPositive.1, by simpa only [mass, Yw] using hmassPos⟩
        have hiLower : i ∈ lower.activeAtPoint u := by
          rw [hactiveEq]
          exact hiPositive
        have hmassLower : floor ≤ mass i := by
          have h := (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
            Y active f hf X hX I hI floor u i).mp (by
              simpa only [lower] using hiLower)
          simpa only [mass, Yw] using h.2.2
        obtain ⟨k, hk, hkBucket⟩ := exists_upwardDyadicFibreBucket_of_between
          floor hfloorPos cutoff hmassLower (by
            simpa only [mass, Yw] using hmassUpper i hi)
        have hkMem : k ∈ levels := by
          simpa only [levels, Finset.mem_range, Nat.lt_succ_iff] using hk
        calc
          mass i = upwardDyadicFibreBucketTerm floor k (mass i) := by
            simp [upwardDyadicFibreBucketTerm, hkBucket]
          _ ≤ ∑ l ∈ levels,
              upwardDyadicFibreBucketTerm floor l (mass i) := by
            exact Finset.single_le_sum
              (s := levels)
              (f := fun l ↦ upwardDyadicFibreBucketTerm floor l (mass i))
              (fun _l _hl ↦ bot_le) hkMem
    _ = ∑ k ∈ levels,
        upwardDyadicFibreLevelWeightedIntegrand
          Y active f hf X hX I hI floor k u := by
      rw [Finset.sum_comm]
      rfl

theorem projectedActiveShadingMass_le_sum_upwardBuckets_of_upper
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (hfloorPos : 0 < floor)
    (cutoff n : Nat)
    (hmassUpper : ∀ i ∈ active, ∀ u : ProjectionSpace,
      shadingFiberMass (shadingWindowRestriction Y f hf X hX I hI) f i u <
        2 * upwardDyadicFibreLevel floor cutoff) :
    let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
    let lower := shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI floor
    let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
    projectedActiveShadingMassMeasure
        (shadingWindowRestriction Y f hf X hX I hI) active f E ≤
      ∑ k ∈ Finset.range (cutoff + 1),
        dyadicFibreBucketWeightedMass Y active f hf X hX I hI
          (upwardDyadicFibreLevel floor k) E := by
  dsimp only
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI floor
  let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
  let g : ProjectionSpace → ENNReal := fun u ↦
    projectedActiveMultiplicity Yw active f u
  let term := fun k : Nat ↦ upwardDyadicFibreLevelWeightedIntegrand
    Y active f hf X hX I hI floor k
  have hE : MeasurableSet E :=
    (positive.measurableSet_multiplicityBand n n).inter
      (lower.measurableSet_multiplicityBand n n)
  have hEX : E ⊆ X := fun _u hu ↦
    (positive.mem_multiplicityBand.mp hu.1).1
  have hpoint : ∀ u, u ∈ E → g u ≤
      ∑ k ∈ Finset.range (cutoff + 1), term k u := by
    intro u hu
    exact projectedActiveMultiplicity_le_sum_upwardIntegrand_of_upper
      Y active f hf X hX I hI floor hfloorPos cutoff n u hu
        (fun i hi ↦ hmassUpper i hi u)
  have hterm (k : Nat) :
      ∫⁻ u in E, term k u ∂(volume : Measure ProjectionSpace) =
        dyadicFibreBucketWeightedMass Y active f hf X hX I hI
          (upwardDyadicFibreLevel floor k) E := by
    unfold dyadicFibreBucketWeightedMass
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hE] with u hu
    exact (dyadicFibreBucketWeightedMultiplicity_eq_upwardIntegrand
      Y active f hf X hX I hI floor k u (hEX hu)).symm
  calc
    projectedActiveShadingMassMeasure Yw active f E =
        ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace) := by
      rw [projectedActiveShadingMassMeasure,
        MeasureTheory.withDensity_apply _ hE]
    _ ≤ ∫⁻ u in E, ∑ k ∈ Finset.range (cutoff + 1), term k u
        ∂(volume : Measure ProjectionSpace) := setLIntegral_mono' hE hpoint
    _ = ∑ k ∈ Finset.range (cutoff + 1),
        ∫⁻ u in E, term k u ∂(volume : Measure ProjectionSpace) := by
      rw [lintegral_finsetSum]
      intro k _hk
      exact measurable_upwardDyadicFibreLevelWeightedIntegrand
        Y active f hf X hX I hI floor k
    _ = ∑ k ∈ Finset.range (cutoff + 1),
        dyadicFibreBucketWeightedMass Y active f hf X hX I hI
          (upwardDyadicFibreLevel floor k) E := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact hterm k



theorem exists_upwardDyadicBucketWeightedMass_ge_finite_average_of_upper
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (hfloorPos : 0 < floor)
    (cutoff n : Nat)
    (hmassUpper : ∀ i ∈ active, ∀ u : ProjectionSpace,
      shadingFiberMass (shadingWindowRestriction Y f hf X hX I hI) f i u <
        2 * upwardDyadicFibreLevel floor cutoff) :
    let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
    let lower := shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI floor
    let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
    let source := projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E
    ∃ k : Nat, k ≤ cutoff ∧
      source ≤ ((cutoff + 1 : Nat) : ENNReal) *
        dyadicFibreBucketWeightedMass Y active f hf X hX I hI
          (upwardDyadicFibreLevel floor k) E := by
  dsimp only
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI floor
  let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
  let source := projectedActiveShadingMassMeasure
    (shadingWindowRestriction Y f hf X hX I hI) active f E
  let weight : Nat → ENNReal := fun k ↦ dyadicFibreBucketWeightedMass
    Y active f hf X hX I hI (upwardDyadicFibreLevel floor k) E
  let bins := Finset.range (cutoff + 1)
  have hbins : bins.Nonempty := by simp [bins]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image bins weight hbins
  have hsum : (∑ j ∈ bins, weight j) ≤ bins.card • weight k :=
    Finset.sum_le_card_nsmul bins weight (weight k)
      (fun j hj ↦ hmax j hj)
  have hcover : source ≤ ∑ j ∈ bins, weight j := by
    simpa only [source, weight, bins, E, positive, lower] using
      projectedActiveShadingMass_le_sum_upwardBuckets_of_upper
        Y active f hf X hX I hI floor hfloorPos cutoff n hmassUpper
  refine ⟨k, ?_, ?_⟩
  · simpa only [bins, Finset.mem_range, Nat.lt_succ_iff] using hk
  · calc
      source ≤ ∑ j ∈ bins, weight j := hcover
      _ ≤ bins.card • weight k := hsum
      _ = ((cutoff + 1 : Nat) : ENNReal) *
          dyadicFibreBucketWeightedMass Y active f hf X hX I hI
            (upwardDyadicFibreLevel floor k) E := by
        simp [bins, weight, nsmul_eq_mul]

theorem upwardDyadicFibreLevel_dyadicFibreFloor_self (ell : Nat) :
    upwardDyadicFibreLevel (dyadicFibreFloor ell) ell = 1 := by
  unfold upwardDyadicFibreLevel dyadicFibreFloor
  calc
    (2 : ENNReal)⁻¹ ^ ell * 2 ^ ell =
        ((2 : ENNReal)⁻¹ * 2) ^ ell := (mul_pow _ _ _).symm
    _ = 1 := by
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      simp

theorem upwardDyadicFibreLevel_dyadicFibreFloor_add_one (ell : Nat) :
    upwardDyadicFibreLevel (dyadicFibreFloor ell) (ell + 1) = 2 := by
  rw [← two_mul_upwardDyadicFibreLevel,
    upwardDyadicFibreLevel_dyadicFibreFloor_self]
  norm_num

theorem exists_zeroGraph_upwardDyadicBucketWeightedMass_ge_finite_average
    {delta : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (ell n : Nat) :
    let f0 : Real → Real := fun _ ↦ 0
    let floor := dyadicFibreFloor ell
    let positive := shadingAwareProjectedPhysical
      Y active f0 measurable_const X hX I hI
    let lower := shadingAwareProjectedPhysicalLowerBucket
      Y active f0 measurable_const X hX I hI floor
    let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
    let source := projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f0 measurable_const X hX I hI) active f0 E
    ∃ k : Nat, k ≤ ell + 1 ∧
      source ≤ ((ell + 2 : Nat) : ENNReal) *
        dyadicFibreBucketWeightedMass Y active f0 measurable_const X hX I hI
          (upwardDyadicFibreLevel floor k) E := by
  dsimp only
  let f0 : Real → Real := fun _ ↦ 0
  let floor := dyadicFibreFloor ell
  have hmassUpper : ∀ i ∈ active, ∀ u : ProjectionSpace,
      shadingFiberMass
        (shadingWindowRestriction Y f0 measurable_const X hX I hI) f0 i u <
        2 * upwardDyadicFibreLevel floor (ell + 1) := by
    intro i _hi u
    calc
      shadingFiberMass
          (shadingWindowRestriction Y f0 measurable_const X hX I hI)
            f0 i u ≤ 2 := by
        simpa only [f0] using shadingFiberMass_zero_le_two fine
          (shadingWindowRestriction Y f0 measurable_const X hX I hI)
          hdeltaHalf i u
      _ < 2 * upwardDyadicFibreLevel floor (ell + 1) := by
        rw [show floor = dyadicFibreFloor ell by rfl,
          upwardDyadicFibreLevel_dyadicFibreFloor_add_one]
        norm_num
  simpa only [f0, floor, Nat.add_assoc] using
    exists_upwardDyadicBucketWeightedMass_ge_finite_average_of_upper
      Y active f0 measurable_const X hX I hI floor
        (dyadicFibreFloor_pos ell) (ell + 1) n hmassUpper



theorem exists_lowerBucket_exactCard_weightedMass_ge_average
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (level : ENNReal) (hlevel : 0 < level)
    (n : Nat) (hn : 1 ≤ n)
    (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E ⊆
      (shadingAwareProjectedPhysical
        Y active f hf X hX I hI).multiplicityBand n n) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ n ∧
      dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI level E ≤
        (n : ENNReal) *
          dyadicFibreBucketWeightedMass
            Y active f hf X hX I hI level
              (E ∩ (shadingAwareProjectedPhysicalLowerBucket
                Y active f hf X hX I hI level).multiplicityBand p p) := by
  classical
  let bucket := shadingAwareProjectedPhysicalDyadicFibreBucket
    Y active f hf X hX I hI level
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI level
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let w : ProjectionSpace → ENNReal :=
    dyadicFibreBucketWeightedMultiplicity Y active f hf X hX I hI level
  let mu : Measure ProjectionSpace :=
    (volume : Measure ProjectionSpace).withDensity w
  let bucketCard : ProjectionSpace → Nat :=
    fun u ↦ (bucket.activeAtPoint u).card
  let cardAt : ProjectionSpace → Nat :=
    fun u ↦ (lower.activeAtPoint u).card
  let R : Set ProjectionSpace := E ∩ {u | 1 ≤ bucketCard u}
  let labels : Finset Nat := Finset.Icc 1 n
  have hw : Measurable w := by
    let Yw := shadingWindowRestriction Y f hf X hX I hI
    let mass : iota → ProjectionSpace → ENNReal :=
      fun i u ↦ shadingFiberMass Yw f i u
    have hrewrite : w = fun u ↦ ∑ i ∈ active,
        if u ∈ bucket.carrier i then mass i u else 0 := by
      funext u
      change (∑ i ∈ bucket.activeAtPoint u, mass i u) =
        ∑ i ∈ active, if u ∈ bucket.carrier i then mass i u else 0
      have hactive : bucket.activeAtPoint u =
          active.filter (fun i ↦ u ∈ bucket.carrier i) := by rfl
      rw [hactive]
      exact Finset.sum_filter (fun i ↦ u ∈ bucket.carrier i)
        (fun i ↦ mass i u)
    rw [hrewrite]
    exact Finset.measurable_fun_sum active fun i hi ↦
      Measurable.ite (bucket.measurable_carrier i hi)
        (measurable_shadingFiberMass Yw f hf i) measurable_const
  have hbucketCardMeasurable : Measurable bucketCard :=
    bucket.measurable_activeValue fun s ↦ s.card
  have hcardMeasurable : Measurable cardAt :=
    lower.measurable_activeValue fun s ↦ s.card
  have hR : MeasurableSet R := hE.inter <|
    hbucketCardMeasurable
      (Set.to_countable {k : Nat | 1 ≤ k}).measurableSet
  have hRsubset : R ⊆ E := fun _u hu ↦ hu.1
  have hdiffZero : mu (E \ R) = 0 := by
    change (volume.withDensity w) (E \ R) = 0
    apply (MeasureTheory.withDensity_apply_eq_zero hw).2
    have hempty : {u : ProjectionSpace | w u ≠ 0} ∩ (E \ R) = ∅ := by
      apply Set.Subset.antisymm
      · intro u hu
        rcases hu with ⟨hwu, huE, huNotR⟩
        have hnotOne : ¬ 1 ≤ bucketCard u := by
          intro hone
          exact huNotR ⟨huE, hone⟩
        have hcardZero : bucketCard u = 0 := by omega
        have hactiveEmpty : bucket.activeAtPoint u = ∅ := by
          apply Finset.card_eq_zero.mp
          exact hcardZero
        exfalso
        apply hwu
        change (∑ i ∈ bucket.activeAtPoint u,
          shadingFiberMass
            (shadingWindowRestriction Y f hf X hX I hI) f i u) = 0
        rw [hactiveEmpty]
        simp
      · exact Set.empty_subset _
    rw [hempty, measure_empty]
  have hmuRE : mu R = mu E :=
    measure_eq_measure_of_null_sdiff hRsubset hdiffZero
  have hlabels : labels.Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  have hrange : ∀ u, u ∈ R → cardAt u ∈ labels := by
    intro u hu
    have huPositive := positive.mem_multiplicityBand.mp (hEband hu.1)
    have hpositiveCard : (positive.activeAtPoint u).card = n := by omega
    have hbucketNonempty : (bucket.activeAtPoint u).Nonempty := by
      exact Finset.one_le_card.mp hu.2
    have hbucketLower : bucket.activeAtPoint u ⊆ lower.activeAtPoint u := by
      intro i hi
      have hiData :=
        (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI level u i).mp hi
      apply (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI level u i).mpr
      exact ⟨hiData.1, hiData.2.1, hiData.2.2.1⟩
    have hlowerPositive : lower.activeAtPoint u ⊆ positive.activeAtPoint u := by
      simpa only [lower, positive] using
        activeAtPoint_lowerBucket_subset_positive
          Y active f hf X hX I hI hlevel u
    apply Finset.mem_Icc.mpr
    constructor
    · change 1 ≤ (lower.activeAtPoint u).card
      exact Finset.one_le_card.mpr (hbucketNonempty.mono hbucketLower)
    · change (lower.activeAtPoint u).card ≤ n
      exact (Finset.card_le_card hlowerPositive).trans_eq hpositiveCard
  let cellMass : Nat → ENNReal :=
    fun p ↦ mu (measurableLabelCell R cardAt p)
  obtain ⟨p, hp, hmax⟩ :=
    Finset.exists_max_image labels cellMass hlabels
  have hsum : (∑ k ∈ labels, cellMass k) ≤
      labels.card • cellMass p :=
    Finset.sum_le_card_nsmul labels cellMass (cellMass p)
      (fun k hk ↦ hmax k hk)
  have htotalR : mu R ≤ (labels.card : ENNReal) *
      mu (measurableLabelCell R cardAt p) := by
    rw [measure_eq_sum_measurableLabelCell
      mu labels hR hcardMeasurable hrange]
    simpa only [cellMass, nsmul_eq_mul] using hsum
  have hpData := Finset.mem_Icc.mp hp
  have hlabelsCard : labels.card = n := by simp [labels]
  let selected := E ∩ lower.multiplicityBand p p
  have hselected : MeasurableSet selected :=
    hE.inter (lower.measurableSet_multiplicityBand p p)
  have hcellSubset : measurableLabelCell R cardAt p ⊆ selected := by
    intro u hu
    have huR := hu.1
    have huCard : cardAt u = p := by
      simpa [measurableLabelCell] using hu.2
    have huPositive := positive.mem_multiplicityBand.mp (hEband huR.1)
    refine ⟨huR.1, lower.mem_multiplicityBand.mpr ⟨huPositive.1, ?_, ?_⟩⟩
    · change p ≤ (lower.activeAtPoint u).card
      simpa only [cardAt] using huCard.symm.le
    · change (lower.activeAtPoint u).card ≤ p
      simpa only [cardAt] using huCard.le
  have hmuE : mu E = dyadicFibreBucketWeightedMass
      Y active f hf X hX I hI level E := by
    change (volume.withDensity w) E = ∫⁻ u in E, w u ∂volume
    rw [MeasureTheory.withDensity_apply _ hE]
  have hmuSelected : mu selected = dyadicFibreBucketWeightedMass
      Y active f hf X hX I hI level selected := by
    change (volume.withDensity w) selected =
      ∫⁻ u in selected, w u ∂volume
    rw [MeasureTheory.withDensity_apply _ hselected]
  refine ⟨p, hpData.1, hpData.2, ?_⟩
  calc
    dyadicFibreBucketWeightedMass Y active f hf X hX I hI level E =
        mu E := hmuE.symm
    _ = mu R := hmuRE.symm
    _ ≤ (labels.card : ENNReal) *
        mu (measurableLabelCell R cardAt p) := htotalR
    _ ≤ (n : ENNReal) * mu selected := by
      rw [hlabelsCard]
      gcongr
    _ = (n : ENNReal) * dyadicFibreBucketWeightedMass
        Y active f hf X hX I hI level selected := by rw [hmuSelected]
    _ = _ := by rfl

theorem dyadicFibreBucketWeightedMass_le_two_mul_level_mul_lowerCard_mul_volume
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (level : ENNReal) (p : Nat)
    (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E ⊆ (shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level).multiplicityBand p p) :
    dyadicFibreBucketWeightedMass Y active f hf X hX I hI level E ≤
      (2 * level) * (p : ENNReal) * volume E := by
  let bucket := shadingAwareProjectedPhysicalDyadicFibreBucket
    Y active f hf X hX I hI level
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI level
  have hpoint : ∀ u, u ∈ E →
      dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI level u ≤
        (2 * level) * (p : ENNReal) := by
    intro u hu
    have huLower := lower.mem_multiplicityBand.mp (hEband hu)
    have hlowerCard : (lower.activeAtPoint u).card = p := by omega
    have hsubset : bucket.activeAtPoint u ⊆ lower.activeAtPoint u := by
      intro i hi
      have hiData :=
        (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI level u i).mp hi
      apply (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
        Y active f hf X hX I hI level u i).mpr
      exact ⟨hiData.1, hiData.2.1, hiData.2.2.1⟩
    calc
      dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI level u ≤
        (2 * level) * ((bucket.activeAtPoint u).card : ENNReal) :=
          dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_card
            Y active f hf X hX I hI level u
      _ ≤ (2 * level) * (p : ENNReal) := by
        gcongr
        exact_mod_cast (Finset.card_le_card hsubset).trans_eq hlowerCard
  unfold dyadicFibreBucketWeightedMass
  calc
    (∫⁻ u in E, dyadicFibreBucketWeightedMultiplicity
        Y active f hf X hX I hI level u ∂volume) ≤
      ∫⁻ _u in E, (2 * level) * (p : ENNReal) ∂volume :=
        setLIntegral_mono' hE hpoint
    _ = (2 * level) * (p : ENNReal) * volume E := by
      rw [setLIntegral_const]



theorem exists_upwardDyadicBucket_lowerCard_retention_and_ceiling_of_upper
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (floor : ENNReal) (hfloorPos : 0 < floor)
    (cutoff n : Nat) (hn : 1 ≤ n)
    (hmassUpper : ∀ i ∈ active, ∀ u : ProjectionSpace,
      shadingFiberMass (shadingWindowRestriction Y f hf X hX I hI) f i u <
        2 * upwardDyadicFibreLevel floor cutoff) :
    let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
    let lower := shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI floor
    let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
    let source := projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E
    ∃ k p : Nat, k ≤ cutoff ∧ 1 ≤ p ∧ p ≤ n ∧
      let level := upwardDyadicFibreLevel floor k
      let selected := E ∩
        (shadingAwareProjectedPhysicalLowerBucket
          Y active f hf X hX I hI level).multiplicityBand p p
      source ≤ ((cutoff + 1 : Nat) : ENNReal) * (n : ENNReal) *
          dyadicFibreBucketWeightedMass
            Y active f hf X hX I hI level selected ∧
        dyadicFibreBucketWeightedMass
            Y active f hf X hX I hI level selected ≤
          (2 * level) * (p : ENNReal) * volume selected ∧
        source ≤ 2 * ((cutoff + 1 : Nat) : ENNReal) *
          (n : ENNReal) ^ 2 * level * volume selected := by
  dsimp only
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI floor
  let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
  let source := projectedActiveShadingMassMeasure
    (shadingWindowRestriction Y f hf X hX I hI) active f E
  obtain ⟨k, hk, hretainLevel⟩ :=
    exists_upwardDyadicBucketWeightedMass_ge_finite_average_of_upper
      Y active f hf X hX I hI floor hfloorPos cutoff n hmassUpper
  let level := upwardDyadicFibreLevel floor k
  have hlevelPos : 0 < level := upwardDyadicFibreLevel_pos hfloorPos k
  have hE : MeasurableSet E :=
    (positive.measurableSet_multiplicityBand n n).inter
      (lower.measurableSet_multiplicityBand n n)
  obtain ⟨p, hpOne, hpN, hsplit⟩ :=
    exists_lowerBucket_exactCard_weightedMass_ge_average
      Y active f hf X hX I hI level hlevelPos n hn E hE
        Set.inter_subset_left
  let selected := E ∩
    (shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level).multiplicityBand p p
  have hselected : MeasurableSet selected := hE.inter
    ((shadingAwareProjectedPhysicalLowerBucket
      Y active f hf X hX I hI level).measurableSet_multiplicityBand p p)
  have hceiling :
      dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI level selected ≤
        (2 * level) * (p : ENNReal) * volume selected :=
    dyadicFibreBucketWeightedMass_le_two_mul_level_mul_lowerCard_mul_volume
      Y active f hf X hX I hI level p selected hselected
        Set.inter_subset_right
  have hretain :
      source ≤ ((cutoff + 1 : Nat) : ENNReal) * (n : ENNReal) *
        dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI level selected := by
    calc
      source ≤ ((cutoff + 1 : Nat) : ENNReal) *
          dyadicFibreBucketWeightedMass
            Y active f hf X hX I hI level E := by
        simpa only [source, E, positive, lower, level] using hretainLevel
      _ ≤ ((cutoff + 1 : Nat) : ENNReal) * ((n : ENNReal) *
          dyadicFibreBucketWeightedMass
            Y active f hf X hX I hI level selected) := by
        gcongr
      _ = ((cutoff + 1 : Nat) : ENNReal) * (n : ENNReal) *
          dyadicFibreBucketWeightedMass
            Y active f hf X hX I hI level selected := by ring
  have hfinal :
      source ≤ 2 * ((cutoff + 1 : Nat) : ENNReal) *
        (n : ENNReal) ^ 2 * level * volume selected := by
    calc
      source ≤ ((cutoff + 1 : Nat) : ENNReal) * (n : ENNReal) *
          dyadicFibreBucketWeightedMass
            Y active f hf X hX I hI level selected := hretain
      _ ≤ ((cutoff + 1 : Nat) : ENNReal) * (n : ENNReal) *
          ((2 * level) * (p : ENNReal) * volume selected) := by
        gcongr
      _ ≤ ((cutoff + 1 : Nat) : ENNReal) * (n : ENNReal) *
          ((2 * level) * (n : ENNReal) * volume selected) := by
        gcongr
      _ = 2 * ((cutoff + 1 : Nat) : ENNReal) *
          (n : ENNReal) ^ 2 * level * volume selected := by ring
  exact ⟨k, p, hk, hpOne, hpN, hretain, hceiling, hfinal⟩





theorem exists_zeroGraph_upwardDyadicBucket_lowerCard_retention_and_ceiling
    {delta : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (active : Finset iota)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (ell n : Nat) (hn : 1 ≤ n) :
    let f0 : Real → Real := fun _ ↦ 0
    let floor := Family8Family7QuantitativeFibreFloorSelectionV2.dyadicFibreFloor ell
    let positive := shadingAwareProjectedPhysical
      Y active f0 measurable_const X hX I hI
    let lower := shadingAwareProjectedPhysicalLowerBucket
      Y active f0 measurable_const X hX I hI floor
    let E := positive.multiplicityBand n n ∩ lower.multiplicityBand n n
    let source := projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f0 measurable_const X hX I hI) active f0 E
    ∃ k p : Nat, k ≤ ell + 1 ∧ 1 ≤ p ∧ p ≤ n ∧
      let level := upwardDyadicFibreLevel floor k
      let selected := E ∩
        (shadingAwareProjectedPhysicalLowerBucket
          Y active f0 measurable_const X hX I hI level).multiplicityBand p p
      source ≤ ((ell + 2 : Nat) : ENNReal) * (n : ENNReal) *
          dyadicFibreBucketWeightedMass
            Y active f0 measurable_const X hX I hI level selected ∧
        dyadicFibreBucketWeightedMass
            Y active f0 measurable_const X hX I hI level selected ≤
          (2 * level) * (p : ENNReal) * volume selected ∧
        source ≤ 2 * ((ell + 2 : Nat) : ENNReal) *
          (n : ENNReal) ^ 2 * level * volume selected := by
  dsimp only
  let f0 : Real → Real := fun _ ↦ 0
  let floor :=
    Family8Family7QuantitativeFibreFloorSelectionV2.dyadicFibreFloor ell
  have hmassUpper : ∀ i ∈ active, ∀ u : ProjectionSpace,
      shadingFiberMass
        (shadingWindowRestriction Y f0 measurable_const X hX I hI) f0 i u <
        2 * upwardDyadicFibreLevel floor (ell + 1) := by
    intro i _hi u
    calc
      shadingFiberMass
          (shadingWindowRestriction Y f0 measurable_const X hX I hI)
            f0 i u ≤ 2 := by
        simpa only [f0] using
          Family8UniformTubeZeroFibreMassCapV1.shadingFiberMass_zero_le_two
            fine
            (shadingWindowRestriction Y f0 measurable_const X hX I hI)
            hdeltaHalf i u
      _ < 2 * upwardDyadicFibreLevel floor (ell + 1) := by
        rw [show floor =
            Family8Family7QuantitativeFibreFloorSelectionV2.dyadicFibreFloor ell
              by rfl,
          upwardDyadicFibreLevel_dyadicFibreFloor_add_one]
        norm_num
  simpa only [f0, floor, Nat.add_assoc] using
    exists_upwardDyadicBucket_lowerCard_retention_and_ceiling_of_upper
      Y active f0 measurable_const X hX I hI floor
        (Family8Family7QuantitativeFibreFloorSelectionV2.dyadicFibreFloor_pos ell)
        (ell + 1) n hn hmassUpper


#print axioms exists_zeroGraph_upwardDyadicBucket_lowerCard_retention_and_ceiling

end
end Family8ProjectedActiveShadingMassDyadicBucketRetentionV1
