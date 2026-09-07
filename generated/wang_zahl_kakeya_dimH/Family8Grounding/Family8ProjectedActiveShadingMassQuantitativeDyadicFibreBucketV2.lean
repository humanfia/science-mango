import Family8Grounding.Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1
import Family8Grounding.Family8ShadingAwareProjectedPhysicalDyadicFibreBucketV1
import Mathlib.Tactic

/-!
# Quantitative projected mass in a two-sided dyadic fibre bucket

This file is an additive successor to the weighted-mass-first exact-card
selection.  It keeps the same shading, active family, twisted projection and
two windows.  The two-sided fibre bucket supplies the direction needed by the
tail budget: its genuine weighted mass is at most
`2 * fibreLevel * exactCard * planarVolume`.

We do not assert that all fibres at one projected point have a common dyadic
scale.  The exact-card datum in the upper bound is the original positive
active pattern; a two-sided bucket is only a subpattern of it.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ProjectedActiveShadingMassQuantitativeDyadicFibreBucketV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1
open Family8Family7QuantitativeFibreFloorSelectionV2
open Family8ShadingAwareProjectedPhysicalDyadicFibreBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

universe u

/-- A positive two-sided fibre bucket is a literal subpattern of the
positivity-based projected datum on the same inputs. -/
theorem activeAtPoint_dyadicFibreBucket_subset_positive
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    {level : ENNReal} (hlevel : 0 < level) (u : ProjectionSpace) :
    (shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI level).activeAtPoint u ⊆
      (shadingAwareProjectedPhysical
        Y active f hf X hX I hI).activeAtPoint u := by
  intro i hi
  have hiData :=
    (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI level u i).mp hi
  apply (mem_activeAtPoint_shadingAwareProjectedPhysical
    Y active f hf X hX I hI u i).mpr
  exact ⟨hiData.1, hiData.2.1, hlevel.trans_le hiData.2.2.1⟩

/-- Consecutive inverse powers of two are the endpoints of one half-open
dyadic interval. -/
theorem two_mul_dyadicFibreFloor_succ (k : Nat) :
    2 * dyadicFibreFloor (k + 1) = dyadicFibreFloor k := by
  unfold dyadicFibreFloor
  rw [pow_succ]
  calc
    2 * (2⁻¹ ^ k * (2 : ENNReal)⁻¹) =
        2⁻¹ ^ k * (2 * (2 : ENNReal)⁻¹) := by ac_rfl
    _ = 2⁻¹ ^ k := by
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- A mass between the cutoff floor and one lies in one of the finitely many
two-sided dyadic bins numbered from zero through the cutoff. -/
theorem exists_dyadicFibreFloor_bucket_of_between
    (cutoff : Nat) {mass : ENNReal}
    (hlower : dyadicFibreFloor cutoff ≤ mass)
    (hupper : mass ≤ 1) :
    ∃ level : Nat, level ≤ cutoff ∧
      dyadicFibreFloor level ≤ mass ∧
      mass < 2 * dyadicFibreFloor level := by
  induction cutoff generalizing mass with
  | zero =>
      refine ⟨0, le_rfl, ?_, ?_⟩
      · simpa [dyadicFibreFloor] using hlower
      · have honeTwo : (1 : ENNReal) < 2 := by norm_num
        simpa [dyadicFibreFloor] using hupper.trans_lt honeTwo
  | succ cutoff ih =>
      by_cases hprev : dyadicFibreFloor cutoff ≤ mass
      · obtain ⟨level, hlevel, hlevelLower, hlevelUpper⟩ :=
          ih hprev hupper
        exact ⟨level, hlevel.trans (Nat.le_succ cutoff),
          hlevelLower, hlevelUpper⟩
      · refine ⟨cutoff + 1, le_rfl, hlower, ?_⟩
        rw [two_mul_dyadicFibreFloor_succ]
        exact lt_of_not_ge hprev

/-! ## An honest all-scale dyadic partition -/

/-- A countable enumeration of all integer dyadic exponents. -/
def fullScaleDyadicExponent (k : Nat) : Int :=
  Equiv.intEquivNat.symm k

/-- The corresponding enumeration of every positive dyadic scale
`2^z`, `z : Int`. -/
def fullScaleDyadicFibreLevel (k : Nat) : ENNReal :=
  (2 : ENNReal) ^ fullScaleDyadicExponent k

theorem fullScaleDyadicFibreLevel_pos (k : Nat) :
    0 < fullScaleDyadicFibreLevel k := by
  exact ENNReal.zpow_pos (by norm_num) (by norm_num)
    (fullScaleDyadicExponent k)

theorem fullScaleDyadicFibreLevel_ne_top (k : Nat) :
    fullScaleDyadicFibreLevel k ≠ ∞ :=
  (ENNReal.zpow_lt_top (by norm_num) (by norm_num)
    (fullScaleDyadicExponent k)).ne

/-- The upper endpoint of a full-scale bucket is the next integer power. -/
theorem two_mul_fullScaleDyadicFibreLevel (k : Nat) :
    2 * fullScaleDyadicFibreLevel k =
      (2 : ENNReal) ^ (fullScaleDyadicExponent k + 1) := by
  calc
    2 * fullScaleDyadicFibreLevel k =
        fullScaleDyadicFibreLevel k * 2 := mul_comm _ _
    _ = (2 : ENNReal) ^ (fullScaleDyadicExponent k + 1) := by
      rw [ENNReal.zpow_add (by norm_num) (by norm_num)]
      simp [fullScaleDyadicFibreLevel]

/-- Every positive finite mass lies in one enumerated half-open dyadic
bucket, with no upper bound on the fibre window. -/
theorem exists_fullScaleDyadicFibreBucket
    {mass : ENNReal} (hmassZero : mass ≠ 0) (hmassTop : mass ≠ ∞) :
    ∃ k : Nat,
      fullScaleDyadicFibreLevel k ≤ mass ∧
      mass < 2 * fullScaleDyadicFibreLevel k := by
  obtain ⟨z, hzLower, hzUpper⟩ :=
    ENNReal.exists_mem_Ico_zpow hmassZero hmassTop
      (y := (2 : ENNReal)) (by norm_num) (by norm_num)
  let k : Nat := Equiv.intEquivNat z
  have hk : fullScaleDyadicExponent k = z := by
    simp [fullScaleDyadicExponent, k]
  refine ⟨k, ?_, ?_⟩
  · simpa only [fullScaleDyadicFibreLevel, hk] using hzLower
  · rw [two_mul_fullScaleDyadicFibreLevel]
    simpa only [hk] using hzUpper

/-- The full-scale half-open dyadic buckets are disjoint. -/
theorem fullScaleDyadicFibreBucket_index_unique
    {mass : ENNReal} {k l : Nat}
    (hkLower : fullScaleDyadicFibreLevel k ≤ mass)
    (hkUpper : mass < 2 * fullScaleDyadicFibreLevel k)
    (hlLower : fullScaleDyadicFibreLevel l ≤ mass)
    (hlUpper : mass < 2 * fullScaleDyadicFibreLevel l) :
    k = l := by
  apply Equiv.intEquivNat.symm.injective
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hkl' :
        fullScaleDyadicExponent k < fullScaleDyadicExponent l := by
      simpa only [fullScaleDyadicExponent] using hkl
    have hsucc :
        fullScaleDyadicExponent k + 1 ≤ fullScaleDyadicExponent l := by
      omega
    have hpow :
        (2 : ENNReal) ^ (fullScaleDyadicExponent k + 1) ≤
          (2 : ENNReal) ^ fullScaleDyadicExponent l :=
      ENNReal.monotone_zpow (by norm_num) hsucc
    have hmassLower :
        (2 : ENNReal) ^ (fullScaleDyadicExponent k + 1) ≤ mass :=
      hpow.trans (by
        simpa only [fullScaleDyadicFibreLevel] using hlLower)
    exact (not_lt_of_ge hmassLower) (by
      simpa only [two_mul_fullScaleDyadicFibreLevel] using hkUpper)
  · have hlk' :
        fullScaleDyadicExponent l < fullScaleDyadicExponent k := by
      simpa only [fullScaleDyadicExponent] using hlk
    have hsucc :
        fullScaleDyadicExponent l + 1 ≤ fullScaleDyadicExponent k := by
      omega
    have hpow :
        (2 : ENNReal) ^ (fullScaleDyadicExponent l + 1) ≤
          (2 : ENNReal) ^ fullScaleDyadicExponent k :=
      ENNReal.monotone_zpow (by norm_num) hsucc
    have hmassLower :
        (2 : ENNReal) ^ (fullScaleDyadicExponent l + 1) ≤ mass :=
      hpow.trans (by
        simpa only [fullScaleDyadicFibreLevel] using hkLower)
    exact (not_lt_of_ge hmassLower) (by
      simpa only [two_mul_fullScaleDyadicFibreLevel] using hlUpper)

/-- One positive finite fibre mass is exactly the sum of its contributions
over the enumerated full-scale buckets.  Half-open disjointness makes all but
one term zero. -/
theorem shadingFiberMass_eq_tsum_fullScaleDyadicFibreBuckets
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (u : ProjectionSpace) (huX : u ∈ X)
    (i : iota) (hi : i ∈ active)
    (hmassTop : shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u ≠ ∞) :
    shadingFiberMass
        (shadingWindowRestriction Y f hf X hX I hI) f i u =
      ∑' k : Nat,
        if i ∈ (shadingAwareProjectedPhysicalDyadicFibreBucket
            Y active f hf X hX I hI
              (fullScaleDyadicFibreLevel k)).activeAtPoint u then
          shadingFiberMass
            (shadingWindowRestriction Y f hf X hX I hI) f i u
        else 0 := by
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let mass : ENNReal := shadingFiberMass Yw f i u
  let bucketAt := fun k : Nat ↦
    shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI (fullScaleDyadicFibreLevel k)
  by_cases hmassZero : mass = 0
  · simp [mass, Yw, hmassZero]
  · obtain ⟨k, hkLower, hkUpper⟩ :=
      exists_fullScaleDyadicFibreBucket hmassZero (by
        simpa only [mass, Yw] using hmassTop)
    have hiBucket : i ∈ (bucketAt k).activeAtPoint u := by
      apply
        (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
          Y active f hf X hX I hI
            (fullScaleDyadicFibreLevel k) u i).mpr
      exact ⟨hi, huX,
        by simpa only [mass, Yw] using hkLower,
        by simpa only [mass, Yw] using hkUpper⟩
    change mass = ∑' l : Nat,
      if i ∈ (bucketAt l).activeAtPoint u then mass else 0
    symm
    calc
      (∑' l : Nat,
          if i ∈ (bucketAt l).activeAtPoint u then mass else 0) =
          (if i ∈ (bucketAt k).activeAtPoint u then mass else 0) := by
        apply tsum_eq_single k
        intro l hl
        rw [if_neg]
        intro hiOther
        have hiData :=
          (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
            Y active f hf X hX I hI
              (fullScaleDyadicFibreLevel l) u i).mp (by
                simpa only [bucketAt] using hiOther)
        have hlLower : fullScaleDyadicFibreLevel l ≤ mass := by
          simpa only [mass, Yw] using hiData.2.2.1
        have hlUpper : mass < 2 * fullScaleDyadicFibreLevel l := by
          simpa only [mass, Yw] using hiData.2.2.2
        exact hl
          (fullScaleDyadicFibreBucket_index_unique
            hlLower hlUpper hkLower hkUpper)
      _ = mass := by simp [hiBucket]

/-- The genuine fibre-mass-weighted multiplicity of one fixed two-sided
bucket is measurable. -/
theorem measurable_dyadicFibreBucketWeightedMultiplicity
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (level : ENNReal) :
    Measurable (dyadicFibreBucketWeightedMultiplicity
      Y active f hf X hX I hI level) := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let bucket := shadingAwareProjectedPhysicalDyadicFibreBucket
    Y active f hf X hX I hI level
  let mass : iota → ProjectionSpace → ENNReal :=
    fun i u ↦ shadingFiberMass Yw f i u
  have hrewrite :
      dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI level =
        fun u ↦ ∑ i ∈ active,
          if u ∈ bucket.carrier i then mass i u else 0 := by
    funext u
    simp [dyadicFibreBucketWeightedMultiplicity,
      FiniteProjectedShading.activeAtPoint,
      finiteIncidenceActiveAtPoint,
      shadingAwareProjectedPhysicalDyadicFibreBucket,
      bucket, mass, Yw]
    rw [Finset.sum_filter]
  rw [hrewrite]
  exact Finset.measurable_fun_sum active fun i hi ↦
    Measurable.ite (bucket.measurable_carrier i hi)
      (measurable_shadingFiberMass Yw f hf i) measurable_const

/-- At a point of the projected base where the total multiplicity is finite,
the projected multiplicity is exactly the countable sum of the full-scale
two-sided bucket multiplicities.  Different fibres may use different
scales. -/
theorem projectedActiveMultiplicity_eq_tsum_fullScaleDyadicFibreBuckets
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (u : ProjectionSpace) (huX : u ∈ X)
    (hfinite : projectedActiveMultiplicity
      (shadingWindowRestriction Y f hf X hX I hI) active f u ≠ ∞) :
    projectedActiveMultiplicity
        (shadingWindowRestriction Y f hf X hX I hI) active f u =
      ∑' k : Nat,
        dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI
            (fullScaleDyadicFibreLevel k) u := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let mass : iota → ENNReal := fun i ↦ shadingFiberMass Yw f i u
  let bucketAt := fun k : Nat ↦
    shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI (fullScaleDyadicFibreLevel k)
  have hsumFinite : (∑ i ∈ active, mass i) ≠ ∞ := by
    simpa only [mass, Yw,
      projectedActiveMultiplicity_eq_sum_shadingFiberMass
        Yw active f hf u] using hfinite
  have hmassFinite : ∀ i, i ∈ active → mass i ≠ ∞ := by
    intro i hi hmassTop
    apply hsumFinite
    apply top_unique
    have hsingle : mass i ≤ ∑ j ∈ active, mass j :=
      Finset.single_le_sum (fun _j _hj ↦ bot_le) hi
    simpa only [hmassTop] using hsingle
  rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
    Yw active f hf u]
  change (∑ i ∈ active, mass i) =
    ∑' k : Nat,
      dyadicFibreBucketWeightedMultiplicity
        Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) u
  calc
    (∑ i ∈ active, mass i) =
        ∑ i ∈ active, ∑' k : Nat,
          if i ∈ (bucketAt k).activeAtPoint u then mass i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [mass, Yw, bucketAt] using
        shadingFiberMass_eq_tsum_fullScaleDyadicFibreBuckets
          Y active f hf X hX I hI u huX i hi (hmassFinite i hi)
    _ = ∑' k : Nat, ∑ i ∈ active,
          if i ∈ (bucketAt k).activeAtPoint u then mass i else 0 := by
      exact (Summable.tsum_finsetSum
        (fun i _hi ↦ ENNReal.summable)).symm
    _ = ∑' k : Nat,
        dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI
            (fullScaleDyadicFibreLevel k) u := by
      apply tsum_congr
      intro k
      simp [dyadicFibreBucketWeightedMultiplicity,
        FiniteProjectedShading.activeAtPoint,
        finiteIncidenceActiveAtPoint,
        shadingAwareProjectedPhysicalDyadicFibreBucket,
        bucketAt, mass, Yw]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]

/-- A finite projected weighted mass on a measurable subset of the base is
exactly the sum of the weighted masses of all full-scale two-sided buckets.
Finiteness removes the possible infinite-density exceptional set; no bound
on the fibre window is used. -/
theorem projectedActiveShadingMassMeasure_eq_tsum_fullScaleDyadicFibreBucketWeightedMass
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (E : Set ProjectionSpace) (hE : MeasurableSet E) (hEX : E ⊆ X)
    (hfinite : projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E ≠ ∞) :
    projectedActiveShadingMassMeasure
        (shadingWindowRestriction Y f hf X hX I hI) active f E =
      ∑' k : Nat,
        dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E := by
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let g : ProjectionSpace → ENNReal :=
    fun u ↦ projectedActiveMultiplicity Yw active f u
  let mu : Measure ProjectionSpace :=
    projectedActiveShadingMassMeasure Yw active f
  have hg : Measurable g := by
    have hsum : Measurable fun u : ProjectionSpace ↦
        ∑ i ∈ active, shadingFiberMass Yw f i u := by
      exact Finset.measurable_fun_sum active fun i _hi ↦
        measurable_shadingFiberMass Yw f hf i
    simpa only [g,
      projectedActiveMultiplicity_eq_sum_shadingFiberMass
        Yw active f hf] using hsum
  have hmuApply :
      mu E = ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace) := by
    change ((volume : Measure ProjectionSpace).withDensity g) E =
      ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace)
    rw [MeasureTheory.withDensity_apply _ hE]
  have hIntegralFinite :
      (∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace)) ≠ ∞ := by
    rw [← hmuApply]
    simpa only [mu, Yw] using hfinite
  have htopNull :
      (volume : Measure ProjectionSpace) {u ∈ E | g u = ∞} = 0 :=
    measure_eq_top_of_setLIntegral_ne_top
      (μ := (volume : Measure ProjectionSpace))
      hg.aemeasurable hIntegralFinite
  have hfiniteGlobal :
      ∀ᵐ u ∂(volume : Measure ProjectionSpace), u ∈ E → g u ≠ ∞ := by
    rw [ae_iff]
    have hbad :
        {u : ProjectionSpace | ¬(u ∈ E → g u ≠ ∞)} =
          {u ∈ E | g u = ∞} := by
      ext u
      simp only [Set.mem_ofPred_eq]
      tauto
    rw [hbad]
    exact htopNull
  have hpointAE :
      g =ᵐ[(volume : Measure ProjectionSpace).restrict E]
        fun u ↦ ∑' k : Nat,
          dyadicFibreBucketWeightedMultiplicity
            Y active f hf X hX I hI
              (fullScaleDyadicFibreLevel k) u := by
    apply (ae_restrict_iff' hE).2
    filter_upwards [hfiniteGlobal] with u huFinite
    intro huE
    simpa only [g, Yw] using
      projectedActiveMultiplicity_eq_tsum_fullScaleDyadicFibreBuckets
        Y active f hf X hX I hI u (hEX huE) (huFinite huE)
  calc
    projectedActiveShadingMassMeasure Yw active f E =
        ∫⁻ u in E, g u ∂(volume : Measure ProjectionSpace) := hmuApply
    _ = ∫⁻ u in E, (∑' k : Nat,
          dyadicFibreBucketWeightedMultiplicity
            Y active f hf X hX I hI
              (fullScaleDyadicFibreLevel k) u)
          ∂(volume : Measure ProjectionSpace) :=
      lintegral_congr_ae hpointAE
    _ = ∑' k : Nat, ∫⁻ u in E,
          dyadicFibreBucketWeightedMultiplicity
            Y active f hf X hX I hI
              (fullScaleDyadicFibreLevel k) u
          ∂(volume : Measure ProjectionSpace) := by
      rw [lintegral_tsum]
      intro k
      exact (measurable_dyadicFibreBucketWeightedMultiplicity
        Y active f hf X hX I hI
          (fullScaleDyadicFibreLevel k)).aemeasurable
    _ = ∑' k : Nat,
        dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E := by
      apply tsum_congr
      intro k
      rfl

/-- A positive finite projected mass has one bucket among a finite initial
segment retaining its adaptive average.  The factor `2` is the
finite-partial-sum truncation loss and `binCount` is the exact number of
bins searched. -/
theorem exists_fullScaleDyadicFibreBucketWeightedMass_ge_adaptive_average
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (E : Set ProjectionSpace) (hE : MeasurableSet E) (hEX : E ⊆ X)
    (hpositive : 0 < projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E)
    (hfinite : projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E ≠ ∞) :
    ∃ binCount k : Nat, 1 ≤ binCount ∧ k < binCount ∧
      projectedActiveShadingMassMeasure
          (shadingWindowRestriction Y f hf X hX I hI) active f E /
          (2 * (binCount : ENNReal)) ≤
        dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E := by
  classical
  let sourceMass : ENNReal :=
    projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E
  let weight : Nat → ENNReal := fun k ↦
    dyadicFibreBucketWeightedMass
      Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E
  have hdecomp : sourceMass = ∑' k : Nat, weight k := by
    simpa only [sourceMass, weight] using
      projectedActiveShadingMassMeasure_eq_tsum_fullScaleDyadicFibreBucketWeightedMass
        Y active f hf X hX I hI E hE hEX hfinite
  have hhalf : sourceMass / 2 < sourceMass := by
    exact ENNReal.half_lt_self (by
      simpa only [sourceMass] using hpositive.ne') (by
        simpa only [sourceMass] using hfinite)
  have hhalfTsum : sourceMass / 2 < ∑' k : Nat, weight k := by
    rwa [← hdecomp]
  rw [ENNReal.tsum_eq_iSup_nat] at hhalfTsum
  obtain ⟨binCount, hpartial⟩ := lt_iSup_iff.mp hhalfTsum
  have hbinCountNe : binCount ≠ 0 := by
    intro hzero
    have himpossible : sourceMass / 2 < 0 := by
      simpa only [hzero, Finset.range_zero, Finset.sum_empty] using hpartial
    exact (not_lt_of_ge bot_le) himpossible
  have hbinCountPos : 0 < binCount := Nat.pos_of_ne_zero hbinCountNe
  let bins := Finset.range binCount
  have hbins : bins.Nonempty := by
    exact ⟨0, by simpa only [bins, Finset.mem_range] using hbinCountPos⟩
  obtain ⟨k, hk, hmax⟩ :=
    Finset.exists_max_image bins weight hbins
  have hsum :
      (∑ j ∈ bins, weight j) ≤ bins.card • weight k :=
    Finset.sum_le_card_nsmul bins weight (weight k)
      (fun j hj ↦ hmax j hj)
  have hpartialMax :
      (∑ j ∈ Finset.range binCount, weight j) ≤
        (binCount : ENNReal) * weight k := by
    simpa only [bins, Finset.card_range, nsmul_eq_mul] using hsum
  have hsourceDouble :
      sourceMass ≤ (∑ j ∈ Finset.range binCount, weight j) * 2 :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
      (le_of_lt hpartial)
  have hsourceLoss :
      sourceMass ≤ (2 * (binCount : ENNReal)) * weight k := by
    calc
      sourceMass ≤
          (∑ j ∈ Finset.range binCount, weight j) * 2 :=
        hsourceDouble
      _ ≤ ((binCount : ENNReal) * weight k) * 2 := by
        gcongr
      _ = (2 * (binCount : ENNReal)) * weight k := by ac_rfl
  have hlossZero : 2 * (binCount : ENNReal) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by
      exact_mod_cast hbinCountNe)
  have hlossTop : 2 * (binCount : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top binCount)
  refine ⟨binCount, k, hbinCountPos, by
    simpa only [bins, Finset.mem_range] using hk, ?_⟩
  apply (ENNReal.div_le_iff hlossZero hlossTop).mpr
  simpa only [sourceMass, weight, mul_comm] using hsourceLoss

/-
/-- The actual retained full-scale bucket and its geometric ceiling on the
same original positive exact-card band.  The retained mass uses the explicit
adaptive loss `2 * binCount`; no common fibre scale is assumed. -/
theorem exists_fullScaleDyadicFibreBucket_retention_and_originalCard_ceiling
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (n : Nat) (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E ⊆
      (shadingAwareProjectedPhysical
        Y active f hf X hX I hI).multiplicityBand n n)
    (hpositive : 0 < projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E)
    (hfinite : projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E ≠ ∞) :
    ∃ binCount k : Nat, 1 ≤ binCount ∧ k < binCount ∧
      projectedActiveShadingMassMeasure
          (shadingWindowRestriction Y f hf X hX I hI) active f E /
          (2 * (binCount : ENNReal)) ≤
        dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E ∧
      dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E ≤
        (2 * fullScaleDyadicFibreLevel k) *
          (n : ENNReal) * volume E := by
  have hEX : E ⊆ X := by
    intro u hu
    exact ((shadingAwareProjectedPhysical
      Y active f hf X hX I hI).mem_multiplicityBand.mp
        (hEband hu)).1
  obtain ⟨binCount, k, hbinCount, hk, hretain⟩ :=
    exists_fullScaleDyadicFibreBucketWeightedMass_ge_adaptive_average
      Y active f hf X hX I hI E hE hEX hpositive hfinite
  refine ⟨binCount, k, hbinCount, hk, hretain, ?_⟩
  exact
    dyadicFibreBucketWeightedMass_le_two_mul_level_mul_originalCard_mul_volume
      Y active f hf X hX I hI (fullScaleDyadicFibreLevel k)
        (fullScaleDyadicFibreLevel_pos k) n E hE hEband
-/

/-
/-- On the exact-card set where the cutoff lower bucket still contains all
positive fibres, every fibre may choose its own level among the first
`cutoff + 1` two-sided dyadic bins.  Their weighted contributions cover the
full projected multiplicity. -/
theorem projectedActiveMultiplicity_le_sum_dyadicFibreBucketWeightedMultiplicity
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hIone : volume I ≤ 1)
    (cutoff n : Nat) (u : ProjectionSpace)
    (hu : u ∈
      (shadingAwareProjectedPhysical
          Y active f hf X hX I hI).multiplicityBand n n ∩
        (shadingAwareProjectedPhysicalLowerBucket
          Y active f hf X hX I hI
            (dyadicFibreFloor cutoff)).multiplicityBand n n) :
    projectedActiveMultiplicity
        (shadingWindowRestriction Y f hf X hX I hI) active f u ≤
      ∑ level ∈ Finset.range (cutoff + 1),
        dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI (dyadicFibreFloor level) u := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let positive := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let lower := shadingAwareProjectedPhysicalLowerBucket
    Y active f hf X hX I hI (dyadicFibreFloor cutoff)
  let bucketAt := fun level : Nat ↦
    shadingAwareProjectedPhysicalDyadicFibreBucket
      Y active f hf X hX I hI (dyadicFibreFloor level)
  let mass : iota → ENNReal := fun i ↦ shadingFiberMass Yw f i u
  let levels := Finset.range (cutoff + 1)
  have huPositive := positive.mem_multiplicityBand.mp (by
    simpa only [positive] using hu.1)
  have huLower := lower.mem_multiplicityBand.mp (by
    simpa only [lower] using hu.2)
  have hactiveSubset :
      lower.activeAtPoint u ⊆ positive.activeAtPoint u := by
    simpa only [lower, positive] using
      activeAtPoint_lowerBucket_subset_positive
        Y active f hf X hX I hI
          (Family8Family7QuantitativeFibreFloorSelectionV2.dyadicFibreFloor_pos
            cutoff) u
  have hactiveEq :
      lower.activeAtPoint u = positive.activeAtPoint u := by
    apply Finset.eq_of_subset_of_card_le hactiveSubset
    omega
  rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
    Yw active f hf u]
  change (∑ i ∈ active, mass i) ≤
    ∑ level ∈ levels,
      dyadicFibreBucketWeightedMultiplicity
        Y active f hf X hX I hI (dyadicFibreFloor level) u
  calc
    (∑ i ∈ active, mass i) ≤
        ∑ i ∈ active, ∑ level ∈ levels,
          if i ∈ (bucketAt level).activeAtPoint u then mass i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hmassZero : mass i = 0
      · simp [hmassZero]
      · have hmassPos : 0 < mass i := pos_iff_ne_zero.mpr hmassZero
        have hiPositive : i ∈ positive.activeAtPoint u := by
          apply (mem_activeAtPoint_shadingAwareProjectedPhysical
            Y active f hf X hX I hI u i).mpr
          exact ⟨hi, huPositive.1, by simpa only [mass, Yw] using hmassPos⟩
        have hiLower : i ∈ lower.activeAtPoint u := by
          rw [hactiveEq]
          exact hiPositive
        have hmassLower : dyadicFibreFloor cutoff ≤ mass i := by
          have h := (mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
            Y active f hf X hX I hI
              (dyadicFibreFloor cutoff) u i).mp (by
                simpa only [lower] using hiLower)
          simpa only [mass, Yw] using h.2.2
        have hmassUpper : mass i ≤ 1 := by
          exact (by
            simpa only [mass, Yw] using
              (shadingFiberMass_shadingWindowRestriction_le_volume
                Y f hf X hX I hI i u).trans hIone)
        obtain ⟨level, hlevel, hlevelLower, hlevelUpper⟩ :=
          exists_dyadicFibreFloor_bucket_of_between
            cutoff hmassLower hmassUpper
        have hlevelMem : level ∈ levels := by
          simpa only [levels, Finset.mem_range, Nat.lt_succ_iff] using hlevel
        have hiBucket : i ∈ (bucketAt level).activeAtPoint u := by
          apply
            (mem_activeAtPoint_shadingAwareProjectedPhysicalDyadicFibreBucket
              Y active f hf X hX I hI
                (dyadicFibreFloor level) u i).mpr
          exact ⟨hi, huPositive.1,
            by simpa only [mass, Yw] using hlevelLower,
            by simpa only [mass, Yw] using hlevelUpper⟩
        calc
          mass i =
              (if i ∈ (bucketAt level).activeAtPoint u then mass i else 0) := by
            simp [hiBucket]
          _ ≤ ∑ k ∈ levels,
              if i ∈ (bucketAt k).activeAtPoint u then mass i else 0 := by
            exact Finset.single_le_sum
              (fun _k _hk ↦ bot_le) hlevelMem
    _ = ∑ level ∈ levels,
        dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI (dyadicFibreFloor level) u := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro level _hlevel
      simp [dyadicFibreBucketWeightedMultiplicity,
        FiniteProjectedShading.activeAtPoint,
        finiteIncidenceActiveAtPoint,
        shadingAwareProjectedPhysicalDyadicFibreBucket,
        bucketAt, mass, Yw]
-/

/-- On any measurable subset of an original positive exact-card band, the
weighted contribution of one two-sided fibre bucket is bounded by
`2 * level * n * volume`.  No false common-scale assertion is used. -/
theorem dyadicFibreBucketWeightedMass_le_two_mul_level_mul_originalCard_mul_volume
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (level : ENNReal) (hlevel : 0 < level)
    (n : Nat) (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E ⊆
      (shadingAwareProjectedPhysical
        Y active f hf X hX I hI).multiplicityBand n n) :
    dyadicFibreBucketWeightedMass
        Y active f hf X hX I hI level E ≤
      (2 * level) * (n : ENNReal) * volume E := by
  let bucket := shadingAwareProjectedPhysicalDyadicFibreBucket
    Y active f hf X hX I hI level
  let positive := shadingAwareProjectedPhysical
    Y active f hf X hX I hI
  have hpoint : ∀ u, u ∈ E →
      dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI level u ≤
        (2 * level) * (n : ENNReal) := by
    intro u hu
    have huPositive := positive.mem_multiplicityBand.mp (hEband hu)
    have hpositiveCard : (positive.activeAtPoint u).card = n := by omega
    have hbucketCard :
        (bucket.activeAtPoint u).card ≤ n := by
      calc
        (bucket.activeAtPoint u).card ≤
            (positive.activeAtPoint u).card :=
          Finset.card_le_card
            (activeAtPoint_dyadicFibreBucket_subset_positive
              Y active f hf X hX I hI hlevel u)
        _ = n := hpositiveCard
    calc
      dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI level u ≤
          (2 * level) * ((bucket.activeAtPoint u).card : ENNReal) := by
        simpa only [bucket] using
          dyadicFibreBucketWeightedMultiplicity_le_two_mul_level_mul_card
            Y active f hf X hX I hI level u
      _ ≤ (2 * level) * (n : ENNReal) := by
        gcongr
  unfold dyadicFibreBucketWeightedMass
  calc
    (∫⁻ u in E,
        dyadicFibreBucketWeightedMultiplicity
          Y active f hf X hX I hI level u
          ∂(volume : Measure ProjectionSpace)) ≤
        ∫⁻ _u in E, (2 * level) * (n : ENNReal)
          ∂(volume : Measure ProjectionSpace) :=
      setLIntegral_mono' hE hpoint
    _ = (2 * level) * (n : ENNReal) * volume E := by
      rw [setLIntegral_const]

/-- The actual retained full-scale bucket and its geometric ceiling on the
same original positive exact-card band. The retained mass uses the explicit
adaptive loss `2 * binCount`; no common fibre scale is assumed. -/
theorem exists_fullScaleDyadicFibreBucket_retention_and_originalCard_ceiling
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (n : Nat) (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E ⊆
      (shadingAwareProjectedPhysical
        Y active f hf X hX I hI).multiplicityBand n n)
    (hpositive : 0 < projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E)
    (hfinite : projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f E ≠ ∞) :
    ∃ binCount k : Nat, 1 ≤ binCount ∧ k < binCount ∧
      projectedActiveShadingMassMeasure
          (shadingWindowRestriction Y f hf X hX I hI) active f E /
          (2 * (binCount : ENNReal)) ≤
        dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E ∧
      dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI (fullScaleDyadicFibreLevel k) E ≤
        (2 * fullScaleDyadicFibreLevel k) *
          (n : ENNReal) * volume E := by
  have hEX : E ⊆ X := by
    intro u hu
    exact ((shadingAwareProjectedPhysical
      Y active f hf X hX I hI).mem_multiplicityBand.mp
        (hEband hu)).1
  obtain ⟨binCount, k, hbinCount, hk, hretain⟩ :=
    exists_fullScaleDyadicFibreBucketWeightedMass_ge_adaptive_average
      Y active f hf X hX I hI E hE hEX hpositive hfinite
  refine ⟨binCount, k, hbinCount, hk, hretain, ?_⟩
  exact
    dyadicFibreBucketWeightedMass_le_two_mul_level_mul_originalCard_mul_volume
      Y active f hf X hX I hI (fullScaleDyadicFibreLevel k)
        (fullScaleDyadicFibreLevel_pos k) n E hE hEband

/-- Once a two-sided bucket has retained a stated fraction of the literal
source weighted mass, its geometric ceiling pays exactly the desired
`level * volume` lower bound (up to the displayed losses). -/
theorem sourceWeightedMass_div_loss_le_two_mul_level_mul_card_mul_volume
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (sourceWeightedMass loss level : ENNReal)
    (hlevel : 0 < level)
    (n : Nat) (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E ⊆
      (shadingAwareProjectedPhysical
        Y active f hf X hX I hI).multiplicityBand n n)
    (hretain :
      sourceWeightedMass / loss ≤
        dyadicFibreBucketWeightedMass
          Y active f hf X hX I hI level E) :
    sourceWeightedMass / loss ≤
      (2 * level) * (n : ENNReal) * volume E :=
  hretain.trans
    (dyadicFibreBucketWeightedMass_le_two_mul_level_mul_originalCard_mul_volume
      Y active f hf X hX I hI level hlevel n E hE hEband)

#print axioms activeAtPoint_dyadicFibreBucket_subset_positive
#print axioms
  dyadicFibreBucketWeightedMass_le_two_mul_level_mul_originalCard_mul_volume
#print axioms
  exists_fullScaleDyadicFibreBucket_retention_and_originalCard_ceiling
#print axioms
  sourceWeightedMass_div_loss_le_two_mul_level_mul_card_mul_volume

end
end Family8ProjectedActiveShadingMassQuantitativeDyadicFibreBucketV2
