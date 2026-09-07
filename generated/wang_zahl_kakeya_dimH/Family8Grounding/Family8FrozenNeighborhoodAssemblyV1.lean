import Family8Grounding.Family8ComparableMultiplicityBucketsV1

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family8FrozenNeighborhoodAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
open Family8ComparableMultiplicityBucketsV1

noncomputable section
set_option linter.unusedSectionVars false

local instance family8FrozenAssemblyPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}

theorem fiberMultiplicity_restrictSet
    (P : ConvexFactorization F W) (Y : Shading F)
    (Omega : Set Space) (hOmega : MeasurableSet Omega) (k : kappa) (x : Space) :
    P.fiberMultiplicity (Y.restrictSet Omega hOmega) k x =
      if x ∈ Omega then P.fiberMultiplicity Y k x else 0 := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  by_cases hx : x ∈ Omega
  · rw [if_pos hx]
    apply congrArg Finset.card
    ext i
    simp [hx]
  · rw [if_neg hx, Finset.card_eq_zero]
    ext i
    simp [hx]

theorem parentFiberMultiplicity_restrictComparableBucket_eq
    (P : ConvexFactorization F W) (Y : Shading F) (b : Nat)
    (i : iota) (x : Space)
    (hx : x ∈ (restrictComparableCarrierStatisticBucket Y
      (parentFiberPointStatistic P Y)
      (measurableSet_parentFiberPointStatistic_eq P Y) b).carrier i) :
    P.fiberMultiplicity
        (restrictComparableCarrierStatisticBucket Y
          (parentFiberPointStatistic P Y)
          (measurableSet_parentFiberPointStatistic_eq P Y) b)
        (P.index.parent i) x =
      P.fiberMultiplicity Y (P.index.parent i) x := by
  classical
  have hlabel :
      comparableLabel (P.fiberMultiplicity Y (P.index.parent i) x) = b :=
    hx.2
  unfold ConvexFactorization.fiberMultiplicity
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hjFiber, hjx⟩
    exact ⟨hjFiber, hjx.1⟩
  · rintro ⟨hjFiber, hjx⟩
    refine ⟨hjFiber, hjx, ?_⟩
    have hp : P.index.parent j = P.index.parent i :=
      (P.index.mem_fiber j (P.index.parent i)).1 hjFiber |>.2
    simpa [parentFiberPointStatistic, hp] using hlabel

theorem recomputed_parentFiberMultiplicity_zeroOrComparable
    (P : ConvexFactorization F W) (Y : Shading F) (b : Nat)
    (i : iota) (x : Space)
    (hx : x ∈ (restrictComparableCarrierStatisticBucket Y
      (parentFiberPointStatistic P Y)
      (measurableSet_parentFiberPointStatistic_eq P Y) b).carrier i) :
    ZeroOrComparable (comparableBase b)
      (P.fiberMultiplicity
        (restrictComparableCarrierStatisticBucket Y
          (parentFiberPointStatistic P Y)
          (measurableSet_parentFiberPointStatistic_eq P Y) b)
        (P.index.parent i) x) := by
  rw [parentFiberMultiplicity_restrictComparableBucket_eq P Y b i x hx]
  apply zeroOrComparable_of_comparableLabel_eq
  exact hx.2

/-- The final fine refinement and frozen auxiliary coarse cover.  The
comparability fields are outputs of `exists_assembly`, not caller-supplied
estimates in the canonical theorem below. -/
structure Assembly
    (P : ConvexFactorization F W) (Y : Shading F) (r : Real) where
  refinement : IndexedShadingRefinement Y
  frozenCoarse : Shading W
  fiberLabel : Nat
  outerLabel : Nat
  loss : Nat
  indices_subset_fine : refinement.indices ⊆ P.index.fine
  retained : WithinFactor loss
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass
    refinement.shading.shadingMass
  covers : ∀ i x, x ∈ refinement.shading.carrier i →
    x ∈ frozenCoarse.carrier (P.index.parent i)
  fiber_comparable : ∀ k ∈ P.index.coarse, ∀ x ∈
      P.fiberShadedUnion refinement.shading k,
    ZeroOrComparable (comparableBase fiberLabel)
      (P.fiberMultiplicity refinement.shading k x)
  outer_comparable : ∀ x ∈ frozenCoarse.shadedUnion,
    ZeroOrComparable (comparableBase outerLabel)
      (frozenCoarse.pointMultiplicity x)

namespace Assembly

variable {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

theorem shadedUnion_subset_frozenCoarse (A : Assembly P Y r) :
    A.refinement.shading.shadedUnion ⊆ A.frozenCoarse.shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨P.index.parent i, A.covers i x hxi⟩

theorem outerMultiplicity_le_frozenCoarse
    (A : Assembly P Y r) (x : Space) :
    P.outerMultiplicity A.refinement.shading x ≤
      A.frozenCoarse.pointMultiplicity x := by
  classical
  unfold ConvexFactorization.outerMultiplicity Shading.pointMultiplicity
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨_hkCoarse, i, hiFiber, hxi⟩ :=
    (P.mem_inducedShading_carrier_iff A.refinement.shading k x).1 hk.2
  have hp : P.index.parent i = k :=
    (P.index.mem_fiber i k).1 hiFiber |>.2
  simpa [hp] using A.covers i x hxi

theorem fiberMultiplicity_le_twice_base
    (A : Assembly P Y r)
    (k : kappa) (hk : k ∈ P.index.coarse) (x : Space) :
    P.fiberMultiplicity A.refinement.shading k x ≤
      2 * comparableBase A.fiberLabel := by
  by_cases hzero : P.fiberMultiplicity A.refinement.shading k x = 0
  · simp [hzero]
  · have hpos : 0 < P.fiberMultiplicity A.refinement.shading k x :=
      Nat.pos_of_ne_zero hzero
    have hxInduced :
        x ∈ (P.inducedShading A.refinement.shading).carrier k :=
      (P.mem_inducedShading_iff_fiberMultiplicity_pos
        A.refinement.shading k x).2 hpos
    obtain ⟨_hk, i, hiFiber, hxi⟩ :=
      (P.mem_inducedShading_carrier_iff
        A.refinement.shading k x).1 hxInduced
    have hxFiber : x ∈ P.fiberShadedUnion A.refinement.shading k :=
      Set.mem_iUnion.mpr ⟨⟨i, hiFiber⟩, hxi⟩
    exact (A.fiber_comparable k hk x hxFiber).le_twice

theorem pointMultiplicity_eq_fineMultiplicity
    (A : Assembly P Y r) (x : Space) :
    A.refinement.shading.pointMultiplicity x =
      P.fineMultiplicity A.refinement.shading x := by
  classical
  unfold Shading.pointMultiplicity ConvexFactorization.fineMultiplicity
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hxi
    refine ⟨?_, hxi⟩
    by_contra hiFine
    have hiIndices : i ∉ A.refinement.indices :=
      fun hi => hiFine (A.indices_subset_fine hi)
    rw [A.refinement.carrier_eq_empty_of_not_mem i hiIndices] at hxi
    exact hxi
  · exact fun hi => hi.2

theorem pointMultiplicity_le_frozenProduct
    (A : Assembly P Y r) (x : Space) :
    A.refinement.shading.pointMultiplicity x ≤
      A.frozenCoarse.pointMultiplicity x *
        (2 * comparableBase A.fiberLabel) := by
  rw [A.pointMultiplicity_eq_fineMultiplicity]
  calc
    P.fineMultiplicity A.refinement.shading x ≤
        P.outerMultiplicity A.refinement.shading x *
          (2 * comparableBase A.fiberLabel) :=
      P.fineMultiplicity_le_outer_mul A.refinement.shading x
        (2 * comparableBase A.fiberLabel)
        (fun k hk => A.fiberMultiplicity_le_twice_base k hk x)
    _ ≤ A.frozenCoarse.pointMultiplicity x *
          (2 * comparableBase A.fiberLabel) :=
      Nat.mul_le_mul_right _ (A.outerMultiplicity_le_frozenCoarse x)

theorem pointMultiplicity_le_comparableProduct
    (A : Assembly P Y r) (x : Space) :
    A.refinement.shading.pointMultiplicity x ≤
      (2 * comparableBase A.outerLabel) *
        (2 * comparableBase A.fiberLabel) := by
  by_cases hx : x ∈ A.refinement.shading.shadedUnion
  · calc
      A.refinement.shading.pointMultiplicity x ≤
          A.frozenCoarse.pointMultiplicity x *
            (2 * comparableBase A.fiberLabel) :=
        A.pointMultiplicity_le_frozenProduct x
      _ ≤ (2 * comparableBase A.outerLabel) *
            (2 * comparableBase A.fiberLabel) :=
        Nat.mul_le_mul_right _
          ((A.outer_comparable x (A.shadedUnion_subset_frozenCoarse hx)).le_twice)
  · have hzero : A.refinement.shading.pointMultiplicity x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hx
        ((A.refinement.shading.pointMultiplicity_pos_iff_mem_shadedUnion x).1 hpos)
    simp [hzero]

theorem shadingMass_le_comparableProduct_nsmul_volume
    (A : Assembly P Y r) :
    A.refinement.shading.shadingMass ≤
      ((2 * comparableBase A.outerLabel) *
        (2 * comparableBase A.fiberLabel)) •
          volume A.refinement.shading.shadedUnion :=
  FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
      A.refinement.shading _ A.pointMultiplicity_le_comparableProduct

end Assembly

/-- Collision-free canonical construction of the two comparable buckets. -/
theorem exists_assembly
    (P : ConvexFactorization F W) (Y : Shading F)
    (r : Real) (hr : 0 < r) :
    ∃ A : Assembly P Y r,
      A.loss =
        (Nat.log 2 (Fintype.card iota) + 2) *
          (Nat.log 2 (Fintype.card kappa) + 2) ∧
      A.fiberLabel ∈ Finset.range (Nat.log 2 (Fintype.card iota) + 2) ∧
      A.outerLabel ∈ Finset.range (Nat.log 2 (Fintype.card kappa) + 2) := by
  classical
  let Yfine :=
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading
  let statF : iota → Space → Nat := parentFiberPointStatistic P Yfine
  have hstatF : ∀ i n, MeasurableSet {x | statF i x = n} := by
    intro i n
    exact measurableSet_parentFiberPointStatistic_eq P Yfine i n
  have hboundF : ∀ i x, x ∈ Yfine.carrier i →
      statF i x ≤ Fintype.card iota := by
    intro i x hx
    exact fiberMultiplicity_le_card P Yfine (P.index.parent i) x
  obtain ⟨bF, hbF, hmassF, _hcompF⟩ :=
    exists_restrictComparableCarrierStatisticBucket_with_large_mass
      Yfine statF (Fintype.card iota) hstatF hboundF
  let R0 := restrictComparableCarrierStatisticBucket Yfine statF hstatF bF
  let Z0 := P.neighborhoodInducedShading R0 r
  let statO : Space → Nat := Z0.pointMultiplicity
  have hstatO : ∀ n, MeasurableSet {x | statO x = n} := by
    intro n
    exact measurableSet_pointMultiplicity_eq Z0 n
  have hboundO : ∀ x ∈ R0.shadedUnion,
      statO x ≤ Fintype.card kappa := by
    intro x hx
    exact Z0.pointMultiplicity_le_card x
  obtain ⟨bO, hbO, hmassO, hcompO⟩ :=
    exists_restrictComparableStatisticBucket_with_large_mass
      R0 statO (Fintype.card kappa) hstatO hboundO
  let Omega : Set Space :=
    statisticSlice R0 (fun x => comparableLabel (statO x)) bO
  have hOmega : MeasurableSet Omega := by
    exact measurableSet_statisticSlice R0
      (fun x => comparableLabel (statO x))
      (measurableSet_comparableLabel_eq statO hstatO) bO
  let R : Shading F := R0.restrictSet Omega hOmega
  let Z : Shading W := Z0.restrictSet Omega hOmega
  let Ref : IndexedShadingRefinement Y := {
    indices := P.index.fine
    shading := R
    carrier_subset := fun i => by
      intro x hx
      have hxR0 : x ∈ R0.carrier i := hx.1
      have hxYfine : x ∈ Yfine.carrier i := hxR0.1
      exact (IndexedShadingRefinement.restrictTo Y P.index.fine).carrier_subset i hxYfine
    carrier_eq_empty_of_not_mem := fun i hi => by
      apply Set.Subset.antisymm
      · intro x hx
        have hxR0 : x ∈ R0.carrier i := hx.1
        have hxYfine : x ∈ Yfine.carrier i := hxR0.1
        simp [Yfine, IndexedShadingRefinement.restrictTo_carrier, hi] at hxYfine
      · exact Set.empty_subset _ }
  have hR_def : R = restrictComparableStatisticBucket R0 statO hstatO bO := by
    rfl
  have hretained : WithinFactor
      ((Nat.log 2 (Fintype.card iota) + 2) *
        (Nat.log 2 (Fintype.card kappa) + 2))
      Yfine.shadingMass R.shadingMass := by
    unfold WithinFactor
    calc
      Yfine.shadingMass ≤
          (Nat.log 2 (Fintype.card iota) + 2) • R0.shadingMass := by
        simpa [R0, statF] using hmassF
      _ ≤ (Nat.log 2 (Fintype.card iota) + 2) •
          ((Nat.log 2 (Fintype.card kappa) + 2) • R.shadingMass) := by
        gcongr
        simpa [R, hR_def] using hmassO
      _ = ((Nat.log 2 (Fintype.card iota) + 2) *
          (Nat.log 2 (Fintype.card kappa) + 2)) • R.shadingMass := by
        simpa [Nat.mul_comm] using
          (mul_nsmul R.shadingMass
            (Nat.log 2 (Fintype.card kappa) + 2)
            (Nat.log 2 (Fintype.card iota) + 2)).symm
  refine ⟨{
    refinement := Ref
    frozenCoarse := Z
    fiberLabel := bF
    outerLabel := bO
    loss :=
      (Nat.log 2 (Fintype.card iota) + 2) *
        (Nat.log 2 (Fintype.card kappa) + 2)
    indices_subset_fine := fun _ hi => hi
    retained := by simpa [Yfine, Ref] using hretained
    covers := ?_
    fiber_comparable := ?_
    outer_comparable := ?_ }, rfl, hbF, hbO⟩
  · intro i x hx
    have hxR0 : x ∈ R0.carrier i := hx.1
    have hxOmega : x ∈ Omega := hx.2
    have hiFine : i ∈ P.index.fine := by
      by_contra hi
      have hxYfine : x ∈ Yfine.carrier i := hxR0.1
      simp [Yfine, IndexedShadingRefinement.restrictTo_carrier, hi] at hxYfine
    have hxFiber : x ∈ P.fiberShadedUnion R0 (P.index.parent i) := by
      apply Set.mem_iUnion.mpr
      exact ⟨⟨i, (P.index.mem_fiber i (P.index.parent i)).2
        ⟨hiFine, rfl⟩⟩, hxR0⟩
    have hxZ0 : x ∈ Z0.carrier (P.index.parent i) :=
      P.fiberShadedUnion_subset_neighborhoodInducedShading
        R0 hr (P.index.parent i) hxFiber
    exact ⟨hxZ0, hxOmega⟩
  · intro k hk x hxFiberR
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxFiberR
    have hxR0 : x ∈ R0.carrier i.1 := hxi.1
    have hxOmega : x ∈ Omega := hxi.2
    have hp : P.index.parent i.1 = k :=
      (P.index.mem_fiber i.1 k).1 i.2 |>.2
    rw [show P.fiberMultiplicity R k x =
        P.fiberMultiplicity R0 k x by
      simpa [R, if_pos hxOmega] using
        fiberMultiplicity_restrictSet P R0 Omega hOmega k x]
    rw [← hp]
    exact recomputed_parentFiberMultiplicity_zeroOrComparable
      P Yfine bF i.1 x hxR0
  · intro x hxZ
    have hxPair : x ∈ Z0.shadedUnion ∩ Omega := by
      change x ∈ (Z0.restrictSet Omega hOmega).shadedUnion at hxZ
      rwa [Shading.restrictSet_shadedUnion] at hxZ
    have hxOmega : x ∈ Omega := hxPair.2
    have hxR : x ∈ R.shadedUnion := by
      change x ∈ (R0.restrictSet Omega hOmega).shadedUnion
      rw [Shading.restrictSet_shadedUnion]
      exact ⟨hxOmega.1, hxOmega⟩
    rw [show Z.pointMultiplicity x = Z0.pointMultiplicity x by
      simpa [Z, if_pos hxOmega] using
        Shading.pointMultiplicity_restrictSet Z0 Omega hOmega x]
    exact hcompO x (by simpa [hR_def] using hxR)

#print axioms recomputed_parentFiberMultiplicity_zeroOrComparable
#print axioms Assembly.shadingMass_le_comparableProduct_nsmul_volume
#print axioms exists_assembly

end

end Family8FrozenNeighborhoodAssemblyV1
