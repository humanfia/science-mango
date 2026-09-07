import Family8Grounding.Family8FrozenNeighborhoodAssemblyV1

/-!
# Polylogarithmic exact-outer comparable assembly, V2

V1 is a frozen carrier/shaded-union elaboration draft.  This construction
keeps the carrierwise comparable fibre bucket and uses the recomputed exact
induced outer multiplicity for the second bucket.  Its stored coarse shading
is definitionally the exact induced shading of the final refinement.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family8ExactOuterComparableAssemblyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

local instance family8ExactOuterPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}

theorem exists_exactOuter_assembly
    (P : ConvexFactorization F W) (Y : Shading F) (r : Real) :
    ∃ A : Assembly P Y r,
      A.loss =
        (Nat.log 2 (Fintype.card iota) + 2) *
          (Nat.log 2 (Fintype.card kappa) + 2) ∧
      A.fiberLabel ∈ Finset.range (Nat.log 2 (Fintype.card iota) + 2) ∧
      A.outerLabel ∈ Finset.range (Nat.log 2 (Fintype.card kappa) + 2) ∧
      A.frozenCoarse = P.inducedShading A.refinement.shading := by
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
  let Z0 := P.inducedShading R0
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
    statisticSlice R0 (fun x ↦ comparableLabel (statO x)) bO
  have hOmega : MeasurableSet Omega := by
    exact measurableSet_statisticSlice R0
      (fun x ↦ comparableLabel (statO x))
      (measurableSet_comparableLabel_eq statO hstatO) bO
  let R : Shading F := R0.restrictSet Omega hOmega
  let Z : Shading W := P.inducedShading R
  let Ref : IndexedShadingRefinement Y := {
    indices := P.index.fine
    shading := R
    carrier_subset := fun i ↦ by
      intro x hx
      have hxR0 : x ∈ R0.carrier i := hx.1
      have hxYfine : x ∈ Yfine.carrier i := hxR0.1
      exact (IndexedShadingRefinement.restrictTo Y P.index.fine).carrier_subset
        i hxYfine
    carrier_eq_empty_of_not_mem := fun i hi ↦ by
      apply Set.Subset.antisymm
      · intro x hx
        have hxR0 : x ∈ R0.carrier i := hx.1
        have hxYfine : x ∈ Yfine.carrier i := hxR0.1
        simp [Yfine, IndexedShadingRefinement.restrictTo_carrier, hi] at hxYfine
      · exact Set.empty_subset _ }
  have hR_def : R =
      restrictComparableStatisticBucket R0 statO hstatO bO := by
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
    indices_subset_fine := fun _ hi ↦ hi
    retained := by simpa [Yfine, Ref] using hretained
    covers := ?_
    fiber_comparable := ?_
    outer_comparable := ?_ }, rfl, hbF, hbO, rfl⟩
  · intro i x hx
    have hiFine : i ∈ P.index.fine := by
      by_contra hi
      have hiRef : i ∉ Ref.indices := by simpa [Ref] using hi
      rw [Ref.carrier_eq_empty_of_not_mem i hiRef] at hx
      exact hx
    apply (P.mem_inducedShading_carrier_iff R (P.index.parent i) x).2
    exact ⟨P.index.parent_mem i hiFine, i,
      (P.index.mem_fiber i (P.index.parent i)).2 ⟨hiFine, rfl⟩, hx⟩
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
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxZ
    obtain ⟨_hk, i, _hiFiber, hxi⟩ :=
      (P.mem_inducedShading_carrier_iff R k x).1 hxk
    have hxR : x ∈ R.shadedUnion := Set.mem_iUnion.mpr ⟨i, hxi⟩
    change x ∈ R0.carrier i ∩ Omega at hxi
    have hxOmega : x ∈ Omega := hxi.2
    have hpoint : Z.pointMultiplicity x = Z0.pointMultiplicity x := by
      have h := pointMultiplicity_inducedShading_restrictSet
        P R0 Omega hOmega x
      simpa [R, Z, Z0, if_pos hxOmega] using h
    have hxBucket : x ∈
        (restrictComparableStatisticBucket R0 statO hstatO bO).shadedUnion := by
      rw [← hR_def]
      exact hxR
    rw [hpoint]
    exact hcompO x hxBucket

#print axioms exists_exactOuter_assembly

end
end Family8ExactOuterComparableAssemblyV2
