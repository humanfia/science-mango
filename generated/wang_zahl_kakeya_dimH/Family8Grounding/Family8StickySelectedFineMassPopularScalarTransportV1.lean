import Family8Grounding.Family8StickySelectedFineAssemblyMassPopularV1
import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFineMassPopularScalarTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineAssemblyMassPopularV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Scalar transport on the mass-popular selected fibre

The mass-popular parent is retained as the same literal selected-fine
subtype used by the contracted-John endpoint.  Its shading mass is bounded
by its indexed body volume, and every radius-`delta` tube has volume at most
`8 delta^2`.  Thus the source mass gives both a fibre-cardinality floor and,
after an honest bounded-fibre cap, a source-density floor.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- An arbitrary Sticky fibre has indexed body volume at most its literal
cardinality times `8 delta^2`. -/
theorem stickyFiber_familyVolume_le_card_mul_eight_sq
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (k : Fin S.coarseCard) :
    familyVolume (S.fiberFamily k) <=
      (Fintype.card {i // i ∈ S.fiber k} : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
  unfold familyVolume
  simp only [StickyScaleCover.fiberFamily, UniformTubeFamily.bodyFamily,
    Tube.coe_body]
  calc
    (∑ i : {i // i ∈ S.fiber k}, volume (fine.tubes i.1).carrier) <=
        ∑ _i : {i // i ∈ S.fiber k}, 8 * (delta : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        (fine.tubes i.1).volume_le_eight_mul_sq_of_le_half hdeltaHalf
    _ = (Fintype.card {i // i ∈ S.fiber k} : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- A selected-fine fibre injects into the old fibre over the exact parent
value recorded by the reindexing equivalence. -/
theorem selectedFine_fiber_card_le_original
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (q : Fin (selectedFineParentValues S selected).card) :
    Fintype.card {i // i ∈
        (selectedFineScaleCover S selected hselected).fiber q} <=
      (S.fiber
        ((selectedFineParentValues S selected).equivFin.symm q).1).card := by
  classical
  let oldK :=
    ((selectedFineParentValues S selected).equivFin.symm q).1
  let T := selectedFineScaleCover S selected hselected
  let embed : {i // i ∈ T.fiber q} -> {i // i ∈ S.fiber oldK} :=
    fun i => ⟨i.1.1, (S.mem_fiber i.1.1 oldK).2 ⟨
      hselected i.1.2,
      (mem_selectedFineScaleCover_fiber_iff
        S selected hselected i.1 q).1 i.2⟩⟩
  have hinjective : Function.Injective embed := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {i // i ∈ S.fiber oldK} => z.1) hij
  have hcard := Fintype.card_le_of_injective embed hinjective
  simpa only [T, oldK, Fintype.card_coe] using hcard

/-- The old uniform fibre bound remains valid on every selected-fine fibre.
The parent is the same old parent, not a merely isomorphic replacement. -/
theorem selectedFine_fiber_card_le_bound
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse -> (S.fiber k).card <= M)
    (q : Fin (selectedFineParentValues S selected).card) :
    Fintype.card {i // i ∈
        (selectedFineScaleCover S selected hselected).fiber q} <= M := by
  classical
  let oldK :=
    ((selectedFineParentValues S selected).equivFin.symm q).1
  have holdActive : oldK ∈ S.activeCoarse := by
    obtain ⟨i, hiSelected, hiParent⟩ := Finset.mem_image.mp
      ((selectedFineParentValues S selected).equivFin.symm q).2
    dsimp only [oldK]
    rw [← hiParent]
    exact S.parent_mem i (hselected hiSelected)
  exact (selectedFine_fiber_card_le_original S selected hselected q).trans
    (hM oldK holdActive)

/-- One literal selected parent simultaneously carries the assembly product,
the mass-to-card budget, and the bounded mass-to-density budget. -/
theorem exists_selectedFine_massPopular_card_density_product
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) (r : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse -> (S.fiber k).card <= M)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass
        ≠ 0) :
    ∃ q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      let T := selectedFineScaleCover S A.refinement.indices
        (assembly_indices_subset_activeFine S Y r A)
      let Z := selectedFineShading S A.refinement.indices A.refinement.shading
      let sourceMass :=
        (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass
      let L : ENNReal :=
        (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)
      let fibreCard : ENNReal :=
        Fintype.card {i // i ∈ T.fiber q.1}
      sourceMass <= L * (fibreCard * (8 * (delta : ENNReal) ^ 2)) ∧
      sourceMass <=
        (L * ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) *
          (stickyFiberSourceShading T Z q.1).shadingDensity ∧
      0 < volume (stickyFiberSourceShading T Z q.1).shadedUnion ∧
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          (stickyFiberSourceShading T Z q.1).averageMultiplicity) := by
  classical
  let hselected := assembly_indices_subset_activeFine S Y r A
  let T := selectedFineScaleCover S A.refinement.indices hselected
  let Z := selectedFineShading S A.refinement.indices A.refinement.shading
  let sourceMass :=
    (sourceActiveFineShading (toConvexFactorization S) Y).shadingMass
  let L : ENNReal :=
    (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal)
  obtain ⟨q, hmass, hunion, hproduct⟩ :=
    exists_selectedFine_massPopular_sameAssemblyFiber_product S Y r A hsource
  let fibreZ := stickyFiberSourceShading T Z q.1
  let fibreCard : ENNReal := Fintype.card {i // i ∈ T.fiber q.1}
  have hvolume : familyVolume (T.fiberFamily q.1) <=
      fibreCard * (8 * (delta : ENNReal) ^ 2) := by
    simpa only [T, fibreCard] using
      stickyFiber_familyVolume_le_card_mul_eight_sq T hdeltaHalf q.1
  have hfibreMassCard : fibreZ.shadingMass <=
      fibreCard * (8 * (delta : ENNReal) ^ 2) :=
    fibreZ.shadingMass_le_familyVolume.trans hvolume
  have hcardBound : fibreCard <= (M : ENNReal) := by
    dsimp only [fibreCard]
    exact_mod_cast selectedFine_fiber_card_le_bound
      S A.refinement.indices hselected M hM q.1
  have hfibreMassDensity : fibreZ.shadingMass <=
      fibreZ.shadingDensity *
        ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2)) := by
    rw [← Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume fibreZ]
    exact mul_le_mul' le_rfl
      (hvolume.trans (mul_le_mul' hcardBound le_rfl))
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · calc
      sourceMass <= L * fibreZ.shadingMass := by
        simpa only [sourceMass, L, fibreZ, T, Z, hselected, mul_assoc] using hmass
      _ <= L * (fibreCard * (8 * (delta : ENNReal) ^ 2)) :=
        mul_le_mul' le_rfl hfibreMassCard
  · calc
      sourceMass <= L * fibreZ.shadingMass := by
        simpa only [sourceMass, L, fibreZ, T, Z, hselected, mul_assoc] using hmass
      _ <= L * (fibreZ.shadingDensity *
          ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) :=
        mul_le_mul' le_rfl hfibreMassDensity
      _ = (L * ((M : ENNReal) * (8 * (delta : ENNReal) ^ 2))) *
          fibreZ.shadingDensity := by ac_rfl
  · simpa only [fibreZ, T, Z, hselected] using hunion
  · simpa only [fibreZ, T, Z, hselected] using hproduct

#print axioms stickyFiber_familyVolume_le_card_mul_eight_sq
#print axioms selectedFine_fiber_card_le_original
#print axioms selectedFine_fiber_card_le_bound
#print axioms exists_selectedFine_massPopular_card_density_product

end
end Family8StickySelectedFineMassPopularScalarTransportV1
