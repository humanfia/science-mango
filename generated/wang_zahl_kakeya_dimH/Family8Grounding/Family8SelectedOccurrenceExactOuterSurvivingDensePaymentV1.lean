import Family8Grounding.Family8ActualRefinementSurvivingDenseFiberV1
import Family8Grounding.Family8ExactOuterComparableActualAverageMassDensityV1
import Family8Grounding.Family8SelectedOccurrenceFineBucketSupportV1
import Family8Grounding.Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

/-!
# Exact-outer selected occurrence with a surviving-fibre density payment

The actual refinement is averaged over its literal surviving fibres before an
occurrence is decoded.  The resulting occurrence is simultaneously
density-good and the second actual-average factor.  Its local payment is
weighted by the honest number of surviving indices, and therefore contains no
factor `R.card`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceExactOuterSurvivingDensePaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8ActualRefinementSurvivingDenseFiberV1
open Family8ExactOuterComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFineBucketSupportV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1.StickyScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- A shading supported on the active fine set has ambient density at most
its literal active-subtype density.  The masses agree, while the active
family-volume denominator can only decrease. -/
theorem shadingDensity_le_sourceActiveFineShading_of_restrict_eq
    {l : Type*} [Fintype l] [DecidableEq l]
    {G : ConvexFamily iota} {W : ConvexFamily l}
    (Q : ConvexFactorization G W) (source : Shading G)
    (hrestrict :
      (IndexedShadingRefinement.restrictTo source Q.index.fine).shading =
        source) :
    source.shadingDensity ≤ (sourceActiveFineShading Q source).shadingDensity := by
  let selectedSource := sourceActiveFineShading Q source
  have hfamily : familyVolume (sourceActiveFineFamily Q) ≤ familyVolume G := by
    unfold sourceActiveFineFamily
    rw [selectedCoarseFamily_volume]
    unfold familyVolume
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hmass : selectedSource.shadingMass = source.shadingMass := by
    unfold selectedSource
    rw [sourceActiveFineShading_shadingMass, hrestrict]
  by_cases hzero : familyVolume G = 0
  · have hsourceMass : source.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp
        (source.shadingMass_le_familyVolume.trans_eq hzero)
    simp [Shading.shadingDensity, hzero, hsourceMass]
  · rw [← ENNReal.mul_le_mul_iff_right hzero (familyVolume_ne_top G)]
    calc
      familyVolume G * source.shadingDensity = source.shadingMass := by
        rw [mul_comm]
        exact
          Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume
            source
      _ = selectedSource.shadingMass := hmass.symm
      _ = selectedSource.shadingDensity *
          familyVolume (sourceActiveFineFamily Q) := by
        exact
          (Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume
            selectedSource).symm
      _ ≤ selectedSource.shadingDensity * familyVolume G :=
        mul_le_mul' le_rfl hfamily
      _ = familyVolume G * selectedSource.shadingDensity := by ac_rfl

/-- The block-subtype reindex used by selected-parent Córdoba has exactly the
mass of the ambient-index final fibre. -/
theorem selectedOccurrenceFrozenFinalFiberBlockShading_mass_eq_finalFiber
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) {Y : Shading F} {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) Y r)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    (selectedOccurrenceFrozenFinalFiberBlockShading P R A q).shadingMass =
      (finalFiberShading A (some q)).shadingMass := by
  classical
  rw [selectedOccurrenceFrozenFinalFiberBlockShading,
    selectedCoarseShading_mass]
  rw [finalFiberShading, fiberShading_mass_eq_sum_fiber,
    selectedOccurrenceFactorization_fiber P R q hq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fiberShading_carrier, if_pos]
  rw [selectedOccurrenceFactorization_fiber P R q hq]
  exact hi

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Exact-outer frozen assembly with one density-good selected occurrence.
The source is the ambient restricted shading, while the local card counts only
the indices that genuinely survived the assembly in that occurrence. -/
theorem exists_selectedOccurrence_exactOuter_survivingDensePayment
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (hfineBucket : fineBucket ⊆ selectedOccurrenceFineIndices P R)
    (hYbucket :
      (IndexedShadingRefinement.restrictTo Y fineBucket).shading.shadingMass ≠
        0)
    (rFrozen : Real) (hrFrozen : 0 < rFrozen) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (selectedOccurrenceFactorization P R)
        (IndexedShadingRefinement.restrictTo Y fineBucket).shading rFrozen,
      A.loss = frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) ∧
      A.frozenCoarse =
        (selectedOccurrenceFactorization P R).inducedShading
          A.refinement.shading ∧
      ∃ q ∈ R,
        let source :=
          (IndexedShadingRefinement.restrictTo Y fineBucket).shading
        let surviving := actualRefinementSurvivingFiberIndices A (some q)
        let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
        source.shadingDensity *
            ((surviving.card : ENNReal) * ((rho : ENNReal) ^ 2 / 2)) ≤
          (frozenComparableLoss (ActiveParentIndex S)
              (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) *
            Z.shadingMass ∧
        (actualRefinementSurvivingFiberShading A (some q)).shadingMass =
          Z.shadingMass ∧
        0 < volume (finalFiberShading A (some q)).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A (some q)).averageMultiplicity) := by
  classical
  let Q := selectedOccurrenceFactorization P R
  let source :=
    (IndexedShadingRefinement.restrictTo Y fineBucket).shading
  let area : ENNReal := (rho : ENNReal) ^ 2 / 2
  have hrestrict :
      (IndexedShadingRefinement.restrictTo source Q.index.fine).shading =
        source := by
    simpa only [Q, source] using
      selectedOccurrenceFineBucket_restrictTo_fine_eq
        P R Y fineBucket hfineBucket
  have hsource :
      (IndexedShadingRefinement.restrictTo source Q.index.fine).shading.shadingMass
        ≠ 0 := by
    rw [hrestrict]
    exact hYbucket
  obtain ⟨A, hLoss, _hFiberLabel, _hOuterLabel, hExactOuter,
      _hMass, hDensityDiv, _oldK, _holdK, _holdVolume,
      _hFiberLower, _hFiberUpper, _hOuterLower, _hOuterUpper, _holdProduct⟩ :=
    exists_exactOuter_frozenComparableAssembly_with_actualAverages_mass_density
      Q source rFrozen hrFrozen hsource
  have harea0 : area ≠ 0 := by
    dsimp only [area]
    apply ENNReal.div_ne_zero.mpr
    exact ⟨ENNReal.pow_ne_zero
      (ENNReal.coe_ne_zero.mpr hrho.ne') 2, by norm_num⟩
  have harea : ∀ i ∈ A.refinement.indices,
      area ≤ volume (S.activeCoarseFamily i : Set Space) := by
    intro i _hi
    change area ≤ volume (S.coarse.tubes i.1).carrier
    simpa only [area] using
      (S.coarse.tubes i.1).half_sq_le_volume_of_le_half hrhoHalf
  obtain ⟨k, hk, hdense, hcardArea, hmassEq, hvolume, hproduct⟩ :=
    exists_actualRefinementSurvivingFiber_dense_sameAssemblyProduct
      A area harea0 harea hsource
  have hkSelected : k ∈ selectedOccurrenceIndices P R := by
    simpa only [Q, selectedOccurrenceFactorization_coarse] using hk
  obtain ⟨q, hq, hqk⟩ :=
    (mem_selectedOccurrenceIndices P R k).1 hkSelected
  subst k
  let loss : ENNReal :=
    frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length))
  have hlossNatPos : 0 < frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length)) := by
    unfold frozenComparableLoss
    positivity
  have hloss0 : loss ≠ 0 := by
    dsimp only [loss]
    exact_mod_cast hlossNatPos.ne'
  have hlossTop : loss ≠ ∞ := by simp [loss]
  have hambientActive : source.shadingDensity ≤
      (sourceActiveFineShading Q source).shadingDensity :=
    shadingDensity_le_sourceActiveFineShading_of_restrict_eq
      Q source hrestrict
  have hactiveActual :
      (sourceActiveFineShading Q source).shadingDensity ≤
        loss * (actualRefinementShading A).shadingDensity := by
    calc
      (sourceActiveFineShading Q source).shadingDensity =
          ((sourceActiveFineShading Q source).shadingDensity / loss) * loss :=
        (ENNReal.div_mul_cancel hloss0 hlossTop).symm
      _ ≤ (actualRefinementShading A).shadingDensity * loss :=
        mul_le_mul' (by simpa only [loss] using hDensityDiv) le_rfl
      _ = loss * (actualRefinementShading A).shadingDensity := by ac_rfl
  have hambientActual : source.shadingDensity ≤
      loss * (actualRefinementShading A).shadingDensity :=
    hambientActive.trans hactiveActual
  have hlocalPayment :
      source.shadingDensity *
          (((actualRefinementSurvivingFiberIndices A (some q)).card : ENNReal) *
            area) ≤
        loss *
          (actualRefinementSurvivingFiberShading A (some q)).shadingMass := by
    calc
      source.shadingDensity *
          (((actualRefinementSurvivingFiberIndices A (some q)).card : ENNReal) *
            area) ≤
        (loss * (actualRefinementShading A).shadingDensity) *
          (((actualRefinementSurvivingFiberIndices A (some q)).card : ENNReal) *
            area) := mul_le_mul' hambientActual le_rfl
      _ = loss * ((actualRefinementShading A).shadingDensity *
          (((actualRefinementSurvivingFiberIndices A (some q)).card : ENNReal) *
            area)) := by ac_rfl
      _ ≤ loss * ((actualRefinementShading A).shadingDensity *
          familyVolume
            (actualRefinementSurvivingFiberFamily A (some q))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hcardArea)
      _ ≤ loss *
          ((actualRefinementSurvivingFiberShading A (some q)).shadingDensity *
            familyVolume
              (actualRefinementSurvivingFiberFamily A (some q))) :=
        mul_le_mul' le_rfl (mul_le_mul' hdense le_rfl)
      _ = loss *
          (actualRefinementSurvivingFiberShading A (some q)).shadingMass := by
        rw [Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume]
  have hblockMass :=
    selectedOccurrenceFrozenFinalFiberBlockShading_mass_eq_finalFiber
      P R A q hq
  have hlocalBlock :
      (actualRefinementSurvivingFiberShading A (some q)).shadingMass =
        (selectedOccurrenceFrozenFinalFiberBlockShading P R A q).shadingMass :=
    hmassEq.trans hblockMass.symm
  refine ⟨A, ?_, ?_, q, hq, ?_⟩
  · simpa only [Q, source] using hLoss
  · simpa only [Q, source] using hExactOuter
  · dsimp only
    refine ⟨?_, hlocalBlock, ?_, ?_⟩
    · simpa only [source, area, loss, hlocalBlock] using hlocalPayment
    · simpa only [Q, source] using hvolume
    · simpa only [Q, source] using hproduct

#print axioms shadingDensity_le_sourceActiveFineShading_of_restrict_eq
#print axioms selectedOccurrenceFrozenFinalFiberBlockShading_mass_eq_finalFiber
#print axioms exists_selectedOccurrence_exactOuter_survivingDensePayment

end
end Family8SelectedOccurrenceExactOuterSurvivingDensePaymentV1
