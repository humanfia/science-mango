import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.JointTubeFactoring
import Mathlib.Tactic

/-!
# A density-good surviving fibre of one frozen assembly

The final refinement indices are first regarded as their own raw
factorization, with the original parent map.  Exact body- and shaded-mass
decompositions on that factorization select one literal surviving fibre whose
density is at least the density of the whole actual refinement.  The same old
parent is then used in the frozen assembly product.

No coarse-cardinality or mass-popularity loss occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ActualRefinementSurvivingDenseFiberV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Family8ExactAssemblyActualAverageBridgeV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- The surviving refinement indices, with the original assembly parent map. -/
def actualRefinementSurvivingFactorization
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    ConvexFactorization F W where
  index := rawIndexFactorization A.refinement.indices P.index.parent
  contained := by
    intro i hi
    exact P.contained i (A.indices_subset_fine hi)

@[simp] theorem actualRefinementSurvivingFactorization_fine
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (actualRefinementSurvivingFactorization A).index.fine =
      A.refinement.indices := rfl

@[simp] theorem actualRefinementSurvivingFactorization_coarse
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (actualRefinementSurvivingFactorization A).index.coarse =
      A.refinement.indices.image P.index.parent := rfl

/-- The surviving indices over one old parent. -/
def actualRefinementSurvivingFiberIndices
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) : Finset iota :=
  (actualRefinementSurvivingFactorization A).index.fiber k

/-- The literal body family of the surviving indices over one parent. -/
def actualRefinementSurvivingFiberFamily
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) :
    ConvexFamily {i // i ∈ actualRefinementSurvivingFiberIndices A k} :=
  selectedCoarseFamily F (actualRefinementSurvivingFiberIndices A k)

/-- The final refinement shading on the literal surviving fibre subtype. -/
def actualRefinementSurvivingFiberShading
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) : Shading (actualRefinementSurvivingFiberFamily A k) :=
  selectedCoarseShading A.refinement.shading
    (actualRefinementSurvivingFiberIndices A k)

theorem actualRefinementSurvivingFiberShading_shadingMass_eq_sum
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) :
    (actualRefinementSurvivingFiberShading A k).shadingMass =
      ∑ i ∈ actualRefinementSurvivingFiberIndices A k,
        volume (A.refinement.shading.carrier i) := by
  unfold actualRefinementSurvivingFiberShading
    actualRefinementSurvivingFiberFamily Shading.shadingMass
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach (actualRefinementSurvivingFiberIndices A k)
    (fun i => volume (A.refinement.shading.carrier i))

theorem surviving_activeBodyMass_eq_actualRefinementFamilyVolume
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    activeBodyMass (actualRefinementSurvivingFactorization A) =
      familyVolume (actualRefinementFamily A) := by
  unfold activeBodyMass actualRefinementSurvivingFactorization
    actualRefinementFamily
  rw [selectedCoarseFamily_volume]
  rfl

theorem surviving_activeShadingMass_eq_actualRefinementShadingMass
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    activeShadingMass (actualRefinementSurvivingFactorization A)
        A.refinement.shading =
      (actualRefinementShading A).shadingMass := by
  unfold activeShadingMass actualRefinementSurvivingFactorization
    actualRefinementShading actualRefinementFamily
  rw [selectedCoarseShading_mass]
  rfl

theorem surviving_fiberBodyMass_eq_familyVolume
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) :
    fiberBodyMass (actualRefinementSurvivingFactorization A) k =
      familyVolume (actualRefinementSurvivingFiberFamily A k) := by
  unfold fiberBodyMass actualRefinementSurvivingFiberFamily
    actualRefinementSurvivingFiberIndices
  rw [selectedCoarseFamily_volume]

theorem surviving_fiberShadingMass_eq_shadingMass
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) :
    HeavyParentSelection.fiberShadingMass
        (actualRefinementSurvivingFactorization A)
        A.refinement.shading k =
      (actualRefinementSurvivingFiberShading A k).shadingMass := by
  calc
    HeavyParentSelection.fiberShadingMass
        (actualRefinementSurvivingFactorization A)
        A.refinement.shading k =
        ∑ i ∈ actualRefinementSurvivingFiberIndices A k,
          volume (A.refinement.shading.carrier i) := rfl
    _ = (actualRefinementSurvivingFiberShading A k).shadingMass :=
      (actualRefinementSurvivingFiberShading_shadingMass_eq_sum A k).symm

/-- Discarded indices have empty final carrier, so the literal surviving
fibre has exactly the mass of the ambient-index `finalFiberShading`. -/
theorem actualRefinementSurvivingFiberShading_shadingMass_eq_finalFiberShading
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) :
    (actualRefinementSurvivingFiberShading A k).shadingMass =
      (finalFiberShading A k).shadingMass := by
  classical
  rw [actualRefinementSurvivingFiberShading_shadingMass_eq_sum]
  rw [finalFiberShading, fiberShading_mass_eq_sum_fiber]
  apply Finset.sum_subset
  · intro i hi
    have hi' :=
      (actualRefinementSurvivingFactorization A).index.fiber_subset_fine k hi
    have hiParent :=
      ((actualRefinementSurvivingFactorization A).index.mem_fiber i k).1 hi |>.2
    exact P.index.mem_fiber i k |>.2
      ⟨A.indices_subset_fine (by simpa using hi'), hiParent⟩
  · intro i hiFiber hiNot
    have hiNotIndices : i ∉ A.refinement.indices := by
      intro hiIndices
      apply hiNot
      exact (actualRefinementSurvivingFactorization A).index.mem_fiber i k |>.2
        ⟨by simpa using hiIndices,
          (P.index.mem_fiber i k).1 hiFiber |>.2⟩
    rw [A.refinement.carrier_eq_empty_of_not_mem i hiNotIndices,
      measure_empty]

/-- A pointwise lower bound for every surviving body sums to the literal
surviving-fibre cardinality times that lower bound. -/
theorem survivingFiber_card_mul_le_familyVolume
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) (area : ENNReal)
    (harea : ∀ i ∈ A.refinement.indices,
      area ≤ volume (F i : Set Space)) :
    ((actualRefinementSurvivingFiberIndices A k).card : ENNReal) * area ≤
      familyVolume (actualRefinementSurvivingFiberFamily A k) := by
  rw [actualRefinementSurvivingFiberFamily, selectedCoarseFamily_volume]
  calc
    ((actualRefinementSurvivingFiberIndices A k).card : ENNReal) * area =
        ∑ _i ∈ actualRefinementSurvivingFiberIndices A k, area := by simp
    _ ≤ ∑ i ∈ actualRefinementSurvivingFiberIndices A k,
        volume (F i : Set Space) := by
      apply Finset.sum_le_sum
      intro i hi
      apply harea i
      exact (actualRefinementSurvivingFactorization A).index.fiber_subset_fine
        k hi

/-- Exact weighted averaging on the final surviving indices.  The selected
old parent is density-good, its literal surviving fibre has positive mass,
and that same parent supplies the second factor in the assembly product. -/
theorem exists_actualRefinementSurvivingFiber_dense_sameAssemblyProduct
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (area : ENNReal) (harea0 : area ≠ 0)
    (harea : ∀ i ∈ A.refinement.indices,
      area ≤ volume (F i : Set Space))
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      (actualRefinementShading A).shadingDensity ≤
        (actualRefinementSurvivingFiberShading A k).shadingDensity ∧
      ((actualRefinementSurvivingFiberIndices A k).card : ENNReal) * area ≤
        familyVolume (actualRefinementSurvivingFiberFamily A k) ∧
      (actualRefinementSurvivingFiberShading A k).shadingMass =
        (finalFiberShading A k).shadingMass ∧
      0 < volume (finalFiberShading A k).shadedUnion ∧
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) := by
  classical
  let Q := actualRefinementSurvivingFactorization A
  let Z := A.refinement.shading
  let lambda := (actualRefinementShading A).shadingDensity
  have hrefinementMass : A.refinement.shading.shadingMass ≠ 0 :=
    refinement_shadingMass_ne_zero A hsource
  have hactualMass : (actualRefinementShading A).shadingMass ≠ 0 := by
    rw [actualRefinementShading_shadingMass]
    exact hrefinementMass
  have hindices : A.refinement.indices.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    apply hrefinementMass
    unfold Shading.shadingMass
    apply Finset.sum_eq_zero
    intro i _hi
    rw [A.refinement.carrier_eq_empty_of_not_mem i (by simp [hnot]),
      measure_empty]
  have hcoarse : Q.index.coarse.Nonempty := by
    obtain ⟨i, hi⟩ := hindices
    refine ⟨P.index.parent i, ?_⟩
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hbody : activeBodyMass Q =
      familyVolume (actualRefinementFamily A) := by
    simpa only [Q] using
      surviving_activeBodyMass_eq_actualRefinementFamilyVolume A
  have hmass : activeShadingMass Q Z =
      (actualRefinementShading A).shadingMass := by
    simpa only [Q, Z] using
      surviving_activeShadingMass_eq_actualRefinementShadingMass A
  have hglobal : lambda * activeBodyMass Q = activeShadingMass Q Z := by
    rw [hbody, hmass]
    exact
      InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume
        (actualRefinementShading A)
  have hsum :
      (∑ k ∈ Q.index.coarse, lambda * fiberBodyMass Q k) ≤
        ∑ k ∈ Q.index.coarse,
          HeavyParentSelection.fiberShadingMass Q Z k := by
    calc
      (∑ k ∈ Q.index.coarse, lambda * fiberBodyMass Q k) =
          lambda * ∑ k ∈ Q.index.coarse, fiberBodyMass Q k := by
        rw [Finset.mul_sum]
      _ = lambda * activeBodyMass Q := by
        rw [activeBodyMass_eq_sum_fiberBodyMass]
      _ = activeShadingMass Q Z := hglobal
      _ ≤ ∑ k ∈ Q.index.coarse,
          HeavyParentSelection.fiberShadingMass Q Z k :=
        (HeavyParentSelection.activeShadingMass_eq_sum_fiberShadingMass
          Q Z).le
  obtain ⟨k, hkQ, hkDense⟩ := ENNReal.exists_le_of_sum_le hcoarse hsum
  have hkP : k ∈ P.index.coarse := by
    change k ∈ A.refinement.indices.image P.index.parent at hkQ
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkQ
    rw [← hik]
    exact P.index.parent_mem i (A.indices_subset_fine hi)
  have hkFiberNonempty :
      (actualRefinementSurvivingFiberIndices A k).Nonempty := by
    change Q.index.fiber k |>.Nonempty
    change k ∈ A.refinement.indices.image P.index.parent at hkQ
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkQ
    refine ⟨i, Q.index.mem_fiber i k |>.2 ?_⟩
    have hiQ : i ∈ Q.index.fine := by
      change i ∈ A.refinement.indices
      exact hi
    exact ⟨hiQ, hik⟩
  have hcardPos : 0 < (actualRefinementSurvivingFiberIndices A k).card :=
    Finset.card_pos.mpr hkFiberNonempty
  have hcardArea := survivingFiber_card_mul_le_familyVolume A k area harea
  have hfiberVolumePos :
      0 < familyVolume (actualRefinementSurvivingFiberFamily A k) := by
    have hleft : 0 <
        ((actualRefinementSurvivingFiberIndices A k).card : ENNReal) * area :=
      ENNReal.mul_pos (by exact_mod_cast hcardPos.ne') harea0
    exact hleft.trans_le hcardArea
  have hfiberBody : fiberBodyMass Q k =
      familyVolume (actualRefinementSurvivingFiberFamily A k) := by
    simpa only [Q] using surviving_fiberBodyMass_eq_familyVolume A k
  have hfiberMass : HeavyParentSelection.fiberShadingMass Q Z k =
      (actualRefinementSurvivingFiberShading A k).shadingMass := by
    simpa only [Q, Z] using surviving_fiberShadingMass_eq_shadingMass A k
  have hdense : lambda ≤
      (actualRefinementSurvivingFiberShading A k).shadingDensity := by
    unfold Shading.shadingDensity
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hfiberVolumePos.ne')
      (Or.inl (familyVolume_ne_top
        (actualRefinementSurvivingFiberFamily A k)))).2
    rw [← hfiberBody, ← hfiberMass]
    exact hkDense
  have hlambdaPos : 0 < lambda := by
    dsimp only [lambda]
    unfold Shading.shadingDensity
    exact ENNReal.div_pos hactualMass
      (familyVolume_ne_top (actualRefinementFamily A))
  have hfiberDensityPos :
      0 < (actualRefinementSurvivingFiberShading A k).shadingDensity :=
    hlambdaPos.trans_le hdense
  have hfiberMass0 :
      (actualRefinementSurvivingFiberShading A k).shadingMass ≠ 0 := by
    unfold Shading.shadingDensity at hfiberDensityPos
    exact (ENNReal.div_pos_iff.mp hfiberDensityPos).1
  have hmassEq :=
    actualRefinementSurvivingFiberShading_shadingMass_eq_finalFiberShading A k
  have hfinalMass0 : (finalFiberShading A k).shadingMass ≠ 0 := by
    rw [← hmassEq]
    exact hfiberMass0
  have hfinalVolume : 0 < volume (finalFiberShading A k).shadedUnion :=
    bot_lt_iff_ne_bot.mpr
      (volume_shadedUnion_ne_zero_of_shadingMass_ne_zero
        (finalFiberShading A k) hfinalMass0)
  obtain ⟨_oldK, _holdK, _holdFiber, _hrefinementVolume, houterVolume⟩ :=
    exists_positive_finalFiber A hsource
  have hproduct := refinement_averageMultiplicity_le_four_mul_actualAverages
    A k hkP (ne_of_gt hfinalVolume) (ne_of_gt houterVolume)
  refine ⟨k, hkP, ?_, hcardArea, hmassEq, hfinalVolume, ?_⟩
  · simpa only [lambda] using hdense
  · rw [actualRefinementShading_averageMultiplicity]
    exact hproduct

#print axioms actualRefinementSurvivingFactorization
#print axioms
  actualRefinementSurvivingFiberShading_shadingMass_eq_finalFiberShading
#print axioms survivingFiber_card_mul_le_familyVolume
#print axioms exists_actualRefinementSurvivingFiber_dense_sameAssemblyProduct

end
end Family8ActualRefinementSurvivingDenseFiberV1
