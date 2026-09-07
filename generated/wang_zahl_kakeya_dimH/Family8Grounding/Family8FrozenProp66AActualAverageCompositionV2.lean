import Family8Grounding.Family8FrozenProp66AActualAverageCompositionV1
import Family8Grounding.Family8Prop66AUniformCountLossAlgebraV3

/-!
# Frozen Proposition 6.6(A) with uniform-count loss, V2

This successor replaces V1's exact count identity by the comparison actually
provided by a dyadically uniform family:

`plankCount * tubesPerPlank <= countLoss * totalCount`.

The resulting coefficient is exactly `countLoss^(1-beta/2)`.  All shadings
remain the literal frozen outer object, one surviving actual fibre, and the
same retained actual refinement from the polylogarithmic assembly.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FrozenProp66AActualAverageCompositionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AUniformCountLossAlgebraV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true

namespace Assembly

variable {delta : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {W : ConvexFamily kappa}
  {D : ActualTubeDatum delta iota}
  {P : ConvexFactorization D.family.bodyFamily W} {r : Real}

/-- Actual frozen outer/fibre composition with the honest multiplicative
uniform-count loss. -/
theorem actualRefinement_averageMultiplicity_le_uniformCountLoss_mul_actualFrostmanRHS
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P D.shading r)
    (k : kappa) (hk : k ∈ P.index.coarse)
    (hfiber :
      volume (Assembly.finalFiberShading A k).shadedUnion ≠ 0)
    (houterVolume : volume A.frozenCoarse.shadedUnion ≠ 0)
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF countLoss : ENNReal} {epsilon beta : Real}
    (hD : D.IsAdmissible) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : (((plankCount * tubesPerPlank : Nat) : ENNReal)) ≤
      countLoss * (Fintype.card iota : ENNReal))
    (houter : A.frozenCoarse.averageMultiplicity ≤
      proposition66AOuterFactor delta a b plankCount CF epsilon beta)
    (hinner : (Assembly.finalFiberShading A k).averageMultiplicity ≤
      proposition66AInnerFactor delta a b tubesPerPlank epsilon beta) :
    (Assembly.actualRefinementShading A).averageMultiplicity ≤
      4 * (countLoss ^ (1 - beta / 2) *
        ((proposition66AFrostmanAspectGain a b CF beta *
            (2 : ENNReal) ^ (1 - beta / 2)) *
          frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta)) := by
  have hproduct :
      (Assembly.actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (Assembly.finalFiberShading A k).averageMultiplicity) := by
    rw [Assembly.actualRefinementShading_averageMultiplicity]
    exact Assembly.refinement_averageMultiplicity_le_four_mul_actualAverages
      A k hk hfiber houterVolume
  have hcounted :
      proposition66AOuterFactor delta a b plankCount CF epsilon beta *
          proposition66AInnerFactor delta a b tubesPerPlank epsilon beta ≤
        countLoss ^ (1 - beta / 2) *
          proposition66AFrostmanFactor delta a b (Fintype.card iota)
            CF epsilon beta :=
    proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
      hD.delta_pos ha hb hbeta hbetaOne hcount
  have hactual :
      proposition66AFrostmanFactor delta a b (Fintype.card iota)
          CF epsilon beta ≤
        (proposition66AFrostmanAspectGain a b CF beta *
          (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta :=
    proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
      D hD.delta_le_half (hbetaOne.trans (by norm_num))
  calc
    (Assembly.actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (Assembly.finalFiberShading A k).averageMultiplicity) := hproduct
    _ ≤ 4 *
        (proposition66AOuterFactor delta a b plankCount CF epsilon beta *
          proposition66AInnerFactor delta a b tubesPerPlank epsilon beta) := by
      exact mul_le_mul' le_rfl (mul_le_mul' houter hinner)
    _ ≤ 4 * (countLoss ^ (1 - beta / 2) *
        proposition66AFrostmanFactor delta a b (Fintype.card iota)
          CF epsilon beta) :=
      mul_le_mul' le_rfl hcounted
    _ ≤ 4 * (countLoss ^ (1 - beta / 2) *
        ((proposition66AFrostmanAspectGain a b CF beta *
            (2 : ENNReal) ^ (1 - beta / 2)) *
          frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hactual)

/-- Nonzero source mass automatically chooses the actual surviving fibre;
only the two genuine geometric bounds and uniform-count comparison remain. -/
theorem exists_survivingFiber_actualRefinement_le_uniformCountLoss_mul_actualFrostmanRHS
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P D.shading r)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        P.index.fine).shading.shadingMass ≠ 0)
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF countLoss : ENNReal} {epsilon beta : Real}
    (hD : D.IsAdmissible) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : (((plankCount * tubesPerPlank : Nat) : ENNReal)) ≤
      countLoss * (Fintype.card iota : ENNReal))
    (houter : A.frozenCoarse.averageMultiplicity ≤
      proposition66AOuterFactor delta a b plankCount CF epsilon beta)
    (hinner : ∀ k, k ∈ P.index.coarse →
      (Assembly.finalFiberShading A k).averageMultiplicity ≤
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta) :
    ∃ k ∈ P.index.coarse,
      0 < volume (Assembly.finalFiberShading A k).shadedUnion ∧
      (Assembly.actualRefinementShading A).averageMultiplicity ≤
        4 * (countLoss ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain a b CF beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta)) := by
  obtain ⟨k, hk, hfiber, _hrefinement, houterVolume⟩ :=
    Assembly.exists_positive_finalFiber A hsource
  refine ⟨k, hk, hfiber, ?_⟩
  exact actualRefinement_averageMultiplicity_le_uniformCountLoss_mul_actualFrostmanRHS
    A k hk (ne_of_gt hfiber) (ne_of_gt houterVolume)
      hD ha hb hbeta hbetaOne hcount houter (hinner k hk)

#print axioms
  actualRefinement_averageMultiplicity_le_uniformCountLoss_mul_actualFrostmanRHS
#print axioms
  exists_survivingFiber_actualRefinement_le_uniformCountLoss_mul_actualFrostmanRHS

end Assembly

end
end Family8FrozenProp66AActualAverageCompositionV2
