import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8Prop66AActualAverageCompositionV4

/-!
# Proposition 6.6(A) directly on the polylogarithmic frozen assembly

The frozen comparable construction already puts the final fine shading, one
surviving source fibre, and the independently frozen coarse shading on the
same data.  Its pointwise comparison gives the actual-average product with
the explicit constant four.  This file composes that genuine product with
the two visible Lemma 6.4 bounds and the existing Proposition 6.6(A) scalar
identity.  It therefore avoids converting the frozen assembly into the
different exact-level assembly interface.

Neither the outer nor the inner geometric estimate is asserted here.  They
remain ordinary theorem arguments about the literal frozen shadings.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FrozenProp66AActualAverageCompositionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1

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

/-- A fixed positive frozen fibre and the actual frozen outer shading feed
directly into Proposition 6.6(A), with only the proved constant four from
the two comparable multiplicity buckets. -/
theorem actualRefinement_averageMultiplicity_le_four_mul_gain_mul_actualFrostmanRHS
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P D.shading r)
    (k : kappa) (hk : k ∈ P.index.coarse)
    (hfiber :
      volume (Assembly.finalFiberShading A k).shadedUnion ≠ 0)
    (houterVolume : volume A.frozenCoarse.shadedUnion ≠ 0)
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hD : D.IsAdmissible) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : Fintype.card iota = plankCount * tubesPerPlank)
    (houter : A.frozenCoarse.averageMultiplicity ≤
      proposition66AOuterFactor delta a b plankCount CF epsilon beta)
    (hinner : (Assembly.finalFiberShading A k).averageMultiplicity ≤
      proposition66AInnerFactor delta a b tubesPerPlank epsilon beta) :
    (Assembly.actualRefinementShading A).averageMultiplicity ≤
      4 * ((proposition66AFrostmanAspectGain a b CF beta *
          (2 : ENNReal) ^ (1 - beta / 2)) *
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta) := by
  have hproduct :
      (Assembly.actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (Assembly.finalFiberShading A k).averageMultiplicity) := by
    rw [Assembly.actualRefinementShading_averageMultiplicity]
    exact Assembly.refinement_averageMultiplicity_le_four_mul_actualAverages
      A k hk hfiber houterVolume
  have hfactor :
      proposition66AOuterFactor delta a b plankCount CF epsilon beta *
          proposition66AInnerFactor delta a b tubesPerPlank epsilon beta =
        proposition66AFrostmanFactor delta a b (Fintype.card iota)
          CF epsilon beta :=
    proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
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
    _ = 4 * proposition66AFrostmanFactor delta a b (Fintype.card iota)
          CF epsilon beta := by rw [hfactor]
    _ ≤ 4 * ((proposition66AFrostmanAspectGain a b CF beta *
          (2 : ENNReal) ^ (1 - beta / 2)) *
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta) :=
      mul_le_mul' le_rfl hactual

/-- Nonzero source active mass automatically supplies the positive frozen
fibre and outer union needed above.  Thus only the genuine outer and inner
Lemma 6.4 estimates remain, now on the exact objects returned by the
polylogarithmic producer. -/
theorem exists_survivingFiber_actualRefinement_le_four_mul_gain_mul_actualFrostmanRHS
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P D.shading r)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        P.index.fine).shading.shadingMass ≠ 0)
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hD : D.IsAdmissible) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : Fintype.card iota = plankCount * tubesPerPlank)
    (houter : A.frozenCoarse.averageMultiplicity ≤
      proposition66AOuterFactor delta a b plankCount CF epsilon beta)
    (hinner : ∀ k, k ∈ P.index.coarse →
      (Assembly.finalFiberShading A k).averageMultiplicity ≤
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta) :
    ∃ k ∈ P.index.coarse,
      0 < volume (Assembly.finalFiberShading A k).shadedUnion ∧
      (Assembly.actualRefinementShading A).averageMultiplicity ≤
        4 * ((proposition66AFrostmanAspectGain a b CF beta *
            (2 : ENNReal) ^ (1 - beta / 2)) *
          frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta) := by
  obtain ⟨k, hk, hfiber, _hrefinement, houterVolume⟩ :=
    Assembly.exists_positive_finalFiber A hsource
  refine ⟨k, hk, hfiber, ?_⟩
  exact actualRefinement_averageMultiplicity_le_four_mul_gain_mul_actualFrostmanRHS
    A k hk (ne_of_gt hfiber) (ne_of_gt houterVolume)
      hD ha hb hbeta hbetaOne hcount houter (hinner k hk)

#print axioms
  actualRefinement_averageMultiplicity_le_four_mul_gain_mul_actualFrostmanRHS
#print axioms
  exists_survivingFiber_actualRefinement_le_four_mul_gain_mul_actualFrostmanRHS

end Assembly

end
end Family8FrozenProp66AActualAverageCompositionV1
