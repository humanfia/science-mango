import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1

/-!
# Proposition 6.6(A): compose the two actual Lemma 6.4 outputs, V2

The exact factoring assembly already bounds its final refinement average by
the product of the actual induced-coarse average and one positive actual
source-fibre average.  Separately, the scalar algebra identifies the product
of the paper's outer and inner Lemma 6.4 factors with the displayed
Proposition 6.6(A) Frostman factor.

This module joins precisely those two proved mechanical statements.  The two
analytic inequalities remain explicit theorem arguments: no geometric
estimate, angle/container construction, or multiplicity conclusion is put
in a structure field or asserted here.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Prop66AActualAverageCompositionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

namespace ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : Nat}

/-- Once the two actual shaded families exposed by an exact assembly satisfy
the paper's outer and inner Lemma 6.4 estimates, their already-proved product
bound is exactly the Proposition 6.6(A) Frostman factor.

The hypotheses `houter` and `hinner` are the transparent analytic outputs
still to be produced from certified plank geometry; this theorem does not
replace them by a conclusion-bearing data package. -/
theorem refinement_averageMultiplicity_le_proposition66AFrostmanFactor
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0)
    {delta a b : NNReal}
    {plankCount tubesPerPlank totalCount : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hcount : totalCount = plankCount * tubesPerPlank)
    (houter :
      (P.inducedShading A.refinement.shading).averageMultiplicity <=
        proposition66AOuterFactor delta a b plankCount CF epsilon beta)
    (hinner : forall k, k ∈ P.index.coarse ->
      (sourceFineLevelShading A k).averageMultiplicity <=
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta) :
    A.refinement.shading.averageMultiplicity <=
      proposition66AFrostmanFactor delta a b totalCount CF epsilon beta := by
  obtain ⟨k, hk, _hvolume, hproduct⟩ :=
    refinement_averageMultiplicity_le_product_actualAverages A hsource
  calc
    A.refinement.shading.averageMultiplicity <=
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A k).averageMultiplicity := hproduct
    _ <= proposition66AOuterFactor delta a b plankCount CF epsilon beta *
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta :=
      mul_le_mul' houter (hinner k hk)
    _ = proposition66AFrostmanFactor delta a b totalCount CF epsilon beta :=
      proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
        hdelta ha hb hbeta hbetaOne hcount

#print axioms
  refinement_averageMultiplicity_le_proposition66AFrostmanFactor

end ExactAssembly

end
end Family8Prop66AActualAverageCompositionV2
