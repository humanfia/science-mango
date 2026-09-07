import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Submission.Kakeya.ConvexFactoring.CertifiedSlabDyadicCordoba

/-!
# Two actual certified-slab Córdoba bounds in an exact factoring assembly

This file applies the proved certified-slab dyadic Córdoba theorem to the
two genuine shadings exposed by an exact factoring assembly.  The outer
object is the induced coarse shading of the final refinement.  The inner
object is a positive surviving source fine-level fibre shading.

The certificate below contains only the geometric inputs of the Córdoba
argument: slab frames, an actual sine-level assignment, containing bodies,
Katz--Tao nonconcentration, and the container-scale inequality.  It has no
field asserting an average-multiplicity conclusion.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ExactAssemblyCertifiedSlabCordobaCompositionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.CertifiedSlabDyadicCordoba
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-- All actual geometric data needed by the certified-slab dyadic Córdoba
estimate for one shaded convex family.  In particular, the desired
multiplicity inequality is not a field. -/
structure CertifiedSlabCordobaData
    {alpha : Type*} (levelIndex : Type*) [Fintype alpha]
    [Fintype levelIndex] [DecidableEq levelIndex]
    (F : ConvexFamily alpha) (Y : Shading F) where
  comparisonConstant : NNReal
  slabWidth : NNReal
  cert : ∀ i, SlabDimensionsCertificate comparisonConstant slabWidth (F i)
  levels : Finset levelIndex
  level : alpha → alpha → Option levelIndex
  inverseSineWeight : levelIndex → ENNReal
  container : alpha → Option levelIndex → ConvexBody Space
  katzTaoConstant : ENNReal
  rowScale : ENNReal
  level_mem : ∀ i j, level i j ∈ slabAngleLevels levels
  transverse : ∀ i j k, level i j = some k →
    0 < certifiedSlabPairSine cert i j
  inverseSine_le : ∀ i j k, level i j = some k →
    ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
      inverseSineWeight k
  contained : ∀ i j,
    (F j : Set Space) ⊆ (container i (level i j) : Set Space)
  katzTao : IsKatzTao katzTaoConstant F
  scale : ∀ i k, k ∈ slabAngleLevels levels →
    certifiedSlabAngleScale comparisonConstant slabWidth
        inverseSineWeight k * volume (container i k : Set Space) ≤
      rowScale * volume (Y.carrier i)

namespace CertifiedSlabCordobaData

variable {alpha levelIndex : Type*} [Fintype alpha]
  [Fintype levelIndex] [DecidableEq levelIndex]
  {F : ConvexFamily alpha} {Y : Shading F}

/-- The explicit factor produced by the genuine certified-slab theorem. -/
def factor (Q : CertifiedSlabCordobaData levelIndex F Y) : ENNReal :=
  certifiedSlabDyadicFactor Q.levels Q.katzTaoConstant Q.rowScale

/-- Apply the analytic theorem to the stored geometric data. -/
theorem averageMultiplicity_le
    (Q : CertifiedSlabCordobaData levelIndex F Y) :
    Y.averageMultiplicity ≤ Q.factor := by
  exact certifiedSlabDyadic_averageMultiplicity_le
    Q.cert Q.levels Q.level Q.inverseSineWeight Q.container
    Q.katzTaoConstant Q.rowScale Q.level_mem Q.transverse
    Q.inverseSine_le Q.contained Q.katzTao Q.scale

end CertifiedSlabCordobaData

namespace ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : Nat}

/-- The two analytic Lemma 6.4 applications, composed on the actual shadings
of an exact assembly.  Positive source mass chooses a genuine surviving
inner fibre; the two multiplicity estimates themselves are derived from
certified slab geometry by `certifiedSlabDyadic_averageMultiplicity_le`.

What remains after this theorem is to construct the displayed geometric
data with the paper's parameter choices and compare the two explicit
Córdoba factors with Equations (45) and (46). -/
theorem refinement_averageMultiplicity_le_product_certifiedSlabFactors
    {outerLevelIndex innerLevelIndex : Type*}
    [Fintype outerLevelIndex] [DecidableEq outerLevelIndex]
    [Fintype innerLevelIndex] [DecidableEq innerLevelIndex]
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0)
    (outer : CertifiedSlabCordobaData outerLevelIndex W
      (P.inducedShading A.refinement.shading))
    (inner : ∀ k, k ∈ P.index.coarse →
      CertifiedSlabCordobaData innerLevelIndex F
        (sourceFineLevelShading A k)) :
    ∃ k, ∃ hk : k ∈ P.index.coarse,
      0 < volume (sourceFineLevelShading A k).shadedUnion ∧
      A.refinement.shading.averageMultiplicity ≤
        outer.factor * (inner k hk).factor := by
  obtain ⟨k, hk, hvolume, hproduct⟩ :=
    refinement_averageMultiplicity_le_product_actualAverages A hsource
  refine ⟨k, hk, hvolume, ?_⟩
  calc
    A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A k).averageMultiplicity := hproduct
    _ ≤ outer.factor * (inner k hk).factor := by
      exact mul_le_mul' outer.averageMultiplicity_le
        (inner k hk).averageMultiplicity_le

end ExactAssembly

#print axioms CertifiedSlabCordobaData.averageMultiplicity_le
#print axioms
  ExactAssembly.refinement_averageMultiplicity_le_product_certifiedSlabFactors

end

end Family8ExactAssemblyCertifiedSlabCordobaCompositionV3
