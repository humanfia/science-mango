import Family8Grounding.Family8ZeroColorPolynomialJohnKatzTaoV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ZeroColorPolynomialJohnScaleContainedV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorPolynomialJohnKatzTaoV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8PolynomialJohnFrameBoxAllConvexV1
open Family8RestrictedActualDatumMassBridgeV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

/-!
# Polynomial John sampling before essential-distinct selection

The polynomial John catalogue argument uses positivity of the tube scale,
the half-scale bound, unit-ball containment, and source Katz--Tao
concentration.  It does not use pairwise essential distinctness of the
source tubes.  Recording that weaker interface lets the paper's generalized
Katz--Tao argument first sample an arbitrary concentrated coarse family and
only then run a fresh conflict-free selection on the sampled family.

V1 omitted two namespace opens and is not imported.
-/

/-- A single zero-colour sample has retained mass, the polynomial sampled
cardinality cap, and global Katz--Tao concentration without assuming that
the unsampled source family is already pairwise essentially distinct. -/
theorem exists_zeroColorActualDatum_polynomialJohn_isKatzTao_of_scale_contained
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hcontained : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (C : ENNReal) (k : Nat) [NeZero k]
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hCfinite : C ≠ ∞)
    (hCscale : C.toReal / (k : Real) ≤ 1) :
    ∃ omega : iota → Fin k,
      D.shading.shadingMass.toReal / (2 * (k : Real)) ≤
          (zeroColorActualDatum D k omega).shading.shadingMass.toReal ∧
        ((zeroColorSample k omega).card : Real) ≤
          polynomialJohnTailParameter delta k *
            averageZeroColorCardinalCap iota k ∧
        IsKatzTao
          ((ENNReal.ofReal (polynomialJohnTailParameter delta k)) *
            johnCatalogueVolumeConstant)
          (zeroColorActualDatum D k omega).family.bodyFamily := by
  classical
  obtain ⟨omega, hretained, hcard, htests⟩ :=
    exists_zeroColorActualDatum_polynomialJohnTests D
      hdelta (by simpa [div_eq_mul_inv] using hdeltaHalf)
      C k hsource hCfinite hCscale
  refine ⟨omega, hretained, hcard, ?_⟩
  have htail0 : 0 ≤ polynomialJohnTailParameter delta k :=
    zero_le_one.trans (one_le_polynomialJohnTailParameter delta k)
  have hcatalogue :
      ∀ q : CatalogueIndex delta hdelta,
        IsKatzTaoAt
          (ENNReal.ofReal (polynomialJohnTailParameter delta k))
          (tubeBodyFamily
            (zeroColorActualDatum D k omega).family.tubes)
          (representativeTestBody delta hdelta q) := by
    intro q
    have hreal :
        (containedMass (zeroColorActualDatum D k omega).family.bodyFamily
          (representativeTestBody delta hdelta q)).toReal ≤
        polynomialJohnTailParameter delta k *
          polynomialJohnTestCap hdelta q := by
      rw [zeroColorActualDatum_containedMass,
        containedMassOn_toReal_eq_sum_containedBodyRealWeight]
      simpa [zeroColorSampleRealWeight, polynomialJohnTestWeight] using
        htests q
    change containedMass
        (zeroColorActualDatum D k omega).family.bodyFamily
        (representativeTestBody delta hdelta q) ≤
      ENNReal.ofReal (polynomialJohnTailParameter delta k) *
        volume (representativeTestBody delta hdelta q : Set Space)
    apply (ENNReal.toReal_le_toReal
      (containedMass_lt_top _ _).ne
      (ENNReal.mul_ne_top (by simp)
        (representativeTestBody delta hdelta q).isCompact.measure_lt_top.ne)).mp
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal htail0,
      polynomialJohnTestCap] using hreal
  have hall :=
    isKatzTao_of_polynomialJohnCatalogue hdelta
      (zeroColorActualDatum D k omega).family.tubes
      (fun i => by
        change (D.family.tubes i.1).carrier ⊆ Metric.closedBall 0 1
        exact hcontained i.1)
      (ENNReal.ofReal (polynomialJohnTailParameter delta k))
      hcatalogue
  change IsKatzTao
    (ENNReal.ofReal (polynomialJohnTailParameter delta k) *
      johnCatalogueVolumeConstant)
    (tubeBodyFamily (zeroColorActualDatum D k omega).family.tubes)
  exact hall

#print axioms
  exists_zeroColorActualDatum_polynomialJohn_isKatzTao_of_scale_contained

end
end Family8ZeroColorPolynomialJohnScaleContainedV2
