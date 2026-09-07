import Family8Grounding.Family8CanonicalExactAssemblySameDataFiberV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

/-!
# Actual mass and density retention for the canonical exact assembly

An indexed refinement still uses the ambient index type, so its ordinary
`shadingDensity` has the ambient family volume as denominator.  The paper's
refined family is instead the literal subtype of surviving indices.  Here we
construct that family and shading, prove exact mass and union identities, and
transport the assembly's automatic mass retention to a genuine density lower
bound.  No density comparison is supplied as data.

The subtype family evaluates to the same source convex bodies.  Thus every
body-level property (in particular any externally known common tube scale) is
preserved definitionally; the abstract `ConvexFactorization` itself contains
no numeric scale parameter.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalExactAssemblyMassDensityRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8ExactAssemblySameDataFiberBridgeV1
open Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly
open Family8CanonicalExactAssemblySameDataFiberV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : Nat}

/-- The literal source active-fine family, reindexed by its finite subtype. -/
def sourceActiveFineFamily (P : ConvexFactorization F W) :
    ConvexFamily {i // i ∈ P.index.fine} :=
  selectedCoarseFamily F P.index.fine

/-- The source shading on the literal active-fine subtype. -/
def sourceActiveFineShading (P : ConvexFactorization F W) (Y : Shading F) :
    Shading (sourceActiveFineFamily P) :=
  selectedCoarseShading Y P.index.fine

/-- The literal family of indices retained by an exact assembly. -/
def actualRefinementFamily
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    ConvexFamily {i // i ∈ A.refinement.indices} :=
  selectedCoarseFamily F A.refinement.indices

/-- The final refinement shading on its literal surviving-index subtype. -/
def actualRefinementShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    Shading (actualRefinementFamily A) :=
  selectedCoarseShading A.refinement.shading A.refinement.indices

/-- Inclusion of the literal final index family into the source active-fine
family, derived from `ExactAssembly.indices_subset_fine`. -/
def actualRefinementToSourceActiveFine
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    {i // i ∈ A.refinement.indices} ↪ {i // i ∈ P.index.fine} where
  toFun i := ⟨i.1, A.indices_subset_fine i.2⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun z : {i // i ∈ P.index.fine} => z.1) hij

@[simp] theorem sourceActiveFineFamily_apply
    (P : ConvexFactorization F W) (i : {i // i ∈ P.index.fine}) :
    sourceActiveFineFamily P i = F i.1 := rfl

@[simp] theorem sourceActiveFineShading_carrier
    (P : ConvexFactorization F W) (Y : Shading F)
    (i : {i // i ∈ P.index.fine}) :
    (sourceActiveFineShading P Y).carrier i = Y.carrier i.1 := rfl

@[simp] theorem actualRefinementFamily_apply
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (i : {i // i ∈ A.refinement.indices}) :
    actualRefinementFamily A i = F i.1 := rfl

@[simp] theorem actualRefinementShading_carrier
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (i : {i // i ∈ A.refinement.indices}) :
    (actualRefinementShading A).carrier i =
      A.refinement.shading.carrier i.1 := rfl

/-- The final subtype family uses exactly the same convex body as its image in
the source active family.  This is the available definition-level scale
preservation statement in the scale-free factorization API. -/
theorem actualRefinementFamily_eq_sourceActiveFineFamily_on_embedding
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss)
    (i : {i // i ∈ A.refinement.indices}) :
    actualRefinementFamily A i =
      sourceActiveFineFamily P (actualRefinementToSourceActiveFine A i) := rfl

/-- The literal active-fine shading mass is exactly the mass appearing on the
source side of `ExactAssembly.retained`. -/
theorem sourceActiveFineShading_shadingMass
    (P : ConvexFactorization F W) (Y : Shading F) :
    (sourceActiveFineShading P Y).shadingMass =
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass := by
  unfold sourceActiveFineShading sourceActiveFineFamily
  rw [selectedCoarseShading_mass, shadingMass_restrictTo_eq_sum]

/-- Reindexing the supported final refinement by its literal index subtype
does not change its total shaded mass. -/
theorem actualRefinementShading_shadingMass
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (actualRefinementShading A).shadingMass =
      A.refinement.shading.shadingMass := by
  unfold actualRefinementShading actualRefinementFamily
  rw [selectedCoarseShading_mass]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hni
  rw [A.refinement.carrier_eq_empty_of_not_mem i hni, measure_empty]

/-- The literal final subtype shading has exactly the same shaded union as the
ambient-index refinement, since every carrier outside the retained index set
is empty. -/
theorem actualRefinementShading_shadedUnion
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (actualRefinementShading A).shadedUnion =
      A.refinement.shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i.1, hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hi : i ∈ A.refinement.indices := by
      by_contra hni
      rw [A.refinement.carrier_eq_empty_of_not_mem i hni] at hxi
      exact hxi
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩

/-- Consequently, the actual subtype refinement has exactly the same average
multiplicity as the ambient-index representation used by `ExactAssembly`. -/
theorem actualRefinementShading_averageMultiplicity
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (actualRefinementShading A).averageMultiplicity =
      A.refinement.shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [actualRefinementShading_shadingMass,
    actualRefinementShading_shadedUnion]

/-- The final literal family-volume denominator is no larger than the source
active-fine denominator, purely because the final indices form a subset. -/
theorem actualRefinementFamily_volume_le_sourceActiveFineFamily
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    familyVolume (actualRefinementFamily A) ≤
      familyVolume (sourceActiveFineFamily P) := by
  unfold actualRefinementFamily sourceActiveFineFamily
  rw [selectedCoarseFamily_volume, selectedCoarseFamily_volume]
  exact Finset.sum_le_sum_of_subset A.indices_subset_fine

/-- The assembly's stored retention statement is an actual mass comparison
between the two literal subtype shadings. -/
theorem sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (sourceActiveFineShading P Y).shadingMass ≤
      (loss : ENNReal) * (actualRefinementShading A).shadingMass := by
  rw [sourceActiveFineShading_shadingMass,
    actualRefinementShading_shadingMass]
  simpa only [WithinFactor, nsmul_eq_mul] using A.retained

/-- The automatic mass retention and the automatic subtype-denominator
monotonicity imply genuine density retention with precisely the assembly loss.
This statement is total: no nonzero-volume side condition is required. -/
theorem sourceActiveFineShading_density_div_loss_le_actualRefinementShading
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (sourceActiveFineShading P Y).shadingDensity / (loss : ENNReal) ≤
      (actualRefinementShading A).shadingDensity := by
  let source := sourceActiveFineShading P Y
  let target := actualRefinementShading A
  have hfamily : familyVolume (actualRefinementFamily A) ≤
      familyVolume (sourceActiveFineFamily P) :=
    actualRefinementFamily_volume_le_sourceActiveFineFamily A
  have hmass : source.shadingMass ≤
      (loss : ENNReal) * target.shadingMass := by
    simpa only [source, target] using
      sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
  have hdensity : source.shadingDensity ≤
      (loss : ENNReal) * target.shadingDensity := by
    by_cases hzero : familyVolume (sourceActiveFineFamily P) = 0
    · have hsourceMass : source.shadingMass = 0 :=
        nonpos_iff_eq_zero.mp
          (source.shadingMass_le_familyVolume.trans_eq hzero)
      simp [Shading.shadingDensity, source, hzero, hsourceMass]
    · rw [← ENNReal.mul_le_mul_iff_right hzero
        (familyVolume_ne_top (sourceActiveFineFamily P))]
      calc
        familyVolume (sourceActiveFineFamily P) * source.shadingDensity =
            source.shadingMass := by
          rw [mul_comm, shadingDensity_mul_familyVolume]
        _ ≤ (loss : ENNReal) * target.shadingMass := hmass
        _ = (loss : ENNReal) *
            (target.shadingDensity *
              familyVolume (actualRefinementFamily A)) := by
          rw [shadingDensity_mul_familyVolume]
        _ ≤ (loss : ENNReal) *
            (target.shadingDensity *
              familyVolume (sourceActiveFineFamily P)) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hfamily)
        _ = familyVolume (sourceActiveFineFamily P) *
            ((loss : ENNReal) * target.shadingDensity) := by ac_rfl
  exact ENNReal.div_le_of_le_mul' hdensity

end ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}

/-- The canonical saturated producer simultaneously supplies an actual
source-to-final mass comparison and the resulting actual density comparison.
Both are derived from its constructed refinement and literal index subtypes. -/
theorem exists_exactAssembly_with_sameDataFiber_mass_density_of_fiber_card_le
    (P : ConvexFactorization F W) (Y : Shading F) (M : Nat)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) :
    ∃ A : FactoringMultiplicityAssembly.ExactAssembly P Y
        (((M + 1) * (M + 1)) * (Fintype.card kappa + 1)),
      A.fineLevel ≤ M ∧
      A.outerLevel ≤ Fintype.card kappa ∧
      (∀ (k : kappa) (x : Space),
        x ∈ (finalFiberShading A k).shadedUnion →
          (finalFiberShading A k).pointMultiplicity x = A.fineLevel) ∧
      (ExactAssembly.sourceActiveFineShading P Y).shadingMass ≤
        ((((M + 1) * (M + 1)) * (Fintype.card kappa + 1) : Nat) : ENNReal) *
          (ExactAssembly.actualRefinementShading A).shadingMass ∧
      (ExactAssembly.sourceActiveFineShading P Y).shadingDensity /
          ((((M + 1) * (M + 1)) *
            (Fintype.card kappa + 1) : Nat) : ENNReal) ≤
        (ExactAssembly.actualRefinementShading A).shadingDensity := by
  obtain ⟨A, hfine, houter, hsaturation⟩ :=
    exists_exactAssembly_with_sameDataFiber_saturation_of_fiber_card_le
      P Y M hM
  exact ⟨A, hfine, houter, hsaturation,
    ExactAssembly.sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading
      A,
    ExactAssembly.sourceActiveFineShading_density_div_loss_le_actualRefinementShading
      A⟩

/-- With nonzero source active mass, the same canonical object also realizes
the two natural levels as actual averages on the same final data, while the
mass and density comparisons above remain available. -/
theorem exists_exactAssembly_with_actualAverages_mass_density_of_fiber_card_le
    (P : ConvexFactorization F W) (Y : Shading F) (M : Nat)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ A : FactoringMultiplicityAssembly.ExactAssembly P Y
        (((M + 1) * (M + 1)) * (Fintype.card kappa + 1)),
      A.fineLevel ≤ M ∧
      A.outerLevel ≤ Fintype.card kappa ∧
      (ExactAssembly.sourceActiveFineShading P Y).shadingDensity /
          ((((M + 1) * (M + 1)) *
            (Fintype.card kappa + 1) : Nat) : ENNReal) ≤
        (ExactAssembly.actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ P.index.coarse,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (finalFiberShading A k).averageMultiplicity =
          (A.fineLevel : ENNReal) ∧
        (P.inducedShading A.refinement.shading).averageMultiplicity =
          (A.outerLevel : ENNReal) ∧
        (ExactAssembly.actualRefinementShading A).averageMultiplicity ≤
          (P.inducedShading A.refinement.shading).averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity := by
  obtain ⟨A, hfine, houter, k, hk, hvolume, hfineAverage,
      houterAverage, hproduct⟩ :=
    exists_exactAssembly_with_sameDataFiber_actualAverage_product_of_fiber_card_le
      P Y M hM hsource
  have hdensity :=
    ExactAssembly.sourceActiveFineShading_density_div_loss_le_actualRefinementShading
      A
  have hactualProduct :
      (ExactAssembly.actualRefinementShading A).averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity := by
    rw [ExactAssembly.actualRefinementShading_averageMultiplicity]
    exact hproduct
  exact ⟨A, hfine, houter, hdensity, k, hk, hvolume,
    hfineAverage, houterAverage, hactualProduct⟩

#print axioms ExactAssembly.actualRefinementFamily_eq_sourceActiveFineFamily_on_embedding
#print axioms ExactAssembly.sourceActiveFineShading_shadingMass
#print axioms ExactAssembly.actualRefinementShading_shadingMass
#print axioms ExactAssembly.actualRefinementShading_shadedUnion
#print axioms ExactAssembly.actualRefinementShading_averageMultiplicity
#print axioms ExactAssembly.actualRefinementFamily_volume_le_sourceActiveFineFamily
#print axioms
  ExactAssembly.sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading
#print axioms
  ExactAssembly.sourceActiveFineShading_density_div_loss_le_actualRefinementShading
#print axioms
  exists_exactAssembly_with_sameDataFiber_mass_density_of_fiber_card_le
#print axioms
  exists_exactAssembly_with_actualAverages_mass_density_of_fiber_card_le

end


end Family8CanonicalExactAssemblyMassDensityRetentionV1
