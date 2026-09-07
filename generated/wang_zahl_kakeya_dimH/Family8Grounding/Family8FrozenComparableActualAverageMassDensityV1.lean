import Family8Grounding.Family8FrozenNeighborhoodAssemblyV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

/-!
# Polylogarithmic frozen assembly with actual averages, mass, and density

`Family8FrozenNeighborhoodAssemblyV1.exists_assembly` already performs the two honest
zero/dyadic pigeonholes required in the multiplicity step: first inside the
actual parent fibres, then on the independently frozen coarse cover.  Its
loss is

`(log₂ (# fine) + 2) * (log₂ (# coarse) + 2)`.

This file supplies the downstream data bridge.  The final fine family is the
literal subtype of surviving indices, its mass and union agree exactly with
the ambient-index refinement, and the automatic mass retention gives an
actual density lower bound.  If the source active mass is nonzero, one actual
surviving fibre has positive union volume.  Both that fibre and the frozen
coarse shading realize their dyadic bases as lower bounds for their actual
average multiplicities.  Hence the comparable pointwise product becomes a
product of actual averages with only the explicit constant `4`.

No scale bound, retention estimate, or target comparison is accepted as an
extra field or callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FrozenComparableActualAverageMassDensityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenNeighborhoodAssemblyV1
open Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The concrete two-level dyadic loss of the frozen assembly. -/
def frozenComparableLoss (iota kappa : Type*) [Fintype iota] [Fintype kappa] : Nat :=
  (Nat.log 2 (Fintype.card iota) + 2) *
    (Nat.log 2 (Fintype.card kappa) + 2)

namespace Assembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- The source active-fine family, as a literal finite subtype. -/
def sourceActiveFineFamily (P : ConvexFactorization F W) :
    ConvexFamily {i // i ∈ P.index.fine} :=
  selectedCoarseFamily F P.index.fine

/-- The source shading on the literal active-fine subtype. -/
def sourceActiveFineShading (P : ConvexFactorization F W) (Y : Shading F) :
    Shading (sourceActiveFineFamily P) :=
  selectedCoarseShading Y P.index.fine

/-- The literal family retained by a frozen comparable assembly. -/
def actualRefinementFamily (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    ConvexFamily {i // i ∈ A.refinement.indices} :=
  selectedCoarseFamily F A.refinement.indices

/-- The final shading on its literal surviving-index subtype. -/
def actualRefinementShading (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    Shading (actualRefinementFamily A) :=
  selectedCoarseShading A.refinement.shading A.refinement.indices

/-- Inclusion of the literal final family in the source active-fine family. -/
def actualRefinementToSourceActiveFine
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
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
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (i : {i // i ∈ A.refinement.indices}) :
    actualRefinementFamily A i = F i.1 := rfl

@[simp] theorem actualRefinementShading_carrier
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (i : {i // i ∈ A.refinement.indices}) :
    (actualRefinementShading A).carrier i =
      A.refinement.shading.carrier i.1 := rfl

theorem actualRefinementFamily_eq_sourceActiveFineFamily_on_embedding
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (i : {i // i ∈ A.refinement.indices}) :
    actualRefinementFamily A i =
      sourceActiveFineFamily P (actualRefinementToSourceActiveFine A i) := rfl

theorem sourceActiveFineShading_shadingMass
    (P : ConvexFactorization F W) (Y : Shading F) :
    (sourceActiveFineShading P Y).shadingMass =
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass := by
  unfold sourceActiveFineShading sourceActiveFineFamily
  rw [selectedCoarseShading_mass, shadingMass_restrictTo_eq_sum]

theorem actualRefinementShading_shadingMass
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (actualRefinementShading A).shadingMass =
      A.refinement.shading.shadingMass := by
  unfold actualRefinementShading actualRefinementFamily
  rw [selectedCoarseShading_mass]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hni
  rw [A.refinement.carrier_eq_empty_of_not_mem i hni, measure_empty]

theorem actualRefinementShading_shadedUnion
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
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

theorem actualRefinementShading_averageMultiplicity
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (actualRefinementShading A).averageMultiplicity =
      A.refinement.shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [actualRefinementShading_shadingMass,
    actualRefinementShading_shadedUnion]

theorem actualRefinementFamily_volume_le_sourceActiveFineFamily
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    familyVolume (actualRefinementFamily A) ≤
      familyVolume (sourceActiveFineFamily P) := by
  unfold actualRefinementFamily sourceActiveFineFamily
  rw [selectedCoarseFamily_volume, selectedCoarseFamily_volume]
  exact Finset.sum_le_sum_of_subset A.indices_subset_fine

theorem sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (sourceActiveFineShading P Y).shadingMass ≤
      (A.loss : ENNReal) * (actualRefinementShading A).shadingMass := by
  rw [sourceActiveFineShading_shadingMass,
    actualRefinementShading_shadingMass]
  simpa only [WithinFactor, nsmul_eq_mul] using A.retained

theorem sourceActiveFineShading_density_div_loss_le_actualRefinementShading
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (sourceActiveFineShading P Y).shadingDensity / (A.loss : ENNReal) ≤
      (actualRefinementShading A).shadingDensity := by
  let source := sourceActiveFineShading P Y
  let target := actualRefinementShading A
  have hfamily : familyVolume (actualRefinementFamily A) ≤
      familyVolume (sourceActiveFineFamily P) :=
    actualRefinementFamily_volume_le_sourceActiveFineFamily A
  have hmass : source.shadingMass ≤
      (A.loss : ENNReal) * target.shadingMass := by
    simpa only [source, target] using
      sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
  have hdensity : source.shadingDensity ≤
      (A.loss : ENNReal) * target.shadingDensity := by
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
        _ ≤ (A.loss : ENNReal) * target.shadingMass := hmass
        _ = (A.loss : ENNReal) *
            (target.shadingDensity *
              familyVolume (actualRefinementFamily A)) := by
          rw [shadingDensity_mul_familyVolume]
        _ ≤ (A.loss : ENNReal) *
            (target.shadingDensity *
              familyVolume (sourceActiveFineFamily P)) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hfamily)
        _ = familyVolume (sourceActiveFineFamily P) *
            ((A.loss : ENNReal) * target.shadingDensity) := by ac_rfl
  exact ENNReal.div_le_of_le_mul' hdensity

/-- The actual final shading restricted to one actual factorization fibre. -/
def finalFiberShading
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) (k : kappa) : Shading F :=
  fiberShading P A.refinement.shading k

@[simp] theorem finalFiberShading_pointMultiplicity
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) (x : Space) :
    (finalFiberShading A k).pointMultiplicity x =
      P.fiberMultiplicity A.refinement.shading k x := by
  exact fiberShading_pointMultiplicity P A.refinement.shading k x

theorem finalFiberShading_shadedUnion
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) (k : kappa) :
    (finalFiberShading A k).shadedUnion =
      P.fiberShadedUnion A.refinement.shading k := by
  exact fiberShading_shadedUnion_eq_fiberShadedUnion
    P A.refinement.shading k

/-- Integrating a pointwise lower multiplicity bound on the actual union. -/
theorem natCast_mul_volume_le_shadingMass_of_pointMultiplicity_lower
    {alpha : Type*} [Fintype alpha] {G : ConvexFamily alpha}
    (Z : Shading G) (n : Nat)
    (hpoint : ∀ x ∈ Z.shadedUnion, n ≤ Z.pointMultiplicity x) :
    (n : ENNReal) * volume Z.shadedUnion ≤ Z.shadingMass := by
  rw [← Z.lintegral_pointMultiplicity]
  calc
    (n : ENNReal) * volume Z.shadedUnion =
        ∫⁻ x, Z.shadedUnion.indicator (fun _ => (n : ENNReal)) x ∂volume := by
      rw [lintegral_indicator Z.shadedUnion_measurableSet]
      simp
    _ ≤ ∫⁻ x, (Z.pointMultiplicity x : ENNReal) ∂volume := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Z.shadedUnion
      · simp only [Set.indicator_of_mem hx]
        exact_mod_cast hpoint x hx
      · simp [hx]

/-- A pointwise lower multiplicity bound gives the same lower bound for the
actual average when the actual shaded union has positive volume. -/
theorem natCast_le_averageMultiplicity_of_pointMultiplicity_lower
    {alpha : Type*} [Fintype alpha] {G : ConvexFamily alpha}
    (Z : Shading G) (n : Nat)
    (hvolume : volume Z.shadedUnion ≠ 0)
    (hpoint : ∀ x ∈ Z.shadedUnion, n ≤ Z.pointMultiplicity x) :
    (n : ENNReal) ≤ Z.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hvolume) (Or.inl (Family8ExactAssemblyActualAverageBridgeV1.volume_shadedUnion_ne_top Z))).2
  exact natCast_mul_volume_le_shadingMass_of_pointMultiplicity_lower
    Z n hpoint

theorem finalFiberShading_pointMultiplicity_lower
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) (hk : k ∈ P.index.coarse)
    (x : Space) (hx : x ∈ (finalFiberShading A k).shadedUnion) :
    comparableBase A.fiberLabel ≤
      (finalFiberShading A k).pointMultiplicity x := by
  have hxFiber : x ∈ P.fiberShadedUnion A.refinement.shading k := by
    rwa [← finalFiberShading_shadedUnion A k]
  have hcomp := A.fiber_comparable k hk x hxFiber
  rw [finalFiberShading_pointMultiplicity]
  rcases hcomp with hzero | hpositive
  · have hpos : 0 < P.fiberMultiplicity A.refinement.shading k x := by
      rw [← finalFiberShading_pointMultiplicity A k x]
      exact ((finalFiberShading A k).pointMultiplicity_pos_iff_mem_shadedUnion x).2 hx
    omega
  · exact hpositive.2.1

theorem finalFiberShading_averageMultiplicity_lower
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) (hk : k ∈ P.index.coarse)
    (hvolume : volume (finalFiberShading A k).shadedUnion ≠ 0) :
    (comparableBase A.fiberLabel : ENNReal) ≤
      (finalFiberShading A k).averageMultiplicity := by
  exact natCast_le_averageMultiplicity_of_pointMultiplicity_lower
    (finalFiberShading A k) (comparableBase A.fiberLabel) hvolume
    (finalFiberShading_pointMultiplicity_lower A k hk)

theorem finalFiberShading_averageMultiplicity_upper
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) (hk : k ∈ P.index.coarse) :
    (finalFiberShading A k).averageMultiplicity ≤
      (2 * comparableBase A.fiberLabel : Nat) := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  simpa only [nsmul_eq_mul] using
    (FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
        (finalFiberShading A k) (2 * comparableBase A.fiberLabel)
        (fun x => by
          rw [finalFiberShading_pointMultiplicity]
          exact A.fiberMultiplicity_le_twice_base k hk x))

theorem frozenCoarse_pointMultiplicity_lower
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (x : Space) (hx : x ∈ A.frozenCoarse.shadedUnion) :
    comparableBase A.outerLabel ≤ A.frozenCoarse.pointMultiplicity x := by
  have hcomp := A.outer_comparable x hx
  rcases hcomp with hzero | hpositive
  · have hpos : 0 < A.frozenCoarse.pointMultiplicity x :=
      (A.frozenCoarse.pointMultiplicity_pos_iff_mem_shadedUnion x).2 hx
    omega
  · exact hpositive.2.1

theorem frozenCoarse_averageMultiplicity_lower
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (hvolume : volume A.frozenCoarse.shadedUnion ≠ 0) :
    (comparableBase A.outerLabel : ENNReal) ≤
      A.frozenCoarse.averageMultiplicity := by
  exact natCast_le_averageMultiplicity_of_pointMultiplicity_lower
    A.frozenCoarse (comparableBase A.outerLabel) hvolume
    (frozenCoarse_pointMultiplicity_lower A)

theorem frozenCoarse_averageMultiplicity_upper
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    A.frozenCoarse.averageMultiplicity ≤
      (2 * comparableBase A.outerLabel : Nat) := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  simpa only [nsmul_eq_mul] using
    (FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
        A.frozenCoarse (2 * comparableBase A.outerLabel)
        (fun x => by
          by_cases hx : x ∈ A.frozenCoarse.shadedUnion
          · exact (A.outer_comparable x hx).le_twice
          · have hzero : A.frozenCoarse.pointMultiplicity x = 0 := by
              apply Nat.eq_zero_of_not_pos
              intro hpos
              exact hx
                ((A.frozenCoarse.pointMultiplicity_pos_iff_mem_shadedUnion x).1 hpos)
            simp [hzero]))

theorem refinement_averageMultiplicity_le_comparableProduct
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    A.refinement.shading.averageMultiplicity ≤
      (((2 * comparableBase A.outerLabel) *
        (2 * comparableBase A.fiberLabel) : Nat) : ENNReal) := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  simpa only [nsmul_eq_mul] using A.shadingMass_le_comparableProduct_nsmul_volume

/-- Once one actual surviving fibre has positive volume, the comparable
pointwise product is bounded by four times the product of the actual frozen
coarse average and that actual same-data fibre average. -/
theorem refinement_averageMultiplicity_le_four_mul_actualAverages
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (k : kappa) (hk : k ∈ P.index.coarse)
    (hfiber : volume (finalFiberShading A k).shadedUnion ≠ 0)
    (houter : volume A.frozenCoarse.shadedUnion ≠ 0) :
    A.refinement.shading.averageMultiplicity ≤
      4 * (A.frozenCoarse.averageMultiplicity *
        (finalFiberShading A k).averageMultiplicity) := by
  have houterLower := frozenCoarse_averageMultiplicity_lower A houter
  have hfiberLower :=
    finalFiberShading_averageMultiplicity_lower A k hk hfiber
  calc
    A.refinement.shading.averageMultiplicity ≤
        (((2 * comparableBase A.outerLabel) *
          (2 * comparableBase A.fiberLabel) : Nat) : ENNReal) :=
      refinement_averageMultiplicity_le_comparableProduct A
    _ = 4 * ((comparableBase A.outerLabel : ENNReal) *
          (comparableBase A.fiberLabel : ENNReal)) := by
      push_cast
      ring
    _ ≤ 4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) := by
      exact mul_le_mul' le_rfl (mul_le_mul' houterLower hfiberLower)

theorem refinement_shadingMass_ne_zero
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    A.refinement.shading.shadingMass ≠ 0 := by
  intro hzero
  apply hsource
  apply le_antisymm
  · simpa only [WithinFactor, hzero, nsmul_zero] using A.retained
  · exact bot_le

/-- Positive source active mass yields one genuinely surviving positive
fibre; the final refinement union and its frozen coarse cover are therefore
also positive-volume actual objects. -/
theorem exists_positive_finalFiber
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ k ∈ P.index.coarse,
      0 < volume (finalFiberShading A k).shadedUnion ∧
      0 < volume A.refinement.shading.shadedUnion ∧
      0 < volume A.frozenCoarse.shadedUnion := by
  have href0 := refinement_shadingMass_ne_zero A hsource
  have hexists : ∃ i : iota,
      volume (A.refinement.shading.carrier i) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply href0
    unfold Shading.shadingMass
    simp only [h, Finset.sum_const_zero]
  obtain ⟨i, hiVolume⟩ := hexists
  have hiIndices : i ∈ A.refinement.indices := by
    by_contra hni
    rw [A.refinement.carrier_eq_empty_of_not_mem i hni, measure_empty] at hiVolume
    exact hiVolume rfl
  have hif : i ∈ P.index.fine := A.indices_subset_fine hiIndices
  let k : kappa := P.index.parent i
  have hk : k ∈ P.index.coarse := P.index.parent_mem i hif
  have hiFiber : i ∈ P.index.fiber k :=
    (P.index.mem_fiber i k).2 ⟨hif, rfl⟩
  have hsubsetFiber : A.refinement.shading.carrier i ⊆
      (finalFiberShading A k).shadedUnion := by
    intro x hx
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change x ∈ (fiberShading P A.refinement.shading k).carrier i
    rw [fiberShading_carrier, if_pos hiFiber]
    exact hx
  have hsubsetRefinement : (finalFiberShading A k).shadedUnion ⊆
      A.refinement.shading.shadedUnion := by
    intro x hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    change x ∈ (fiberShading P A.refinement.shading k).carrier j at hxj
    rw [fiberShading_carrier] at hxj
    by_cases hj : j ∈ P.index.fiber k
    · exact Set.mem_iUnion.mpr ⟨j, by simpa [hj] using hxj⟩
    · simp [hj] at hxj
  have hfiber0 : volume (finalFiberShading A k).shadedUnion ≠ 0 := by
    intro hzero
    apply hiVolume
    have hle : volume (A.refinement.shading.carrier i) ≤
        volume (finalFiberShading A k).shadedUnion := measure_mono hsubsetFiber
    rw [hzero] at hle
    exact le_antisymm hle bot_le
  have hrefVolume0 : volume A.refinement.shading.shadedUnion ≠ 0 := by
    intro hzero
    apply hfiber0
    have hle : volume (finalFiberShading A k).shadedUnion ≤
        volume A.refinement.shading.shadedUnion := measure_mono hsubsetRefinement
    rw [hzero] at hle
    exact le_antisymm hle bot_le
  have houter0 : volume A.frozenCoarse.shadedUnion ≠ 0 := by
    intro hzero
    apply hrefVolume0
    have hle : volume A.refinement.shading.shadedUnion ≤
        volume A.frozenCoarse.shadedUnion :=
      measure_mono A.shadedUnion_subset_frozenCoarse
    rw [hzero] at hle
    exact le_antisymm hle bot_le
  exact ⟨k, hk, bot_lt_iff_ne_bot.mpr hfiber0,
    bot_lt_iff_ne_bot.mpr hrefVolume0, bot_lt_iff_ne_bot.mpr houter0⟩

end Assembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}

/-- Canonical paper-facing producer: two genuine dyadic selections give a
polylogarithmic mass/density loss and, on the very same final data, actual
outer/fibre average bounds and the product estimate with constant `4`. -/
theorem exists_frozenComparableAssembly_with_actualAverages_mass_density
    (P : ConvexFactorization F W) (Y : Shading F)
    (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r,
      A.loss = frozenComparableLoss iota kappa ∧
      A.fiberLabel ∈ Finset.range (Nat.log 2 (Fintype.card iota) + 2) ∧
      A.outerLabel ∈ Finset.range (Nat.log 2 (Fintype.card kappa) + 2) ∧
      (Assembly.sourceActiveFineShading P Y).shadingMass ≤
        (frozenComparableLoss iota kappa : ENNReal) *
          (Assembly.actualRefinementShading A).shadingMass ∧
      (Assembly.sourceActiveFineShading P Y).shadingDensity /
          (frozenComparableLoss iota kappa : ENNReal) ≤
        (Assembly.actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ P.index.coarse,
        0 < volume (Assembly.finalFiberShading A k).shadedUnion ∧
        (comparableBase A.fiberLabel : ENNReal) ≤
          (Assembly.finalFiberShading A k).averageMultiplicity ∧
        (Assembly.finalFiberShading A k).averageMultiplicity ≤
          (2 * comparableBase A.fiberLabel : Nat) ∧
        (comparableBase A.outerLabel : ENNReal) ≤
          A.frozenCoarse.averageMultiplicity ∧
        A.frozenCoarse.averageMultiplicity ≤
          (2 * comparableBase A.outerLabel : Nat) ∧
        (Assembly.actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (Assembly.finalFiberShading A k).averageMultiplicity) := by
  obtain ⟨A, hLoss, hFiberLabel, hOuterLabel⟩ :=
    Family8FrozenNeighborhoodAssemblyV1.exists_assembly P Y r hr
  have hmass :=
    Assembly.sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
  have hdensity :=
    Assembly.sourceActiveFineShading_density_div_loss_le_actualRefinementShading A
  obtain ⟨k, hk, hfiber, _hrefinement, houter⟩ :=
    Assembly.exists_positive_finalFiber A hsource
  have hfiberLower :=
    Assembly.finalFiberShading_averageMultiplicity_lower A k hk (ne_of_gt hfiber)
  have hfiberUpper :=
    Assembly.finalFiberShading_averageMultiplicity_upper A k hk
  have houterLower :=
    Assembly.frozenCoarse_averageMultiplicity_lower A (ne_of_gt houter)
  have houterUpper := Assembly.frozenCoarse_averageMultiplicity_upper A
  have hproduct :=
    Assembly.refinement_averageMultiplicity_le_four_mul_actualAverages
      A k hk (ne_of_gt hfiber) (ne_of_gt houter)
  have hactualProduct :
      (Assembly.actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (Assembly.finalFiberShading A k).averageMultiplicity) := by
    rw [Assembly.actualRefinementShading_averageMultiplicity]
    exact hproduct
  refine ⟨A, ?_, hFiberLabel, hOuterLabel, ?_, ?_, k, hk, hfiber,
    hfiberLower, hfiberUpper, houterLower, houterUpper, hactualProduct⟩
  · simpa only [frozenComparableLoss] using hLoss
  · simpa only [hLoss, frozenComparableLoss] using hmass
  · simpa only [hLoss, frozenComparableLoss] using hdensity

#print axioms Assembly.actualRefinementFamily_eq_sourceActiveFineFamily_on_embedding
#print axioms Assembly.sourceActiveFineShading_shadingMass
#print axioms Assembly.actualRefinementShading_shadingMass
#print axioms Assembly.actualRefinementShading_shadedUnion
#print axioms Assembly.actualRefinementShading_averageMultiplicity
#print axioms Assembly.actualRefinementFamily_volume_le_sourceActiveFineFamily
#print axioms Assembly.sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading
#print axioms Assembly.sourceActiveFineShading_density_div_loss_le_actualRefinementShading
#print axioms Assembly.natCast_mul_volume_le_shadingMass_of_pointMultiplicity_lower
#print axioms Assembly.finalFiberShading_averageMultiplicity_lower
#print axioms Assembly.finalFiberShading_averageMultiplicity_upper
#print axioms Assembly.frozenCoarse_averageMultiplicity_lower
#print axioms Assembly.frozenCoarse_averageMultiplicity_upper
#print axioms Assembly.refinement_averageMultiplicity_le_four_mul_actualAverages
#print axioms Assembly.exists_positive_finalFiber
#print axioms exists_frozenComparableAssembly_with_actualAverages_mass_density

end

end Family8FrozenComparableActualAverageMassDensityV1
