import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV8
import Family8Grounding.Family8SharpKatzTaoOrGreedyHighConcentrationV1
import Mathlib.Tactic

/-!
# The selected Joint coarse shading as an actual Katz--Tao datum

An exact-uniform `CoarseTubePartition` already carries the literal coarse
shading induced by any fine shading.  This file restricts that actual coarse
datum to the partition's selected parent subtype.  Since the induced shading
is empty off those selected parents, this changes neither its mass, union,
nor average multiplicity.  Active `IsKatzTaoOn` control then becomes the
ordinary Katz--Tao hypothesis on precisely the datum to which
`KatzTaoAtParameters` is applied.

The endpoint deliberately retains the two genuine inputs not supplied by
JointTubeFactoring: admissibility of the selected coarse tubes and a density
floor for their induced shading.  V1--V6 are failed elaboration drafts and
are not imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8JointExactUniformCoarseKatzTaoAtParametersV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The full-index actual coarse datum with the partition's genuine induced
shading. -/
def jointInducedCoarseActualDatum
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) : ActualTubeDatum rho kappa where
  family := coarse
  shading := P.asConvexFactorization.inducedShading Y

/-- The exact selected-parent subtype of the induced coarse datum. -/
def jointSelectedCoarseActualDatum
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) :
    ActualTubeDatum rho {k // k ∈ P.coarseIndices} :=
  restrictActualTubeDatum (jointInducedCoarseActualDatum P Y) P.coarseIndices

@[simp] theorem jointInducedCoarseActualDatum_family
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) :
    (jointInducedCoarseActualDatum P Y).family = coarse := by
  rfl

@[simp] theorem jointInducedCoarseActualDatum_shading
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) :
    (jointInducedCoarseActualDatum P Y).shading =
      P.asConvexFactorization.inducedShading Y := by
  rfl

/-- Restriction to selected coarse indices preserves the exact induced
shading mass because every carrier outside `P.coarseIndices` is empty. -/
theorem jointSelectedCoarseActualDatum_shadingMass_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) :
    (jointSelectedCoarseActualDatum P Y).shading.shadingMass =
      (P.asConvexFactorization.inducedShading Y).shadingMass := by
  rw [jointSelectedCoarseActualDatum, restrictActualTubeDatum_shadingMass]
  unfold Shading.shadingMass
  change
    (∑ k ∈ P.coarseIndices,
      volume ((P.asConvexFactorization.inducedShading Y).carrier k)) =
        ∑ k, volume ((P.asConvexFactorization.inducedShading Y).carrier k)
  apply Finset.sum_subset (Finset.subset_univ P.coarseIndices)
  intro k _hkUniv hk
  have hk' : k ∉ P.asConvexFactorization.index.coarse := by
    simpa only [CoarseTubePartition.coarseIndices,
      CoarseTubePartition.asConvexFactorization] using hk
  have hempty :
      (P.asConvexFactorization.inducedShading Y).carrier k = ∅ := by
    ext x
    constructor
    · intro hx
      have hkMem :=
        (P.asConvexFactorization.mem_inducedShading_carrier_iff Y k x).mp hx
      exact (hk' hkMem.1).elim
    · intro hx
      exact hx.elim
  rw [hempty, measure_empty]

/-- The selected subtype has exactly the same shaded union as the full
induced coarse shading. -/
theorem jointSelectedCoarseActualDatum_shadedUnion_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) :
    (jointSelectedCoarseActualDatum P Y).shading.shadedUnion =
      (P.asConvexFactorization.inducedShading Y).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨k.1, hxk⟩
  · intro hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    have hk : k ∈ P.coarseIndices := by
      exact (P.asConvexFactorization.mem_inducedShading_carrier_iff
        Y k x).mp hxk |>.1
    exact Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hxk⟩

/-- Consequently the exact selected datum has the same actual outer average
as the original induced coarse shading. -/
theorem jointSelectedCoarseActualDatum_averageMultiplicity_eq
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) :
    (jointSelectedCoarseActualDatum P Y).shading.averageMultiplicity =
      (P.asConvexFactorization.inducedShading Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [jointSelectedCoarseActualDatum_shadingMass_eq P Y,
    jointSelectedCoarseActualDatum_shadedUnion_eq P Y]

/-- The Joint producer's active coarse Katz--Tao output is ordinary
Katz--Tao control on the exact selected actual datum. -/
theorem jointSelectedCoarseActualDatum_isKatzTao
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {C : ENNReal}
    (hKT : IsKatzTaoOn C coarse.bodyFamily P.coarseIndices) :
    IsKatzTao C
      (jointSelectedCoarseActualDatum P Y).family.bodyFamily := by
  exact isKatzTao_restrictActualTubeDatum_of_isKatzTaoOn
    (jointInducedCoarseActualDatum P Y) P.coarseIndices C hKT

/-- Same-object application of `KatzTaoAtParameters` to the selected Joint
coarse shading.  The active KT coefficient may be smaller than the target
power coefficient; monotonicity performs that honest scalar transport. -/
theorem inducedCoarse_averageMultiplicity_le_katzTaoMultiplicityRHS
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hKKT : KatzTaoAtParameters beta epsilon eta delta0)
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily)
    (hAdmissible : (jointSelectedCoarseActualDatum P Y).IsAdmissible)
    (hrho : rho ≤ delta0)
    {C : ENNReal}
    (hKT : IsKatzTaoOn C coarse.bodyFamily P.coarseIndices)
    (hC : C ≤ (rho : ENNReal) ^ (-eta))
    (hdensity : (rho : ENNReal) ^ eta ≤
      (jointSelectedCoarseActualDatum P Y).shading.shadingDensity) :
    (P.asConvexFactorization.inducedShading Y).averageMultiplicity ≤
      katzTaoMultiplicityRHS rho P.coarseIndices.card epsilon beta := by
  have hordinary : IsKatzTao ((rho : ENNReal) ^ (-eta))
      (jointSelectedCoarseActualDatum P Y).family.bodyFamily :=
    (jointSelectedCoarseActualDatum_isKatzTao P Y hKT).mono hC
  have hbound := KatzTaoAtParameters.apply hKKT
    (jointSelectedCoarseActualDatum P Y) hAdmissible hrho
      ((katzTaoHypotheses_iff_density_and_isKatzTao
        (jointSelectedCoarseActualDatum P Y) eta).mpr
          ⟨hdensity, hordinary⟩)
  rw [jointSelectedCoarseActualDatum_averageMultiplicity_eq P Y] at hbound
  simpa only [Fintype.card_coe] using hbound

#print axioms jointInducedCoarseActualDatum
#print axioms jointSelectedCoarseActualDatum
#print axioms jointInducedCoarseActualDatum_family
#print axioms jointInducedCoarseActualDatum_shading
#print axioms jointSelectedCoarseActualDatum_shadingMass_eq
#print axioms jointSelectedCoarseActualDatum_shadedUnion_eq
#print axioms jointSelectedCoarseActualDatum_averageMultiplicity_eq
#print axioms jointSelectedCoarseActualDatum_isKatzTao
#print axioms inducedCoarse_averageMultiplicity_le_katzTaoMultiplicityRHS

end
end Family8JointExactUniformCoarseKatzTaoAtParametersV7
