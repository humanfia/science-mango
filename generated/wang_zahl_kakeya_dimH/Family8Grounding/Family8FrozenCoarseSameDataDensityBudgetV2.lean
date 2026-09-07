import Family8Grounding.Family8FrozenCoarseSameDataMassTransportV3
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Family8Grounding.Family8FrozenCoarseB2FrostmanActualDatumV1
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrozenCoarseSameDataDensityBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FrozenNeighborhoodAssemblyV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseSameDataMassTransportV3
open Family8FrozenCoarseSameDataMassTransportV3.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

namespace Assembly

variable {P : CoarseTubePartition fine coarse}
  {Y : Shading fine.bodyFamily} {r : Real}

/-- Generic cancellation on the literal frozen assembly.  Positivity of the
coefficient is not an extra premise: it follows from nonzero source mass and
the already-proved same-data mass transport. -/
theorem frozenCoarse_density_lower_of_sourceMass_scalar
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    {q target Q : ENNReal}
    (hsource0 :
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass ≠ 0)
    (hq : q <=
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass)
    (hvolume : familyVolume coarse.bodyFamily <= Q)
    (hscalar :
      target *
          (((A.loss : ENNReal) *
              ((P.branchingLoss * P.branching : Nat) : ENNReal)) * Q) <= q) :
    target <= A.frozenCoarse.shadingDensity := by
  let G : ENNReal :=
    (A.loss : ENNReal) *
      ((P.branchingLoss * P.branching : Nat) : ENNReal)
  let V : ENNReal := familyVolume coarse.bodyFamily
  have htransport :
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass <=
        G * (A.frozenCoarse.shadingDensity * V) := by
    calc
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass <=
          G * A.frozenCoarse.shadingMass := by
        simpa only [G] using
          sourceActiveFineShading_mass_le_loss_mul_branching_mul_frozenCoarse A
      _ = G * (A.frozenCoarse.shadingDensity * V) := by
        dsimp only [V]
        rw [shadingDensity_mul_familyVolume]
  have hright0 : G * (A.frozenCoarse.shadingDensity * V) ≠ 0 := by
    intro hzero
    have hz :
        (sourceActiveFineShading P.asConvexFactorization Y).shadingMass = 0 :=
      bot_unique (htransport.trans_eq hzero)
    exact hsource0 hz
  have hcoefficient0 : G * V ≠ 0 := by
    intro hzero
    apply hright0
    calc
      G * (A.frozenCoarse.shadingDensity * V) =
          (G * V) * A.frozenCoarse.shadingDensity := by ac_rfl
      _ = 0 := by rw [hzero, zero_mul]
  have hGtop : G ≠ ∞ := by
    dsimp only [G]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _)
  have hcoefficientTop : G * V ≠ ∞ :=
    ENNReal.mul_ne_top hGtop (by
      dsimp only [V]
      exact familyVolume_ne_top coarse.bodyFamily)
  apply (ENNReal.mul_le_mul_iff_right hcoefficient0 hcoefficientTop).mp
  calc
    (G * V) * target = target * (G * V) := by ac_rfl
    _ <= target * (G * Q) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hvolume)
    _ <= q := by simpa only [G] using hscalar
    _ <= (sourceActiveFineShading P.asConvexFactorization Y).shadingMass := hq
    _ <= G * (A.frozenCoarse.shadingDensity * V) := htransport
    _ = (G * V) * A.frozenCoarse.shadingDensity := by ac_rfl

end Assembly

/-- Any finite uniform radius-`rho` tube family has total indexed volume at
most `card * 8 rho^2`. -/
theorem uniformTubeFamily_familyVolume_le_card_mul_eight_sq
    (coarse : UniformTubeFamily rho kappa)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    familyVolume coarse.bodyFamily <=
      (Fintype.card kappa : ENNReal) * (8 * (rho : ENNReal) ^ 2) := by
  unfold familyVolume
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (∑ k : kappa, volume (coarse.tubes k).carrier) <=
        ∑ _k : kappa, 8 * (rho : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun k _ =>
        (coarse.tubes k).volume_le_eight_mul_sq_of_le_half hrhoHalf
    _ = (Fintype.card kappa : ENNReal) *
        (8 * (rho : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

variable {index : Type} [Fintype index] [DecidableEq index]
  {sourceFine : UniformTubeFamily delta index}

/-- The reindexed active-parent family has volume at most `8X`, with `X`
the exact active coarse card-scale mass. -/
theorem activeFineRestrictedCoarse_familyVolume_le_eight_mul_cardScaleMass
    (S : StickyScaleCover sourceFine rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    familyVolume (activeFineRestrictedScaleCover S).coarse.bodyFamily <=
      8 * (activeCoarseCardScaleMass S : ENNReal) := by
  calc
    familyVolume (activeFineRestrictedScaleCover S).coarse.bodyFamily <=
        (Fintype.card
            (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
          (8 * (rho : ENNReal) ^ 2) :=
      uniformTubeFamily_familyVolume_le_card_mul_eight_sq
        (activeFineRestrictedScaleCover S).coarse hrhoHalf
    _ = 8 * (activeCoarseCardScaleMass S : ENNReal) := by
      rw [Fintype.card_fin]
      simp only [activeFineRestrictedScaleCover, activeCoarseCardScaleMass,
        ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_pow]
      ac_rfl

/-- Same-object density budget for an arbitrary existing partition and
frozen assembly over the active-parent reindex. -/
theorem activeFrozenCoarse_normalizedDensityBudget_of_sourceMass
    (S : StickyScaleCover sourceFine rho)
    (P : CoarseTubePartition
      (activeFineRestrictedFamily S)
      (activeFineRestrictedScaleCover S).coarse)
    (Y : Shading (activeFineRestrictedFamily S).bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    {q Q : ENNReal} {eta : Real} {selectionLoss : Nat}
    (hrhoPos : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hselectionLoss : 0 < selectionLoss)
    (hsource0 :
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass ≠ 0)
    (hq : q <=
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass)
    (hXUpper : (activeCoarseCardScaleMass S : ENNReal) <= Q)
    (hscalar :
      ((((rho / 8 : NNReal) : ENNReal) ^ eta *
            (selectionLoss : ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((P.branchingLoss * P.branching : Nat) : ENNReal)) *
            (8 * Q)) <= q) :
    ((rho / 8 : NNReal) : ENNReal) ^ eta <=
      (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
        (frozenCoarseActualDatum P Y A)).shading.shadingDensity /
          (selectionLoss : ENNReal) := by
  classical
  letI : Nonempty
      (Fin (activeFineRestrictedScaleCover S).coarseCard) := by
    obtain ⟨k, _hk⟩ := P.coarse_nonempty
    exact ⟨k⟩
  have hvolume :
      familyVolume (activeFineRestrictedScaleCover S).coarse.bodyFamily <=
        8 * Q := by
    exact
      (activeFineRestrictedCoarse_familyVolume_le_eight_mul_cardScaleMass
        S hrhoHalf).trans (mul_le_mul' le_rfl hXUpper)
  have hdensity :
      ((((rho / 8 : NNReal) : ENNReal) ^ eta *
          (selectionLoss : ENNReal)) * 128) <=
        A.frozenCoarse.shadingDensity := by
    exact Assembly.frozenCoarse_density_lower_of_sourceMass_scalar
      A hsource0 hq hvolume hscalar
  have hsourceDiv :
      ((rho / 8 : NNReal) : ENNReal) ^ eta *
          (selectionLoss : ENNReal) <=
        A.frozenCoarse.shadingDensity / 128 := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (128 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (128 : ENNReal) ≠ ∞))).2
    exact hdensity
  have hnormalized :
      ((rho / 8 : NNReal) : ENNReal) ^ eta *
          (selectionLoss : ENNReal) <=
        (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
          (frozenCoarseActualDatum P Y A)).shading.shadingDensity :=
    hsourceDiv.trans
      (Family8FrozenCoarseB2DensityTransportScaleOnlyV1.source_shadingDensity_div_128_le_eighthNormalized_of_scale
        (frozenCoarseActualDatum P Y A) hrhoPos hrhoHalf)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by exact_mod_cast (Nat.ne_of_gt hselectionLoss) :
      (selectionLoss : ENNReal) ≠ 0))
    (Or.inl (by simp : (selectionLoss : ENNReal) ≠ ∞))).2
  exact hnormalized

#print axioms Assembly.frozenCoarse_density_lower_of_sourceMass_scalar
#print axioms uniformTubeFamily_familyVolume_le_card_mul_eight_sq
#print axioms
  activeFineRestrictedCoarse_familyVolume_le_eight_mul_cardScaleMass
#print axioms activeFrozenCoarse_normalizedDensityBudget_of_sourceMass

end
end Family8FrozenCoarseSameDataDensityBudgetV2
