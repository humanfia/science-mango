import Family8Grounding.Family8CommonPointTubePackingV1
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8AdmissibleCommonPointGlobalKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8PointwisePackingVolumeV1
open Family8CommonPointTubePackingV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# The automatic coarse global Katz--Tao bound

A pointwise cap for the full carriers bounds the contained mass in every
convex test body.  Applying the proved common-point tube packing theorem gives
an unconditional global Katz--Tao coefficient of order `delta ^ (-2)` for an
admissible actual datum.  This is the honest source coefficient available
before any polynomial John sampling; it is deliberately not weakened to an
arbitrarily small power.
-/

/-- Restricting the full-carrier shading to a convex test body dominates the
mass of all family members wholly contained in that body. -/
theorem containedMass_le_restrict_actualCarrierShading_mass
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (K : ConvexBody Space) :
    containedMass D.family.bodyFamily K <=
      ((actualCarrierShading D).restrictSet (K : Set Space)
        K.isCompact.measurableSet).shadingMass := by
  classical
  let Z := (actualCarrierShading D).restrictSet (K : Set Space)
    K.isCompact.measurableSet
  have heq : containedMass D.family.bodyFamily K =
      ∑ i ∈ containedIndices D.family.bodyFamily K,
        volume (Z.carrier i) := by
    unfold containedMass
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Z]
    rw [Shading.restrictSet_carrier]
    have hsub : (D.family.bodyFamily i : Set Space) <= (K : Set Space) :=
      (mem_containedIndices D.family.bodyFamily K i).1 hi
    rw [actualCarrierShading_carrier]
    change volume (D.family.tubes i).carrier =
      volume ((D.family.tubes i).carrier ∩ (K : Set Space))
    have hsub' : (D.family.tubes i).carrier ⊆ (K : Set Space) := hsub
    rw [Set.inter_eq_left.mpr hsub']
  rw [heq]
  unfold Shading.shadingMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) (fun i _hi _hnot => bot_le)

/-- A pointwise natural cap for the full carriers is already a global
Katz--Tao cap for the actual body family. -/
theorem isKatzTao_of_actualCarrierShading_pointMultiplicity_le
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (M : Nat)
    (hpoint : forall x, (actualCarrierShading D).pointMultiplicity x <= M) :
    IsKatzTao (M : ENNReal) D.family.bodyFamily := by
  intro K
  let Z := (actualCarrierShading D).restrictSet (K : Set Space)
    K.isCompact.measurableSet
  have hZpoint : forall x, Z.pointMultiplicity x <= M := by
    intro x
    rw [Shading.pointMultiplicity_restrictSet]
    split_ifs
    · exact hpoint x
    · exact Nat.zero_le _
  have hmass : Z.shadingMass <= (M : ENNReal) * volume Z.shadedUnion := by
    simpa only [nsmul_eq_mul] using
      (FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
          Z M hZpoint)
  have hunion : Z.shadedUnion <= (K : Set Space) := by
    rw [Shading.restrictSet_shadedUnion]
    exact inter_subset_right
  calc
    containedMass D.family.bodyFamily K <= Z.shadingMass := by
      simpa only [Z] using
        containedMass_le_restrict_actualCarrierShading_mass D K
    _ <= (M : ENNReal) * volume Z.shadedUnion := hmass
    _ <= (M : ENNReal) * volume (K : Set Space) := by
      gcongr

/-- The literal common-point packing cap gives an automatic global
Katz--Tao theorem with no concentration premise. -/
theorem isKatzTao_commonPointTubePackingNatCap
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    IsKatzTao (commonPointTubePackingNatCap delta : ENNReal)
      D.family.bodyFamily := by
  exact isKatzTao_of_actualCarrierShading_pointMultiplicity_le D
    (commonPointTubePackingNatCap delta)
    (actualCarrierShading_pointMultiplicity_le_commonPointTubePackingNatCap
      D hD hdeltaSmall)

/-- Scale-invariant coarse form: admissibility automatically supplies a
global coefficient bounded by a fixed constant times `delta ^ (-2)`. -/
theorem isKatzTao_commonPointTubePacking_rpow
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    IsKatzTao
      (commonPointTubePackingConstant *
        (delta : ENNReal) ^ (-2 : Real))
      D.family.bodyFamily := by
  exact (isKatzTao_commonPointTubePackingNatCap D hD hdeltaSmall).mono
    (commonPointTubePackingNatCap_coe_le_rpow
      delta hD.delta_pos hdeltaSmall)

#print axioms containedMass_le_restrict_actualCarrierShading_mass
#print axioms isKatzTao_of_actualCarrierShading_pointMultiplicity_le
#print axioms isKatzTao_commonPointTubePackingNatCap
#print axioms isKatzTao_commonPointTubePacking_rpow

end
end Family8AdmissibleCommonPointGlobalKatzTaoV1
