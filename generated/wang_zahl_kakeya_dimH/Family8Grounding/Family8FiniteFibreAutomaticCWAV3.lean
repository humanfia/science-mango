import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteFibreAutomaticCWAV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1

noncomputable section

/-!
# Automatic finite-fibre Convex Wolff constants

Every finite convex family whose members have positive volume satisfies the
cardinality-normalized Convex Wolff axioms for some finite natural constant.
The constant here is deliberately non-quantitative: it is obtained from the
sum of inverse member volumes.  Applying the same bound simultaneously to
all active rescaled fibres gives one common natural `Cnn`.
-/

/-- A finite nonempty positive-volume convex family satisfies CWA whenever
`C` dominates its inverse-volume sum. -/
theorem satisfiesConvexWolffAxioms_of_inverseVolumeSum_le
    {index : Type} [Fintype index]
    (F : ConvexFamily index) (hindex : Nonempty index)
    (hvolume : forall i, 0 < volume (F i : Set Space))
    {C : ENNReal}
    (hsum : (∑ i, (volume (F i : Set Space))⁻¹) <= C) :
    SatisfiesConvexWolffAxioms C F := by
  classical
  intro K
  have hone (i : index) (hi : i ∈ containedIndices F K) :
      (1 : ENNReal) <=
        volume (K : Set Space) * (volume (F i : Set Space))⁻¹ := by
    have hsubset : (F i : Set Space) ⊆ (K : Set Space) :=
      (mem_containedIndices F K i).mp hi
    calc
      (1 : ENNReal) =
          volume (F i : Set Space) * (volume (F i : Set Space))⁻¹ :=
        (ENNReal.mul_inv_cancel (hvolume i).ne'
          (F i).isCompact.measure_lt_top.ne).symm
      _ = (volume (F i : Set Space))⁻¹ * volume (F i : Set Space) := by
        rw [mul_comm]
      _ <= (volume (F i : Set Space))⁻¹ * volume (K : Set Space) :=
        mul_le_mul' le_rfl (measure_mono hsubset)
      _ = volume (K : Set Space) * (volume (F i : Set Space))⁻¹ := by
        rw [mul_comm]
  have hcardOne : (1 : ENNReal) <= (Fintype.card index : ENNReal) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hindex)
  have hcaptured :
      ((containedIndices F K).card : ENNReal) <=
        volume (K : Set Space) *
          ∑ i, (volume (F i : Set Space))⁻¹ := by
    calc
      ((containedIndices F K).card : ENNReal) =
          ∑ i ∈ containedIndices F K, (1 : ENNReal) := by simp
      _ <= ∑ i ∈ containedIndices F K,
          volume (K : Set Space) * (volume (F i : Set Space))⁻¹ := by
        exact Finset.sum_le_sum fun i hi => hone i hi
      _ = volume (K : Set Space) *
          ∑ i ∈ containedIndices F K,
            (volume (F i : Set Space))⁻¹ := by
        rw [Finset.mul_sum]
      _ <= volume (K : Set Space) *
          ∑ i, (volume (F i : Set Space))⁻¹ := by
        exact mul_le_mul' le_rfl
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
  calc
    ((containedIndices F K).card : ENNReal) <=
        volume (K : Set Space) *
          ∑ i, (volume (F i : Set Space))⁻¹ := hcaptured
    _ <= volume (K : Set Space) * C := mul_le_mul' le_rfl hsum
    _ = C * volume (K : Set Space) := mul_comm _ _
    _ = C * volume (K : Set Space) * 1 := by rw [mul_one]
    _ <= C * volume (K : Set Space) * (Fintype.card index : ENNReal) :=
      mul_le_mul' le_rfl hcardOne

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {S : StickyScaleCover fine rho}

/-- The inverse-volume budget of one active rescaled fibre. -/
def fibreInverseVolumeSum (R : UnitRescalingGeometry S)
    (k : {k // k ∈ S.activeCoarse}) : ENNReal :=
  ∑ i : {i // i ∈ S.fiber k.1},
    (volume (R.rescaledFiberFamily k i : Set Space))⁻¹

/-- The single finite inverse-volume budget shared by every active fibre. -/
def fibresInverseVolumeSum (R : UnitRescalingGeometry S) : ENNReal :=
  ∑ k : {k // k ∈ S.activeCoarse}, fibreInverseVolumeSum R k

/-- Positive volume of every rescaled member makes the double inverse-volume
sum finite. -/
theorem fibresInverseVolumeSum_ne_top
    (R : UnitRescalingGeometry S)
    (hvolume : forall k i,
      0 < volume (R.rescaledFiberFamily k i : Set Space)) :
    fibresInverseVolumeSum R ≠ ∞ := by
  unfold fibresInverseVolumeSum
  apply ENNReal.sum_ne_top.mpr
  intro k _hk
  unfold fibreInverseVolumeSum
  apply ENNReal.sum_ne_top.mpr
  intro i _hi
  exact ENNReal.inv_ne_top.mpr (hvolume k i).ne'

/-- One common natural constant controls every finite rescaled fibre. -/
theorem exists_nat_fibresSatisfyCWA_of_volume_pos
    (R : UnitRescalingGeometry S)
    (hvolume : forall k i,
      0 < volume (R.rescaledFiberFamily k i : Set Space)) :
    exists Cnn : Nat, 1 <= Cnn ∧
      R.FibresSatisfyCWA (Cnn : ENNReal) := by
  have hsumTop : fibresInverseVolumeSum R ≠ ∞ :=
    fibresInverseVolumeSum_ne_top R hvolume
  obtain ⟨Cnn, hCnn⟩ := ENNReal.exists_nat_gt hsumTop
  have hCnnPos : 0 < Cnn := by
    have hcast : (0 : ENNReal) < (Cnn : ENNReal) := bot_le.trans_lt hCnn
    exact_mod_cast hcast
  refine ⟨Cnn, hCnnPos, ?_⟩
  intro k
  have hfiberNonempty : Nonempty {i // i ∈ S.fiber k.1} := by
    obtain ⟨i, hiActive, hparent⟩ := S.parent_surjective k.1 k.2
    exact ⟨⟨i, (S.mem_fiber i k.1).mpr ⟨hiActive, hparent⟩⟩⟩
  apply satisfiesConvexWolffAxioms_of_inverseVolumeSum_le
    (R.rescaledFiberFamily k) hfiberNonempty (hvolume k)
  change fibreInverseVolumeSum R k <= (Cnn : ENNReal)
  have hlocal : fibreInverseVolumeSum R k <=
      fibresInverseVolumeSum R := by
    unfold fibresInverseVolumeSum
    exact Finset.single_le_sum
      (fun l _hl => show (0 : ENNReal) <=
        fibreInverseVolumeSum R l from bot_le)
      (Finset.mem_univ k)
  exact hlocal.trans hCnn.le

/-! ## Identity-radius specialization -/

/-- Affine Jacobian positivity and the positive tube radius automatically
give positive volume for every rescaled identity-cover fibre member. -/
theorem identityRadiusScaleCover_rescaledFiberFamily_volume_pos
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho) (hdeltaPos : 0 < delta)
    (R : UnitRescalingGeometry
      (identityRadiusScaleCover fine rho hdelta)) :
    forall k i,
      0 < volume (R.rescaledFiberFamily k i : Set Space) := by
  intro k i
  change 0 < volume
    (affineImageConvexBody (R.unitRescaling k)
      ((identityRadiusScaleCover fine rho hdelta).fiberFamily k.1 i) :
        Set Space)
  rw [volume_affineImageConvexBody]
  have hfiberVolume : 0 <
      volume ((identityRadiusScaleCover fine rho hdelta).fiberFamily k.1 i :
        Set Space) := by
    simpa only [StickyScaleCover.fiberFamily,
      UniformTubeFamily.bodyFamily_apply, Tube.coe_body] using
      (fine.tubes i.1).volume_pos hdeltaPos
  exact ENNReal.mul_pos (affineJacobian_pos (R.unitRescaling k)).ne'
    hfiberVolume.ne'

/-- Singleton active fibres make the identity-radius cover `Cnn`-uniform for
every natural `Cnn >= 1`. -/
theorem identityRadiusScaleCover_isCUniform_of_one_le
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho)
    (Cnn : Nat) (hCnn : 1 <= Cnn) :
    IsCUniform (identityRadiusScaleCover fine rho hdelta)
      (Cnn : ENNReal) := by
  intro k hk l hl
  rw [identityRadiusScaleCover_fiber_eq_singleton
      fine rho hdelta k hk,
    identityRadiusScaleCover_fiber_eq_singleton
      fine rho hdelta l hl]
  norm_num
  exact_mod_cast hCnn

/-- Callback-free finite CWA and C-uniformity for any supplied John
unit-rescaling geometry on the identity-radius cover.  `Cnn` is only an
existential finite constant; no quantitative sharpness is claimed. -/
theorem exists_nat_identityRadiusScaleCover_cUniform_fibresCWA
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho) (hdeltaPos : 0 < delta)
    (R : UnitRescalingGeometry
      (identityRadiusScaleCover fine rho hdelta)) :
    exists Cnn : Nat, 1 <= Cnn ∧
      IsCUniform (identityRadiusScaleCover fine rho hdelta)
        (Cnn : ENNReal) ∧
      R.FibresSatisfyCWA (Cnn : ENNReal) := by
  obtain ⟨Cnn, hCnn, hCWA⟩ :=
    exists_nat_fibresSatisfyCWA_of_volume_pos R
      (identityRadiusScaleCover_rescaledFiberFamily_volume_pos
        fine rho hdelta hdeltaPos R)
  exact ⟨Cnn, hCnn,
    identityRadiusScaleCover_isCUniform_of_one_le
      fine rho hdelta Cnn hCnn,
    hCWA⟩

#print axioms satisfiesConvexWolffAxioms_of_inverseVolumeSum_le
#print axioms fibresInverseVolumeSum_ne_top
#print axioms exists_nat_fibresSatisfyCWA_of_volume_pos
#print axioms identityRadiusScaleCover_rescaledFiberFamily_volume_pos
#print axioms identityRadiusScaleCover_isCUniform_of_one_le
#print axioms exists_nat_identityRadiusScaleCover_cUniform_fibresCWA

end
end Family8FiniteFibreAutomaticCWAV3
