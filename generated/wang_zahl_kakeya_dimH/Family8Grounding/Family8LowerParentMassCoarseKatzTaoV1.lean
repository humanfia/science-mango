import Family8Grounding.Family8NormalizedLongIntervalAdjacentUpperV2
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Submission.Kakeya.ConvexFactoring.JointTubeFactoring

/-!
# Coarse Katz--Tao from genuine lower parent mass

The radius-changed identity cover pays a transverse volume-ratio loss because
it keeps one coarse parent for every fine tube.  A genuinely aggregated cover
has a better route: if every active parent carries at least `lower` times its
own volume in assigned fine mass, then source Katz--Tao control transfers to
the active coarse family with loss exactly `lower⁻¹`.

This is a reverse mass-localization theorem.  It uses only the literal cover
fibres and carrier containment; it assumes neither disjoint coarse carriers
nor a Katz--Tao conclusion for the coarse family.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8LowerParentMassCoarseKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8NormalizedCFDividingWitnessBridgeV4.StickyScaleCover
open Family8NormalizedLongIntervalAdjacentUpperV2
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The `JointTubeFactoring` assigned mass is exactly the mass of the literal
sticky-cover fibre. -/
theorem assignedBodyMass_eq_familyVolume_fiberFamily
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    assignedBodyMass fine S.activeFine S.parent k =
      familyVolume (S.fiberFamily k) := by
  classical
  unfold assignedBodyMass familyVolume StickyScaleCover.fiberFamily
  change (∑ i ∈ S.activeFine.filter (fun i => S.parent i = k),
      volume (fine.tubes i).carrier) =
    ∑ i : {i // i ∈ S.fiber k},
      volume (fine.bodyFamily i.1 : Set Space)
  rw [← Finset.attach_eq_univ]
  simpa only [StickyScaleCover.fiber, UniformTubeFamily.bodyFamily,
    Tube.coe_body] using
      (Finset.sum_attach (S.fiber k)
        (fun i => volume (fine.bodyFamily i : Set Space))).symm

/-- Summing a lower assigned-mass bound over precisely the parents contained
in a test body controls their total parent volume by the contained active fine
mass. -/
theorem lower_mul_containedMass_activeCoarse_le_activeFine
    (S : StickyScaleCover fine rho) (lower : ENNReal)
    (hlower : forall k, k ∈ S.activeCoarse ->
      lower * volume (S.coarse.tubes k).carrier <=
        familyVolume (S.fiberFamily k))
    (K : ConvexBody Space) :
    lower * containedMass S.activeCoarseFamily K <=
      containedMass (activeFineFamily S) K := by
  let inside : Finset (Fin S.coarseCard) :=
    S.activeCoarse ∩ containedIndices S.coarse.bodyFamily K
  have hinside : forall k, k ∈ inside ->
      (S.coarse.bodyFamily k : Set Space) ⊆ (K : Set Space) := by
    intro k hk
    exact (mem_containedIndices S.coarse.bodyFamily K k).1
      (Finset.mem_inter.mp hk).2
  have hassigned :
      (∑ k ∈ inside, assignedBodyMass fine S.activeFine S.parent k) <=
        containedMassOn fine.bodyFamily S.activeFine K := by
    apply selectedAssignedMass_le_containedMassOn
      fine S.coarse S.activeFine S.parent
    · intro i hi
      simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
        S.carrier_subset i hi
    · exact hinside
  have hlowerSum :
      lower * (∑ k ∈ inside, volume (S.coarse.tubes k).carrier) <=
        ∑ k ∈ inside, assignedBodyMass fine S.activeFine S.parent k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [assignedBodyMass_eq_familyVolume_fiberFamily]
    exact hlower k (Finset.mem_inter.mp hk).1
  have hcoarse :
      containedMass S.activeCoarseFamily K =
        ∑ k ∈ inside, volume (S.coarse.tubes k).carrier := by
    change containedMass
      (activeSubtypeFamily S.coarse.bodyFamily S.activeCoarse) K = _
    rw [containedMass_activeSubtypeFamily]
    unfold containedMassOn
    apply Finset.sum_congr
    · ext k
      simp only [inside, Finset.mem_inter]
    · intro k hk
      rfl
  have hfine :
      containedMass (activeFineFamily S) K =
        containedMassOn fine.bodyFamily S.activeFine K := by
    change containedMass (activeSubtypeFamily fine.bodyFamily S.activeFine) K = _
    exact containedMass_activeSubtypeFamily fine.bodyFamily S.activeFine K
  rw [hcoarse, hfine]
  exact hlowerSum.trans hassigned

/-- A positive finite lower parent-density converts source Katz--Tao directly
to coarse Katz--Tao.  No radius-volume ratio occurs. -/
theorem activeCoarseFamily_isKatzTao_of_lowerParentMass
    (S : StickyScaleCover fine rho) {A lower : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hlower : forall k, k ∈ S.activeCoarse ->
      lower * volume (S.coarse.tubes k).carrier <=
        familyVolume (S.fiberFamily k))
    (hfineKT : IsKatzTao A fine.bodyFamily) :
    IsKatzTao (A * lower⁻¹) S.activeCoarseFamily := by
  have hfineActive : IsKatzTao A (activeFineFamily S) := by
    intro K
    change containedMass (activeSubtypeFamily fine.bodyFamily S.activeFine) K <= _
    rw [containedMass_activeSubtypeFamily]
    exact (hfineKT.on S.activeFine) K
  intro K
  apply (ENNReal.mul_le_mul_iff_left hlower0 hlowerTop).mp
  calc
    containedMass S.activeCoarseFamily K * lower =
        lower * containedMass S.activeCoarseFamily K := mul_comm _ _
    _ <= containedMass (activeFineFamily S) K :=
      lower_mul_containedMass_activeCoarse_le_activeFine S lower hlower K
    _ <= A * volume (K : Set Space) := hfineActive K
    _ = ((A * lower⁻¹) * volume (K : Set Space)) * lower := by
      have hcancel : lower⁻¹ * lower = 1 :=
        ENNReal.inv_mul_cancel hlower0 hlowerTop
      rw [show ((A * lower⁻¹) * volume (K : Set Space)) * lower =
          (A * volume (K : Set Space)) * (lower⁻¹ * lower) by ac_rfl,
        hcancel, mul_one]

/-- The same producer in the exact sticky-cover interface consumed by the
long-interval bootstrap. -/
theorem isKatzTaoAtScale_of_lowerParentMass
    (S : StickyScaleCover fine rho) {A lower : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hlower : forall k, k ∈ S.activeCoarse ->
      lower * volume (S.coarse.tubes k).carrier <=
        familyVolume (S.fiberFamily k))
    (hfineKT : IsKatzTao A fine.bodyFamily) :
    S.IsKatzTaoAtScale (A * lower⁻¹) := by
  exact (isKatzTao_iff_concentration_le.mp
    (activeCoarseFamily_isKatzTao_of_lowerParentMass
      S hlower0 hlowerTop hlower hfineKT))

variable {C : CoherentStickyMultiscaleCover fine}
  {tau : NNReal} {hdeltaTau : delta <= tau} {hTauOne : tau <= 1}
  {lower upper A : ENNReal}

/-- Any existing interval parent-mass package automatically supplies the
coarse Katz--Tao bound at its lower endpoint.  Parent commutation and the
upper mass field are not consumed by this projection. -/
theorem IntervalParentMassComparison.lowerEndpoint_isKatzTaoAtScale
    (H : IntervalParentMassComparison C tau hdeltaTau hTauOne lower upper)
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfineKT : IsKatzTao A fine.bodyFamily) :
    (C.base.cover tau hdeltaTau hTauOne).IsKatzTaoAtScale
      (A * lower⁻¹) := by
  exact isKatzTaoAtScale_of_lowerParentMass
    (C.base.cover tau hdeltaTau hTauOne)
    hlower0 hlowerTop H.lower_parent_mass hfineKT

/-- The repository's automatic geometric one-child floor gives a fully
concrete specialization.  A stronger regularized lower mass may be inserted
in the preceding theorem to avoid this fallback floor. -/
theorem baseCover_isKatzTaoAtScale_source_div_parentFiberMassRatioFloor
    (C : CoherentStickyMultiscaleCover fine)
    (tau : NNReal) (hdeltaTau : delta <= tau) (hTauOne : tau <= 1)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (htauHalf : tau <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hfineKT : IsKatzTao A fine.bodyFamily) :
    (C.base.cover tau hdeltaTau hTauOne).IsKatzTaoAtScale
      (A * (parentFiberMassRatioFloor delta tau)⁻¹) := by
  apply isKatzTaoAtScale_of_lowerParentMass
    (C.base.cover tau hdeltaTau hTauOne)
    (parentFiberMassRatioFloor_ne_zero hdeltaPos tau)
    (parentFiberMassRatioFloor_ne_top delta tau
      (hdeltaPos.trans_le hdeltaTau))
  · intro q hq
    let T := C.base.cover tau hdeltaTau hTauOne
    let qq : {q // q ∈ T.activeCoarse} := ⟨q, hq⟩
    have htauPos : 0 < tau := hdeltaPos.trans_le hdeltaTau
    have hratio := parentFiberMassRatioFloor_le T hdeltaHalf htauHalf qq
    have hvol0 : volume (T.coarse.tubes q).carrier ≠ 0 :=
      (T.coarse.tubes q).volume_pos htauPos |>.ne'
    have hvolTop : volume (T.coarse.tubes q).carrier ≠ ∞ :=
      (T.coarse.tubes q).volume_lt_top.ne
    have hcross :=
      (ENNReal.le_div_iff_mul_le (Or.inl hvol0) (Or.inl hvolTop)).1 hratio
    simpa only [parentFiberMassRatio, StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body, T, qq] using hcross
  · exact hfineKT

#print axioms assignedBodyMass_eq_familyVolume_fiberFamily
#print axioms lower_mul_containedMass_activeCoarse_le_activeFine
#print axioms activeCoarseFamily_isKatzTao_of_lowerParentMass
#print axioms isKatzTaoAtScale_of_lowerParentMass
#print axioms IntervalParentMassComparison.lowerEndpoint_isKatzTaoAtScale

end
end Family8LowerParentMassCoarseKatzTaoV1
