import Family8Grounding.Family8NormalizedLongIntervalEndpointParentMassV1
import Family8Grounding.Family8CUniformPairwiseFiberDensityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalCUniformEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedLongIntervalEndpointParentMassV1
open Family8CUniformPairwiseFiberDensityV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainHierarchySiblingRigidityV1
open FamilyStickyScaleChainHierarchySiblingRigidityProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- C-uniformity replaces the absolute upper/lower parent-density quotient.
Pairwise density comparison is summed inside each upper endpoint fibre, and
the total original fine mass cancels.  The resulting adjacent Frostman loss
is the fixed tube-volume factor `(16*C)*16`, not
`actualParentFiberMassLoss * parentFiberMassRatioFloor⁻¹`. -/
theorem intervalScaleCover_isFrostmanAtScale_of_baseFrostman_cUniform
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta ≤ tau)
    (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    {baseError uniformity : ENNReal}
    (hparent : ∀ (i : iota),
      i ∈ (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).activeFine →
        (C.base.cover rho (hdeltaTau.trans hTauRho)
          hRhoOne).parent i =
          C.parent tau rho hdeltaTau hTauRho hRhoOne
            ((C.base.cover tau hdeltaTau
              (hTauRho.trans hRhoOne)).parent i))
    (huniform : IsCUniform
      (C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne))
      uniformity)
    (hbase : StickyScaleCover.IsFrostmanAtScale
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne)
      baseError) :
    StickyScaleCover.IsFrostmanAtScale
      (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne)
      (baseError * ((16 * uniformity) * 16)) := by
  let T := C.base.cover tau hdeltaTau (hTauRho.trans hRhoOne)
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let I := C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne
  let H :=
    @Family8NormalizedLongIntervalEndpointParentMassV1.actualIntervalEndpointParentMassComparison
      delta iota _ _ fine C tau rho hdeltaTau hTauRho hRhoOne
      hdeltaPos hdeltaHalf htauHalf hparent
  intro k hk K hK
  let P := H.endpointFiberFactorization k
  have hfineSubtype :
      IsFrostmanIn baseError (R.fiberFamily k) (R.coarse.tubes k).body := by
    apply (isFrostmanIn_iff_concentration_le).2
    refine ⟨R.fiber_carrier_subset_parent k, ?_⟩
    exact hbase k hk
  have hfineActive :
      IsFrostmanOn baseError fine.bodyFamily P.index.fine
        (R.coarse.tubes k).body := by
    rw [H.endpointFiberFactorization_fine_eq_baseFiber]
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      fine.bodyFamily (R.fiber k) (R.coarse.tubes k).body).2 hfineSubtype
  have hcoarseContained : ∀ q ∈ P.index.coarse,
      (T.coarse.bodyFamily q : Set Space) ⊆
        ((R.coarse.tubes k).body : Set Space) := by
    intro q hq
    have hqFiber : q ∈ I.fiber k := hq
    have hqData := (I.mem_fiber q k).1 hqFiber
    have hcarrier := I.carrier_subset q hqData.1
    rw [hqData.2] at hcarrier
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body, I, R, T,
      CoherentStickyMultiscaleCover.intervalScaleCover] using hcarrier
  have hfineMassEq :
      bodyMassOn fine.bodyFamily P.index.fine =
        familyVolume (R.fiberFamily k) := by
    rw [H.endpointFiberFactorization_fine_eq_baseFiber]
    unfold bodyMassOn
    rw [familyVolume_fiberFamily_eq_sum R k]
  have hfineMass0 : bodyMassOn fine.bodyFamily P.index.fine ≠ 0 := by
    rw [hfineMassEq]
    exact (fiberFamilyVolume_pos R hdeltaPos ⟨k, hk⟩).ne'
  have hfineMassTop : bodyMassOn fine.bodyFamily P.index.fine ≠ ∞ := by
    rw [hfineMassEq]
    exact familyVolume_ne_top (R.fiberFamily k)
  have hlocal :
      IsFrostmanOn (baseError * ((16 * uniformity) * 16))
        T.coarse.bodyFamily P.index.coarse (R.coarse.tubes k).body := by
    apply
      Family8PairwiseFiberDensityFrostmanInheritanceV1.activeCoarse_isFrostmanOn_of_pairwise_fiberDensity
        P (R.coarse.tubes k).body hfineActive hcoarseContained
        hfineMass0 hfineMassTop
    intro q hq l hl
    have hqFiber : q ∈ I.fiber k := hq
    have hlFiber : l ∈ I.fiber k := hl
    have hqActive : q ∈ T.activeCoarse :=
      ((I.mem_fiber q k).1 hqFiber).1
    have hlActive : l ∈ T.activeCoarse :=
      ((I.mem_fiber l k).1 hlFiber).1
    rw [H.endpointFiberFactorization_fiberBodyMass_eq k l hlFiber,
      H.endpointFiberFactorization_fiberBodyMass_eq k q hqFiber]
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      (pairwiseFiberDensity_of_isCUniform
        T hdeltaHalf htauHalf huniform q hqActive l hlActive)
  have hlocalSubtype :
      IsFrostmanIn (baseError * ((16 * uniformity) * 16))
        (I.fiberFamily k) (R.coarse.tubes k).body := by
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      T.coarse.bodyFamily (I.fiber k) (R.coarse.tubes k).body).1 hlocal
  exact (isFrostmanIn_iff_concentration_le).1 hlocalSubtype |>.2 K hK

#print axioms
  intervalScaleCover_isFrostmanAtScale_of_baseFrostman_cUniform

end
end Family8NormalizedLongIntervalCUniformEndpointV1
