import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1.IntervalParentMassComparison
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover

noncomputable section

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-!
# Pointwise Frostman inheritance for a selected upper parent

The all-parent theorem
`Family8NormalizedLongIntervalFrostmanInheritanceV1.intervalScaleCover_isFrostmanAtScale`
proves its conclusion one upper parent at a time.  Lemma 7.7(A)'s recursive
factor split needs that pointwise statement: the old factor is one selected
fibre, and its upper child must retain the same literal upper parent.

This module extracts exactly that seam.  No maximum over unrelated parents
is introduced.  The commuting parent square and the two-sided assigned-mass
comparison remain the genuine structural input through
`IntervalParentMassComparison`.
-/

/-- Frostman control of one selected base fibre is inherited by the coarse
fibre over the same literal upper parent.  The loss is exactly the same
`upper * lower⁻¹` loss as in the existing all-parent theorem. -/
theorem selectedUpperChild_cfAt_le
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauOne : tau <= 1) (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    {baseError lower upper : ENNReal}
    (hdelta : 0 < delta)
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (H : IntervalParentMassComparison C tau hdeltaTau hTauOne lower upper)
    (k : {k // k ∈
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).activeCoarse})
    (hbase : parentNormalizedFiberCFAt
        (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne) k <=
      baseError) :
    parentNormalizedFiberCFAt
        (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne) k <=
      baseError * upper * lower⁻¹ := by
  let T := C.base.cover tau hdeltaTau hTauOne
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let I := C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne
  let P := H.intervalFiberFactorization rho hTauRho hRhoOne k.1
  have hfineCanonical :
      IsFrostmanIn (parentNormalizedFiberCFAt R k)
        (R.fiberFamily k.1) (R.activeCoarseFamily k) := by
    unfold parentNormalizedFiberCFAt
    apply
      Family8ActiveCoarseCanonicalFrostmanXLowerV3.canonicalFrostmanConstant_isFrostmanIn
    · exact fiberFamily_subset_parent R k
    · rw [containedMass_fiberFamily_parent_eq_familyVolume]
      exact (fiberFamilyVolume_pos R hdelta k).ne'
    · rw [containedMass_fiberFamily_parent_eq_familyVolume]
      exact familyVolume_ne_top (R.fiberFamily k.1)
  have hfineSubtype :
      IsFrostmanIn baseError (R.fiberFamily k.1)
        (R.activeCoarseFamily k) :=
    hfineCanonical.mono hbase
  have hfineActive :
      IsFrostmanOn baseError fine.bodyFamily P.index.fine
        (R.coarse.tubes k).body := by
    change IsFrostmanOn baseError fine.bodyFamily
      (H.intervalFiberFactorization rho hTauRho hRhoOne k.1).index.fine
        (R.coarse.tubes k).body
    rw [H.intervalFiberFactorization_fine_eq_baseFiber
      rho hTauRho hRhoOne k.1]
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      fine.bodyFamily (R.fiber k.1) (R.coarse.tubes k).body).2 hfineSubtype
  have hcoarseContained : ∀ q ∈ P.index.coarse,
      (T.coarse.bodyFamily q : Set Space) ⊆
        ((R.coarse.tubes k).body : Set Space) := by
    intro q hq
    have hqFiber : q ∈ I.fiber k.1 := hq
    have hqData := (I.mem_fiber q k.1).1 hqFiber
    have hcarrier := I.carrier_subset q hqData.1
    rw [hqData.2] at hcarrier
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body, I, R, T,
      CoherentStickyMultiscaleCover.intervalScaleCover] using hcarrier
  have hlocal :
      IsFrostmanOn (baseError * upper * lower⁻¹)
        T.coarse.bodyFamily P.index.coarse (R.coarse.tubes k).body := by
    apply
      Family8FrostmanInheritanceToActiveCoarseV3.activeCoarse_isFrostmanOn_of_comparable_fiberDensity
        P (R.coarse.tubes k).body hlower0 hlowerTop hfineActive
        hcoarseContained
    · intro q hq
      have hqFiber : q ∈ I.fiber k.1 := hq
      have hqActive := (I.mem_fiber q k.1).1 hqFiber |>.1
      rw [H.intervalFiberFactorization_fiberBodyMass_eq
        rho hTauRho hRhoOne k.1 q hqFiber]
      exact H.lower_parent_mass q hqActive
    · intro q hq
      have hqFiber : q ∈ I.fiber k.1 := hq
      have hqActive := (I.mem_fiber q k.1).1 hqFiber |>.1
      rw [H.intervalFiberFactorization_fiberBodyMass_eq
        rho hTauRho hRhoOne k.1 q hqFiber]
      exact H.upper_parent_mass q hqActive
  have hlocalSubtype :
      IsFrostmanIn (baseError * upper * lower⁻¹)
        (I.fiberFamily k.1) (R.coarse.tubes k).body := by
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      T.coarse.bodyFamily (I.fiber k.1) (R.coarse.tubes k).body).1 hlocal
  unfold parentNormalizedFiberCFAt
  apply
    Family8GreedyOccurrenceCanonicalFrostmanBridgeV2.canonicalFrostmanConstant_le_of_isFrostmanIn
      hlocalSubtype
  rw [Family6CanonicalFrostmanConstantCoreV1.containedMass_eq_familyVolume_of_contained
    (I.fiberFamily k.1) (R.coarse.tubes k).body hlocalSubtype.1]
  exact (fiberFamilyVolume_pos I (hdelta.trans_le hdeltaTau) k).ne'

#print axioms selectedUpperChild_cfAt_le

end
end Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1
