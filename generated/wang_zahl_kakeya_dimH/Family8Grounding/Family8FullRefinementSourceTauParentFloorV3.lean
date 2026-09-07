import Family8Grounding.Family8SourceMassPartitionParentAggregatedFloorV3
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8KatzTaoDoubledFiberActiveIndexCapV3
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FullRefinementSourceTauParentFloorV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8AllFrostmanStickyUnionProducerV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8KatzTaoDoubledFiberActiveIndexCapV3.StickyScaleCover
open Family8SourceMassPartitionParentAggregatedFloorV3
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8FullRefinementActualDatumV1

noncomputable section

/-!
# Frostman source mass divided by the exact source-to-tau fibre cap

This quantitative core uses the actual source-to-tau cover and its literal
Katz--Tao doubled-fibre cap.  The successor divisor is positive, so the
Frostman source mass can be cancelled into an actual parent-shading floor.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem fullRefinement_sourceTau_parentAggregated_mass_lower
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    {etaF etaKT : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT) :
    (delta : ENNReal) ^ (2 * etaF) /
        ((katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) + 1 : Nat) : ENNReal) <=
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading).shadingMass := by
  let E := fullRefinementDatum D
  let S0 := tauScaleCover E Cmulti Sseq W
  let M : Nat := katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
    ((delta : ENNReal) ^ (-etaKT)) + 1
  have hmassLower : (delta : ENNReal) ^ (2 * etaF) <=
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
  have hAfinite : (delta : ENNReal) ^ (-etaKT) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  have hKTfull : IsKatzTao ((delta : ENNReal) ^ (-etaKT))
      E.family.bodyFamily := by
    exact (maximalConcentration_le_iff_isKatzTao).1 hKTsource.2
  have hcap0 := activeIndexFiber_card_le_katzTaoDoubledFiberNatCap
    S0 hD.delta_pos hD.delta_le_half
      (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m)
      hAfinite hKTfull
  have hcap : forall k : {k // k ∈ S0.activeCoarse},
      ((activeIndexFactorization S0).fiber k).card <= M := by
    intro k
    exact (hcap0 k).trans (Nat.le_succ _)
  have hMpos : 0 < M := by
    dsimp only [M]
    exact Nat.zero_lt_succ _
  have hM0 : (M : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMpos
  have hMTop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hactive : S0.activeFine = Finset.univ := by
    have h := (tauScaleCover E Cmulti Sseq W).activeFine_eq_refined
    simpa only [S0, E, fullRefinementDatum_refined] using h
  have hactiveMass : (activeFineShading S0 E.shading).shadingMass =
      D.shading.shadingMass := by
    rw [activeFineShading_shadingMass_eq_of_activeFine_eq_univ
      S0 E.shading hactive]
    exact fullRefinementDatum_shadingMass D
  have hscaled : (M : ENNReal) *
      ((delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)) <=
        (activeFineShading S0 E.shading).shadingMass := by
    calc
      (M : ENNReal) *
          ((delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)) =
          ((delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)) * M :=
        mul_comm _ _
      _ = (delta : ENNReal) ^ (2 * etaF) :=
        ENNReal.div_mul_cancel hM0 hMTop
      _ <= D.shading.shadingMass := hmassLower
      _ = (activeFineShading S0 E.shading).shadingMass := hactiveMass.symm
  exact sourceFloor_le_parentAggregatedShading_of_fiberCard
    S0 E.shading M hMpos hcap hscaled

#print axioms fullRefinement_sourceTau_parentAggregated_mass_lower

end Witness
end
end Family8FullRefinementSourceTauParentFloorV3
