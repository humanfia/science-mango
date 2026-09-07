import Family8Grounding.Family8FullRefinementSourceTauParentFloorV5
import Family8Grounding.Family8SelectedParentMassPopularProp66AInnerV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauMassPopularEq46ExactCapV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8AllFrostmanStickyUnionProducerV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8KatzTaoDoubledFiberActiveIndexCapV3.StickyScaleCover
open Family8FullRefinementActualDatumV1
open Family8FullRefinementSourceTauParentFloorV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularCordobaCoreV2
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8Prop66AOuterInnerProductAlgebraV1

noncomputable section

/-!
# Exact-cap cancellation in the mass-popular Equation (46) budget

V1--V3 are namespace/cancellation-orientation drafts and are intentionally
not imported.  Here the same natural cap is the exact source-floor divisor
and the literal `tubesPerPlank` argument of Equation (46).
-/

theorem massPopularCrossEq46Budget_of_sourceFloor_crossMultiplied
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (Pgreedy : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily Pgreedy).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S Pgreedy)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal)
    (M : Nat) (hMpos : 0 < M)
    {sourceFloor : ENNReal} {lossEta epsilon beta : Real}
    (hsourceLower : sourceFloor ≤
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S Pgreedy).index.fine).shading.shadingMass)
    (hcross :
      (M : ENNReal) *
        ((rho : ENNReal) ^ (-lossEta) *
          selectedParentMassPopularCordobaCoreBudget
            D S hrho Pgreedy k r hr A label KT) ≤
      (affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                S hrho Pgreedy k) r hr)
            label) * ((M : ENNReal) * sourceFloor)) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label) M epsilon beta) :
    MassPopularCrossEq46Budget D S hrho Pgreedy k r hr A label KT
      lossEta M epsilon beta := by
  let J := affineJacobian
    (bucketNormalizedAffineEquiv
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho Pgreedy k) r hr)
      label)
  let inner := proposition66AInnerFactor rho
    (bucketShortA label) (bucketShortB label) M epsilon beta
  let core := (rho : ENNReal) ^ (-lossEta) *
    selectedParentMassPopularCordobaCoreBudget
      D S hrho Pgreedy k r hr A label KT
  have hM0 : (M : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMpos
  have hMTop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hsourceFactor : J * sourceFloor ≤
      selectedParentMassPopularSourceFactor
        D S hrho Pgreedy k r hr label := by
    unfold selectedParentMassPopularSourceFactor
    exact mul_le_mul' le_rfl hsourceLower
  have hcross' : (M : ENNReal) * core ≤
      (J * ((M : ENNReal) * sourceFloor)) * inner := by
    simpa only [J, inner, core] using hcross
  have hcancelled : core ≤
      selectedParentMassPopularSourceFactor
          D S hrho Pgreedy k r hr label * inner := by
    apply (ENNReal.mul_le_mul_iff_left hM0 hMTop).mp
    calc
      core * (M : ENNReal) = (M : ENNReal) * core := mul_comm _ _
      _ ≤ (J * ((M : ENNReal) * sourceFloor)) * inner := hcross'
      _ = ((J * sourceFloor) * inner) * (M : ENNReal) := by
        ac_rfl
      _ ≤ (selectedParentMassPopularSourceFactor
              D S hrho Pgreedy k r hr label * inner) * (M : ENNReal) := by
        exact mul_le_mul' (mul_le_mul' hsourceFactor le_rfl) le_rfl
  simpa only [MassPopularCrossEq46Budget, core, inner] using hcancelled

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem fullRefinement_sourceTau_exactKatzTaoCap_pos
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    {etaF etaKT : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT) :
    0 < katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
      ((delta : ENNReal) ^ (-etaKT)) := by
  let E := fullRefinementDatum D
  let S0 := tauScaleCover E Cmulti Sseq W
  let M := katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
    ((delta : ENNReal) ^ (-etaKT))
  have hvolume : D.actualFamilyVolume ≠ 0 :=
    actualFamilyVolume_ne_zero_of_frostmanDensity D hD hFsource
  have hiota : Nonempty index :=
    nonempty_of_actualFamilyVolume_ne_zero D hvolume
  have hAfinite : (delta : ENNReal) ^ (-etaKT) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  have hKTfull : IsKatzTao ((delta : ENNReal) ^ (-etaKT))
      E.family.bodyFamily := by
    exact (maximalConcentration_le_iff_isKatzTao).1 hKTsource.2
  have hcap : ∀ k : {k // k ∈ S0.activeCoarse},
      ((activeIndexFactorization S0).fiber k).card ≤ M :=
    activeIndexFiber_card_le_katzTaoDoubledFiberNatCap
      S0 hD.delta_pos hD.delta_le_half
        (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m)
        hAfinite hKTfull
  have hactive : S0.activeFine = Finset.univ := by
    have h := S0.activeFine_eq_refined
    simpa only [S0, E, fullRefinementDatum_refined] using h
  obtain ⟨i⟩ := hiota
  have hiActive : i ∈ S0.activeFine := by
    rw [hactive]
    exact Finset.mem_univ i
  let k : {k // k ∈ S0.activeCoarse} :=
    ⟨S0.parent i, S0.parent_mem i hiActive⟩
  let ii : {i // i ∈ S0.activeFine} := ⟨i, hiActive⟩
  have hiiFiber : ii ∈ (activeIndexFactorization S0).fiber k := by
    rw [IndexFactorization.mem_fiber]
    exact ⟨Finset.mem_univ ii, rfl⟩
  have hfiberPos : 0 < ((activeIndexFactorization S0).fiber k).card :=
    Finset.card_pos.mpr ⟨ii, hiiFiber⟩
  exact hfiberPos.trans_le (hcap k)

theorem fullRefinement_sourceTau_greedySource_mass_lower_exactCap
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
      Finset.univ)
    {etaF etaKT : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT) :
    (delta : ENNReal) ^ (2 * etaF) /
        (katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) ≤
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (fullRefinementDatum D).shading)
        (greedyParentFactorization
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          Pgreedy).index.fine).shading.shadingMass := by
  have hfloor :=
    fullRefinement_sourceTau_parentAggregated_mass_lower_exactCap
      D hD Cmulti Sseq W hFsource hKTsource
  change _ ≤ (IndexedShadingRefinement.restrictTo
    (parentAggregatedShading
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (fullRefinementDatum D).shading) Finset.univ).shading.shadingMass
  rw [restrictTo_univ_shadingMass]
  exact hfloor

theorem fullRefinement_sourceTau_massPopularCrossEq46Budget_of_exactCap
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
      Finset.univ)
    (k : Fin
      (blocks
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
        Pgreedy).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal)
    {etaF etaKT lossEta epsilon beta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hcross :
      (katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
          ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
        ((Sseq.tau W.m : ENNReal) ^ (-lossEta) *
          selectedParentMassPopularCordobaCoreBudget
            (fullRefinementDatum D)
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
            Pgreedy k r hr A label KT) ≤
      (affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                Pgreedy k) r hr)
            label) * (delta : ENNReal) ^ (2 * etaF)) *
        proposition66AInnerFactor (Sseq.tau W.m)
          (bucketShortA label) (bucketShortB label)
          (katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
            ((delta : ENNReal) ^ (-etaKT))) epsilon beta) :
    MassPopularCrossEq46Budget
      (fullRefinementDatum D)
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      Pgreedy k r hr A label KT lossEta
      (katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
        ((delta : ENNReal) ^ (-etaKT))) epsilon beta := by
  let M := katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
    ((delta : ENNReal) ^ (-etaKT))
  let floor : ENNReal := (delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)
  have hMpos : 0 < M :=
    fullRefinement_sourceTau_exactKatzTaoCap_pos
      D hD Cmulti Sseq W hFsource hKTsource
  have hM0 : (M : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMpos
  have hMTop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hfloor : floor ≤
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (fullRefinementDatum D).shading)
        (greedyParentFactorization
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          Pgreedy).index.fine).shading.shadingMass := by
    simpa only [M, floor] using
      fullRefinement_sourceTau_greedySource_mass_lower_exactCap
        D hD Cmulti Sseq W Pgreedy hFsource hKTsource
  have hcrossFloor :
      (M : ENNReal) *
        ((Sseq.tau W.m : ENNReal) ^ (-lossEta) *
          selectedParentMassPopularCordobaCoreBudget
            (fullRefinementDatum D)
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
            Pgreedy k r hr A label KT) ≤
      (affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                Pgreedy k) r hr)
            label) * ((M : ENNReal) * floor)) *
        proposition66AInnerFactor (Sseq.tau W.m)
          (bucketShortA label) (bucketShortB label) M epsilon beta := by
    rw [show (M : ENNReal) * floor =
        (delta : ENNReal) ^ (2 * etaF) by
      dsimp only [floor]
      calc
        (M : ENNReal) *
            ((delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)) =
          ((delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)) *
            (M : ENNReal) := mul_comm _ _
        _ = (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.div_mul_cancel hM0 hMTop]
    simpa only [M] using hcross
  exact massPopularCrossEq46Budget_of_sourceFloor_crossMultiplied
    (fullRefinementDatum D)
    (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
    (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
    Pgreedy k r hr A label KT M hMpos hfloor hcrossFloor

#print axioms massPopularCrossEq46Budget_of_sourceFloor_crossMultiplied
#print axioms fullRefinement_sourceTau_exactKatzTaoCap_pos
#print axioms fullRefinement_sourceTau_greedySource_mass_lower_exactCap
#print axioms
  fullRefinement_sourceTau_massPopularCrossEq46Budget_of_exactCap

end Witness
end
end Family8FullRefinementSourceTauMassPopularEq46ExactCapV4
