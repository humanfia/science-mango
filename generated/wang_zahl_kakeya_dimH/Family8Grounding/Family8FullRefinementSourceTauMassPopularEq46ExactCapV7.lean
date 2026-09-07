import Family8Grounding.Family8FullRefinementSourceTauMassPopularEq46ExactCapV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauMassPopularEq46ExactCapV7

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
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
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
open Family8FullRefinementSourceTauMassPopularEq46ExactCapV4.Witness

noncomputable section

/-!
# Honest source-cap cancellation in the mass-popular Equation (46) budget

The source fibre cap and the actual uniform `tubesPerPlank` count have
different geometric meanings.  Only the source cap is cancelled against the
source-mass floor; the actual count remains unchanged in Equation (46).
-/

/-- A finite positive natural source cap cancels from the source floor.  The
right-hand factor `inner` is deliberately arbitrary, so in particular it can
retain a distinct actual uniform tube count. -/
theorem cancel_positive_nat_sourceCap
    (sourceCap : Nat) (hsourceCapPos : 0 < sourceCap)
    {core J sourceFloor sourceFactor inner : ENNReal}
    (hsource : J * sourceFloor ≤ sourceFactor)
    (hcross : (sourceCap : ENNReal) * core ≤
      (J * ((sourceCap : ENNReal) * sourceFloor)) * inner) :
    core ≤ sourceFactor * inner := by
  have hcap0 : (sourceCap : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hsourceCapPos
  have hcapTop : (sourceCap : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  apply (ENNReal.mul_le_mul_iff_left hcap0 hcapTop).mp
  calc
    core * (sourceCap : ENNReal) =
        (sourceCap : ENNReal) * core := mul_comm _ _
    _ ≤ (J * ((sourceCap : ENNReal) * sourceFloor)) * inner := hcross
    _ = ((J * sourceFloor) * inner) * (sourceCap : ENNReal) := by
      ac_rfl
    _ ≤ (sourceFactor * inner) * (sourceCap : ENNReal) := by
      exact mul_le_mul' (mul_le_mul' hsource le_rfl) le_rfl

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem fullRefinement_sourceTau_massPopularCrossEq46Budget_of_exactSourceCap
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
    (tubesPerPlank : Nat)
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
          tubesPerPlank epsilon beta) :
    MassPopularCrossEq46Budget
      (fullRefinementDatum D)
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      Pgreedy k r hr A label KT lossEta
      tubesPerPlank epsilon beta := by
  let S := tauScaleCover (fullRefinementDatum D) Cmulti Sseq W
  let hrho : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  let M := katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
    ((delta : ENNReal) ^ (-etaKT))
  let sourceFloor : ENNReal :=
    (delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)
  let J := affineJacobian
    (bucketNormalizedAffineEquiv
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho Pgreedy k) r hr)
      label)
  let core := (Sseq.tau W.m : ENNReal) ^ (-lossEta) *
    selectedParentMassPopularCordobaCoreBudget
      (fullRefinementDatum D) S hrho Pgreedy k r hr A label KT
  let inner := proposition66AInnerFactor (Sseq.tau W.m)
    (bucketShortA label) (bucketShortB label)
    tubesPerPlank epsilon beta
  have hMpos : 0 < M := by
    simpa only [M] using
      fullRefinement_sourceTau_exactKatzTaoCap_pos
        D hD Cmulti Sseq W hFsource hKTsource
  have hM0 : (M : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMpos
  have hMTop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hfloor : sourceFloor ≤
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S (fullRefinementDatum D).shading)
        (greedyParentFactorization S Pgreedy).index.fine).shading.shadingMass := by
    simpa only [S, M, sourceFloor] using
      fullRefinement_sourceTau_greedySource_mass_lower_exactCap
        D hD Cmulti Sseq W Pgreedy hFsource hKTsource
  have hsource : J * sourceFloor ≤
      selectedParentMassPopularSourceFactor
        (fullRefinementDatum D) S hrho Pgreedy k r hr label := by
    unfold selectedParentMassPopularSourceFactor
    exact mul_le_mul' le_rfl hfloor
  have hcrossFloor : (M : ENNReal) * core ≤
      (J * ((M : ENNReal) * sourceFloor)) * inner := by
    rw [show (M : ENNReal) * sourceFloor =
        (delta : ENNReal) ^ (2 * etaF) by
      dsimp only [sourceFloor]
      calc
        (M : ENNReal) *
            ((delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)) =
          ((delta : ENNReal) ^ (2 * etaF) / (M : ENNReal)) *
            (M : ENNReal) := mul_comm _ _
        _ = (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.div_mul_cancel hM0 hMTop]
    simpa only [S, hrho, M, J, core, inner] using hcross
  have hbudget := cancel_positive_nat_sourceCap M hMpos hsource hcrossFloor
  simpa only [MassPopularCrossEq46Budget, S, hrho, core, inner] using hbudget

#print axioms cancel_positive_nat_sourceCap
#print axioms
  fullRefinement_sourceTau_massPopularCrossEq46Budget_of_exactSourceCap

end Witness
end
end Family8FullRefinementSourceTauMassPopularEq46ExactCapV7
