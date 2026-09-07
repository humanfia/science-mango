import Family8Grounding.Family8Family7FirstCrossingActiveIndexGraphFrostmanAssemblyV4

/-!
# Structural finiteness of a FirstCrossing graph coefficient, V5

V4 is frozen after its deeply nested dependent `let` binder failed to parse.
This successor states the actual mathematical lemma generically on a literal
factorization, shading, assembly, and chosen active coarse index.  The active
bundle supplies those exact objects and its source-mass certificate directly.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingActiveIndexGraphFrostmanConstantFiniteV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FirstActualCrossingNormalizedFrostmanV2
open Family8FirstActualCrossingNormalizedFrostmanV2.FirstActualNormalizedCrossingWitness
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

universe u v

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

/-- Nonzero source mass, a chosen active coarse index, and the positive
FirstCrossing scales force the exact graph Frostman coefficient to be finite.
This statement is independent of how the literal factorization was built. -/
theorem firstCrossing_graphFrostmanConstant_ne_top_of_sourceMass
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    (Y : Shading F.bodyFamily)
    {r : Real} (A : Assembly P Y r)
    (k : kappa) (hk : k ∈ P.index.coarse)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass ≠ 0) :
    let baseLoss : ENNReal :=
      (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
    let d : ENNReal :=
      (sourceActiveFineShading P Y).shadingDensity / baseLoss
    let graphLoss : ENNReal :=
      ((3 * verticalGraphCBucketLoss
        (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
    let frostmanC : ENNReal :=
      (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)
    frostmanC * (d⁻¹ * graphLoss) ≠ ∞ := by
  dsimp only
  let baseLoss : ENNReal :=
    (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  let d : ENNReal :=
    (sourceActiveFineShading P Y).shadingDensity / baseLoss
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss
      (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
  let frostmanC : ENNReal :=
    (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)
  have hsourceMass :
      (sourceActiveFineShading P Y).shadingMass ≠ 0 := by
    rw [sourceActiveFineShading_shadingMass]
    exact hsource
  have hsourceVolume : familyVolume (sourceActiveFineFamily P) ≠ 0 := by
    intro hzero
    apply hsourceMass
    exact le_antisymm
      ((sourceActiveFineShading P Y).shadingMass_le_familyVolume.trans_eq
        hzero)
      bot_le
  have hsourceDensity0 :
      (sourceActiveFineShading P Y).shadingDensity ≠ 0 := by
    unfold Shading.shadingDensity
    exact ENNReal.div_ne_zero.mpr
      ⟨hsourceMass, familyVolume_ne_top (sourceActiveFineFamily P)⟩
  have hloss0 : (A.loss : ENNReal) ≠ 0 := by
    intro hzero
    apply hsourceMass
    apply le_antisymm
    · have hretained :=
        sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
      simpa only [hzero, zero_mul] using hretained
    · exact bot_le
  have hcard0 : (P.index.coarse.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨k, hk⟩
  have hbaseTop : baseLoss ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top A.loss)
      (ENNReal.natCast_ne_top P.index.coarse.card)
  have hd0 : d ≠ 0 := by
    exact ENNReal.div_ne_zero.mpr
      ⟨hsourceDensity0, hbaseTop⟩
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < W.rho :=
    htau.trans_le (actualDatum_tau_le_of_isBuffered
      D hD S hepsilon W.m W.rho W.buffered)
  have hratio0 :
      (((W.rho / S.tau W.m : NNReal) : ENNReal)) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (div_pos hrho htau).ne'
  have hfrostmanTop : frostmanC ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_ne_zero hratio0 ENNReal.coe_ne_top
  have hgraphLossTop : graphLoss ≠ ∞ := by
    exact ENNReal.natCast_ne_top _
  exact ENNReal.mul_ne_top hfrostmanTop
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hd0) hgraphLossTop)

#print axioms firstCrossing_graphFrostmanConstant_ne_top_of_sourceMass

end
end Family8Family7FirstCrossingActiveIndexGraphFrostmanConstantFiniteV5
