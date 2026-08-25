import FamilyStickyGrounding.FamilyStickyScaleChainArbitraryRadiusBoundsV1
import FamilyStickyGrounding.FamilyStickyScaleChainParentFiberMassToFiberDeltaV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

open MeasureTheory
namespace FamilyStickyScaleChainParentNormalizerReverseProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassToFiberDeltaV1.StickyScaleCover

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Producing the reverse parent normalizer

For an intermediate cover `L`, its cross-scale cover `I`, and the upper
endpoint cover `U`, carrier containment already gives

`volume (parent_L k) <= volume (parent_U (I.parent k))`.

Thus the denominator in the upper parent concentration is automatically no
worse than the lower denominator.  The sole genuine extra input is weighted
sibling growth: the mass of the full upper fiber must be controlled by the
mass of the selected lower fiber.  This file packages exactly that one input,
constructs the concentration comparison from it, and also supplies a
data-dependent actual loss obtained from the finite fibers themselves.

The final finite model shows sharpness.  An `N`-to-one merge has exact reverse
growth `N`, while satisfying parent composition.  Consequently no universal
loss follows from parent maps and carrier containment alone; a uniform bound
on the actual loss requires branching or sibling-mass rigidity.
-/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  (S : FiniteScaleSequence delta depth)

/-! ## The automatic denominator comparison -/

/-- Parent carrier containment already gives the favorable comparison of the
two normalizing volumes. -/
theorem lowerParentVolume_le_upperParentVolume
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) :
    volume
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).coarse.tubes k).carrier <=
      volume
        ((upperEndpointCover C S m).coarse.tubes
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).carrier := by
  exact measure_mono
    ((rhoToUpperCover C S m rho hTauRho hRhoTheta).carrier_subset k hk)

/-- An active lower parent has a nonempty fine fiber.  Positive original tube
radius therefore makes the summed mass of that fiber positive. -/
theorem lowerFiberFamilyVolume_pos
    (hdelta : 0 < delta)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) :
    0 < familyVolume
      ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) := by
  let L := lowerScaleCover C S m rho hTauRho hRhoTheta
  obtain ⟨i, hiActive, hiParent⟩ := L.parent_surjective k hk
  have hiFiber : i ∈ L.fiber k :=
    (L.mem_fiber i k).2 ⟨hiActive, hiParent⟩
  unfold familyVolume
  rw [Finset.sum_pos_iff]
  refine ⟨⟨i, hiFiber⟩, Finset.mem_univ _, ?_⟩
  simpa [L, StickyScaleCover.fiberFamily,
    UniformTubeFamily.bodyFamily, Tube.coe_body] using
    (fine.tubes i).volume_pos hdelta

/-- Once upper-fiber mass growth is known, the reverse parent-normalizer
concentration comparison follows automatically.  The numerator uses the
supplied growth bound; the denominator uses literal parent containment. -/
theorem fiberParentConcentration_le_of_reverseFiberMass
    (loss : ENNReal)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse)
    (hmass :
      familyVolume
          ((upperEndpointCover C S m).fiberFamily
            ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) <=
        loss * familyVolume
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)) :
    concentration
        ((upperEndpointCover C S m).fiberFamily
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k))
        ((upperEndpointCover C S m).coarse.tubes
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).body <=
      loss *
        concentration
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).coarse.tubes k).body := by
  let L := lowerScaleCover C S m rho hTauRho hRhoTheta
  let U := upperEndpointCover C S m
  let I := rhoToUpperCover C S m rho hTauRho hRhoTheta
  let p : Fin U.coarseCard := I.parent k
  have hp : p ∈ U.activeCoarse := by
    dsimp [p, U, I, rhoToUpperCover, upperEndpointCover,
      CoherentStickyMultiscaleCover.intervalScaleCover]
    exact C.parent_mem rho (S.theta m)
      ((S.delta_le_tau m).trans hTauRho) hRhoTheta (S.theta_le_one m) k hk
  have hmass' :
      familyVolume (U.fiberFamily p) <=
        loss * familyVolume (L.fiberFamily k) := by
    simpa [L, U, I, p] using hmass
  have hvolume :
      volume (L.coarse.tubes k).carrier <=
        volume (U.coarse.tubes p).carrier := by
    simpa [L, U, I, p] using
      lowerParentVolume_le_upperParentVolume C S m rho
        hTauRho hRhoTheta k hk
  have hupper :
      concentration (U.fiberFamily p) (U.coarse.tubes p).body =
        familyVolume (U.fiberFamily p) /
          volume (U.coarse.tubes p).carrier := by
    calc
      concentration (U.fiberFamily p) (U.coarse.tubes p).body =
          parentFiberMassRatio U ⟨p, hp⟩ := by
        symm
        simpa [StickyScaleCover.activeCoarseFamily,
          UniformTubeFamily.bodyFamily] using
          parentFiberMassRatio_eq_concentration_parent U ⟨p, hp⟩
      _ = familyVolume (U.fiberFamily p) /
          volume (U.coarse.tubes p).carrier := by rfl
  have hlower :
      concentration (L.fiberFamily k) (L.coarse.tubes k).body =
        familyVolume (L.fiberFamily k) /
          volume (L.coarse.tubes k).carrier := by
    calc
      concentration (L.fiberFamily k) (L.coarse.tubes k).body =
          parentFiberMassRatio L ⟨k, hk⟩ := by
        symm
        simpa [StickyScaleCover.activeCoarseFamily,
          UniformTubeFamily.bodyFamily] using
          parentFiberMassRatio_eq_concentration_parent L ⟨k, hk⟩
      _ = familyVolume (L.fiberFamily k) /
          volume (L.coarse.tubes k).carrier := by rfl
  have hquotient :
      familyVolume (U.fiberFamily p) / volume (U.coarse.tubes p).carrier <=
        loss * (familyVolume (L.fiberFamily k) /
          volume (L.coarse.tubes k).carrier) := by
    calc
      familyVolume (U.fiberFamily p) / volume (U.coarse.tubes p).carrier <=
          (loss * familyVolume (L.fiberFamily k)) /
            volume (U.coarse.tubes p).carrier :=
        ENNReal.div_le_div_right hmass' _
      _ <= (loss * familyVolume (L.fiberFamily k)) /
            volume (L.coarse.tubes k).carrier :=
        ENNReal.div_le_div_left hvolume _
      _ = loss * (familyVolume (L.fiberFamily k) /
            volume (L.coarse.tubes k).carrier) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  have hresult :
      concentration (U.fiberFamily p) (U.coarse.tubes p).body <=
        loss * concentration (L.fiberFamily k) (L.coarse.tubes k).body := by
    rw [hupper, hlower]
    exact hquotient
  simpa [L, U, I, p] using hresult

/-! ## Minimal weighted sibling-growth certificate -/

/-- The only nonautomatic datum needed for the reverse normalizer.  It is a
weighted branching/rigidity statement: every upper fiber created by merging
siblings has mass at most `loss` times the mass of each selected active lower
fiber in that merge. -/
structure LargeIntervalReverseFiberMassGrowth
    (epsilon : Real) (loss : ENNReal) : Prop where
  mass_le : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    S.IsLarge epsilon m ->
      forall k : Fin
        (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard,
      k ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse ->
        familyVolume
            ((upperEndpointCover C S m).fiberFamily
              ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) <=
          loss * familyVolume
            ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)

namespace LargeIntervalReverseFiberMassGrowth

/-- The minimal weighted growth certificate fills the former raw
concentration field. -/
theorem fiber_parent_concentration_le
    {loss : ENNReal}
    (G : LargeIntervalReverseFiberMassGrowth C S epsilon loss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (hlarge : S.IsLarge epsilon m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) :
    concentration
        ((upperEndpointCover C S m).fiberFamily
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k))
        ((upperEndpointCover C S m).coarse.tubes
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).body <=
      loss *
        concentration
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).coarse.tubes k).body :=
  fiberParentConcentration_le_of_reverseFiberMass C S loss m rho
    hTauRho hRhoTheta k hk
    (G.mass_le m rho hTauRho hRhoTheta hlarge k hk)

end LargeIntervalReverseFiberMassGrowth

/-! ## An automatically computed actual loss -/

/-- The literal mass ratio at one legal intermediate parent.  Inactive
indices are totalized by zero. -/
def actualReverseFiberMassRatio
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard) :
    ENNReal :=
  if _hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse then
    familyVolume
        ((upperEndpointCover C S m).fiberFamily
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) /
      familyVolume
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)
  else 0

/-- The exact worst reverse fiber-mass ratio over all legal intermediate
radii.  This is computed from `C`; it is not an externally supplied
concentration callback. -/
def actualReverseParentNormalizerLoss : ENNReal :=
  ⨆ (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard),
      actualReverseFiberMassRatio C S m rho hTauRho hRhoTheta k

theorem actualReverseFiberMassRatio_le
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard) :
    actualReverseFiberMassRatio C S m rho hTauRho hRhoTheta k <=
      actualReverseParentNormalizerLoss C S := by
  exact le_iSup_of_le m <| le_iSup_of_le rho <|
    le_iSup_of_le hTauRho <| le_iSup_of_le hRhoTheta <|
      le_iSup_of_le k le_rfl

/-- At positive fine radius, the automatically computed worst ratio controls
every active upper fiber mass. -/
theorem upperFiberMass_le_actualReverseParentNormalizerLoss
    (hdelta : 0 < delta)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) :
    familyVolume
        ((upperEndpointCover C S m).fiberFamily
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) <=
      actualReverseParentNormalizerLoss C S *
        familyVolume
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) := by
  have hratioRaw :=
    actualReverseFiberMassRatio_le C S m rho hTauRho hRhoTheta k
  have hratio :
      familyVolume
          ((upperEndpointCover C S m).fiberFamily
            ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) /
          familyVolume
            ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) <=
        actualReverseParentNormalizerLoss C S := by
    simpa [actualReverseFiberMassRatio, hk] using hratioRaw
  have hlowerPos :=
    lowerFiberFamilyVolume_pos C S hdelta m rho hTauRho hRhoTheta k hk
  calc
    familyVolume
          ((upperEndpointCover C S m).fiberFamily
            ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) =
        (familyVolume
            ((upperEndpointCover C S m).fiberFamily
              ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) /
          familyVolume
            ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)) *
          familyVolume
            ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) := by
      symm
      exact ENNReal.div_mul_cancel hlowerPos.ne'
        (familyVolume_ne_top
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k))
    _ <= actualReverseParentNormalizerLoss C S *
          familyVolume
            ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) :=
      by gcongr

/-- The actual worst ratio automatically produces the minimal weighted
growth certificate. -/
theorem actualReverseFiberMassGrowth
    (hdelta : 0 < delta) :
    LargeIntervalReverseFiberMassGrowth C S epsilon
      (actualReverseParentNormalizerLoss C S) where
  mass_le := by
    intro m rho hTauRho hRhoTheta _hlarge k hk
    exact upperFiberMass_le_actualReverseParentNormalizerLoss C S hdelta
      m rho hTauRho hRhoTheta k hk

/-! ## Rebuilding the arbitrary-radius input with no raw normalizer field -/

/-- All local inputs other than reverse fiber-mass growth.  In particular,
this structure contains no parent-normalizer concentration inequality. -/
structure LargeIntervalLocalGeometry
    (epsilon : Real) (massLoss bodyLoss katzTaoLoss : ENNReal) : Prop where
  parent_compatible : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : iota),
    i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)
  parentFiberMass : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    S.IsLarge epsilon m ->
      ParentFiberMassMonotonicity
        (rhoToUpperCover C S m rho hTauRho hRhoTheta) massLoss
  thickeningVolume : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    S.IsLarge epsilon m ->
      CapturingThickeningVolumeControl
        (rhoToUpperCover C S m rho hTauRho hRhoTheta) bodyLoss
  katzTaoLoss_bound : massLoss * bodyLoss <= katzTaoLoss

namespace LargeIntervalLocalGeometry

/-- Supplying only weighted sibling growth reconstructs the full
`LargeIntervalCoverCoherence` consumed by the existing arbitrary-radius
theorems. -/
theorem toLargeIntervalCoverCoherence
    {reverseLoss massLoss bodyLoss katzTaoLoss : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (G : LargeIntervalReverseFiberMassGrowth C S epsilon reverseLoss) :
    LargeIntervalCoverCoherence C S epsilon
      reverseLoss katzTaoLoss massLoss bodyLoss where
  parent_compatible := D.parent_compatible
  fiber_parent_concentration_le := by
    intro m rho hTauRho hRhoTheta hlarge k hk
    exact LargeIntervalReverseFiberMassGrowth.fiber_parent_concentration_le C S G m rho hTauRho hRhoTheta
      hlarge k hk
  parentFiberMass := D.parentFiberMass
  thickeningVolume := D.thickeningVolume
  katzTaoLoss_bound := D.katzTaoLoss_bound

/-- Positive fine radius removes even the weighted-growth certificate by
using the actual worst ratio computed above. -/
theorem toLargeIntervalCoverCoherenceWithActualLoss
    {massLoss bodyLoss katzTaoLoss : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (hdelta : 0 < delta) :
    LargeIntervalCoverCoherence C S epsilon
      (actualReverseParentNormalizerLoss C S)
      katzTaoLoss massLoss bodyLoss :=
  LargeIntervalLocalGeometry.toLargeIntervalCoverCoherence C S D
    (actualReverseFiberMassGrowth C S (epsilon := epsilon) hdelta)

end LargeIntervalLocalGeometry

/-- End-to-end arbitrary-radius endpoint with the reverse normalizer generated
from actual fiber masses.  No raw concentration comparison is an input. -/
theorem isStickyAtEveryScale_of_actualReverseParentNormalizerLoss
    (hdepth : 0 < depth) (hdelta : 0 < delta)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError) :
    C.base.IsStickyAtEveryScale
      (actualReverseParentNormalizerLoss C S * frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_discreteAllLarge C S hdepth
    (LargeIntervalLocalGeometry.toLargeIntervalCoverCoherenceWithActualLoss C S D hdelta) B

/-! ## Sharp finite obstruction -/

/-- Finite version of the collapsed cross-parent map. -/
def collapsedCrossParentFin {N : Nat} : Fin N -> Fin 1 := fun _ => 0
theorem collapsed_parent_compatible_fin {N : Nat}
    (i : SplitSource N) :
    collapsedUpperParentFin i =
      collapsedCrossParentFin (identityLowerParent i) :=
  rfl

/-- In the collapsed model the upper/lower fiber growth is exactly `N`, not
merely bounded below by `N`. -/
theorem collapsed_reverse_fiber_growth_exact
    {N : Nat} (k : Fin N) :
    (assignmentFiber (collapsedUpperParentFin (N := N)) (0 : Fin 1)).card =
      N * (assignmentFiber (identityLowerParent (N := N)) k).card := by
  rw [collapsedUpperFiber_card, identityLowerFiber_card, Nat.mul_one]

/-- Any claimed reverse-growth factor for the `N`-to-one merge must be at
least `N`. -/
theorem collapsed_reverse_fiber_growth_forces
    {N loss : Nat} (k : Fin N)
    (hgrowth :
      (assignmentFiber (collapsedUpperParentFin (N := N)) (0 : Fin 1)).card <=
        loss * (assignmentFiber (identityLowerParent (N := N)) k).card) :
    N <= loss := by
  simpa [collapsedUpperFiber_card, identityLowerFiber_card] using hgrowth

/-- Parent composition allows arbitrarily large exact weighted sibling
growth.  This is the sharp obstruction to replacing the actual loss by a
universal constant without branching or sibling-mass rigidity. -/
theorem no_uniform_reverse_fiber_growth (loss : Nat) :
    exists (N : Nat) (k : Fin N),
      (forall i : SplitSource N,
        collapsedUpperParentFin i =
          collapsedCrossParentFin (identityLowerParent i)) ∧
      loss * (assignmentFiber (identityLowerParent (N := N)) k).card <
        (assignmentFiber
          (collapsedUpperParentFin (N := N)) (0 : Fin 1)).card := by
  let N := loss + 1
  let k : Fin N := ⟨0, by simp [N]⟩
  refine ⟨N, k, ?_, ?_⟩
  · exact collapsed_parent_compatible_fin
  · rw [identityLowerFiber_card, collapsedUpperFiber_card]
    simp only [Nat.mul_one, N]
    exact Nat.lt_succ_self loss

#print axioms lowerParentVolume_le_upperParentVolume
#print axioms lowerFiberFamilyVolume_pos
#print axioms fiberParentConcentration_le_of_reverseFiberMass
#print axioms LargeIntervalReverseFiberMassGrowth.fiber_parent_concentration_le
#print axioms actualReverseFiberMassRatio_le
#print axioms upperFiberMass_le_actualReverseParentNormalizerLoss
#print axioms actualReverseFiberMassGrowth
#print axioms LargeIntervalLocalGeometry.toLargeIntervalCoverCoherence
#print axioms LargeIntervalLocalGeometry.toLargeIntervalCoverCoherenceWithActualLoss
#print axioms isStickyAtEveryScale_of_actualReverseParentNormalizerLoss
#print axioms collapsed_reverse_fiber_growth_exact
#print axioms collapsed_reverse_fiber_growth_forces
#print axioms no_uniform_reverse_fiber_growth

end

end FamilyStickyScaleChainParentNormalizerReverseProducerV1
