import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import FamilyStickyGrounding.FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowGeometryV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllFrostmanStickyUnionProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family6CanonicalFrostmanConstantCoreV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
open FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowGeometryV1

noncomputable section

/-!
# The strongest current Sticky-to-union adapter

The formal Sticky development produces actual at-every-scale covers and the
Family 7 development produces the difficult local incidence/cardinality
endpoint.  The two are not yet joined by a theorem bounding the global
canonical overlap-row scale.  This file closes every deterministic step on
the other side of that seam.

For a Sticky cover whose active fine set is the whole actual family, parent
aggregation preserves the literal source shaded union.  Katz--Tao at the
chosen scale and the callback-free canonical row geometry then give a
division-free source shading-mass bound.  A density lower bound from
`FrostmanHypotheses`, the resulting lower bound on actual family volume, and
an explicit power budget for the resulting canonical factor imply the paper
lower bound `delta^(gamma/2) <= volume shadedUnion`.

No union lower bound, average-multiplicity conclusion, or equivalent
division statement occurs among the hypotheses below.
-/

/-- The complete multiplicative loss supplied by one Sticky scale after
parent aggregation, using the explicit canonical overlap-row geometry. -/
def stickyCanonicalFineMultiplicityFactor
    {delta rho : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (fiberCap : Nat) (katzTaoError : ENNReal) : ENNReal :=
  (fiberCap : ENNReal) *
    (katzTaoError * canonicalOverlapScaleFactor
      (parentAggregatedShading S Y))

/-- If every fine index is active, restricting a shading to the active
subtype preserves its literal shaded union. -/
theorem activeFineShading_shadedUnion_eq_of_activeFine_eq_univ
    {delta rho : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ) :
    (activeFineShading S Y).shadedUnion = Y.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i.1, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hiActive : i ∈ S.activeFine := by
      rw [hactive]
      exact Finset.mem_univ i
    exact Set.mem_iUnion.mpr ⟨⟨i, hiActive⟩, hi⟩

/-- Full activity also preserves the exact summed shading mass. -/
theorem activeFineShading_shadingMass_eq_of_activeFine_eq_univ
    {delta rho : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ) :
    (activeFineShading S Y).shadingMass = Y.shadingMass := by
  classical
  let e : {i // i ∈ S.activeFine} ≃ iota :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, by rw [hactive]; exact Finset.mem_univ i⟩
      left_inv := fun i => Subtype.ext rfl
      right_inv := fun _ => rfl }
  unfold Shading.shadingMass
  exact Fintype.sum_equiv e
    (fun i : {i // i ∈ S.activeFine} =>
      volume ((activeFineShading S Y).carrier i))
    (fun i : iota => volume (Y.carrier i))
    (fun _ => rfl)

/-- One actual Sticky scale gives a division-free mass-to-union estimate on
the original actual shading.  The canonical overlap majorant, active rows,
and convex containers are all constructed in the imported Family 6/Sticky
geometry module; only their explicit scalar size remains in the factor. -/
theorem shadingMass_le_stickyCanonicalFactor_mul_shadedUnion
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (cover : StickyMultiscaleCover fine)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (Y : Shading fine.bodyFamily)
    (hactive : (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (fiberCap : Nat)
    (hfiber : ∀ k :
      {k // k ∈ (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k).card ≤ fiberCap) :
    Y.shadingMass ≤
      stickyCanonicalFineMultiplicityFactor
          (cover.cover rho hdeltaRho hrhoOne) Y fiberCap katzTaoError *
        volume Y.shadedUnion := by
  let S := cover.cover rho hdeltaRho hrhoOne
  let R := canonicalKatzTaoOverlapRowGeometry
    (parentAggregatedShading S Y)
  have hparent :
      (parentAggregatedShading S Y).shadingMass ≤
        (katzTaoError * canonicalOverlapScaleFactor
          (parentAggregatedShading S Y)) *
          volume (parentAggregatedShading S Y).shadedUnion := by
    simpa only [R, canonicalKatzTaoOverlapRowGeometry] using
      (FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1.StickyScaleCover.shadingMass_le_of_isKatzTaoAtScale
        S (hsticky.katzTao rho hdeltaRho hrhoOne)
          (parentAggregatedShading S Y) R)
  have hfineParent :
      (activeFineShading S Y).shadingMass ≤
        (fiberCap : ENNReal) * (parentAggregatedShading S Y).shadingMass := by
    simpa only [nsmul_eq_mul] using
      (activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
        S Y fiberCap hfiber)
  rw [← activeFineShading_shadingMass_eq_of_activeFine_eq_univ
    S Y hactive]
  calc
    (activeFineShading S Y).shadingMass ≤
        (fiberCap : ENNReal) * (parentAggregatedShading S Y).shadingMass :=
      hfineParent
    _ ≤ (fiberCap : ENNReal) *
        ((katzTaoError * canonicalOverlapScaleFactor
          (parentAggregatedShading S Y)) *
            volume (parentAggregatedShading S Y).shadedUnion) := by
      exact mul_le_mul_right hparent _
    _ = stickyCanonicalFineMultiplicityFactor S Y fiberCap katzTaoError *
        volume Y.shadedUnion := by
      rw [parentAggregatedShading_shadedUnion S Y,
        activeFineShading_shadedUnion_eq_of_activeFine_eq_univ S Y hactive]
      simp only [stickyCanonicalFineMultiplicityFactor, mul_assoc]

/-! ## Frostman normalization from the actual data -/

/-- The three-dimensional closed unit ball has volume at least one.  This is
the only ambient-volume normalization used below. -/
theorem one_le_volume_unitBallBody :
    (1 : ENNReal) ≤ volume (unitBallBody : Set Space) := by
  rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
  norm_num
  nlinarith [Real.pi_gt_three]

/-- Positive Frostman density forces the indexed actual family volume to be
nonzero. -/
theorem actualFamilyVolume_ne_zero_of_frostmanDensity
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {eta : Real} (hF : FrostmanHypotheses D eta) :
    D.actualFamilyVolume ≠ 0 := by
  have hpowPos : 0 < (delta : ENNReal) ^ eta :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  have hdensityPos : 0 < D.shading.shadingDensity :=
    hpowPos.trans_le hF.1
  intro hvolume
  have hfamilyVolume : familyVolume D.family.bodyFamily = 0 := by
    simpa only [ActualTubeDatum.actualFamilyVolume] using hvolume
  have hmassZero : D.shading.shadingMass = 0 :=
    nonpos_iff_eq_zero.mp
      (D.shading.shadingMass_le_familyVolume.trans_eq hfamilyVolume)
  have hdensityZero : D.shading.shadingDensity = 0 := by
    simp [Shading.shadingDensity, hfamilyVolume, hmassZero]
  exact (ne_of_gt hdensityPos) hdensityZero

/-- A nonzero indexed actual family volume supplies an actual tube index. -/
theorem nonempty_of_actualFamilyVolume_ne_zero
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hvolume : D.actualFamilyVolume ≠ 0) : Nonempty iota := by
  by_contra hnot
  let _ : IsEmpty iota := not_nonempty_iff.mp hnot
  apply hvolume
  simp [ActualTubeDatum.actualFamilyVolume, familyVolume]

/-- The actual Frostman condition itself supplies the missing family-volume
normalization.  Applying it to one tube body, cancelling that tube's positive
finite volume, and using the volume of the ambient unit ball gives
`delta^eta ≤ actualFamilyVolume`. -/
theorem delta_rpow_eta_le_actualFamilyVolume_of_frostman
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {eta : Real} (hF : FrostmanHypotheses D eta) :
    (delta : ENNReal) ^ eta ≤ D.actualFamilyVolume := by
  classical
  have hvolume0 := actualFamilyVolume_ne_zero_of_frostmanDensity D hD hF
  let i : iota := Classical.choice
    (nonempty_of_actualFamilyVolume_ne_zero D hvolume0)
  let Kprime : ConvexBody Space := (D.family.tubes i).body
  have hsubset : (Kprime : Set Space) ⊆ (unitBallBody : Set Space) := by
    simpa only [Kprime, Tube.coe_body, coe_unitBallBody] using
      hD.contained_in_unit_ball i
  have htubeMass :
      volume (D.family.tubes i).carrier ≤
        containedMass D.family.bodyFamily Kprime := by
    unfold containedMass
    exact Finset.single_le_sum
      (fun j _ => show
        (0 : ENNReal) ≤ volume (D.family.bodyFamily j : Set Space) from bot_le)
      ((mem_containedIndices D.family.bodyFamily Kprime i).2 (by
        exact subset_rfl))
  have hambient :
      containedMass D.family.bodyFamily unitBallBody =
        D.actualFamilyVolume := by
    simpa only [ActualTubeDatum.actualFamilyVolume] using
      (containedMass_eq_familyVolume_of_contained
        D.family.bodyFamily unitBallBody (fun j => by
          simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body,
            coe_unitBallBody] using hD.contained_in_unit_ball j))
  have hcross := IsFrostmanIn.cross_le hF.2 hsubset
  rw [hambient] at hcross
  have hchain :
      volume (D.family.tubes i).carrier *
          volume (unitBallBody : Set Space) ≤
        ((delta : ENNReal) ^ (-eta) * D.actualFamilyVolume) *
          volume (D.family.tubes i).carrier := by
    calc
      volume (D.family.tubes i).carrier *
          volume (unitBallBody : Set Space) ≤
        containedMass D.family.bodyFamily Kprime *
          volume (unitBallBody : Set Space) :=
        mul_le_mul_left htubeMass _
      _ ≤ ((delta : ENNReal) ^ (-eta) * D.actualFamilyVolume) *
          volume (D.family.tubes i).carrier := by
        simpa only [Kprime, UniformTubeFamily.bodyFamily, Tube.coe_body] using
          hcross
  have htube0 : volume (D.family.tubes i).carrier ≠ 0 :=
    ne_of_gt ((D.family.tubes i).volume_pos hD.delta_pos)
  have htubeTop : volume (D.family.tubes i).carrier ≠ ⊤ :=
    (D.family.tubes i).volume_lt_top.ne
  have hbase :
      volume (unitBallBody : Set Space) ≤
        (delta : ENNReal) ^ (-eta) * D.actualFamilyVolume := by
    apply (ENNReal.mul_le_mul_iff_left htube0 htubeTop).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hchain
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hD.delta_pos)
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    (delta : ENNReal) ^ eta =
        (delta : ENNReal) ^ eta * 1 := by simp
    _ ≤ (delta : ENNReal) ^ eta * volume (unitBallBody : Set Space) :=
      mul_le_mul_right one_le_volume_unitBallBody _
    _ ≤ (delta : ENNReal) ^ eta *
        ((delta : ENNReal) ^ (-eta) * D.actualFamilyVolume) :=
      mul_le_mul_right hbase _
    _ = D.actualFamilyVolume := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 hdTop]
      simp

/-- Frostman density and the preceding actual-family-volume lower bound give
the genuine `delta^(2 eta)` lower bound for the multiplicity-counted shaded
mass. -/
theorem delta_rpow_two_eta_le_shadingMass_of_frostman
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {eta : Real} (hF : FrostmanHypotheses D eta) :
    (delta : ENNReal) ^ (2 * eta) ≤ D.shading.shadingMass := by
  have hvolume := delta_rpow_eta_le_actualFamilyVolume_of_frostman D hD hF
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hD.delta_pos)
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [show 2 * eta = eta + eta by ring, ENNReal.rpow_add _ _ hd0 hdTop]
  calc
    (delta : ENNReal) ^ eta * (delta : ENNReal) ^ eta ≤
        D.shading.shadingDensity * D.actualFamilyVolume :=
      mul_le_mul hF.1 hvolume bot_le bot_le
    _ = D.shading.shadingMass := by
      simpa only [ActualTubeDatum.actualFamilyVolume] using
        (shadingDensity_mul_familyVolume D.shading)

/-- Explicit small-base exponent bookkeeping: a `delta^(-zeta)` bound on
the complete Sticky factor is paid for by the gap between `2 * eta` and
`gamma / 2`. -/
theorem stickyFactor_mul_targetPower_le_twoDensityPower
    {delta : NNReal} {factor : ENNReal} {eta zeta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfactor : factor ≤ (delta : ENNReal) ^ (-zeta))
    (hexponent : 2 * eta + zeta ≤ gamma / 2) :
    factor * (delta : ENNReal) ^ (gamma / 2) ≤
      (delta : ENNReal) ^ (2 * eta) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hdelta)
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have heta : 2 * eta ≤ gamma / 2 - zeta := by linarith
  calc
    factor * (delta : ENNReal) ^ (gamma / 2) ≤
        (delta : ENNReal) ^ (-zeta) *
          (delta : ENNReal) ^ (gamma / 2) :=
      mul_le_mul_left hfactor _
    _ = (delta : ENNReal) ^ ((-zeta) + gamma / 2) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^ (gamma / 2 - zeta) := by
      congr 1
      ring
    _ ≤ (delta : ENNReal) ^ (2 * eta) :=
      ENNReal.rpow_le_rpow_of_exponent_ge
        (by exact_mod_cast hdeltaOne) heta

/-- The strongest currently derivable all-Frostman union adapter on an
actual datum.  Besides genuine Sticky data, it exposes only the explicit
power cap on the canonical fine multiplicity factor.  That cap is the first
presently unproved Family7-to-Sticky seam, so this theorem is deliberately
named an adapter rather than the completed paper Sticky theorem. -/
theorem allFrostman_unionLower_of_stickyCanonicalFactor
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {eta zeta gamma : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (hactive : (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (fiberCap : Nat)
    (hfiber : ∀ k :
      {k // k ∈ (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k).card ≤ fiberCap)
    (hexponent : 2 * eta + zeta ≤ gamma / 2)
    (hfactor :
      stickyCanonicalFineMultiplicityFactor
          (cover.cover rho hdeltaRho hrhoOne) D.shading fiberCap
            katzTaoError ≤
        (delta : ENNReal) ^ (-zeta)) :
    (delta : ENNReal) ^ (gamma / 2) ≤
      volume D.shading.shadedUnion := by
  let factor := stickyCanonicalFineMultiplicityFactor
    (cover.cover rho hdeltaRho hrhoOne) D.shading fiberCap katzTaoError
  have hmassUpper :
      D.shading.shadingMass ≤ factor * volume D.shading.shadedUnion := by
    exact shadingMass_le_stickyCanonicalFactor_mul_shadedUnion
      cover hsticky rho hdeltaRho hrhoOne D.shading hactive fiberCap hfiber
  have hdeltaOne : delta ≤ 1 :=
    hD.delta_le_half.trans (by norm_num)
  have hpower :
      factor * (delta : ENNReal) ^ (gamma / 2) ≤
        (delta : ENNReal) ^ (2 * eta) :=
    stickyFactor_mul_targetPower_le_twoDensityPower
      hD.delta_pos hdeltaOne hfactor hexponent
  have hmassLower :
      (delta : ENNReal) ^ (2 * eta) ≤ D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  have hfactorTargetMass :
      factor * (delta : ENNReal) ^ (gamma / 2) ≤
        D.shading.shadingMass :=
    hpower.trans hmassLower
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hD.delta_pos)
  have hfactorTop : factor ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top) hfactor
  have hmassPos : 0 < D.shading.shadingMass := by
    have hpowPos : 0 < (delta : ENNReal) ^ (2 * eta) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
    exact hpowPos.trans_le hmassLower
  have hfactor0 : factor ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmassUpper
    exact (not_le_of_gt hmassPos) hmassUpper
  apply (ENNReal.mul_le_mul_iff_right hfactor0 hfactorTop).mp
  exact hfactorTargetMass.trans hmassUpper

/-- More directly usable conditional form: bound the canonical row scale by
`A`, and budget the explicit finite losses against `delta^(-zeta)`.  The
scale cap remains the exact open geometric seam. -/
theorem allFrostman_unionLower_of_stickyCanonicalScaleCap
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {eta zeta gamma : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError A : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (hactive : (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (fiberCap : Nat)
    (hfiber : ∀ k :
      {k // k ∈ (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k).card ≤ fiberCap)
    (hexponent : 2 * eta + zeta ≤ gamma / 2)
    (hscale : canonicalOverlapScaleFactor
      (parentAggregatedShading
        (cover.cover rho hdeltaRho hrhoOne) D.shading) ≤ A)
    (hloss : (fiberCap : ENNReal) * (katzTaoError * A) ≤
      (delta : ENNReal) ^ (-zeta)) :
    (delta : ENNReal) ^ (gamma / 2) ≤
      volume D.shading.shadedUnion := by
  apply allFrostman_unionLower_of_stickyCanonicalFactor
    D hD hF cover hsticky rho hdeltaRho hrhoOne hactive fiberCap hfiber
      hexponent
  unfold stickyCanonicalFineMultiplicityFactor
  exact
    (mul_le_mul_right (mul_le_mul_right hscale katzTaoError)
      (fiberCap : ENNReal)).trans hloss

#print axioms activeFineShading_shadedUnion_eq_of_activeFine_eq_univ
#print axioms activeFineShading_shadingMass_eq_of_activeFine_eq_univ
#print axioms shadingMass_le_stickyCanonicalFactor_mul_shadedUnion
#print axioms stickyFactor_mul_targetPower_le_twoDensityPower
#print axioms allFrostman_unionLower_of_stickyCanonicalFactor
#print axioms allFrostman_unionLower_of_stickyCanonicalScaleCap

end

end Family8AllFrostmanStickyUnionProducerV1
