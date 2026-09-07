import Family8Grounding.Family8EighthNormalizedKatzTaoAmbientFrostmanV2
import Family8Grounding.Family8ParentwiseBadParentFactorReplacementV1
import Family8Grounding.Family8StickySelectedFiberContractedJohnNormalizedKatzTaoV1
import Family8Grounding.Family8StickySelectedFiberLocalFrostmanKatzTaoV1
import Mathlib.Tactic

/-!
# Same-selected Frostman transport to the literal bad-parent fresh child

This module transports a Frostman certificate on one already selected source
fibre through the actual contracted-John proxy and the honest eighth
normalization.  The target is definitionally the literal
`badParentFreshSuccessorDatum` on the same selected indices.  No identity
cover or transported source hierarchy is asserted.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentFreshProxyFrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8AmbientFamilyVolumeDensityV2
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickySelectedFiberContractedJohnNormalizedKatzTaoV1
open Family8StickySelectedFiberLocalFrostmanKatzTaoV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The exact Katz--Tao constant obtained from the selected source Frostman
certificate, the actual parent density, the contracted-John proxy loss, and
the fixed factor `128` of eighth normalization. -/
def badParentFreshProxyKatzTaoConstant
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (C : ENNReal) : ENNReal :=
  128 * stickyFiberContractedJohnProxyKatzTaoConstant
    S hrho hrhoOne q
      (C * ambientFamilyVolumeDensity
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q))

/-- The exact unit-ball Frostman constant for the literal fresh datum.  Its
denominator is the actual family volume of that same datum, not a cardinality
or a synthetic proxy mass. -/
def badParentFreshProxyFrostmanConstant
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (C : ENNReal) : ENNReal :=
  badParentFreshProxyKatzTaoConstant
      S hrho hrhoOne q selected C *
    volume (unitBallBody : Set Space) /
      familyVolume
        (badParentFreshSuccessorDatum
          S Y hrho hrhoOne q selected).family.bodyFamily

/-- A Frostman certificate on the literal selected source fibre transports
to global Katz--Tao control on the actual eighth-normalized fresh datum, on
exactly the same selected subtype. -/
theorem badParentFreshSuccessorDatum_isKatzTao_of_source_isFrostmanIn
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {C : ENNReal}
    (hSource : IsFrostmanIn C
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q)) :
    IsKatzTao
      (badParentFreshProxyKatzTaoConstant
        S hrho hrhoOne q selected C)
      (badParentFreshSuccessorDatum
        S Y hrho hrhoOne q selected).family.bodyFamily := by
  have hSourceKT : IsKatzTao
      (C * ambientFamilyVolumeDensity
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q))
      (activeSubtypeFamily (S.fiberFamily q.1) selected) :=
    selectedFiber_isKatzTao_of_isFrostmanIn
      S hrho q selected hSource
  have hFreshKT :=
    selectedFiberContractedJohn_restrictEighthNormalized_isKatzTao
      S Y hrho hrhoOne hdelta hdeltaHalf hdeltaRho
        q selected hSourceKT
  simpa only [badParentFreshProxyKatzTaoConstant,
    badParentFreshSuccessorDatum, badParentRescaledFibreDatum] using hFreshKT

/-- The same-selected source Frostman certificate gives an honest unit-ball
Frostman certificate on the actual fresh datum.  Admissibility supplies the
literal unit-ball containment; nonemptiness and positive fresh scale make
the displayed family-volume normalization cancellable. -/
theorem badParentFreshSuccessorDatum_isFrostmanIn_unitBall_of_source
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (hselected : selected.Nonempty)
    {C : ENNReal}
    (hSource : IsFrostmanIn C
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q))
    (hAdmissible :
      (badParentFreshSuccessorDatum
        S Y hrho hrhoOne q selected).IsAdmissible) :
    IsFrostmanIn
      (badParentFreshProxyFrostmanConstant
        S Y hrho hrhoOne q selected C)
      (badParentFreshSuccessorDatum
        S Y hrho hrhoOne q selected).family.bodyFamily
      unitBallBody := by
  let _ : Nonempty {i // i ∈ selected} :=
    Finset.nonempty_coe_sort.mpr hselected
  let freshD := badParentFreshSuccessorDatum
    S Y hrho hrhoOne q selected
  have hKT : IsKatzTao
      (badParentFreshProxyKatzTaoConstant
        S hrho hrhoOne q selected C)
      freshD.family.bodyFamily := by
    simpa only [freshD] using
      (badParentFreshSuccessorDatum_isKatzTao_of_source_isFrostmanIn
        S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho
          q selected hSource)
  have hcontained : forall i,
      (freshD.family.bodyFamily i : Set Space) <=
        (unitBallBody : Set Space) := by
    intro i
    simpa only [freshD, UniformTubeFamily.bodyFamily, Tube.coe_body,
      coe_unitBallBody] using hAdmissible.contained_in_unit_ball i
  have hfamilyZero : familyVolume freshD.family.bodyFamily ≠ 0 :=
    (actualDatum_familyVolume_pos_of_scale freshD
      hAdmissible.delta_pos).ne'
  have hfamilyTop : familyVolume freshD.family.bodyFamily ≠ ∞ :=
    familyVolume_ne_top freshD.family.bodyFamily
  have hmass : containedMass freshD.family.bodyFamily unitBallBody =
      familyVolume freshD.family.bodyFamily :=
    containedMass_eq_familyVolume_of_contained
      freshD.family.bodyFamily unitBallBody hcontained
  apply IsKatzTao.isFrostmanIn hKT hcontained
  rw [hmass]
  unfold badParentFreshProxyFrostmanConstant
  change
    badParentFreshProxyKatzTaoConstant
          S hrho hrhoOne q selected C *
        volume (unitBallBody : Set Space) <=
      (badParentFreshProxyKatzTaoConstant
          S hrho hrhoOne q selected C *
        volume (unitBallBody : Set Space) /
          familyVolume freshD.family.bodyFamily) *
        familyVolume freshD.family.bodyFamily
  rw [ENNReal.div_mul_cancel hfamilyZero hfamilyTop]

#print axioms badParentFreshProxyKatzTaoConstant
#print axioms badParentFreshProxyFrostmanConstant
#print axioms
  badParentFreshSuccessorDatum_isKatzTao_of_source_isFrostmanIn
#print axioms
  badParentFreshSuccessorDatum_isFrostmanIn_unitBall_of_source

end
end Family8ParentwiseBadParentFreshProxyFrostmanV2
