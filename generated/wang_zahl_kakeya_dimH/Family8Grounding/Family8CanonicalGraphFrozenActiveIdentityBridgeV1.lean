import Family8Grounding.Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
import Mathlib.Tactic

/-!
# Active canonical graph identity bridge

The raw graph producer chooses a coarse index which is active, but the first
minimal graph identity did not retain that proof.  This successor stores only
the missing literal fact.  It does not compare assemblies or row objects and
does not add any Equation-(66), displayed-coefficient, or analytic budget.

For the canonical fully-active restriction the proof is automatic because
its active coarse set is `univ`.  The HRow wrappers below therefore reuse the
exact graph identity and exact selected row without accepting `hk` again.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenActiveIdentityBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- The old same-assembly graph identity plus precisely the active proof of
its already-selected coarse index. -/
structure ActiveSameAssemblyFullCoefficientGraphIdentity
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) (fibreCF : ENNReal) where
  graph : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF
  k_active : graph.k ∈ T.activeCoarse

/-- On the canonical active-fine restriction every coarse index is active,
so the successor identity requires no new producer hypothesis. -/
def activeIdentityOfActiveFineRestricted
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    (U : StickyScaleCover F rho)
    {P : ConvexFactorization
      (activeFineRestrictedFamily U).bodyFamily
      (activeFineRestrictedScaleCover U).coarse.bodyFamily}
    {Y : Shading (activeFineRestrictedFamily U).bodyFamily}
    {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) (activeFineRestrictedScaleCover U)
        P Y fibreCF) :
    ActiveSameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) (activeFineRestrictedScaleCover U)
        P Y fibreCF where
  graph := R
  k_active := by
    rw [activeFineRestrictedScaleCover_activeCoarse]
    exact Finset.mem_univ R.k

/-- Lift any existential conclusion on a canonical restricted graph identity
to the active successor while preserving the conclusion literally. -/
theorem exists_activeIdentity_of_exists_activeFineRestricted
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    (U : StickyScaleCover F rho)
    {P : ConvexFactorization
      (activeFineRestrictedFamily U).bodyFamily
      (activeFineRestrictedScaleCover U).coarse.bodyFamily}
    {Y : Shading (activeFineRestrictedFamily U).bodyFamily}
    {fibreCF : ENNReal}
    {Q : SameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) (activeFineRestrictedScaleCover U)
        P Y fibreCF → Prop}
    (h : ∃ R, Q R) :
    ∃ R : ActiveSameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) (activeFineRestrictedScaleCover U)
        P Y fibreCF,
      Q R.graph := by
  obtain ⟨R, hR⟩ := h
  exact ⟨activeIdentityOfActiveFineRestricted U R, hR⟩

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The exact GraphFrozen square-plank datum, now with the stored active proof
and hence no `hk` argument at the consumer. -/
abbrev ActiveSameAssemblyFullCoefficientGraphIdentity.bufferedPlankDatum
    (R : ActiveSameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) :=
  sameAssemblyGraphBufferedPlankDatum
    R.graph htau hrho hrhoOne htauRho R.k_active

/-- Selection-first construction of the HRow setup on the exact graph of the
active successor identity. -/
theorem ActiveSameAssemblyFullCoefficientGraphIdentity.exists_hRowSetup
    (R : ActiveSameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) :
    Nonempty (SquarePlankHRowSelectionFirstSetup
      (R.bufferedPlankDatum htau hrho hrhoOne htauRho)) :=
  exists_sameAssemblyGraphHRowSelectionFirstSetup
    R.graph htau hrho hrhoOne htauRho R.k_active

/-- The same-row graph-average correlation with no repeated active-index
hypothesis. -/
theorem ActiveSameAssemblyFullCoefficientGraphIdentity.graphAverage_le_hRowAverage
    (R : ActiveSameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho)
    (H : SquarePlankHRowSelectionFirstSetup
      (R.bufferedPlankDatum htau hrho hrhoOne htauRho))
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      (R.bufferedPlankDatum htau hrho hrhoOne htauRho)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilon beta eta) :
    R.graph.graphAverage ≤ H.loss *
      (HRowFreshPlankDatum
        (R.bufferedPlankDatum htau hrho hrhoOne htauRho)
        H.C H.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
          B.tau B.S).shading.averageMultiplicity :=
  graphAverage_le_setupLoss_mul_sameHRowAverage
    R.graph htau hrho hrhoOne htauRho R.k_active H B

#print axioms ActiveSameAssemblyFullCoefficientGraphIdentity
#print axioms activeIdentityOfActiveFineRestricted
#print axioms exists_activeIdentity_of_exists_activeFineRestricted
#print axioms ActiveSameAssemblyFullCoefficientGraphIdentity.exists_hRowSetup
#print axioms ActiveSameAssemblyFullCoefficientGraphIdentity.graphAverage_le_hRowAverage

end
end Family8CanonicalGraphFrozenActiveIdentityBridgeV1
