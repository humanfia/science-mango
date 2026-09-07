import Family8Grounding.Family8CanonicalGraphFrozenActiveIdentityBridgeV1
import Mathlib.Tactic

/-!
# Preserve a canonical graph conclusion through the H-row setup

The canonical graph producer returns a property of one literal graph/frozen
identity.  The active-identity bridge can construct the square-plank H-row
setup on that same graph.  This file packages those two operations without
reselecting the graph or its frozen assembly.

The predicate `Q` is deliberately arbitrary.  In the Equation-(66) route it
is instantiated by the selector's loss identity together with its already
proved raw source-to-frozen-average inequality.  Thus this adapter transports
`hRawEq66`; it neither assumes a new copy nor tries to derive it from the
one-sided H-row mass floor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenActiveIdentityHRowAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenActiveIdentityBridgeV1
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}

/-- Lift a conclusion on one canonical restricted graph identity to the
active identity and construct the H-row setup on that exact same graph.

This is the minimal object-identity adapter at the raw Equation-(66) seam:
choosing `Q` to contain the selector's raw inequality keeps its frozen
average definitionally tied to the assembly used by the H-row consumer. -/
theorem exists_activeIdentity_with_hRowSetup_of_exists_activeFineRestricted
    (U : StickyScaleCover F rho)
    {P : ConvexFactorization
      (activeFineRestrictedFamily U).bodyFamily
      (activeFineRestrictedScaleCover U).coarse.bodyFamily}
    {Y : Shading (activeFineRestrictedFamily U).bodyFamily}
    {fibreCF : ENNReal}
    {Q : SameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) (activeFineRestrictedScaleCover U)
        P Y fibreCF -> Prop}
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (htauRho : tau <= rho)
    (h : exists R, Q R) :
    exists R : ActiveSameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U) (activeFineRestrictedScaleCover U)
        P Y fibreCF,
      Q R.graph /\
        Nonempty (SquarePlankHRowSelectionFirstSetup
          (R.bufferedPlankDatum htau hrho hrhoOne htauRho)) := by
  obtain ⟨R, hR⟩ :=
    exists_activeIdentity_of_exists_activeFineRestricted U h
  exact ⟨R, hR,
    R.exists_hRowSetup htau hrho hrhoOne htauRho⟩

#print axioms
  exists_activeIdentity_with_hRowSetup_of_exists_activeFineRestricted

end
end Family8CanonicalGraphFrozenActiveIdentityHRowAdapterV1
