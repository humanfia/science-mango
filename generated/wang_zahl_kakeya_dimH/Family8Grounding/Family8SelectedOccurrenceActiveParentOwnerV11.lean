import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV9
import Mathlib.Tactic

/-!
# Actual owner-fibre Delta-max and thick-plank control

The paper's local statement `Delta_max(W_T_rho) <= Delta` is represented as
a genuine Katz--Tao certificate on every literal owner fibre.  This bounds
the actual supremum `ownerFiberDeltaMax`; combined with the unique-owner
producer it yields Family 6 thickened-plank control with the honest
comparison-dependent `M`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceActiveParentOwnerV11

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6PlankKatzTaoFrostmanActualAdaptersV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceActiveParentOwnerV9
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho a b Delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}
  {R : Finset (Fin (blocks fine.bodyFamily P).length)}

/-- Literal local Katz--Tao control on every actual owner fibre. -/
def OwnerFiberIsKatzTao
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (owner : {q // q ∈ selectedOccurrenceIndices P R} → Fin C.coarseCard) :
    Prop :=
  ∀ p : Fin C.coarseCard,
    IsKatzTao (Delta : ENNReal) (ownerFiberFamily D owner p)

/-- Local Katz--Tao certificates bound the genuine supremum used by V3. -/
theorem ownerFiberDeltaMax_le_of_ownerFiberIsKatzTao
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (owner : {q // q ∈ selectedOccurrenceIndices P R} → Fin C.coarseCard)
    (hlocal : OwnerFiberIsKatzTao (Delta := Delta) C D owner) :
    ownerFiberDeltaMax D owner ≤ (Delta : ENNReal) := by
  unfold ownerFiberDeltaMax
  apply iSup_le
  intro p
  exact isKatzTao_iff_maximalConcentration_le.mp (hlocal p)

/-- The complete thick-plank producer on the owner-selected occurrence set.
Both unique ownership and local Delta-max are derived from their underlying
geometric/Katz--Tao data. -/
theorem frostmanThickenedPlankControl_ownedOccurrences
    (hpure : ParentPure C P)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesOwnedBy C P R0 W.selected)} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P
      (occurrencesOwnedBy C P R0 W.selected))
    (hinside : AdmissibleThickeningInsideOwner C
      (occurrencesOwnedBy C P R0 W.selected) D
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected)))
    (hlocal : OwnerFiberIsKatzTao (Delta := Delta) C D
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected))) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta a b) := by
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax D
    (selectedOccurrenceActiveParent C
      (occurrencesOwnedBy C P R0 W.selected))
  · exact thickenedPlankUniqueOwner_ownedOccurrences C hpure Y R0 loss W D
      hfamily hinside
  · exact ownerFiberDeltaMax_le_of_ownerFiberIsKatzTao
      (Delta := Delta) C D
        (selectedOccurrenceActiveParent C
          (occurrencesOwnedBy C P R0 W.selected)) hlocal

#print axioms ownerFiberDeltaMax_le_of_ownerFiberIsKatzTao
#print axioms frostmanThickenedPlankControl_ownedOccurrences

end

end Family8SelectedOccurrenceActiveParentOwnerV11
