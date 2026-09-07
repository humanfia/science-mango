import Family8Grounding.Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV2
import Family8Grounding.Family8NormalizedLongCoreCorrelatedEq66InputsV1
import Mathlib.Tactic

/-!
# Parentwise LongCore to the correlated Equation (66) consumer

This file is the thin positive bridge at the V535 producer seam.  It keeps
the faithful parentwise LongCore witness, the canonical active-fine assembly
cover, the mass-popular selected parent, and the existing correlated Eq. 66
input record on the same literal objects.

The bridge proves the mass-popular normalized-CF field from the parentwise
barrier.  The analytic fields already exposed by
`NormalizedLongCoreCorrelatedEq66Inputs` remain explicit producer
obligations; none is replaced by a callback or a new assumption.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ParentwiseLongCoreCorrelatedEq66BridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Family4GlobalExtremalUpstream
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllParentCFBarrierSelectedTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8FullRefinementActualDatumV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentwiseLongCoreCanonicalMassPopularCFV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The old normalized witness, obtained only for compatibility with the
established Eq. 66 consumer.  The parentwise witness remains available in
the bridge record below. -/
noncomputable def normalizedWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S)
    (hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty) :
    NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S :=
  Wparent.toNormalizedLongIntervalCoreWitness
    (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C S P.epsilon_pos.le hFine

/-- The literal canonical tau-active cover attached to `Wparent`. -/
noncomputable def tauActiveCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S)
    (hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty)
    (hepsilonHalf : P.epsilon <= 1 / 2) :=
  canonicalBufferedTauActiveCover
    (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C S (normalizedWitness D hD C S P Wparent hFine)
        P.epsilon_pos.le hepsilonHalf

/-- The actual active-fine source cover used by the selected assembly. -/
noncomputable def assemblyCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S)
    (hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty)
    (hepsilonHalf : P.epsilon <= 1 / 2) :=
  activeFineRestrictedScaleCover
    (tauActiveCover D hD C S P Wparent hFine hepsilonHalf)

/-- The canonical LongCore lower value carried to the selected parent. -/
noncomputable def selectedParentLower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S)
    (hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty) :
    ENNReal :=
  let W := normalizedWitness D hD C S P Wparent hFine
  (((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
    P.eta W.stage)

/-- The V535 correlated-input record strengthened on the same literal
canonical active-fine cover and assembly by the mass-popular selected-parent
CF certificate.  The `correlated` field keeps the producer obligations
`selectedThird`, `correlatedPrefixBudget`, `hCount`, and `hAggregateLoss`
explicit through their established record type. -/
structure CorrelatedInputsWithMassPopularCF
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S)
    (hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (Y : Shading
      (activeFineRestrictedFamily
        (tauActiveCover D hD C S P Wparent hFine hepsilonHalf)).bodyFamily)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf)) Y 1)
    (X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal)
    (outputEta : Real) where
  correlated :
    NormalizedLongCoreCorrelatedEq66Inputs D hD C S P
      (normalizedWitness D hD C S P Wparent hFine)
      (activeFineRestrictedFamily
        (tauActiveCover D hD C S P Wparent hFine hepsilonHalf))
      (assemblyCover D hD C S P Wparent hFine hepsilonHalf).coarse.bodyFamily
      (assemblyCover D hD C S P Wparent hFine hepsilonHalf)
      Y
      (toConvexFactorization
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf))
      A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta
  massPopularCF :
    MassPopularSelectedParentWithCF
      (assemblyCover D hD C S P Wparent hFine hepsilonHalf) Y 1 A
      (selectedParentLower D hD C S P Wparent hFine)

namespace CorrelatedInputsWithMassPopularCF

/-- The strengthened record feeds the existing V535 `hPrefix` consumer
without forgetting which selected parent carries the LongCore CF barrier. -/
theorem hPrefix
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family}
    {S : FiniteScaleSequence delta depth}
    {P : ParameterLadder epsilon0 beta gamma}
    {Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S}
    {hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty}
    {hepsilonHalf : P.epsilon <= 1 / 2}
    {Y : Shading
      (activeFineRestrictedFamily
        (tauActiveCover D hD C S P Wparent hFine hepsilonHalf)).bodyFamily}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf)) Y 1}
    {X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal}
    {outputEta : Real}
    (Z : CorrelatedInputsWithMassPopularCF D hD C S P Wparent
      hFine hepsilonHalf Y A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta) :
    Z.correlated.collapsedPrefix <=
      Z.correlated.firstLoss * sectionEightScaleCountFrostmanFactor
        delta Z.correlated.middleScale Z.correlated.middleCount gamma :=
  Z.correlated.hPrefix

/-- The exact selected-parent CF inequality retained while calling the old
correlated Eq. 66 consumer. -/
theorem selectedParent_cf_lower
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family}
    {S : FiniteScaleSequence delta depth}
    {P : ParameterLadder epsilon0 beta gamma}
    {Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S}
    {hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty}
    {hepsilonHalf : P.epsilon <= 1 / 2}
    {Y : Shading
      (activeFineRestrictedFamily
        (tauActiveCover D hD C S P Wparent hFine hepsilonHalf)).bodyFamily}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf)) Y 1}
    {X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal}
    {outputEta : Real}
    (Z : CorrelatedInputsWithMassPopularCF D hD C S P Wparent
      hFine hepsilonHalf Y A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta) :
    selectedParentLower D hD C S P Wparent hFine <=
      parentNormalizedFiberCFAt
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf)
        ⟨selectedFineOldParent
          (assemblyCover D hD C S P Wparent hFine hepsilonHalf)
          A.refinement.indices Z.massPopularCF.q.1,
          Z.massPopularCF.oldParent_active⟩ :=
  Z.massPopularCF.cf_lower

/-- Construct the strengthened consumer input from the existing explicit
V535 correlated inputs.  The only added conclusion is produced by
`IntegrationV2`; the four analytic producer obligations are exactly those
already present in `Z`. -/
theorem nonempty_of_correlated
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family}
    {S : FiniteScaleSequence delta depth}
    {P : ParameterLadder epsilon0 beta gamma}
    {Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C P.N P.epsilon P.epsilon_pos.le P.eta S}
    {hFine : (fullRefinementDatum D).family.refinement.refined.Nonempty}
    {hepsilonHalf : P.epsilon <= 1 / 2}
    {Y : Shading
      (activeFineRestrictedFamily
        (tauActiveCover D hD C S P Wparent hFine hepsilonHalf)).bodyFamily}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf)) Y 1}
    {X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal}
    {outputEta : Real}
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf).activeFine).shading.shadingMass
          ≠ 0)
    (Z : NormalizedLongCoreCorrelatedEq66Inputs D hD C S P
      (normalizedWitness D hD C S P Wparent hFine)
      (activeFineRestrictedFamily
        (tauActiveCover D hD C S P Wparent hFine hepsilonHalf))
      (assemblyCover D hD C S P Wparent hFine hepsilonHalf).coarse.bodyFamily
      (assemblyCover D hD C S P Wparent hFine hepsilonHalf)
      Y
      (toConvexFactorization
        (assemblyCover D hD C S P Wparent hFine hepsilonHalf))
      A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta) :
    Nonempty (CorrelatedInputsWithMassPopularCF D hD C S P Wparent
      hFine hepsilonHalf Y A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta) := by
  have hM : Nonempty (MassPopularSelectedParentWithCF
      (assemblyCover D hD C S P Wparent hFine hepsilonHalf) Y 1 A
      (selectedParentLower D hD C S P Wparent hFine)) := by
    convert
      Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV2.exists_canonicalTauActiveRestricted_massPopularSelectedParentWithCF
        (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P.epsilon_pos.le Wparent hFine hepsilonHalf Y 1 A hsource using 1
    all_goals rfl
  obtain ⟨M⟩ := hM
  exact ⟨{
    correlated := Z
    massPopularCF := M }⟩

end CorrelatedInputsWithMassPopularCF

#print axioms normalizedWitness
#print axioms tauActiveCover
#print axioms assemblyCover
#print axioms selectedParentLower
#print axioms CorrelatedInputsWithMassPopularCF
#print axioms CorrelatedInputsWithMassPopularCF.hPrefix
#print axioms CorrelatedInputsWithMassPopularCF.selectedParent_cf_lower
#print axioms CorrelatedInputsWithMassPopularCF.nonempty_of_correlated

end
end Family8ParentwiseLongCoreCorrelatedEq66BridgeV1
