import Family8Grounding.Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
import Family8Grounding.Family8DoubledParentConflictWeightedDef212ScaleWitnessV2
import Family8Grounding.Family8DoubledParentConflictWeightedFrostmanConnectorV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8DoubledParentConflictWeightedDef212EndpointV1.ScaleCover
open Family8DoubledParentConflictWeightedDef212ScaleWitnessV2.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8DoubledParentConflictWeightedFrostmanConnectorV2.ScaleCover
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Sharp Katz--Tao conflict degree to one common Def. 2.12/Frostman endpoint

The exact Katz--Tao incidence theorem supplies the doubled-parent degree of
one existing Definition 2.12 scale.  Weighted greedy selection is then
performed with the literal parent shading masses.  The selected paper scale
witness, actual restricted datum, and source multiplicity comparison all use
the same selection.

The final implication displays the only two numerical inputs still needed
by the Frostman theorem: selected density after the sharp graph loss, and the
unit-ball base estimate.  Neither is hidden as a construction callback.
-/

/-- The explicit sharp conflict loss at fine radius `delta` and coarse
radius `rho`. -/
def katzTaoDoubledParentConflictBudget
    (delta rho : NNReal) (A : ENNReal) : ENNReal :=
  ((1 + katzTaoDoubledFiberNatCap delta rho A *
    katzTaoDoubledParentsNatCap delta rho A : Nat) : ENNReal)

/-- One source Definition 2.12 witness plus source Katz--Tao control produces
one common weighted selected witness and actual Frostman consumer. -/
theorem Def212ScaleWitness.exists_katzTaoWeightedDef212_frostmanEndpoint
    {beta epsilon eta : Real} {delta0 delta rho0 Cnn : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (W : Def212ScaleWitness D.family rho0 Cnn)
    (hfull : D.family.refinement.refined = Finset.univ)
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (D.family.tubes i) (D.family.tubes j))
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A D.family.bodyFamily)
    (hrhoSmall : W.rho ≤ (1 / 16 : NNReal))
    (hdelta0 : delta ≤ delta0) :
    ∃ E : WeightedDef212ScaleEndpoint W.cover
        (parentShadingWeight W.cover D.shading)
        (katzTaoDoubledParentConflictBudget delta W.rho A)
        (Cnn : ENNReal),
      Nonempty (Def212ScaleWitness
        (weightedSelectedAssignedFineFamily E.base.selection) rho0 Cnn) ∧
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading E.base.selection)).IsAdmissible ∧
      D.shading.averageMultiplicity ≤
        katzTaoDoubledParentConflictBudget delta W.rho A *
          (restrictActualTubeDatum D
            (weightedSelectedFineIndices D.shading E.base.selection)).shading.averageMultiplicity ∧
      ((delta : ENNReal) ^ eta ≤
          D.shading.shadingDensity /
            katzTaoDoubledParentConflictBudget delta W.rho A →
        A * volume (unitBallBody : Set Space) ≤
          (delta : ENNReal) ^ (-eta) *
            (restrictActualTubeDatum D
              (weightedSelectedFineIndices D.shading
                E.base.selection)).actualFamilyVolume →
        D.shading.averageMultiplicity ≤
          katzTaoDoubledParentConflictBudget delta W.rho A *
            frostmanMultiplicityRHS delta
              (restrictActualTubeDatum D
                (weightedSelectedFineIndices D.shading
                  E.base.selection)).actualFamilyVolume epsilon beta) := by
  let B := katzTaoDoubledParentConflictBudget delta W.rho A
  have hdegree : ClosedDoubledParentConflictDegreeBound W.cover B := by
    simpa only [B, katzTaoDoubledParentConflictBudget] using
      closedDoubledParentConflictDegreeBound_katzTao
        W.cover hD.delta_pos hD.delta_le_half hrhoSmall hAfinite hKT
  obtain ⟨E⟩ :=
    Family8DoubledParentConflictWeightedDef212EndpointV1.ScaleCover.exists_weightedDef212ScaleEndpoint
      W.cover (parentShadingWeight W.cover D.shading) B (Cnn : ENNReal)
      hdegree W.c_uniform hpaper W.unitRescalingGeometry
      W.rescaled_fibres_cwa
  have hactive : W.cover.activeFine = Finset.univ :=
    W.activeFine_eq_univ hfull
  have hadmissible :
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading E.base.selection)).IsAdmissible :=
    Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
      hD _
  have havg : D.shading.averageMultiplicity ≤
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading
          E.base.selection)).shading.averageMultiplicity :=
    source_averageMultiplicity_le_mul_weightedSelected
      D E.base.selection hactive
  refine ⟨E, ?_, hadmissible, ?_, ?_⟩
  · exact ⟨
      Family8DoubledParentConflictWeightedDef212ScaleWitnessV2.ScaleCover.WeightedDef212ScaleEndpoint.toDef212ScaleWitness
        E W.rho0_le_rho W.rho_le_one W.rho_lt_C_mul_rho0⟩
  · simpa only [B] using havg
  · intro hdensity hbase
    simpa only [B] using
      source_averageMultiplicity_le_mul_frostmanRHS_of_weightedSelection
        hF D hD E.base.selection hactive hdelta0 hKT hdensity hbase

#print axioms katzTaoDoubledParentConflictBudget
#print axioms
  Def212ScaleWitness.exists_katzTaoWeightedDef212_frostmanEndpoint

end

end Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
