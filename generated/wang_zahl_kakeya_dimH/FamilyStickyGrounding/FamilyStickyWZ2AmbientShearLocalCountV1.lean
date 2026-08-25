import FamilyStickyGrounding.FamilyStickyWZ2AmbientShearWindowBridgeV1
import FamilyStickyGrounding.FamilyStickyWZ2ShearParameterNonconcentrationV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace FamilyStickyWZ2AmbientShearLocalCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2ShearParameterNonconcentrationV1
open FamilyStickyWZ2AmbientShearWindowBridgeV1

noncomputable section

/-!
# Local source nonconcentration inside an actual ambient shear window

The ambient bridge bounds the translated `d` coordinate of every contained
transported tube.  Encoding only that genuine shear coordinate as a reduced
parameter lets the already proved fibrewise shear-grid theorem retain a local
source-window budget.  The final count has both improvements: the number of
relevant copies is local, and each relevant copy contributes only the source
indices in its corresponding local `d` window.
-/

/-- The reduced parameter retaining exactly the actual tube's shear slope. -/
def tubeShearReducedParameter {delta : NNReal} (T : Tube delta) :
    ReducedLineParameter :=
  (0, (0, tubeGraphD T))

/-- Ambient containment is a literal translated-parameter-window condition
for the actual source shear slopes. -/
theorem containedShearProductIndices_subset_translatedParameterWindow
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {delta : NNReal}
    {spacing : Real} {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) (center radius : Real)
    (hwindow : CoordinateOneWindow K center radius)
    (hvertical : forall i,
      (1 / 2 : Real) <= |(fine.tubes i).axis.direction 2|) :
    containedShearProductIndices spacing (siteCount := siteCount) fine K <=
      translatedParameterWindowIndices
        (shearReducedShift spacing (siteCount := siteCount))
        (fun i => tubeShearReducedParameter (fine.tubes i))
        (0, (0, 0)) (4 * radius) := by
  classical
  intro ji hji
  rw [translatedParameterWindowIndices, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hcontained := (Finset.mem_filter.mp hji).2
  have hshear :=
    abs_indexedTranslatedTubeParameter_shear_le_four_mul
      (shearReducedShift spacing (siteCount := siteCount)) fine
      K center radius hwindow (hvertical ji.2) hcontained
  simpa [reducedParameterDistance, shearReducedShift,
    tubeShearReducedParameter, indexedTranslatedTubeParameter,
    tubeReducedLineParameter, translateReducedLineParameter] using hshear

/-- Actual ambient contained-index count with both a local copy budget and a
local source-shear budget. -/
theorem card_containedShearProductIndices_le_local_sourceBudget
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {delta : NNReal}
    {spacing : Real} {siteCount : Nat}
    (fine : UniformTubeFamily delta kappa)
    (K : ConvexBody Space) (center radius baseD rho : Real)
    (hspacing : 0 < spacing) (hradius : 0 <= radius) (hrho : 0 <= rho)
    (hwindow : CoordinateOneWindow K center radius)
    (hvertical : forall i,
      (1 / 2 : Real) <= |(fine.tubes i).axis.direction 2|)
    (hcluster : forall i, |tubeGraphD (fine.tubes i) - baseD| <= rho)
    (sourceBudget : Nat)
    (hsource : forall q,
      (parameterWindowIndices
        (fun i => tubeShearReducedParameter (fine.tubes i))
        q (4 * radius)).card <= sourceBudget) :
    (containedShearProductIndices spacing (siteCount := siteCount) fine K).card <=
      min siteCount (shearShiftHitBudget spacing (4 * radius + rho)) *
        sourceBudget := by
  have hcluster' : forall i,
      reducedParameterDistance
        (tubeShearReducedParameter (fine.tubes i))
        (0, (0, baseD)) <= rho := by
    intro i
    simpa [reducedParameterDistance, tubeShearReducedParameter] using hcluster i
  calc
    (containedShearProductIndices spacing (siteCount := siteCount) fine K).card <=
        (translatedParameterWindowIndices
          (shearReducedShift spacing (siteCount := siteCount))
          (fun i => tubeShearReducedParameter (fine.tubes i))
          (0, (0, 0)) (4 * radius)).card :=
      Finset.card_le_card
        (containedShearProductIndices_subset_translatedParameterWindow
          fine K center radius hwindow hvertical)
    _ <= min siteCount
          (shearShiftHitBudget spacing (4 * radius + rho)) * sourceBudget := by
      exact card_shearGrid_translatedParameterWindow_le_local
        (fun i => tubeShearReducedParameter (fine.tubes i))
        (0, (0, baseD)) (0, (0, 0)) hspacing hrho
        (mul_nonneg (by norm_num) hradius) hcluster' sourceBudget hsource

#print axioms containedShearProductIndices_subset_translatedParameterWindow
#print axioms card_containedShearProductIndices_le_local_sourceBudget

end
end FamilyStickyWZ2AmbientShearLocalCountV1
