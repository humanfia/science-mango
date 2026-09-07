import Family8Grounding.Family8SelectedParentPlankFineMassProxyDatumV2
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankFineMassProxyFreshSelectionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Mass-retaining fresh selection on one selected-parent plank fibre

The literal proxy now carries the affine image of the actual fine shading.
Consequently the same weighted conflict-graph selection used by the geometric
proxy retains actual shading mass and controls the actual source-fibre average
multiplicity.  The family fields are definitionally the earlier proxy family,
so the established Katz--Tao conflict cap applies to the very same indices.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- One honest same-`W` selection simultaneously retains cardinality, actual
shading mass, normalized Katz--Tao control, and source average multiplicity. -/
theorem exists_selectedPlankFine_massProxy_normalizedFresh_of_isKatzTao
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (s : NNReal) (hs : 0 < s) (hsHalf : s ≤ (2 : NNReal)⁻¹)
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real))
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (selectedPlankFineProxyDatum s e S B hrho label W).family.bodyFamily) :
    let D := selectedPlankFineMassProxyDatum
      s Y e S B hrho label W haxisLength hradius
    let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
    ∃ selected : Finset (SelectedPlankFineIndex S W),
      selected.Nonempty ∧
      Set.Pairwise (selected : Set (SelectedPlankFineIndex S W))
        (fun i j => EssentiallyDistinct
          ((eighthNormalizedDatum D).family.tubes i)
          ((eighthNormalizedDatum D).family.tubes j)) ∧
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      (selectedPlankFineSourceShading
          Y e S B hrho label W).averageMultiplicity ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.averageMultiplicity ∧
      ((threshold + 1 : Nat) : ENNReal) ≤ 480000 * (128 * C) + 2 := by
  dsimp only
  let D := selectedPlankFineMassProxyDatum
    s Y e S B hrho label W haxisLength hradius
  let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
  have hfiberNonempty : (S.fiber W.1.1.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ :=
      S.parent_surjective W.1.1.1 W.1.1.2
    exact ⟨i, (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩⟩
  let _ : Nonempty (SelectedPlankFineIndex S W) :=
    Finset.nonempty_coe_sort.mpr hfiberNonempty
  have hKTmass : IsKatzTao C D.family.bodyFamily := by
    simpa only [D, selectedPlankFineMassProxyDatum_family,
      selectedPlankFineProxyDatum] using hKT
  have hconflict : ∀ i,
      (normalizedConflictIndices D i).card ≤ threshold := by
    intro i
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      D hs hsHalf hCfinite hKTmass i
  obtain ⟨selected, hselected, hpair, hcard, hmass⟩ :=
    exists_normalized_greedyRefinement D hconflict
  have hselectedKT : IsKatzTao (128 * C)
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).family.bodyFamily :=
    restrict_eighthNormalizedDatum_isKatzTao D hsHalf selected hKTmass
  have havgD : D.shading.averageMultiplicity ≤
      (threshold + 1 : Nat) *
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).shading.averageMultiplicity :=
    source_averageMultiplicity_le_loss_mul_normalizedRestricted
      D selected (threshold + 1) hmass
  have havgSource :
      (selectedPlankFineSourceShading
          Y e S B hrho label W).averageMultiplicity ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.averageMultiplicity := by
    rw [← selectedPlankFineMassProxyShading_averageMultiplicity
      s Y e S B hrho label W haxisLength hradius]
    simpa only [D, selectedPlankFineMassProxyDatum] using havgD
  have h128Cfinite : (128 : ENNReal) * C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  have hloss : ((threshold + 1 : Nat) : ENNReal) ≤
      480000 * (128 * C) + 2 := by
    exact fixedKatzTaoClosedLoss_coe_le_add_two h128Cfinite
  exact ⟨selected, hselected, hpair, hcard, hmass,
    hselectedKT, havgSource, hloss⟩

#print axioms exists_selectedPlankFine_massProxy_normalizedFresh_of_isKatzTao

end
end Family8SelectedParentPlankFineMassProxyFreshSelectionV2
