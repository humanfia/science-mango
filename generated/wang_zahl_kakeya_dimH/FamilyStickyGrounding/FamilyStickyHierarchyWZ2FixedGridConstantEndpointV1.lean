import FamilyStickyGrounding.FamilyStickyHierarchyWZ2CollisionCellCopyCapEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
open FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2CopyGridCapEndpointV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Honest fixed-grid-constant endpoint for the hierarchy collision cell

The WZ2 `siteCount` is not the cardinality of the hierarchy collision grid.
It is an independent input to the one-dimensional shear grid
`Fin siteCount -> ReducedLineParameter`.  A selected site `q : Fin siteCount`
only proves that this grid is nonempty; it gives no upper cardinality bound.

For positive spacing the shear sites are genuinely distinct.  Thus no fixed
constant can bound all values admitted by the current API.  The minimal
honest extra datum is an explicit certificate `siteCount <= gridConstant`.
Under that certificate the full collision-cell endpoint has coefficient
`16 * gridConstant * commonHundredNeighbourPackingConstant`.  If
`gridConstant` is chosen once as a dimension-dependent grid constant, this
is the desired dimension-only coefficient.
-/

/-- The minimal upstream datum needed to replace the freely declared shear
grid cardinality by a fixed constant. -/
structure FixedShearCopyGridCertificate
    (siteCount gridConstant : Nat) : Prop where
  siteCount_le_gridConstant : siteCount <= gridConstant

/-- Positive spacing makes the declared WZ2 shear-copy sites genuinely
distinct; the apparent `siteCount` cannot be removed by deduplication. -/
theorem shearReducedShift_injective_of_pos
    {siteCount : Nat} {spacing : Real} (hspacing : 0 < spacing) :
    Function.Injective
      (shearReducedShift spacing (siteCount := siteCount)) := by
  intro j k hjk
  apply Fin.ext
  have hd := congrArg (fun p : ReducedLineParameter => p.2.2) hjk
  simp only [shearReducedShift] at hd
  have hval : ((j : Nat) : Real) = ((k : Nat) : Real) := by
    nlinarith
  exact_mod_cast hval

/-- Consequently the image of the actual finite shear grid has exactly the
declared number of sites. -/
theorem card_shearReducedShift_image_eq_siteCount
    {siteCount : Nat} {spacing : Real} (hspacing : 0 < spacing) :
    ((Finset.univ : Finset (Fin siteCount)).image
      (shearReducedShift spacing (siteCount := siteCount))).card =
        siteCount := by
  rw [Finset.card_image_of_injective _
    (shearReducedShift_injective_of_pos hspacing)]
  simp

/-- Formal obstruction: the present shear-grid API admits arbitrarily large
actual finite grids, even with the fixed positive spacing `1`. -/
theorem no_uniform_card_shearReducedShift_image_cap :
    Not (exists gridConstant : Nat, forall siteCount : Nat,
      ((Finset.univ : Finset (Fin siteCount)).image
        (shearReducedShift (1 : Real) (siteCount := siteCount))).card <=
          gridConstant) := by
  rintro ⟨gridConstant, hcap⟩
  have hlarge := hcap (gridConstant + 1)
  rw [card_shearReducedShift_image_eq_siteCount (by norm_num)] at hlarge
  omega

/-- The same obstruction in the exact logical shape seen by the hierarchy
endpoint: carrying one selected `q : Fin siteCount` only says nonempty. -/
theorem no_uniform_siteCount_cap_from_selected_site :
    Not (exists gridConstant : Nat, forall siteCount : Nat,
      Nonempty (Fin siteCount) -> siteCount <= gridConstant) := by
  rintro ⟨gridConstant, hcap⟩
  have hlarge := hcap (gridConstant + 1)
    ⟨⟨0, Nat.zero_lt_succ gridConstant⟩⟩
  omega

/-- The certified fixed-grid arithmetic replacement. -/
theorem siteCount_mul_WZConstant_le_fixedGridConstant_mul_WZConstant
    {siteCount gridConstant : Nat}
    (grid : FixedShearCopyGridCertificate siteCount gridConstant) :
    siteCount * commonHundredNeighbourPackingConstant <=
      gridConstant * commonHundredNeighbourPackingConstant := by
  exact Nat.mul_le_mul_right commonHundredNeighbourPackingConstant
    grid.siteCount_le_gridConstant

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
  {delta : NNReal} {spacing : Real} {siteCount gridConstant : Nat}

/-- Generic fixed-chart WZ2 endpoint under the minimal fixed-grid
certificate. -/
theorem exists_distortedJohnCertificate_and_containedMass_le_fixedGridConstant_mul_WZConstant_of_fixedVerticalChart
    (grid : FixedShearCopyGridCertificate siteCount gridConstant)
    (fine : UniformTubeFamily delta kappa) (K : ConvexBody Space)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (j : Fin siteCount) (i : kappa)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily fine.tubes) (j, i) : ConvexBody Space) : Set Space) <=
        (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (hpair : Set.Pairwise (Set.univ : Set kappa) fun a b =>
      WZEndpointParameterSeparated (fine.tubes a) (fine.tubes b))
    (shared : SharedHundredSourceContainer fine)
    (source : Finset kappa)
    (hselected : (Finset.univ : Finset kappa) <=
      fixedVerticalChartIndices fine source)
    (hcluster : forall l, |tubeGraphD (fine.tubes l) - baseD| <= rho) :
    exists side : Fin 3 -> NNReal,
      exists _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius delta (shearSiteD spacing j) <= side l) ∧
        (exists l : Fin 3,
          distortedAxisLength (shearSiteD spacing j) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily fine.tubes)) K <=
          (16 *
            ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
              ENNReal)) *
            volume (K : Set Space) := by
  obtain ⟨side, cert, hside, hlong, hmass⟩ :=
    exists_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant_of_fixedVerticalChart
      fine K hdelta hdeltaHalf j i hcontained baseD rho hspacing hrho hpair
      shared source hselected hcluster
  refine ⟨side, cert, hside, hlong, hmass.trans ?_⟩
  have hnat :=
    siteCount_mul_WZConstant_le_fixedGridConstant_mul_WZConstant grid
  have hcast :
      ((siteCount * commonHundredNeighbourPackingConstant : Nat) : ENNReal) <=
        ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
          ENNReal) := by
    exact_mod_cast hnat
  gcongr

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- Fully composed hierarchy collision-cell endpoint.  Its only new input is
the exact missing upstream fact: the external WZ2 shear-copy grid has bounded
cardinality. -/
theorem exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_fixedGridConstant_mul_WZConstant
    (grid : FixedShearCopyGridCertificate siteCount gridConstant)
    (C : HierarchyJointRandomMotionCertificate H G)
    (W : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin (repetitions G.toDependentSource k))
    (K : ConvexBody Space) (q : Fin siteCount)
    (i : SelectedHierarchyCollisionCellIndex H G C k p a r)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily
            (selectedHierarchyCollisionCellFamily H G C k p a r).tubes)
          (q, i) : ConvexBody Space) : Set Space) <= (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex H G C k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex H G C k p a r)) <=
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily H G C k p a r) source)
    (hcluster : forall l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily H G C k p a r).tubes l) -
        baseD| <= rho) :
    exists side : Fin 3 -> NNReal,
      exists _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius (H.effectiveRadius k.1)
            (shearSiteD spacing q) <= side l) ∧
        (exists l : Fin 3,
          distortedAxisLength (shearSiteD spacing q) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily
                (selectedHierarchyCollisionCellFamily H G C k p a r).tubes)) K <=
          (16 *
            ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
              ENNReal)) *
            volume (K : Set Space) := by
  let hshared := selectedHierarchyCollisionCell_sharedHundredSourceContainer
    H G C k p a r
  have hpair :=
    selectedHierarchyCollisionCell_pairwise_WZEndpointParameterSeparated
      H G C W k p hp a r
  exact
    exists_distortedJohnCertificate_and_containedMass_le_fixedGridConstant_mul_WZConstant_of_fixedVerticalChart
      grid (selectedHierarchyCollisionCellFamily H G C k p a r) K
      (G.childRadius_pos k) (G.childRadius_le_half k)
      q i hcontained baseD rho hspacing hrho hpair hshared source hselected
      hcluster

#print axioms shearReducedShift_injective_of_pos
#print axioms card_shearReducedShift_image_eq_siteCount
#print axioms no_uniform_card_shearReducedShift_image_cap
#print axioms no_uniform_siteCount_cap_from_selected_site
#print axioms siteCount_mul_WZConstant_le_fixedGridConstant_mul_WZConstant
#print axioms exists_distortedJohnCertificate_and_containedMass_le_fixedGridConstant_mul_WZConstant_of_fixedVerticalChart
#print axioms exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_fixedGridConstant_mul_WZConstant

end
end FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1
