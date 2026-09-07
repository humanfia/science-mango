import Family8Grounding.Family8SelectedParentPlankFreshPairwisePackingV3
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentPlankFineProxyFreshSelectionV1

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
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFreshPairwisePackingV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Literal fresh selection on one selected-parent plank fibre

For the actual fine fibre of one fixed selected plank `W`, raw Katz--Tao
control of the literal affine-axis proxy family gives the fixed normalized
conflict cap.  The finite greedy theorem then constructs the selected index
set, its pairwise normalized essential distinctness, and its exact cardinality
retention.  No unit-ball support or admissibility callback is needed for this
geometric count route.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Automatic same-`W` fixed-conflict fresh selection and KT transport. -/
theorem exists_selectedPlankFine_normalizedFresh_of_isKatzTao
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (s : NNReal) (hs : 0 < s) (hsHalf : s ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (selectedPlankFineProxyDatum s e S B hrho label W).family.bodyFamily) :
    let D := selectedPlankFineProxyDatum s e S B hrho label W
    let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
    ∃ selected : Finset (SelectedPlankFineIndex S W),
      selected.Nonempty ∧
      Set.Pairwise (selected : Set (SelectedPlankFineIndex S W))
        (fun i j => EssentiallyDistinct
          ((eighthNormalizedDatum D).family.tubes i)
          ((eighthNormalizedDatum D).family.tubes j)) ∧
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      ((threshold + 1 : Nat) : ENNReal) ≤ 480000 * (128 * C) + 2 := by
  dsimp only
  let D := selectedPlankFineProxyDatum s e S B hrho label W
  let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
  have hfiberNonempty : (S.fiber W.1.1.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ :=
      S.parent_surjective W.1.1.1 W.1.1.2
    exact ⟨i, (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩⟩
  let _ : Nonempty (SelectedPlankFineIndex S W) :=
    Finset.nonempty_coe_sort.mpr hfiberNonempty
  have hconflict : ∀ i,
      (normalizedConflictIndices D i).card ≤ threshold := by
    intro i
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      D hs hsHalf hCfinite hKT i
  obtain ⟨selected, hselected, hpair, hcard, _hmass⟩ :=
    exists_normalized_greedyRefinement D hconflict
  have hselectedKT : IsKatzTao (128 * C)
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).family.bodyFamily :=
    restrict_eighthNormalizedDatum_isKatzTao D hsHalf selected hKT
  have h128Cfinite : (128 : ENNReal) * C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  have hloss : ((threshold + 1 : Nat) : ENNReal) ≤
      480000 * (128 * C) + 2 := by
    exact fixedKatzTaoClosedLoss_coe_le_add_two h128Cfinite
  exact ⟨selected, hselected, hpair, hcard, hselectedKT, hloss⟩

/-- The selected set from the same literal conflict graph also obeys the
five-parameter thin-plank count when the genuine two affine-vector estimates
hold on that same `W` fibre. -/
theorem exists_selectedPlankFine_normalizedFresh_with_thinCount
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (s : NNReal) (hs : 0 < s) (hsHalf : s ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C
      (selectedPlankFineProxyDatum s e S B hrho label W).family.bodyFamily)
    (R : Real) (hR : 0 ≤ R)
    (ell : SelectedPlankFineIndex S W → Real)
    (hellNorm : ∀ i,
      ell i ≤ ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖)
    (hvector0 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤ ell i * ((s : Real) / 8))
    (hvector1 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤
        ell i * (R * ((s : Real) / 8)))
    (haScale : bucketShortA label ≤ s)
    (hbScale : (bucketShortB label : Real) ≤ R * (s : Real))
    (hsmall : s / 8 ≤ (1 / 100 : NNReal))
    (hthin :
      ((s / 8 : NNReal) : Real) ^ 2 +
        (R * ((s / 8 : NNReal) : Real)) ^ 2 ≤ (3 : Real) / 4) :
    let D := selectedPlankFineProxyDatum s e S B hrho label W
    let threshold := Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)
    ∃ selected : Finset (SelectedPlankFineIndex S W),
      selected.Nonempty ∧
      Set.Pairwise (selected : Set (SelectedPlankFineIndex S W))
        (fun i j => EssentiallyDistinct
          ((eighthNormalizedDatum D).family.tubes i)
          ((eighthNormalizedDatum D).family.tubes j)) ∧
      (Fintype.card (SelectedPlankFineIndex S W) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      ((threshold + 1 : Nat) : ENNReal) ≤ 480000 * (128 * C) + 2 ∧
      selected.card ≤ thinPlankFivePackingNatCap (3 * R) := by
  dsimp only
  obtain ⟨selected, hselected, hpair, hcard, hselectedKT, hloss⟩ :=
    exists_selectedPlankFine_normalizedFresh_of_isKatzTao
      e S B hrho label W s hs hsHalf hCfinite hKT
  refine ⟨selected, hselected, hpair, hcard, hselectedKT, hloss, ?_⟩
  exact
    normalizedFreshSelectedPlankFine_card_le_fiveParameterCap_of_pairwise
      e S B hrho label hplank W s hs selected hpair R hR ell hellNorm
        hvector0 hvector1 haScale hbScale hsmall hthin

#print axioms exists_selectedPlankFine_normalizedFresh_of_isKatzTao
#print axioms exists_selectedPlankFine_normalizedFresh_with_thinCount

end
end Family8SelectedParentPlankFineProxyFreshSelectionV1
