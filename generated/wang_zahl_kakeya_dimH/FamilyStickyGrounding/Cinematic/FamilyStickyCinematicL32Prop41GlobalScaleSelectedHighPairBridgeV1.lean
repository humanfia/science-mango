import FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41HighPairCenterCoefficientSelectionBridgeV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41GlobalScaleSelectedHighPairBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41HighPairCenterCoefficientSelectionBridgeV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyPyzActualPositiveCenterHighPairCarrierV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# A global-scale selected active pair

Applying `selectedTubes` at the literal scale `tGlobal` makes every distinct
canonical pair `tGlobal`-separated.  The metric half-distance bridge then
selects an active index at distance at least `tGlobal / 2` from any prescribed
centre.

The final two lemmas isolate the exact cardinal input needed to ensure that
this selected family contains a pair: a near-fibre cap at the same scale
`tGlobal`.  A cap available only at the smaller tube radius is not silently
promoted to this premise.
-/

/-- Every canonical pair in a `scale`-selected tube family has the literal
reduced coefficient lower bound `scale`. -/
theorem selected_orientedFirstGenerationPair_reducedCoefficientLower
    {radius : NNReal} (family : Finset (Tube radius)) (scale : Real)
    (curves : Finset (Tube radius))
    (hcurves : curves = selectedTubes family scale)
    (p : FirstGenerationCurvePair curves) :
    let orientation := canonicalFirstGenerationPairOrientation curves p
    scale <= tubePairCoefficientDistance
      (orientation.first : Tube radius)
      (orientation.second : Tube radius) := by
  let orientation := canonicalFirstGenerationPairOrientation curves p
  change scale <= tubePairCoefficientDistance
    (orientation.first : Tube radius) (orientation.second : Tube radius)
  have hfirstSelected : (orientation.first : Tube radius) ∈
      selectedTubes family scale := by
    rw [← hcurves]
    exact orientation.first.property
  have hsecondSelected : (orientation.second : Tube radius) ∈
      selectedTubes family scale := by
    rw [← hcurves]
    exact orientation.second.property
  have hne : (orientation.first : Tube radius) ≠
      (orientation.second : Tube radius) := by
    intro heq
    apply orientation.first_ne_second
    exact Subtype.ext heq
  rw [tubePairCoefficientDistance_eq_projected]
  exact selectedTubes_pairwise_separated family scale
    (orientation.first : Tube radius) hfirstSelected
    (orientation.second : Tube radius) hsecondSelected hne

/-- A canonical pair selected at `scale` from an active tube image yields an
actual active index that is `scale / 2`-far from the prescribed centre. -/
theorem selectedActive_orientedFirstGenerationPair_exists_halfFar_index
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (active : Finset iota)
    (center : Tube radius) (scale : Real)
    (curves : Finset (Tube radius))
    (hcurves : curves = selectedTubes (activeTubeImage fine active) scale)
    (p : FirstGenerationCurvePair curves) :
    exists i, i ∈ active ∧
      scale / 2 <= tubePairCoefficientDistance (fine.tubes i) center := by
  let orientation := canonicalFirstGenerationPairOrientation curves p
  have hfirstSelected : (orientation.first : Tube radius) ∈
      selectedTubes (activeTubeImage fine active) scale := by
    rw [← hcurves]
    exact orientation.first.property
  have hsecondSelected : (orientation.second : Tube radius) ∈
      selectedTubes (activeTubeImage fine active) scale := by
    rw [← hcurves]
    exact orientation.second.property
  have hfirstImage : (orientation.first : Tube radius) ∈
      activeTubeImage fine active :=
    selectedTubes_subset (activeTubeImage fine active) scale hfirstSelected
  have hsecondImage : (orientation.second : Tube radius) ∈
      activeTubeImage fine active :=
    selectedTubes_subset (activeTubeImage fine active) scale hsecondSelected
  obtain ⟨i, hi, hfirstEq⟩ :=
    (mem_activeTubeImage_iff fine active
      (orientation.first : Tube radius)).mp hfirstImage
  obtain ⟨j, hj, hsecondEq⟩ :=
    (mem_activeTubeImage_iff fine active
      (orientation.second : Tube radius)).mp hsecondImage
  have hlower := selected_orientedFirstGenerationPair_reducedCoefficientLower
    (activeTubeImage fine active) scale curves hcurves p
  have hfar := pairCoefficientLower_forces_one_halfFar_from_center
    (orientation.first : Tube radius) (orientation.second : Tube radius)
      center hlower
  rcases hfar with hfirstFar | hsecondFar
  · rw [← hfirstEq] at hfirstFar
    exact ⟨i, hi, hfirstFar⟩
  · rw [← hsecondEq] at hsecondFar
    exact ⟨j, hj, hsecondFar⟩

/-- Indexed cardinal retention for `selectedTubes` at an arbitrary positive
coefficient scale.  The previously tracked indexed wrapper specializes this
statement to the tube radius. -/
theorem active_card_le_multiplicity_mul_selectedTubes_card_at_scale
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (active : Finset iota)
    (hradius : 0 < radius)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} (hscale : 0 < scale) (multiplicity : Nat)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card <=
        multiplicity) :
    active.card <= multiplicity *
      (selectedTubes (activeTubeImage fine active) scale).card := by
  have hconcreteCap :=
    concrete_nearCap_of_activeNearCoefficientIndices_cap
      fine active hradius hpair scale multiplicity hactiveCap
  have hretention := family_card_le_mul_selectedTubes_card_of_near_cap
    (activeTubeImage fine active) hscale multiplicity hconcreteCap
  rw [activeTubeImage_card fine active hradius hpair] at hretention
  exact hretention

/-- If the active fibre contains at least twice the same-scale near-fibre
cap, the global-scale selected family contains two distinct tubes. -/
theorem two_le_selectedTubes_card_at_scale_of_active_cap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (active : Finset iota)
    (hradius : 0 < radius)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} (hscale : 0 < scale) {multiplicity : Nat}
    (hmultiplicity : 0 < multiplicity)
    (hlarge : 2 * multiplicity <= active.card)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card <=
        multiplicity) :
    2 <= (selectedTubes (activeTubeImage fine active) scale).card := by
  have hretention :=
    active_card_le_multiplicity_mul_selectedTubes_card_at_scale
      fine active hradius hpair hscale multiplicity hactiveCap
  have hmul : 2 * multiplicity <= multiplicity *
      (selectedTubes (activeTubeImage fine active) scale).card :=
    hlarge.trans hretention
  rw [Nat.mul_comm 2 multiplicity] at hmul
  exact Nat.le_of_mul_le_mul_left hmul hmultiplicity

#print axioms selected_orientedFirstGenerationPair_reducedCoefficientLower
#print axioms selectedActive_orientedFirstGenerationPair_exists_halfFar_index
#print axioms active_card_le_multiplicity_mul_selectedTubes_card_at_scale
#print axioms two_le_selectedTubes_card_at_scale_of_active_cap

end

end FamilyStickyCinematicL32Prop41GlobalScaleSelectedHighPairBridgeV1
