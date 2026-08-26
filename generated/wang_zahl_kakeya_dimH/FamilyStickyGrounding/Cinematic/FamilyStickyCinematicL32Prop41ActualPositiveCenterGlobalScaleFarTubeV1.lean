import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GlobalScaleSelectedHighPairBridgeV1
import FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41ActualPositiveCenterGlobalScaleFarTubeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41GlobalScaleSelectedHighPairBridgeV1
open FamilyStickyCinematicL32Prop41HighPairCenterCoefficientSelectionBridgeV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyPyzActualPositiveCenterHighPairCarrierV1

noncomputable section

universe u v

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# The exact missing global-scale packing bridge for a positive-centre payload

The `E₂` label gives a literal lower bound for the active fibre at the
payload point.  If that fibre is at least twice a same-`globalScale`
near-coefficient cap, greedy coefficient selection retains two tubes.  They
are genuinely `globalScale`-separated, so one endpoint is at least
`globalScale / 2` from any prescribed centre.

The same-scale cap is intentionally explicit.  The cap currently available
from the ambient extremal input is at the smaller tube radius and cannot be
monotonically promoted to `globalScale`.
-/

/-- An `E₂` degree lower bound exceeding twice the honest same-scale packing
cap produces two selected active tubes at literal `globalScale` separation. -/
theorem exists_payload_globalScale_selected_pair_of_sameScaleCap
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (hradius : 0 < radius) (hglobalScale : 0 < globalScale)
    {multiplicity : Nat} (hmultiplicity : 0 < multiplicity)
    (hdegree :
      2 * multiplicity <= pyzE2DegreeLower payload.finalLabel)
    (hpair :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      Set.Pairwise (Y1.activeAtPoint payload.q : Set iota) (fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j)))
    (hactiveCap :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      let active := Y1.activeAtPoint payload.q
      forall center,
        center ∈ selectedTubes (activeTubeImage fine active) globalScale ->
        (activeNearCoefficientIndices fine active center globalScale).card <=
          multiplicity) :
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
    let active := Y1.activeAtPoint payload.q
    exists T,
      T ∈ selectedTubes (activeTubeImage fine active) globalScale ∧
      exists U,
        U ∈ selectedTubes (activeTubeImage fine active) globalScale ∧
        T ≠ U ∧ globalScale <= tubePairCoefficientDistance T U := by
  dsimp only
  let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
    outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
  let active := Y1.activeAtPoint payload.q
  have hactiveLower : pyzE2DegreeLower payload.finalLabel <= active.card := by
    simpa only [Y1, active] using
      degreeLower_le_payload_active_card mu base hbase fine physical f f1 f2
        outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent payload
  have hlarge : 2 * multiplicity <= active.card :=
    hdegree.trans hactiveLower
  have hpair' : Set.Pairwise (active : Set iota) (fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j)) := by
    simpa only [Y1, active] using hpair
  have hactiveCap' : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) globalScale ->
      (activeNearCoefficientIndices fine active center globalScale).card <=
        multiplicity := by
    simpa only [Y1, active] using hactiveCap
  have htwo : 2 <=
      (selectedTubes (activeTubeImage fine active) globalScale).card :=
    two_le_selectedTubes_card_at_scale_of_active_cap fine active hradius hpair'
      hglobalScale hmultiplicity hlarge hactiveCap'
  have hone : 1 <
      (selectedTubes (activeTubeImage fine active) globalScale).card :=
    (by omega)
  obtain ⟨T, hT, U, hU, hTU⟩ := Finset.one_lt_card.mp hone
  have hlower : globalScale <= tubePairCoefficientDistance T U := by
    rw [tubePairCoefficientDistance_eq_projected]
    exact selectedTubes_pairwise_separated (activeTubeImage fine active)
      globalScale T hT U hU hTU
  exact ⟨T, hT, U, hU, hTU, hlower⟩

/-- The selected pair above yields an actual active index whose tube is
`globalScale / 2`-far from any prescribed centre tube. -/
theorem exists_payload_active_halfFar_from_center_of_sameScaleCap
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real)
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (hradius : 0 < radius) (hglobalScale : 0 < globalScale)
    {multiplicity : Nat} (hmultiplicity : 0 < multiplicity)
    (hdegree :
      2 * multiplicity <= pyzE2DegreeLower payload.finalLabel)
    (hpair :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      Set.Pairwise (Y1.activeAtPoint payload.q : Set iota) (fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j)))
    (hactiveCap :
      let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
        outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
        payload.tangencyLabel
      let active := Y1.activeAtPoint payload.q
      forall center,
        center ∈ selectedTubes (activeTubeImage fine active) globalScale ->
        (activeNearCoefficientIndices fine active center globalScale).card <=
          multiplicity)
    (center : Tube radius) :
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
    exists i, i ∈ Y1.activeAtPoint payload.q ∧
      globalScale / 2 <=
        tubePairCoefficientDistance (fine.tubes i) center := by
  dsimp only
  let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
    outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      payload.tangencyLabel
  let active := Y1.activeAtPoint payload.q
  obtain ⟨T, hT, U, hU, hTU, hlower⟩ :=
    exists_payload_globalScale_selected_pair_of_sameScaleCap mu base hbase
      fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter tangencyExponent payload hradius hglobalScale
      hmultiplicity hdegree hpair hactiveCap
  have hTImage : T ∈ activeTubeImage fine active :=
    selectedTubes_subset (activeTubeImage fine active) globalScale hT
  have hUImage : U ∈ activeTubeImage fine active :=
    selectedTubes_subset (activeTubeImage fine active) globalScale hU
  obtain ⟨i, hi, hTEq⟩ :=
    (mem_activeTubeImage_iff fine active T).mp hTImage
  obtain ⟨j, hj, hUEq⟩ :=
    (mem_activeTubeImage_iff fine active U).mp hUImage
  have hfar := pairCoefficientLower_forces_one_halfFar_from_center
    T U center hlower
  rcases hfar with hTFar | hUFar
  · rw [← hTEq] at hTFar
    exact ⟨i, by simpa only [Y1, active] using hi, hTFar⟩
  · rw [← hUEq] at hUFar
    exact ⟨j, by simpa only [Y1, active] using hj, hUFar⟩

/-!
The following finite example records why membership of a large scale in the
critical carrier does not by itself solve the retained-family problem.  The
carrier witnesses the scale in the source family, while an arbitrary
nonempty retained subfamily can discard one endpoint.
-/

def sourceRetentionToyDistance (x y : Fin 2) : Real :=
  if x = y then 0 else 1

theorem criticalCarrier_source_pair_need_not_survive_retention :
    let family : Finset (Fin 2) := Finset.univ
    let retained : Finset (Fin 2) := {0}
    let distance := sourceRetentionToyDistance
    (1 : Real) ∈ finiteCriticalScaleCarrier family distance (1 / 4) 1 ∧
      (1 / 2 : Real) < 1 ∧
      retained ⊆ family ∧
      (exists T, T ∈ family ∧ exists U, U ∈ family ∧
        T ≠ U ∧ distance T U = 1) ∧
      not (exists T, T ∈ retained ∧ exists U, U ∈ retained ∧ T ≠ U) := by
  norm_num [finiteCriticalScaleCarrier, sourceRetentionToyDistance]

#print axioms exists_payload_globalScale_selected_pair_of_sameScaleCap
#print axioms exists_payload_active_halfFar_from_center_of_sameScaleCap
#print axioms criticalCarrier_source_pair_need_not_survive_retention

end

end FamilyStickyCinematicL32Prop41ActualPositiveCenterGlobalScaleFarTubeV1
