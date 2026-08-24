import FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
import FamilyStickyCinematicL32Lemma57TubeCoefficientDedupV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Lemma57EssentiallyDistinctCoefficientFiberV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Lemma57TubeCoefficientDedupV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

/-!
# Transport of coefficient fibres back to active tube indices

The project geometry is indexed, whereas the cinematic finite theorem uses a
`Finset Tube`.  On a positive-radius essentially-distinct active family, the
actual tube map is injective.  Therefore filtering the concrete tube image by
a coefficient ball has exactly the same cardinality as filtering the active
indices by the pulled-back coefficient ball.
-/

/-- Active indices whose actual tubes lie in one reduced-coefficient ball. -/
def activeNearCoefficientIndices
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (center : Tube delta) (scale : Real) : Finset iota :=
  active.filter fun i =>
    tubePairCoefficientDistance (fine.tubes i) center < scale
/-- Concrete tubes carried by the active near-coefficient indices, with the
classical equality instance hidden behind a noncomputable definition. -/
noncomputable def activeNearTubeImage
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (center : Tube delta) (scale : Real) : Finset (Tube delta) := by
  classical
  exact (activeNearCoefficientIndices fine active center scale).image
    fine.tubes


/-- Filtering the concrete tube image is literally the image of the
corresponding filtered active indices. -/
theorem activeTubeImage_filter_near_eq_image
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (center : Tube delta) (scale : Real) :
    (activeTubeImage fine active).filter (fun T =>
      tubePairCoefficientDistance T center < scale) =
      activeNearTubeImage fine active center scale := by
  classical
  ext T
  simp only [activeTubeImage, activeNearTubeImage, activeNearCoefficientIndices,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hnear⟩
    exact ⟨i, ⟨hi, hnear⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hnear⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, hnear⟩

/-- Positive-radius essential distinctness makes the two coefficient fibres
equinumerous. -/
theorem card_activeTubeImage_filter_near_eq_activeNearCoefficientIndices
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (center : Tube delta) (scale : Real) :
    ((activeTubeImage fine active).filter (fun T =>
      tubePairCoefficientDistance T center < scale)).card =
      (activeNearCoefficientIndices fine active center scale).card := by
  classical
  rw [activeTubeImage_filter_near_eq_image]
  change ((activeNearCoefficientIndices fine active center scale).image
    fine.tubes).card = _
  apply Finset.card_image_iff.mpr
  intro i hi j hj htube
  have hiActive : i ∈ active :=
    (Finset.mem_filter.mp hi).1
  have hjActive : j ∈ active :=
    (Finset.mem_filter.mp hj).1
  exact tubes_injectiveOn_active_of_essentiallyDistinct fine active
    hdelta hpair hiActive hjActive htube

/-- An indexed local coefficient-fibre cap supplies exactly the concrete
near-cap premise consumed by maximal coefficient deduplication. -/
theorem concrete_nearCap_of_activeNearCoefficientIndices_cap
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (scale : Real) (multiplicity : Nat)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card <=
        multiplicity) :
    forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      ((activeTubeImage fine active).filter fun T =>
        tubePairCoefficientDistance T center < scale).card <=
          multiplicity := by
  intro center hcenter
  rw [card_activeTubeImage_filter_near_eq_activeNearCoefficientIndices
    fine active hdelta hpair center scale]
  exact hactiveCap center hcenter

#print axioms activeTubeImage_filter_near_eq_image
#print axioms card_activeTubeImage_filter_near_eq_activeNearCoefficientIndices
#print axioms concrete_nearCap_of_activeNearCoefficientIndices_cap

end


end FamilyStickyCinematicL32Lemma57EssentiallyDistinctCoefficientFiberV1
