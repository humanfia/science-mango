import FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
import FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1

noncomputable section

/-!
# Ambient-normalized actual Tube family for the norm-first selection

The generic measurable-incidence selection asks for a family attached to
every finite pattern, including patterns which never arise geometrically.
We therefore intersect the pattern with the literal ambient index family.
On every actual active pattern this changes nothing, while making ambient
containment automatic rather than an external callback.
-/

universe u v

/-- Image monotonicity for literal indexed tube families. -/
theorem activeTubeImage_mono
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) {active ambient : Finset iota}
    (hactive : active ⊆ ambient) :
    activeTubeImage fine active ⊆ activeTubeImage fine ambient := by
  intro T hT
  obtain ⟨i, hi, rfl⟩ :=
    (mem_activeTubeImage_iff fine active T).mp hT
  exact (mem_activeTubeImage_iff fine ambient (fine.tubes i)).mpr
    ⟨i, hactive hi, rfl⟩

/-- The actual critical tube family, normalized to one fixed ambient family. -/
noncomputable def actualProjectedAmbientCriticalFamily
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (ambient active : Finset iota) :
    Finset (Tube delta) :=
  actualProjectedCriticalFamily fine (active ∩ ambient)

/-- Every normalized critical family lies in the fixed concrete ambient
tube image. -/
theorem actualProjectedAmbientCriticalFamily_subset
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (ambient active : Finset iota) :
    actualProjectedAmbientCriticalFamily fine ambient active ⊆
      activeTubeImage fine ambient := by
  exact (selectedTubes_subset
      (activeTubeImage fine (active ∩ ambient)) (delta : Real)).trans
    (activeTubeImage_mono fine (by
      intro i hi
      exact (Finset.mem_inter.mp hi).2))

/-- Ambient normalization is definitionally harmless on an actual active
subfamily. -/
theorem actualProjectedAmbientCriticalFamily_eq_of_subset
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (ambient active : Finset iota)
    (hactive : active ⊆ ambient) :
    actualProjectedAmbientCriticalFamily fine ambient active =
      actualProjectedCriticalFamily fine active := by
  rw [actualProjectedAmbientCriticalFamily,
    Finset.inter_eq_left.mpr hactive]

/-- Actual incidence patterns are already ambient, so the normalized family
is exactly the original critical family. -/
theorem actualProjectedAmbientCriticalFamily_eq_activeAtPoint
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota) (x : point) :
    actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint x) =
      actualProjectedCriticalFamily fine (physical.activeAtPoint x) := by
  exact actualProjectedAmbientCriticalFamily_eq_of_subset fine
    physical.ambient (physical.activeAtPoint x)
    (finiteIncidenceActiveAtPoint_subset physical.ambient
      (fun i x => x ∈ physical.carrier i) x)

/-- The existing multiplicity/near-coefficient theorem supplies the needed
nonemptiness after ambient normalization. -/
theorem actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    {lower upper multiplicity : Nat}
    (hdelta : 0 < delta) (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hpair : ∀ x, x ∈ physical.multiplicityBand lower upper →
      Set.Pairwise (physical.activeAtPoint x : Set iota) fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hactiveCap : ∀ x, x ∈ physical.multiplicityBand lower upper →
      ∀ center,
        center ∈ actualProjectedCriticalFamily fine
          (physical.activeAtPoint x) →
        (activeNearCoefficientIndices fine (physical.activeAtPoint x) center
          (delta : Real)).card ≤ multiplicity) :
    ∀ x, x ∈ physical.multiplicityBand lower upper →
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint x)).Nonempty := by
  intro x hx
  rw [actualProjectedAmbientCriticalFamily_eq_activeAtPoint fine physical x]
  exact actualProjectedCriticalFamily_nonempty_on_multiplicityBand fine
    physical hdelta hmultiplicity hlower hpair hactiveCap x hx

#print axioms activeTubeImage_mono
#print axioms actualProjectedAmbientCriticalFamily
#print axioms actualProjectedAmbientCriticalFamily_subset
#print axioms actualProjectedAmbientCriticalFamily_eq_activeAtPoint
#print axioms actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand

end

end FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
